/**
 * The write of a value to the canonical value, for the marshaller `native`. The module imports no
 * interpreter, so a key of a table entry with no codec is written with no codec layer in the bundle.
 */
import type { AttributeValue } from './attribute'
import {
    carrying,
    DynamoNumber,
    isNumeral,
    memberOf,
    tooDeeplyNested,
} from './attribute'
import type { native } from './native'
import type { Result } from './result'
import { andThen, CodecError, every, everyEntry } from './result'
import { rendered } from './value'

const BINARY = new Set([
    'ArrayBuffer',
    'Blob',
    'Buffer',
    'DataView',
    'File',
    'Int8Array',
    'Uint8Array',
    'Uint8ClampedArray',
    'Int16Array',
    'Uint16Array',
    'Int32Array',
    'Uint32Array',
    'Float32Array',
    'Float64Array',
    'BigInt64Array',
    'BigUint64Array',
])

const isBinaryValue = (value: unknown): boolean =>
    BINARY.has(value?.constructor?.name as string)

/**
 * The refusal of a number outside the safe range, or `undefined`. `shown` is the number as the SDK
 * prints it, and `asNumber` is what the range test reads: the SDK reads a `bigint` as a number for
 * the test and prints its digits.
 */
const outsideSafeRange = (
    shown: number | bigint | string,
    asNumber: number,
    options: native.Options,
): CodecError | undefined => {
    if (options.allowImpreciseNumbers) return undefined
    if (asNumber > Number.MAX_SAFE_INTEGER) {
        return new CodecError(
            `Number ${shown} is greater than Number.MAX_SAFE_INTEGER. Use DynamoNumber from rotorise.`,
        )
    }
    if (asNumber < Number.MIN_SAFE_INTEGER) {
        return new CodecError(
            `Number ${shown} is lesser than Number.MIN_SAFE_INTEGER. Use DynamoNumber from rotorise.`,
        )
    }
    return undefined
}

/**
 * A number as the codec writes it. The family of the set that holds the number decides the range
 * rule: a number first reads the safe range, and a bigint first or a `DynamoNumber` first writes
 * digits with no range and no special-value test, as the SDK does. `ranged` is that rule, and a
 * number outside a set is ranged.
 */
export const nativeNumber = (
    value: number | bigint,
    options: native.Options,
    ranged = true,
): Result<AttributeValue> => {
    if (typeof value === 'number' && ranged) {
        if (!Number.isFinite(value)) {
            return new CodecError(
                `Special numeric value ${value.toString()} is not allowed`,
            )
        }
        const unsafe = outsideSafeRange(value, value, options)
        if (unsafe) return unsafe
    }
    /**
     * **The gate the SDK does not have.** `Number.isFinite` and the safe range are its two checks,
     * and neither is `Carries('N')`: `5e-324` is finite, inside the safe range, and outside the
     * numerals — 38 significant digits and magnitude `1e-130 … 9.9…e125`. `convertToAttr` writes
     * `{ N: '5e-324' }` happily, and DynamoDB refuses the row.
     *
     * So this is a deliberate divergence from the SDK, in the direction of the store: `ran(e) ⊆ 𝔸`
     * is the obligation every term that writes an `N` carries, and `number`, `literal` and `opaque`
     * all gate on it. A marshaller that skipped it would be the one place in the package that
     * certifies an attribute the model has no point for. `deviations.writeNumber` changes how a
     * number becomes digits, and the canonical write refuses digits that are no numeral.
     */
    const digits = value.toString()
    return isNumeral(digits)
        ? carrying('N', digits)
        : new CodecError(
              `${digits} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125`,
          )
}

/**
 * The bytes of a binary value, as the `Uint8Array` that the store returns for them.
 *
 * The SDK stores a view of any element type, an `ArrayBuffer` and a `DataView` as `B`. The canonical
 * write holds a `Uint8Array`, so the view becomes the `Uint8Array` over the same bytes. A `Blob`
 * and a `File` hold their bytes behind a promise, and a synchronous write cannot read them.
 */
const bytesOf = (value: unknown): Result<Uint8Array> => {
    if (value instanceof Uint8Array) return value
    if (ArrayBuffer.isView(value)) {
        return new Uint8Array(value.buffer, value.byteOffset, value.byteLength)
    }
    if (value instanceof ArrayBuffer) return new Uint8Array(value)
    // a `Blob` and a `File` read their bytes by a promise. Any other value that reaches here only
    // names a binary constructor
    if (
        typeof (value as { arrayBuffer?: unknown })?.arrayBuffer === 'function'
    ) {
        return new CodecError(
            `${rendered(value)} holds its bytes behind a promise, so a synchronous write cannot read them`,
        )
    }
    return new CodecError(
        `${rendered(value)} is no binary value: its constructor is named '${(value as { constructor: { name: string } }).constructor.name}', and a write reads the bytes of a view or an ArrayBuffer`,
    )
}

/**
 * Whether a member of a list, a map or a set is kept: the SDK drops a function, and drops `undefined`
 * where `removeUndefinedValues` is set. The list, the `Map` and the object read this one rule.
 */
const keepsEntry = (held: unknown, options: native.Options): boolean =>
    typeof held !== 'function' &&
    (held !== undefined || !options.removeUndefinedValues)

/** The entries of a record that the SDK keeps, as {@link keepsEntry} reads them. */
const keptEntries = (
    record: Record<string, unknown>,
    options: native.Options,
): Record<string, unknown> =>
    Object.fromEntries(
        Object.entries(record).filter(([, held]) => keepsEntry(held, options)),
    )

/** The enumerable properties of a value, own and inherited, as a `for…in` reads them. */
const enumerable = (
    value: Record<string, unknown>,
): Record<string, unknown> => {
    const entries: [string, unknown][] = []
    for (const key in value) entries.push([key, value[key]])
    return Object.fromEntries(entries)
}

/** One member of a set, written by the writer that `kind` names. */
const setMember = (
    member: unknown,
    kind: 'numberValue' | 'number' | 'bigint' | 'string' | 'binary' | 'other',
    write: (value: number | bigint, ranged?: boolean) => Result<DynamoNumber>,
    options: native.Options,
): Result<unknown> => {
    const named = member?.constructor?.name
    const primitive =
        named === 'Number' || named === 'String'
            ? (member as number | string).valueOf()
            : member
    if (kind === 'binary')
        return isBinaryValue(member) ? bytesOf(member) : member
    if (kind === 'string')
        return typeof primitive === 'string' ? primitive : member
    if (kind === 'other') return member
    if (member instanceof DynamoNumber) {
        if (kind !== 'number') return member
        return (
            outsideSafeRange(member.digits, Number(member.digits), options) ??
            member
        )
    }
    if (typeof primitive !== 'number' && typeof primitive !== 'bigint') {
        return member
    }
    if (kind === 'number') {
        return typeof primitive === 'bigint'
            ? (outsideSafeRange(primitive, Number(primitive), options) ??
                  write(primitive))
            : write(primitive)
    }
    // a `DynamoNumber` or a bigint first writes the digits of each member, with no range
    return write(primitive, false)
}

/** The writer that the SDK picks from the first member of a set. */
const setKind = (first: unknown) =>
    first instanceof DynamoNumber
        ? 'numberValue'
        : typeof first === 'number'
          ? 'number'
          : typeof first === 'bigint'
            ? 'bigint'
            : typeof first === 'string'
              ? 'string'
              : isBinaryValue(first)
                ? 'binary'
                : 'other'

/**
 * A value, as `@aws-sdk/util-dynamodb`'s `convertToAttr` reads it, handed to the canonical write.
 *
 * Ported from that implementation rather than from its documentation, branch for branch — including
 * the order the branches are tried in, which is observable: an `Array` is a list before it is an
 * object, and a `Map` is a map before a class instance is refused.
 *
 * **Value to value, and no attribute.** The result is a value that the canonical `opaque` writes: a
 * number is a `DynamoNumber`, a `Map` and a class instance are a plain object, a binary view is a
 * `Uint8Array`, and an empty value that `convertEmptyValues` reaches is `null`. The canonical
 * write owns the attribute and the rule of a stored set, so a set with two kinds of member and a set
 * that repeats a member are its refusals, with its text. This function refuses the empty set itself,
 * with the text of the SDK.
 */
export const toCanonical = (
    value: unknown,
    options: native.Options,
    write: (value: number | bigint, ranged?: boolean) => Result<DynamoNumber>,
    /**
     * How many `L`/`M` this value already sits inside.
     *
     * The walk stops at the bound and hands the value on unchanged, so a cyclic value reaches the
     * canonical write, which refuses it at the same bound. The SDK's marshaller has no such check
     * and will hand DynamoDB a row it rejects: a deliberate divergence, in the direction of the
     * store.
     */
    enclosing = 0,
): Result<unknown> => {
    if (value === undefined) {
        return new CodecError(
            'Pass options.removeUndefinedValues=true to remove undefined values from map/array/set.',
        )
    }
    if (value === null) return null

    if (Array.isArray(value)) {
        if (tooDeeplyNested(enclosing)) return value
        const kept = value.filter((item) => keepsEntry(item, options))
        return every(kept, (item) =>
            toCanonical(item, options, write, enclosing + 1),
        )
    }

    const named = value?.constructor?.name
    if (named === 'Set') {
        const members = options.removeUndefinedValues
            ? [...(value as ReadonlySet<unknown>)].filter(
                  (member) => member !== undefined,
              )
            : [...(value as ReadonlySet<unknown>)]
        if (!options.removeUndefinedValues && members.includes(undefined)) {
            return new CodecError(
                'Pass options.removeUndefinedValues=true to remove undefined values from map/array/set.',
            )
        }
        if (members.length === 0) {
            return options.convertEmptyValues
                ? null
                : new CodecError(
                      'Pass a non-empty set, or options.convertEmptyValues=true.',
                  )
        }
        const kind = setKind(members[0])
        return andThen(
            every(members, (member) => setMember(member, kind, write, options)),
            (written) => new Set(written),
        )
    }
    if (named === 'Map') {
        if (tooDeeplyNested(enclosing)) return value
        return everyEntry(
            keptEntries(
                Object.fromEntries(value as Map<string, unknown>),
                options,
            ),
            (held) => toCanonical(held, options, write, enclosing + 1),
        )
    }

    // before the class-instance branch, as in the SDK, where `NumberValue` is a number and not a map
    if (value instanceof DynamoNumber) return value

    // the SDK tests `!data.constructor`, so a value whose constructor is a string or a nameless class
    // is no map unless `convertClassInstanceToMap` is set
    const isPlain =
        named === 'Object' || (!value.constructor && typeof value === 'object')
    if (isPlain) {
        if (tooDeeplyNested(enclosing)) return value
        // `for…in`, as the SDK does: enumerable *and* inherited, which is what makes
        // `convertClassInstanceToMap` reach a prototype's own accessors
        return everyEntry(
            keptEntries(enumerable(value as Record<string, unknown>), options),
            (held) => toCanonical(held, options, write, enclosing + 1),
        )
    }

    if (isBinaryValue(value)) {
        // the SDK tests `data.length`, which an `ArrayBuffer` and a `DataView` lack, so an empty one
        // writes `B`. A typed array and a `Buffer` have a length, and an empty one writes `NULL`
        return (value as { readonly length?: number }).length === 0 &&
            options.convertEmptyValues
            ? null
            : bytesOf(value)
    }
    // a boxed primitive is its primitive, by `constructor.name`, as the SDK reads it
    if (typeof value === 'boolean' || named === 'Boolean') {
        return value.valueOf()
    }
    if (typeof value === 'number' || typeof value === 'bigint') {
        return write(value)
    }
    if (named === 'Number') return write((value as number).valueOf())
    if (typeof value === 'string' || named === 'String') {
        const text = String(value)
        return text.length === 0 && options.convertEmptyValues ? null : text
    }
    // the last branch, as in the SDK: a binary view, a boolean, a number and a string are no class
    // instance
    if (options.convertClassInstanceToMap && typeof value === 'object') {
        if (tooDeeplyNested(enclosing)) return value
        return everyEntry(
            keptEntries(enumerable(value as Record<string, unknown>), options),
            (held) => toCanonical(held, options, write, enclosing + 1),
        )
    }
    return new CodecError(
        `Unsupported type passed: ${rendered(value)}. Pass options.convertClassInstanceToMap=true to marshall typeof object as map attribute.`,
    )
}

/**
 * The writer of a number, as the marshaller configures it: the writer of a caller where the caller
 * gives one, and the number of the port otherwise. The result is a `DynamoNumber`.
 */
export const numberWriter =
    (
        options: native.Options,
        writeNumber?: (value: number | bigint) => Result<AttributeValue>,
    ) =>
    (value: number | bigint, ranged = true): Result<DynamoNumber> =>
        andThen(
            writeNumber
                ? writeNumber(value)
                : nativeNumber(value, options, ranged),
            (written) =>
                memberOf(written) === 'N'
                    ? DynamoNumber.from(written.N as string)
                    : new CodecError(
                          'the number writer returned an attribute that is no N',
                      ),
        )

/**
 * The value that the canonical write stores for a key: a string, a `DynamoNumber` or the bytes of a
 * binary value. Any other value is no key, and gives `undefined`. The options are the defaults of
 * `native`, so the value is the one that `native.encode` stores for the key.
 */
export const keyValueOf = (
    value: unknown,
): string | DynamoNumber | Uint8Array | undefined => {
    const canonical = toCanonical(value, {}, numberWriter({}))
    return typeof canonical === 'string' ||
        canonical instanceof DynamoNumber ||
        canonical instanceof Uint8Array
        ? canonical
        : undefined
}
