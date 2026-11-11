/**
 * The marshaller the table was probably written with.
 *
 * A port of `@aws-sdk/util-dynamodb`'s `convertToAttr` / `convertToNative`, so a table written by
 * that marshaller can be read and written as the same stored data while the schema and key layers are
 * adopted around it. Its own entry point, because it is a migration aid rather than part of the library:
 *
 * ```ts
 * import { native } from 'rotorise/native'
 * import type { native } from 'rotorise/native'
 * ```
 *
 * Not the codec to reach for in new code — {@link opaque} refuses what this guesses at, which is
 * the point of declaring a schema — but the one that makes adopting the rest of this package a
 * change of shape rather than a change of data. Pair it with `checkAgainst` from
 * `rotorise/testing` to prove each attribute as it is replaced.
 *
 * Verified against the real SDK by two laws in `native.spec.ts`. The write law draws generated
 * values under every combination of the four options, and compares the write with `convertToAttr`.
 * On each value the two write the same stored data or both refuse. The read law compares the read
 * with `convertToNative` under the default options. The write law counts by name each deviation
 * below that its pool draws, **deviations, in the direction of the store**. The pool draws no
 * `Blob` and no key `__proto__`, and a named test pins each of the two.
 *
 * **The port writes the stored data of the SDK, and not its bytes.** The SDK writes the form that
 * the caller holds, and the store returns a normal form. The port writes the normal form, through
 * the canonical `opaque`. Three classes of request bytes differ: the members of a set, which the
 * canonical write sorts; the spelling of a numeral, so `1e30` is `1000000000000000000000000000000`;
 * and a typed array, an `ArrayBuffer` or a `DataView`, which is the `Uint8Array` of the same bytes.
 *
 * **Each half gates on the predicate of the canonical codec.** `Carries('N')` is the numerals, not
 * the finite doubles, and the SDK checks only the latter: it will marshal `1e300` and `5e-324` into
 * an `N` DynamoDB refuses, and unmarshal `{ N: '' }` as `0` and `{ N: '0x10' }` as `16`. The write
 * gates on `isNumeral` of the digits and then writes the digits in normal form. The read gates on
 * `isNumeral` and on the form that the store returns, so the value that the write produces always
 * passes the read. Both halves refuse an empty `SS`/`NS`/`BS`, a set that repeats a member and a set
 * with a member of another family than the first member (a string among numbers, or a number among
 * strings), where the SDK hands back an empty `Set` or writes the set. A set of numbers and bigints
 * follows the SDK: the first member picks the writer, so `Set([1n, 2 ** 60])` writes `NS` and
 * `Set([1, 2n ** 60n])` is refused as a number outside the safe range.
 *
 * **A `Blob` and a `File` are refused.** The SDK lists both as binary and writes a `B` that holds the
 * object. A synchronous write cannot read their bytes, which sit behind a promise, so the port
 * refuses, and `native.Encode<Blob>` is `never`.
 *
 * **A key named `__proto__` is an attribute.** DynamoDB stores the name. The SDK assigns the key
 * into a plain object, which sets a prototype, so its write drops the attribute with no refusal and
 * its read takes a prototype from the stored data. The port writes and reads the attribute.
 */

import type { ErrorMessage, show } from '../utils'
import type {
    AttributeValue,
    B,
    BOOL,
    BS,
    L,
    M,
    N,
    NS,
    NULL,
    S,
    SS,
} from './attribute'
import {
    carrying,
    DynamoNumber,
    isNumeral,
    memberOf,
    tooDeeplyNested,
} from './attribute'
import { codecOfTerm } from './capabilities'
import type { AttributeCodec, Result } from './codec'
import { andThen, CodecError, every, everyEntry } from './codec'
import { mapNumberLeaves, opaqueTerms } from './denote'
import type { HeldT, TermMark } from './term'
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
    BINARY.has(
        (value as { constructor?: { name?: string } })?.constructor
            ?.name as string,
    )

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
const nativeNumber = (
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
    const named = (member as { constructor?: { name?: string } })?.constructor
        ?.name
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
const toCanonical = (
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

    const named = (value as { constructor?: { name?: string } })?.constructor
        ?.name
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
        named === 'Object' ||
        (!(value as { constructor?: unknown }).constructor &&
            typeof value === 'object')
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
        return (value as boolean | boolean).valueOf()
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
 * A stored number, as `convertToNative` reads it — a `bigint` outside the safe range.
 *
 * **The canonical read has already parsed the digits.** `Number` reads far more than an `N`
 * carries: `''` and whitespace are `0`, `'0x10'` is `16`, `'abc'` is `NaN`, and the SDK hands it the
 * digits unchecked. Each is a value that `native.encode` refuses, which is **(C)** failing: the
 * pair's two halves would disagree about what an `N` holds. So the read refuses every `N` that is
 * not in the form the store returns, before this function runs, and `'1.0'` is refused because the
 * value read would write `'1'`. A caller's `readNumber` meets that same digit string, in normal form.
 */
const fromNativeNumber = (digits: string): Result<unknown> => {
    const asNumber = Number(digits)
    const wide =
        asNumber > Number.MAX_SAFE_INTEGER || asNumber < Number.MIN_SAFE_INTEGER
    if (!wide || !Number.isFinite(asNumber)) return asNumber
    try {
        return BigInt(digits)
    } catch {
        return new CodecError(
            `${digits} can't be converted to BigInt. Set options.wrapNumbers to get string value.`,
        )
    }
}

/**
 * The canonical value that the store holds, as the caller holds it: each `DynamoNumber` read by
 * `readNumber`, in a set, a list and a map.
 */
const toHeld = (
    read: unknown,
    readNumber: (digits: string) => Result<unknown>,
): Result<unknown> =>
    mapNumberLeaves(
        read,
        (stored) => readNumber(stored.digits),
        (members, walk) =>
            andThen(every([...members], walk), (held) => new Set(held)),
    )

/**
 * The term of `native`, in the type: a `held` over the universal sum, whose adapter is the port.
 * The adapter is a function that the term cannot read, so no term decides the null point, and the
 * type of `nullable` refuses `native` as the run time does.
 */
type NativeTerm = HeldT<['opaq'], ['opaq'], ['caller', 'native']>

/**
 * The AWS SDK's marshaller, as a codec.
 *
 * A port of `@aws-sdk/util-dynamodb`'s `convertToAttr` / `convertToNative`, so a table written by
 * that marshaller can be read and written as the same stored data while the schema and key layers
 * are adopted around it. Not the codec to reach for in new code — {@link opaque} refuses what this
 * guesses at, which is the point of declaring a schema — but the one that makes adopting the rest of
 * this package a change of shape rather than a change of data.
 *
 * **A `held` over the canonical `opaque`**, with the closures of this configuration as its tag. A
 * container that holds `native` reads that term, so `native` in an object writes and reads as
 * `native` alone, and two configurations are two adapters. `f` takes the caller's value to the
 * canonical value, and `g` takes the canonical value to the caller's.
 *
 * See {@link native.ItemEncode} for what it produces, as a type.
 */
const configured = (
    options: native.Options = {},
    deviations: native.Deviations = {},
): AttributeCodec<unknown> & TermMark<NativeTerm> => {
    // the caller's writer receives the number alone, and `ranged` reaches the port's own writer only
    const writeAttribute = (value: number | bigint, ranged?: boolean) =>
        deviations.writeNumber
            ? deviations.writeNumber(value)
            : nativeNumber(value, options, ranged)
    const write = (
        value: number | bigint,
        ranged = true,
    ): Result<DynamoNumber> =>
        andThen(writeAttribute(value, ranged), (written) =>
            memberOf(written) === 'N'
                ? DynamoNumber.from(written.N as string)
                : new CodecError(
                      'the number writer returned an attribute that is no N',
                  ),
        )
    const read = deviations.readNumber ?? fromNativeNumber
    return codecOfTerm<unknown, AttributeValue>({
        kind: 'held',
        inner: opaqueTerms.canonical,
        outer: opaqueTerms.canonical,
        f: (value: unknown) => toCanonical(value, options, write),
        g: (held: unknown) => toHeld(held, read),
        via: 'native',
    })
}

/**
 * The SDK's marshaller: a codec, and a way to configure one.
 *
 * One entry point with every parameter optional, rather than three. `native` *is* the marshaller
 * with the SDK's own defaults, so `native.encode(value)` needs no call; calling it returns one
 * configured differently, with some options or with some options and some deviations.
 *
 * ```ts
 * native.encode(value)                                  // the SDK's defaults
 * native({ convertEmptyValues: true }).encode(value)     // an option
 * native({}, { readNumber: (d) => d }).decode(stored)    // a deviation
 * ```
 *
 * Callable *and* a codec, which is what lets `native.encode` and {@link native.Encode} keep the
 * same name — the same shape `opaque` takes for its own policies.
 */
export const native: native.Codec &
    ((
        options?: native.Options,
        deviations?: native.Deviations,
    ) => native.Codec) = Object.assign(
    (options: native.Options = {}, deviations: native.Deviations = {}) =>
        configured(options, deviations),
    configured(),
)

/**
 * Everything else `native` is: its options, its deviations, and the shapes it writes and reads.
 *
 * A type-only namespace merged with the codec above, so `native.Encode<T>` sits beside
 * `native.encode(value)` and reads as the same pair. Non-instantiated — it declares no value — which
 * is what lets it share the name with a `const`, and `import type { native }` brings the types in
 * with no runtime import at all. `rotorise/native` therefore exports one name.
 *
 * **The options that change a shape are parameters; the two that cannot are named below.** A shape
 * that quietly described one configuration would be the worst thing here, because a team diffs
 * against it and migrates on the answer.
 *
 * | option | in the type |
 * | --- | --- |
 * | `convertEmptyValues` | **yes** — `Encode<string, { convertEmptyValues: true }>` is `S \| NULL`, because a type cannot see whether a string is empty. Exact where the type is a literal: `''` is `NULL` alone, `'PET'` is `S` |
 * | `removeUndefinedValues` | **yes, inside a list or set** — an element holding `undefined` is a refusal until the option drops it |
 * | `allowImpreciseNumbers` | no, and there is nothing to reflect: it decides whether a number is *refused*, not which member it reaches. `N` either way |
 * | `convertClassInstanceToMap` | no — a prototype is not visible to a type, so a class instance cannot be told from a plain object. The same limit {@link opaque.Encode} documents |
 * | `convertTopLevelContainer` | **as a type rather than a parameter.** It is an option of `marshall`, not of `convertToAttr`, and this is a codec — `encode` produces one attribute, which is what an attribute codec is. {@link native.Encode} is the wrapped reading (`convertToAttr`, and `marshall` with the option set); {@link native.ItemEncode} is the bare map (`marshall`'s default) |
 *
 * Of `unmarshallOptions`, `convertWithoutMapWrapper` is the same pairing read the other way —
 * {@link native.Decode} takes a wrapped attribute where {@link native.ItemDecode} takes a bare map —
 * and `wrapNumbers` is the `Numbers` parameter when given as a function, which is what
 * {@link native.Deviations.readNumber} is. As `true` it needs `NumberValue` from
 * `@aws-sdk/lib-dynamodb`, which this package will not depend on.
 *
 * Of the deviations, `readNumber` is that `Numbers` parameter, and `writeNumber` is not reflected for
 * the same reason as `allowImpreciseNumbers`.
 *
 * That is the whole option surface of both directions, accounted for.
 *
 * One place the shapes stay deliberately permissive: {@link native.ItemEncode} describes an optional
 * attribute as an optional key, which is the `removeUndefinedValues` reading, and the default
 * *refuses* a key present and holding `undefined`. A type cannot tell that from a key that is
 * absent, and absent is the common case — so the permissive reading is the useful one.
 */
export namespace native {
    /** The codec that `native` is, and that a call of `native` gives. */
    export interface Codec
        extends AttributeCodec<unknown>,
            TermMark<NativeTerm> {}

    export type Options = {
        /** Empty strings, sets and binary become `NULL` instead of failing or storing empty. */
        readonly convertEmptyValues?: boolean
        /** `undefined` inside a map, list or set is dropped instead of failing. */
        readonly removeUndefinedValues?: boolean
        /** A class instance is stored as `M` from its enumerable properties. */
        readonly convertClassInstanceToMap?: boolean
        /** A number outside the safe-integer range is stored rather than refused. */
        readonly allowImpreciseNumbers?: boolean
    }

    /**
     * Where a marshaller deliberately differs from the SDK's.
     *
     * Separate from {@link native.Options} on purpose: those are the SDK's own options and are checked
     * against its `marshallOptions`, so nothing can be invented there without the check failing. A
     * deviation is not an option the SDK has — it is a place a team's marshaller does something else,
     * and naming it here keeps the rest of the port shared rather than forked.
     *
     * The usual one is numbers. A marshaller that hands `N` back as a string keeps a decimal exact
     * where the SDK's would round it, and that single branch is the difference between two marshallers
     * writing the same bytes and reading them differently.
     *
     * They change the number type, and they do not change the numerals. The canonical `opaque` is
     * under the pair in both directions, so a `writeNumber` that returns a non-numeral is refused on
     * write, and a stored `N` that is no numeral is refused before `readNumber` sees it. A caller
     * migrating a table that holds such an `N` repairs the rows first.
     */
    export type Deviations = {
        /** How a stored `N` is read. The SDK's answer is a number, widening to `bigint`. */
        readonly readNumber?: (digits: string) => Result<unknown>
        /** How a number is written. The SDK's answer refuses anything a float cannot hold. */
        readonly writeNumber?: (
            value: number | bigint,
        ) => Result<AttributeValue>
    }

    /**
     * The attribute the SDK's marshaller stores a value as.
     *
     * The type-level half of {@link native}, following the same branches in the same order. What it
     * is *for* is the diff: put it beside {@link Encoded} for a codec and every place the two disagree
     * is a place adopting that codec changes the table.
     *
     * ```ts
     * type Now  = ItemEncode<Pet>        // what the marshaller writes today
     * type Next = Encoded<typeof petSpec>  // what the codec would write
     * ```
     *
     * `undefined` is not a member and never becomes one; an attribute that may be `undefined` is an
     * optional key of the map that holds it, which is where {@link ItemEncode} puts it.
     */
    export type Encode<
        T,
        Of extends Options = Record<never, never>,
    > = EncodeWith<
        T,
        Of['convertEmptyValues'] extends true ? true : false,
        Of['removeUndefinedValues'] extends true ? true : false
    >

    /**
     * The same, with the options already resolved to booleans.
     *
     * `Of['convertEmptyValues']` is an indexed access on a type parameter, which a conditional cannot
     * resolve until the parameter is concrete — so asking it at every node of a *recursive* type
     * defers and re-instantiates the whole chain per attribute. Asked once here and threaded as two
     * booleans, whole-project check time went from 4.8s to 1.2s.
     */
    type EncodeWith<T, Empties extends boolean, Drops extends boolean> = [
        T,
    ] extends [never]
        ? never
        : T extends null
          ? NULL
          : T extends boolean
            ? BOOL
            : T extends number | bigint | DynamoNumber | BoxedNumber
              ? N
              : T extends string | BoxedString
                ? OrNull<S, T, '', Empties>
                : T extends Promised
                  ? never
                  : T extends ArrayBufferView | ArrayBuffer
                    ? OrNull<B, unknown, never, Empties>
                    : T extends ReadonlySet<infer Member> & {
                            readonly get?: never
                        }
                      ? OrNull<
                            SetFamily<Dropped<Member, Drops>>,
                            unknown,
                            never,
                            Empties
                        >
                      : T extends readonly (infer Element)[]
                        ? Dropped<Element, Drops> extends infer Kept
                            ? [Kept] extends [never]
                                ? ErrorMessage<'[native] a list holds `undefined`, which is refused unless `removeUndefinedValues` is set'>
                                : L<
                                      EncodeWith<
                                          Exclude<Kept, Fn>,
                                          Empties,
                                          Drops
                                      >
                                  >
                            : never
                        : T extends object
                          ? M<ItemEncodeWith<MapAsRecord<T>, Empties, Drops>>
                          : never

    /**
     * A `Map` reads as the record of its values, which is how the marshaller writes it. A `Map`
     * satisfies `ReadonlySet` by structure, so the set branch refuses a type that has a `get`.
     */
    type MapAsRecord<T> = T extends ReadonlyMap<unknown, infer Value>
        ? { readonly [key: string]: Value }
        : T

    /**
     * A value that reads its bytes by a promise: a `Blob` and a `File`. No write is possible, so no
     * attribute. The type reads shape, and the run time reads the name of the constructor, which the
     * type cannot see. So only a class instance with the surface of a `Blob` counts as a `Blob` here.
     * One over-match remains: an object that carries all six members by hand is `never` in the type,
     * and the run time writes it as a map.
     */
    type Promised = {
        readonly size: number
        readonly type: string
        readonly arrayBuffer: () => Promise<ArrayBuffer>
        readonly slice: Fn
        readonly stream: Fn
        readonly text: () => Promise<string>
    }

    /**
     * The boxed primitives, which the marshaller writes as their primitive. The type reads them as the
     * interfaces `Number` and `String`, which a plain object does not satisfy. A boxed `Boolean` has
     * no row: the interface `Boolean` is `{ valueOf(): boolean }`, so a class with that method
     * would read as a `BOOL`, and the run time writes it as a map.
     */
    // biome-ignore lint/complexity/noBannedTypes: `Number` is the type of `new Number(1)`
    type BoxedNumber = Number
    // biome-ignore lint/complexity/noBannedTypes: `String` is the type of `new String('a')`
    type BoxedString = String

    /** A member that the marshaller drops from a map and from a list: a function. */
    type Fn = (...args: never[]) => unknown

    /**
     * The wire set of the members that a set holds, or `never` where the set is refused: a member
     * of two families, and a member that is `undefined` where nothing removes it.
     */
    type SetFamily<Member> = [Member] extends [never]
        ? never
        : (
                Member extends string
                    ? 'S'
                    : Member extends number | bigint | DynamoNumber
                      ? 'N'
                      : Member extends ArrayBufferView | ArrayBuffer
                        ? 'B'
                        : 'X'
            ) extends infer Family
          ? [Family] extends ['S']
              ? SS
              : [Family] extends ['N']
                ? NS
                : [Family] extends ['B']
                  ? BS
                  : never
          : never

    /**
     * The member, or `NULL` beside it where `convertEmptyValues` could reach.
     *
     * `Empty` is the type of the value that becomes `NULL` — `''` for a string, and `never` for a set
     * or binary, whose emptiness a type cannot see. So a `string` is `S | NULL`, a `''` is `NULL`
     * alone, a `'PET'` is `S`, and a set is always `SS | NULL` once the option is on. That union is
     * the point: it is what a team reading a shape needs to know may come back holding nothing.
     */
    type OrNull<
        Member,
        Value,
        Empty,
        Empties extends boolean,
    > = Empties extends true
        ? [Empty] extends [never]
            ? Member | NULL
            : Empty extends Value
              ? Value extends Empty
                  ? NULL
                  : Member | NULL
              : Member
        : Member

    /**
     * A list or set element with `undefined` removed, where the option removes it.
     *
     * `never` when the element is `undefined` and nothing removes it, which is what makes the branch
     * above a refusal rather than a list of nothing.
     */
    type Dropped<Element, Drops extends boolean> = [Element] extends [
        Exclude<Element, undefined>,
    ]
        ? Element
        : Drops extends true
          ? Exclude<Element, undefined>
          : never

    /**
     * The item the SDK's marshaller stores an entity as.
     *
     * `marshall(entity)` returns the attributes without the `M` around them, so this is the map itself.
     * An attribute the entity may not have is an optional key here, because that is what
     * `removeUndefinedValues` produces and what the table then holds.
     */
    export type ItemEncode<
        T,
        Of extends Options = Record<never, never>,
    > = ItemEncodeWith<
        T,
        Of['convertEmptyValues'] extends true ? true : false,
        Of['removeUndefinedValues'] extends true ? true : false
    >

    /** {@link ItemEncode}, with the options already resolved — see {@link EncodeWith}. */
    type ItemEncodeWith<
        T,
        Empties extends boolean,
        Drops extends boolean,
    > = show<
        {
            [K in keyof T as undefined extends T[K]
                ? never
                : [Extract<T[K], Fn>] extends [never]
                  ? K
                  : never]: EncodeWith<T[K], Empties, Drops>
        } & {
            [K in keyof T as undefined extends T[K]
                ? [Exclude<T[K], undefined | Fn>] extends [never]
                    ? never
                    : K
                : [Extract<T[K], Fn>] extends [never]
                  ? never
                  : [Exclude<T[K], Fn>] extends [never]
                    ? never
                    : K]?: EncodeWith<
                Exclude<T[K], undefined | Fn>,
                Empties,
                Drops
            >
        }
    >

    /**
     * What a marshaller hands back, given what the table holds.
     *
     * The other direction from {@link ItemEncode}: that says what an entity becomes in the table,
     * this says what a stored attribute becomes in memory. The pair is what makes a custom marshaller
     * describable — you can write down both halves and diff them against somebody else's.
     *
     * `Numbers` is the parameter because it is the branch marshallers actually disagree on. The SDK
     * reads `N` as a `number`, widening to `bigint` past the safe range; a marshaller that keeps the
     * digits reads it as a `string`, which is exact and is what a price has to be. Same bytes, two
     * readings — and with this the difference is a type you can put in a diff rather than a surprise in
     * production.
     *
     * ```ts
     * type Theirs = Decode<M<{ amount: N }>>            // { amount: number | bigint }
     * type Ours   = Decode<M<{ amount: N }>, string>    // { amount: string }
     * ```
     */
    export type Decode<A, Numbers = number | bigint> = A extends NULL
        ? null
        : A extends BOOL
          ? boolean
          : A extends N
            ? Numbers
            : A extends S
              ? string
              : A extends B
                ? Uint8Array
                : A extends SS
                  ? Set<string>
                  : A extends NS
                    ? Set<Numbers>
                    : A extends BS
                      ? Set<Uint8Array>
                      : A extends L<infer Of>
                        ? Decode<Of, Numbers>[]
                        : A extends M<infer Of>
                          ? show<{
                                [K in keyof Of]: Decode<Of[K], Numbers>
                            }>
                          : never

    /**
     * What a marshaller hands back for a whole item.
     *
     * `unmarshall(item)` takes the attributes without the `M` around them, so this is the map itself —
     * the counterpart of {@link ItemEncode}, and the type a custom marshaller's `unmarshall` should
     * be declared to return.
     */
    export type ItemDecode<Item, Numbers = number | bigint> = show<{
        [K in keyof Item]: Decode<Item[K], Numbers>
    }>
}
