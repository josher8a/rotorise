/**
 * The marshaller the table was probably written with.
 *
 * A port of `@aws-sdk/util-dynamodb`'s `convertToAttr` / `convertToNative`, so a table written by
 * that marshaller can be read and written byte for byte while the schema and key layers are adopted
 * around it. Its own entry point, because it is a migration aid rather than part of the library:
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
 * Verified against the real SDK: twenty values and three option sets, both directions, agreeing on
 * every one including the cases where the SDK throws — with **one deliberate divergence, in the
 * direction of the store**. `Carries('N')` is the numerals, not the finite doubles, and the SDK
 * checks only the latter: it will marshal `1e300` and `5e-324` into an `N` DynamoDB refuses, and
 * unmarshal `{ N: '' }` as `0` and `{ N: '0x10' }` as `16`. This gates both halves on the same
 * predicate every other term that touches an `N` uses, and refuses an empty `SS`/`NS`/`BS` on read
 * where the SDK hands back an empty `Set`. {@link native.Deviations} restores the SDK's exact
 * behaviour for a caller who wants the bytes and nothing else.
 */

import type { ErrorMessage, show } from '../utils'
import type {
    AttributeMap,
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
import { carrying, isNumeral, memberOf, tooDeeplyNested } from './attribute'
import { codec } from './build'
import type { AttributeCodec, Result } from './codec'
import { andThen, CodecError, every, everyEntry } from './codec'
import { opaqueTerms, storedTooDeeply } from './denote'

/**
 * The options `@aws-sdk/util-dynamodb` takes, as far as this reproduces them.
 *
 * `wrapNumbers` and `convertWithoutMapWrapper` are not reproduced: the first returns a
 * `NumberValue` from `@aws-sdk/lib-dynamodb`, which this package cannot construct without taking
 * the dependency it exists to avoid, and the second only moves where the map wrapper goes.
 */

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

const nativeNumber = (
    value: number | bigint,
    options: native.Options,
): Result<AttributeValue> => {
    if (typeof value === 'number' && !Number.isFinite(value)) {
        return new CodecError(
            `Special numeric value ${value.toString()} is not allowed`,
        )
    }
    if (typeof value === 'number' && !options.allowImpreciseNumbers) {
        if (value > Number.MAX_SAFE_INTEGER) {
            return new CodecError(
                `Number ${value} is greater than Number.MAX_SAFE_INTEGER.`,
            )
        }
        if (value < Number.MIN_SAFE_INTEGER) {
            return new CodecError(
                `Number ${value} is lesser than Number.MIN_SAFE_INTEGER.`,
            )
        }
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
     * certifies an attribute the model has no point for. `deviations.writeNumber` is there for a
     * caller who wants the SDK's exact behaviour back, byte for byte.
     */
    const digits = value.toString()
    return isNumeral(digits)
        ? carrying('N', digits)
        : new CodecError(
              `${digits} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125`,
          )
}

const nativeSet = (
    value: ReadonlySet<unknown>,
    options: native.Options,
    write: (value: number | bigint) => Result<AttributeValue>,
): Result<AttributeValue> => {
    const members = options.removeUndefinedValues
        ? [...value].filter((member) => member !== undefined)
        : [...value]
    if (!options.removeUndefinedValues && members.includes(undefined)) {
        return new CodecError(
            'Pass options.removeUndefinedValues=true to remove undefined values from map/array/set.',
        )
    }
    if (members.length === 0) {
        return options.convertEmptyValues
            ? carrying('NULL', true)
            : new CodecError(
                  'Pass a non-empty set, or options.convertEmptyValues=true.',
              )
    }

    const first = members[0]
    if (typeof first === 'number' || typeof first === 'bigint') {
        return andThen(
            every(members, (member) => write(member as number | bigint)),
            (written) =>
                carrying(
                    'NS',
                    written.map((one) => (one as { N: string }).N),
                ),
        )
    }
    if (typeof first === 'string') {
        return carrying('SS', members as readonly string[])
    }
    if (isBinaryValue(first)) {
        return carrying('BS', members as readonly Uint8Array[])
    }
    return new CodecError(
        'Only Number Set (NS), Binary Set (BS) or String Set (SS) are allowed.',
    )
}

/**
 * A value, as `@aws-sdk/util-dynamodb`'s `convertToAttr` stores it.
 *
 * Ported from that implementation rather than from its documentation, branch for branch — including
 * the order the branches are tried in, which is observable: an `Array` is a list before it is an
 * object, and a `Map` is a map before a class instance is refused.
 */
const toNative = (
    value: unknown,
    options: native.Options,
    write: (value: number | bigint) => Result<AttributeValue>,
    /**
     * How many `L`/`M` this value already sits inside.
     *
     * The SDK's marshaller has no such check and will hand DynamoDB a row it rejects. This is a
     * deliberate divergence of the same kind as the `N` gate above: `native` mirrors the SDK's
     * *shape*, not its willingness to write what the store refuses.
     */
    enclosing = 0,
): Result<AttributeValue> => {
    if (value === undefined) {
        return new CodecError(
            'Pass options.removeUndefinedValues=true to remove undefined values from map/array/set.',
        )
    }
    if (value === null) return carrying('NULL', true)

    if (Array.isArray(value)) {
        const kept = value.filter(
            (item) =>
                typeof item !== 'function' &&
                (!options.removeUndefinedValues || item !== undefined),
        )
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            every(kept, (item) =>
                toNative(item, options, write, enclosing + 1),
            ),
            (written) => carrying('L', written),
        )
    }

    const named = (value as { constructor?: { name?: string } })?.constructor
        ?.name
    if (named === 'Set')
        return nativeSet(value as ReadonlySet<unknown>, options, write)
    if (named === 'Map') {
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            everyEntry(
                Object.fromEntries(value as Map<string, unknown>),
                (held) => toNative(held, options, write, enclosing + 1),
            ),
            (written) => carrying('M', written),
        )
    }

    const isPlain = named === 'Object' || (!named && typeof value === 'object')
    if (
        isPlain ||
        (options.convertClassInstanceToMap && typeof value === 'object')
    ) {
        const kept: Record<string, unknown> = {}
        // `for…in`, as the SDK does: enumerable *and* inherited, which is what makes
        // `convertClassInstanceToMap` reach a prototype's own accessors
        for (const key in value as Record<string, unknown>) {
            const held = (value as Record<string, unknown>)[key]
            if (typeof held === 'function') continue
            if (held === undefined && options.removeUndefinedValues) continue
            kept[key] = held
        }
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            everyEntry(kept, (held) =>
                toNative(held, options, write, enclosing + 1),
            ),
            (written) => carrying('M', written),
        )
    }

    if (isBinaryValue(value)) {
        return (value as Uint8Array).length === 0 && options.convertEmptyValues
            ? carrying('NULL', true)
            : carrying('B', value as Uint8Array)
    }
    if (typeof value === 'boolean') return carrying('BOOL', value)
    if (typeof value === 'number' || typeof value === 'bigint') {
        return write(value)
    }
    if (typeof value === 'string') {
        return value.length === 0 && options.convertEmptyValues
            ? carrying('NULL', true)
            : carrying('S', value)
    }
    return new CodecError(
        `Unsupported type passed: ${String(value)}. Pass options.convertClassInstanceToMap=true to marshall typeof object as map attribute.`,
    )
}

/** A stored number, as `convertToNative` reads it — a `bigint` outside the safe range. */
const fromNativeNumber = (digits: string): Result<unknown> => {
    /**
     * **`Number` reads far more than an `N` carries**, and the SDK hands it the digits unchecked:
     * `''` and whitespace are `0`, `'0x10'` is `16`, `'abc'` is `NaN`. Each is a value this codec's
     * own `encode` now refuses, which is **(C)** failing — the pair's two halves disagreeing about
     * what an `N` holds. `number` and `opaque` have read through this gate since the numeral domain
     * was tightened; this is the third reader of an `N`, one file over.
     *
     * One gate is enough here, where `number` needs two. `number`'s second gate catches a numeral
     * that rounds *out* of range on the way into a double; this reader hands a wide value back as a
     * `bigint` of the very digits stored, and a narrow one is inside the safe range, so nothing it
     * returns can fail to be writable again.
     */
    if (!isNumeral(digits)) {
        return new CodecError(
            `'${digits}' is not a numeral, so this attribute was not written by DynamoDB`,
        )
    }
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
 * A stored set, refused when empty.
 *
 * DynamoDB has no empty `SS`, `NS` or `BS`, so an item carrying one was written by something else —
 * and {@link nativeSet} refuses to write one, either erroring or storing `NULL`. Reading it would
 * hand back a value this codec's own `encode` cannot produce, which is **(C)** failing. The SDK
 * returns an empty `Set` for all three; this does not.
 */
const nonEmpty = <T>(
    member: 'SS' | 'NS' | 'BS',
    members: readonly T[],
): Result<readonly T[]> =>
    members.length === 0
        ? new CodecError(
              `DynamoDB has no empty ${member}, so this attribute was not written by it; a set this codec would refuse to write is not one it can read`,
          )
        : members

/** A stored value, as `@aws-sdk/util-dynamodb`'s `convertToNative` reads it. */
const fromNative = (
    attribute: AttributeValue,
    read: (digits: string) => Result<unknown>,
): Result<unknown> => {
    const member = memberOf(attribute)
    const carried = (attribute as Record<string, unknown>)[member as string]
    switch (member) {
        case 'NULL':
            return null
        case 'BOOL':
            return Boolean(carried)
        case 'N':
            return read(carried as string)
        case 'B':
        case 'S':
            return carried
        case 'L':
            return every(carried as readonly AttributeValue[], (one) =>
                fromNative(one, read),
            )
        case 'M':
            return everyEntry(carried as AttributeMap, (one) =>
                fromNative(one, read),
            )
        case 'NS':
            return andThen(
                andThen(
                    nonEmpty(member, carried as readonly string[]),
                    (members) => every(members, read),
                ),
                (read) => new Set(read),
            )
        case 'BS':
        case 'SS':
            return andThen(
                nonEmpty(member, carried as readonly unknown[]),
                (members) => new Set(members),
            )
        default:
            return new CodecError(
                `No value defined: ${JSON.stringify(attribute)}`,
            )
    }
}

/**
 * The AWS SDK's marshaller, as a codec.
 *
 * A port of `@aws-sdk/util-dynamodb`'s `convertToAttr` / `convertToNative`, so a table written by
 * that marshaller can be read and written byte for byte while the schema and key layers are adopted
 * around it. Not the codec to reach for in new code — {@link opaque} refuses what this guesses at,
 * which is the point of declaring a schema — but the one that makes adopting the rest of this
 * package a change of shape rather than a change of data.
 *
 * See {@link native.ItemEncode} for what it produces, as a type.
 */
const configured = (
    options: native.Options = {},
    deviations: native.Deviations = {},
): AttributeCodec<unknown> => {
    const write =
        deviations.writeNumber ??
        ((value: number | bigint) => nativeNumber(value, options))
    const read = deviations.readNumber ?? fromNativeNumber
    // reaches the construction site rather than `custom`, and has to: a marshaller describes itself
    // as `opaque`, which is what tells the harness how to generate a value for it, and a
    // hand-written codec cannot claim another kind's definition. This is inside the library, so it
    // has the site that can
    return codec<unknown, AttributeValue>({
        def: opaqueTerms.lossy,
        encode: (value) => toNative(value, options, write),
        decode: (attribute) =>
            storedTooDeeply(attribute, 0) ?? fromNative(attribute, read),
    })
}

/**
 * The SDK's marshaller: a codec, and a way to configure one.
 *
 * One entry point with every parameter optional, rather than three. `native` *is* the marshaller
 * with the SDK's own defaults, so `native.encode(value)` needs no call; calling it returns one
 * configured differently. The two used to be `nativeWith` and `nativeLike`, which is a distinction
 * between "some options" and "some options and some deviations" that nobody making the call cares
 * about — and it left `native` unable to be either.
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
export const native: AttributeCodec<unknown> & {
    (
        options?: native.Options,
        deviations?: native.Deviations,
    ): AttributeCodec<unknown>
} = Object.assign(
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
     * They are also the way *back* to the SDK. This port's own numbers deviate from it — both halves
     * gate on `Carries('N')`, where the SDK checks a finite double on the way in and nothing at all
     * on the way out — so a caller migrating a table that already holds `{ N: '1e300' }` passes
     * `readNumber: Number` and gets the SDK's reading, non-numerals and all, until the rows are
     * repaired.
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
    export type Encode<T, Of extends Options = {}> = EncodeWith<
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
            : T extends number | bigint
              ? N
              : T extends string
                ? OrNull<S, T, '', Empties>
                : T extends Uint8Array
                  ? OrNull<B, unknown, never, Empties>
                  : T extends ReadonlySet<infer Member>
                    ? OrNull<
                          Member extends string
                              ? SS
                              : Member extends number | bigint
                                ? NS
                                : Member extends Uint8Array
                                  ? BS
                                  : never,
                          unknown,
                          never,
                          Empties
                      >
                    : T extends readonly (infer Element)[]
                      ? Dropped<Element, Drops> extends infer Kept
                          ? [Kept] extends [never]
                              ? ErrorMessage<'[native] a list holds `undefined`, which is refused unless `removeUndefinedValues` is set'>
                              : L<EncodeWith<Kept, Empties, Drops>>
                          : never
                      : T extends object
                        ? M<ItemEncodeWith<T, Empties, Drops>>
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
    export type ItemEncode<T, Of extends Options = {}> = ItemEncodeWith<
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
            [K in keyof T as undefined extends T[K] ? never : K]: EncodeWith<
                T[K],
                Empties,
                Drops
            >
        } & {
            [K in keyof T as undefined extends T[K] ? K : never]?: EncodeWith<
                Exclude<T[K], undefined>,
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
