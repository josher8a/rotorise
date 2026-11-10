import type { ErrorMessage, show } from '../utils'
import type {
    AttributeValue,
    B,
    BOOL,
    BS,
    DynamoNumber,
    L,
    M,
    N,
    NS,
    NULL,
    S,
    SS,
} from './attribute'
import type { AttributeCodec } from './build'
import { codecOfTerm } from './capabilities'
import type { OpaqueNumbers } from './denote'
import { opaqueTerms } from './denote'
import type { EveryButNumberT } from './prisms'
import type { HeldT, TermMark } from './term'

// ── the escape hatch ────────────────────────────────────────────────

export const canonicalOpaque = codecOfTerm<unknown, AttributeValue>(
    opaqueTerms.canonical,
)
export const opaquePolicies: {
    readonly [Of in opaque.Numbers]: AttributeCodec<unknown>
} = {
    lossy: codecOfTerm<unknown, AttributeValue>(opaqueTerms.lossy),
    refuse: codecOfTerm<unknown, AttributeValue>(opaqueTerms.refuse),
}

export function opaqueOf(): AttributeCodec<unknown> & TermMark<['opaq']>
export function opaqueOf(
    numbers: 'lossy',
): AttributeCodec<unknown> &
    TermMark<HeldT<['opaq'], ['opaq'], ['caller', 'opaqueLossy']>>
export function opaqueOf(
    numbers: 'refuse',
): AttributeCodec<unknown> &
    TermMark<HeldT<['opaq'], EveryButNumberT, ['caller', 'opaqueRefuse']>>
export function opaqueOf(numbers?: opaque.Numbers): AttributeCodec<unknown>
export function opaqueOf(numbers?: opaque.Numbers): AttributeCodec<unknown> {
    return numbers === undefined ? canonicalOpaque : opaquePolicies[numbers]
}

/**
 * Any attribute, decoded to `unknown`, with a number held exactly as a {@link DynamoNumber}.
 *
 * The honest default, and **total**: every wire value has one value here. `N` reads as a
 * `DynamoNumber` and an `NS` as a `Set` of them, and both write back as they were read. A JS
 * `number` is refused, because a float is not the exact number that `N` stores.
 *
 * One entry point with its only parameter optional, the shape {@link native} takes: `opaque` *is*
 * the canonical codec, so `opaque.encode(value)` needs no call. A call names one of the two
 * numeric policies of {@link opaque.Numbers}. Each policy is a `held` over the canonical codec,
 * so the policies add no term to the language.
 *
 * ```ts
 * opaque.encode(value)             // `DynamoNumber` ⇄ `N`, exact
 * opaque('lossy').encode(value)    // `number` ⇄ `N`, digits only while a float holds them
 * opaque('refuse').encode(value)   // a number is refused, which guesses nothing
 * ```
 *
 * Callable *and* a codec, which is what lets `opaque.encode` and {@link opaque.Encode} keep the same
 * name.
 */
export const opaque: AttributeCodec<unknown> &
    TermMark<['opaq']> &
    typeof opaqueOf = Object.assign(opaqueOf, canonicalOpaque)

/**
 * The shapes, named as the runtime names them.
 *
 * A type-only namespace merged with the codec above, so `opaque.Encode<T>` sits beside
 * `opaque.encode(value)` and reads as the same pair. Non-instantiated — it declares no value — which
 * is what lets it share the name with a `const`, and `import type { opaque }` brings the types in
 * with no runtime import.
 *
 * `Decode` and `ItemDecode` are the two this does not have yet, and their absence is the point of
 * spelling the family out: `decodeUnknown` has behaviour worth describing — every native set comes
 * back as a `Set`, an `N` is a `DynamoNumber`, and an `N` under `'refuse'` is a refusal — and it is not a
 * mirror of {@link native.Decode}.
 */
export namespace opaque {
    /**
     * What a numeric policy of `opaque` does with a JS `number`, where the canonical codec holds a
     * `DynamoNumber`.
     *
     * `N` is a decimal string and no JS scalar carries it faithfully: decoding to `number` rounds
     * anything wider than a float, and decoding to `string` re-encodes as `S` — silently changing
     * the attribute's *stored type* on the next write. The canonical codec reads `N` as a
     * `DynamoNumber`, which is exact. A policy is for a caller who holds JS numbers, and each one
     * is a `held` over the canonical codec:
     *
     * - `'refuse'` — numbers are not written, and reading an `N` throws. Nothing is guessed.
     * - `'lossy'` — `number` ⇄ `N`. The member always survives a read-modify-write; the digits survive
     *   only while they fit in a float.
     */
    export type Numbers = OpaqueNumbers

    /**
     * What {@link opaque} writes for a value of type `T`, or why it refuses to.
     *
     * The counterpart of {@link native.Encode} for *this* package's marshaller, and they are not the
     * same function. The canonical `opaque` writes a `DynamoNumber` as `N` and refuses a JS number,
     * refuses a `bigint`, refuses a `Map`, and refuses a class instance — because each of those decodes
     * back as something else, and its whole domain is the values whose type survives a round trip. The
     * SDK's marshaller accepts all of them. `Of` names a numeric policy, which converts or refuses a JS
     * number and writes no `NS`. So a team whose in-house marshaller resembles `opaque` needs this
     * type to diff against, not that one.
     *
     * Every branch mirrors one in `encodeUnknown` or in a policy, refusals included: where the runtime returns a
     * {@link CodecError}, this resolves to an {@link ErrorMessage} carrying the same reason. A shape
     * containing a refused value therefore fails to *describe*, rather than describing a write that
     * throws.
     *
     * One place it is more permissive than the runtime, and deliberately: a class instance is refused at
     * runtime by checking the prototype, which no type can do. `Date` is named because it is the one the
     * runtime's own error message names, but a type cannot tell an arbitrary instance from a plain
     * object — so `Encode<SomeClass>` describes it as `M` where `encode` would refuse it.
     */
    export type Encode<T, Of extends Numbers | undefined = undefined> = [
        T,
    ] extends [never]
        ? never
        : [Of] extends [undefined]
          ? T extends DynamoNumber
              ? N
              : Encoded<T, Of>
          : Encoded<T, Of>

    /**
     * {@link Encode} after the one row that only the canonical codec has. Under a policy, a
     * `DynamoNumber` is a class instance, and it reaches the object row as today.
     */
    type Encoded<T, Of extends Numbers | undefined> = [T] extends [never]
        ? never
        : T extends null
          ? NULL
          : T extends undefined
            ? ErrorMessage<'[opaque] DynamoDB has no attribute holding undefined; omit the key, or use `optional(...)` on a declared attribute'>
            : T extends string
              ? S
              : T extends boolean
                ? BOOL
                : T extends Uint8Array
                  ? B
                  : T extends number
                    ? Of extends 'lossy'
                        ? N
                        : Of extends 'refuse'
                          ? ErrorMessage<"[opaque] a number is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`. Declare it with `number` or `decimal`, or opt in with `opaque('lossy')`">
                          : ErrorMessage<"[opaque] a JS number is a binary64 float, and `opaque` holds a number exactly, as a `DynamoNumber`. Build one with `DynamoNumber.from` or `DynamoNumber.fromNumber`, declare the attribute with `dynamoNumber` or `number`, or opt in with `opaque('lossy')`">
                    : T extends bigint
                      ? [Of] extends [undefined]
                          ? ErrorMessage<'[opaque] a bigint writes `N` and reads back as a `DynamoNumber`, so `1n` would not come back as `1n`. Pass `DynamoNumber.from(value.toString())`'>
                          : ErrorMessage<'[opaque] a bigint shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`'>
                      : T extends ReadonlySet<infer Member>
                        ? [Member] extends [string]
                            ? SS
                            : [Member] extends [Uint8Array]
                              ? BS
                              : [Of] extends [undefined]
                                ? [Member] extends [DynamoNumber]
                                    ? NS
                                    : ErrorMessage<'[opaque] a set writes `SS`, `BS` or `NS`, and each holds one kind: every member a string, every member binary, or every member a `DynamoNumber`'>
                                : ErrorMessage<'[opaque] `NS` decodes as strings, because its members are decimal strings. Use a set of strings, or `array(number)` if the order does not matter'>
                        : T extends ReadonlyMap<unknown, unknown>
                          ? ErrorMessage<'[opaque] DynamoDB has one map member, `M`, and it decodes as a plain object. Pass an object, or use `object([string, optional(...)])` to state the value type'>
                          : T extends Date
                            ? ErrorMessage<'[opaque] only plain objects survive: `M` carries the own enumerable properties and nothing that says how to rebuild the instance. A `Date` is faithful as an ISO string'>
                            : T extends readonly (infer Element)[]
                              ? Encode<Element, Of> extends infer Written
                                  ? [Written] extends [AttributeValue]
                                      ? L<Written>
                                      : Written
                                  : never
                              : T extends object
                                ? ItemEncode<T, Of> extends infer Item
                                    ? Refused<Item> extends infer Why
                                        ? [Why] extends [never]
                                            ? M<
                                                  Item &
                                                      Readonly<
                                                          Record<
                                                              string,
                                                              | AttributeValue
                                                              | undefined
                                                          >
                                                      >
                                              >
                                            : Why
                                        : never
                                    : never
                                : ErrorMessage<'[opaque] no DynamoDB member carries this'>

    /**
     * A refusal, carried out of the collection that contains it.
     *
     * A list of numbers under `'refuse'`, or an object with a `bigint` attribute, cannot be described —
     * so the refusal *is* the answer rather than something buried in an `L` or an `M`. Without this the
     * refusal fails `L`'s and `M`'s own constraints and the error lands on this file's definitions
     * instead of on the shape somebody wrote.
     */
    type Refused<T> = Extract<T[keyof T], ErrorMessage<string>>

    /**
     * An item {@link opaque} writes, attribute by attribute.
     *
     * Optional exactly where the property is. The runtime *refuses* a property that is present and
     * holding `undefined` — `{ a: undefined }` is an error, where `{}` is fine — and a type cannot tell
     * those apart, so an optional property is described as one that may be absent. The same reading
     * {@link native.ItemEncode} takes, for the same reason.
     */
    export type ItemEncode<
        T,
        Of extends Numbers | undefined = undefined,
    > = show<
        {
            [K in keyof T as undefined extends T[K] ? never : K]: Encode<
                T[K],
                Of
            >
        } & {
            [K in keyof T as undefined extends T[K] ? K : never]?: Encode<
                Exclude<T[K], undefined>,
                Of
            >
        }
    >

    /**
     * What {@link opaque} reads a stored attribute back as, or why it refuses to.
     *
     * The other direction from {@link opaque.Encode}, and *not* a mirror of {@link native.Decode} —
     * `decodeUnknown` is a different function from the SDK's in three places, and each is a reason
     * this type has to exist rather than the SDK's being reused:
     *
     * - `NS` is a `Set<DynamoNumber>`, where the SDK's answers `Set<number | bigint>`: exact, and it
     *   writes back as the `NS` it came from. Under a policy it is a **refusal**, because nothing
     *   without a schema can say which member a JS number holds faithfully, so a policy will not
     *   *write* a set of numbers, and a member it cannot write is one it cannot read. See
     *   `Calculus.Alg.Lawful.no_read_without_write`.
     * - `N` is a `DynamoNumber`, where the SDK's reads a JS number. Under `'refuse'` it is a
     *   *refusal*, and under `'lossy'` it is a `number`.
     * - `L` and `M` carry a refused member out with them, the way {@link opaque.Encode} does, so a
     *   list of `N` under `'refuse'` is the refusal itself rather than a list of nothing.
     *
     * A bare {@link AttributeValue} distributes, which is the useful answer: it resolves to every
     * value a stored attribute could be read as, the refusal for `N` among them.
     */
    export type Decode<A, Of extends Numbers | undefined = undefined> = [
        A,
    ] extends [never]
        ? never
        : A extends NULL
          ? null
          : A extends BOOL
            ? boolean
            : A extends N
              ? [Of] extends [undefined]
                  ? DynamoNumber
                  : Of extends 'lossy'
                    ? number
                    : ErrorMessage<"[opaque] a stored number is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`. Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`">
              : A extends S
                ? string
                : A extends B
                  ? Uint8Array
                  : A extends SS
                    ? Set<string>
                    : A extends NS
                      ? [Of] extends [undefined]
                          ? Set<DynamoNumber>
                          : // a member this codec cannot write is a member it cannot read: `NS`
                            // has no write path here, so reading one would re-encode as `SS` and
                            // change the attribute's stored type — (MP), which `μ = ⊤` leaves as
                            // the only law watching
                            ErrorMessage<'[opaque] a stored set of numbers has no counterpart this codec can write, so reading it would re-encode as `SS`. Declare the attribute with `number.set()` or `decimal.set()`'>
                      : A extends BS
                        ? Set<Uint8Array>
                        : A extends L<infer Element>
                          ? Decode<Element, Of> extends infer Read
                              ? [Read] extends [ErrorMessage<string>]
                                  ? Read
                                  : Read[]
                              : never
                          : A extends M<infer Item>
                            ? ItemDecode<Item, Of> extends infer Read
                                ? Refused<Read> extends infer Why
                                    ? [Why] extends [never]
                                        ? Read
                                        : Why
                                    : never
                                : never
                            : ErrorMessage<'[opaque] an AttributeValue carrying no member'>

    /**
     * An item {@link opaque} reads back, attribute by attribute.
     *
     * Homomorphic, so an attribute the stored shape marks optional stays optional — and its
     * `undefined` is excluded before decoding, since `undefined` is not a member and would otherwise
     * fall through to the refusal at the end.
     */
    export type ItemDecode<
        Item,
        Of extends Numbers | undefined = undefined,
    > = show<{
        [K in keyof Item]: Decode<Exclude<Item[K], undefined>, Of>
    }>
}
