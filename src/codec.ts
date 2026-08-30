import type {
    Attribute,
    AttributeMap,
    AttributeName,
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
    StoredItem,
} from './attribute'
import { carrying, memberOf } from './attribute'
import type { Codec } from './build'
import { codec } from './build'
import {
    andThen,
    asPath,
    CodecError,
    every,
    everyEntry,
    failed,
    orThrow,
    type Result,
} from './result'
import type { ErrorMessage, show } from './utils'

// the failure algebra lives in `./result`, and is re-exported because it is part of the surface a
// caller works in: a `Result` is what every direction returns
export {
    andThen,
    CodecError,
    every,
    everyEntry,
    failed,
    orThrow,
    type Result,
} from './result'

/**
 * Marks a codec whose attribute may be absent.
 *
 * Type-level only. Whether an attribute may be absent is read at runtime from the codec's
 * {@link CodecDef} — `optional` is one of the kinds — so there is nothing for a symbol to carry
 * and nothing for a wrapper to forget to copy. The declaration stays because the *type* needs a
 * brand: {@link ItemSpec} and {@link ObjectOf} decide required from optional by it.
 */
declare const optionalMarker: unique symbol

/**
 * Nothing, or why this element cannot be about absence.
 *
 * `optional` and `fallback` are statements about a *name*: the attribute called this may be missing
 * from the item. A list, a set, a tuple, a record and a union option have no name at that position
 * for anything to be missing from — so one of these there is not a weaker element, it is a category
 * error, and it was a silent one: `array(optional(string))` compiled and wrote `{}` into the list, an
 * attribute carrying no member at all, which DynamoDB rejects on arrival.
 *
 * Intersected with the parameter rather than checked on the result, the same way every other refusal
 * in this file is, so the message lands on the element that is wrong.
 */
type AboutAbsence =
    | { readonly [optionalMarker]: true }
    | { readonly [fallbackMarker]: unknown }
    // a rest element is a position marker too: it says "and then any number of these", which only a
    // tuple's tail can mean. `tuple` exempts it and checks its position itself
    | { readonly [restMarker]: true }

/**
 * `Extract`, not `extends`, and that is the whole of why this works over a tuple.
 *
 * A bare conditional distributes, so asked of `Cs[number]` — the union of a tuple's elements — it
 * answers `unknown | ErrorMessage<…>`, which is `unknown`: one good element absolves every bad one.
 * `Extract` asks whether *any* member is about absence, which is the question.
 */
type NotAboutAbsence<C> = [Extract<C, AboutAbsence>] extends [never]
    ? unknown
    : ErrorMessage<'this element is a position marker, not an attribute: `optional` and `fallback` say a name may be missing from an item and `rest` says a tuple continues, and none of those is a thing an element here can be — use `nullable(...)` for a member that may be stored as NULL'>

declare const fallbackMarker: unique symbol

/**
 * Marks the codec for a tuple's trailing elements.
 *
 * Type-level only, and read at runtime from the definition, for the same reason as
 * {@link optionalMarker}. Like `optional`, it is a marker for a *position* rather than a codec in its
 * own right — it says "and then any number of these" — so it is meaningful in exactly one place: last
 * in a {@link tuple}.
 */
declare const restMarker: unique symbol

/**
 * A deterministic source of randomness.
 *
 * Seeded rather than `Math.random`, so a counterexample found in CI reproduces exactly from the
 * seed printed alongside it.
 */
export type Rng = () => number

/**
 * Reads and writes one attribute.
 *
 * `A` is the attribute type produced, not the member name: a codec may write more than one member
 * (see {@link nullable}), and naming the members instead would collapse to a value carrying all of
 * them at once.
 */
export type AttributeCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = CodecShape<T, T, A>

/**
 * The capabilities a codec has, with the two directions named separately.
 *
 * One record, instantiated twice. {@link AttributeCodec} is the concrete form, where both
 * directions are the same `T`; {@link AnyCodec} is the erased one, where `In` is `never` and `Out`
 * is `unknown` so every concrete codec is assignable to it.
 *
 * Written once because it was written twice: the erased form was a field-for-field copy, and a
 * capability added to one and not the other simply stops being visible through the erased form —
 * which is the form `at`, `set` and `keyUpdates` all read through. Nothing would fail; the fact
 * would just never arrive.
 */
type CodecShape<In, Out, A extends AttributeValue> = {
    /**
     * The attribute this value is written as, or why it cannot be.
     *
     * A {@link Result}: the failure is returned, not thrown, because a row is data somebody else
     * wrote and failing to read one is an ordinary outcome rather than an exception. `CodecError`
     * extends `Error`, so a bare union is enough to tell the two apart and `isError` narrows it.
     */
    readonly encode: (value: In) => Result<A>
    /** The value this attribute holds, or why it cannot be read. */
    readonly decode: (attribute: AttributeValue) => Result<Out>
    /**
     * The same, throwing.
     *
     * What every codec calls to compose with another: a nested decode that returned a union would
     * have to be unwrapped at each of the fifty-odd places one codec reaches into the next, and the
     * unwrapping is the part that gets forgotten. So composition throws and the boundary converts,
     * which is why these are the ones the composites are built from.
     */
    readonly unsafeEncode: (value: In) => A
    /** The same, throwing. */
    readonly unsafeDecode: (attribute: AttributeValue) => Out
    /**
     * A value this codec can faithfully carry, for property testing.
     *
     * Per codec, not derived from the type: `decimal` is a `string` but only a *normalised* one
     * survives, and `set(string)` must not be empty. `size` bounds recursion.
     */
    readonly arbitrary?: (rng: Rng, size: number) => Out
    /**
     * Values simpler than `value`, cheapest first. Must be finite and never yield `value` itself.
     */
    readonly shrink?: (value: In) => readonly Out[]
    /** What this codec is — see {@link CodecDef}. */
    readonly def?: CodecDef
}

/**
 * Anything that can sit where an attribute codec is expected — which is every codec.
 *
 * There used to be a second thing: an item, tagged or untagged codec, which *was* one `M` attribute
 * but exposed it as `.attribute`, so specs had to accept both shapes and every combinator had to
 * convert. The distinction was never about attributes. It was about the top-level map, and the top
 * level is the one place a map is not written — so it belongs to the *view*, not to the codec.
 * {@link object} writes its `M` like anything else, and offers `.item` for the one place that does
 * not: the top level.
 */
export type Nestable<T> = AttributeCodec<T>

/** An attribute that may be absent from the item entirely. */
export type OptionalCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = AttributeCodec<T, A> & { readonly [optionalMarker]: true }

/** Any codec, both directions erased — `never` in and `unknown` out, so every codec fits. */
export type AnyCodec = CodecShape<never, unknown, AttributeValue>

export type Decoded<C> = C extends {
    readonly attribute: AttributeCodec<infer T>
}
    ? T
    : C extends AttributeCodec<infer T, AttributeValue>
      ? T
      : never

/**
 * What a codec *is*, as data rather than as closures.
 *
 * The closures say how to encode and decode; this says which codec it is and what it was built
 * from. Anything that wants to reason about a codec instead of run it reads this — `rotorise/testing`
 * dispatches its generators on `kind`, so they live there rather than being baked into every codec
 * and shipped to production.
 *
 * Not inherited by {@link derive}: a wrapper is a different codec from the one it wraps.
 *
 * ── the grammar ────────────────────────────────────────────────────────────────────────────────
 *
 * This union *is* the abstract syntax, so the term language has a grammar and it is this one, with
 * the nonterminals indexed by the member each term writes. The index is not decoration: it is what
 * makes `⟨set⟩` expressible at all, and it is exactly what {@link writes} computes.
 *
 * ```bnf
 * ⟨member⟩   ::= ⟨attr⟩ | optional(⟨attr⟩) | fallback(⟨attr⟩, ⟨thunk⟩)
 *
 * ⟨attr⟩     ::= ⟨attr:S⟩ | ⟨attr:N⟩ | ⟨attr:BOOL⟩ | ⟨attr:B⟩
 *              | ⟨attr:SS⟩ | ⟨attr:NS⟩ | ⟨attr:BS⟩
 *              | ⟨attr:L⟩  | ⟨attr:M⟩  | ⟨attr:?⟩
 *
 * ⟨attr:S⟩    ::= string | literal(⟨text⟩ +) | ⟨wrap S⟩
 * ⟨attr:N⟩    ::= decimal | number | ⟨wrap N⟩
 * ⟨attr:BOOL⟩ ::= boolean | ⟨wrap BOOL⟩
 * ⟨attr:NULL⟩ ::= nullValue | ⟨wrap NULL⟩
 * ⟨attr:B⟩    ::= binary | ⟨wrap B⟩
 * ⟨attr:kS⟩   ::= set(⟨attr:k⟩)                       for k ∈ { S, N, B }
 * ⟨attr:L⟩    ::= array(⟨attr⟩) | tuple(⟨attr⟩ *) | ⟨wrap L⟩
 * ⟨attr:M⟩    ::= record(⟨attr⟩)
 *               | object({ (⟨name⟩ : ⟨member⟩) * } , ⟨rest⟩)
 *               | discriminatedUnion(⟨name⟩, ⟨object⟩ +)
 *               | ⟨wrap M⟩
 * ⟨attr:?⟩    ::= opaque | custom | lazy(⟨thunk⟩) | held(⟨attr⟩, ⟨iso⟩)
 *               | nullable(⟨attr⟩) | union(⟨attr⟩ +)
 *
 * ⟨wrap k⟩    ::= refine(⟨attr:k⟩, ⟨pred⟩) | legacy(⟨attr:k⟩, ⟨reader⟩) | union(⟨attr:k⟩ +)
 * ⟨rest⟩      ::= 'drop' | 'refuse' | ⟨attr⟩
 * ```
 *
 * Three things it buys, and one it cannot:
 *
 * 1. **The two levels are a stratification, not a convention.** `⟨member⟩` and `⟨attr⟩` are different
 *    nonterminals, so `array(optional(string))` is *ungrammatical* — which is what it always was, and
 *    what it silently was not until `NotAboutAbsence` made the types say so.
 * 2. **`⟨set⟩` is why the index has to exist.** A set of a term that writes no single member names no
 *    set, and the grammar says that structurally rather than by throwing.
 * 3. **`⟨attr:?⟩` is the honest home for the terms whose member is not structural** — `opaque` and
 *    `custom` write what the value turns out to be, `union` writes what its chosen option writes,
 *    `held` writes its inner's, `lazy` cannot be asked without forcing. `writes` returns `undefined`
 *    for exactly this nonterminal.
 *
 * What a grammar cannot state is every constraint *between siblings*, and those are the two side
 * conditions this library checks separately:
 *
 * - `union(c₁ … cₙ)` requires the `cᵢ` pairwise distinguishable — by decoded type for reading
 *   ({@link ValidateOptions}, at compile time) and by kind-of-value for writing (at construction).
 * - `discriminatedUnion(d, o₁ … oₙ)` requires every `oᵢ` to name `d` with a `literal`.
 *
 * Which is the useful conclusion: a grammar is the right formalism for the *terms*, and not for the
 * *codec*. What a codec means needs the two indices as a judgement — `c` holds `T` and stores `A`,
 * which is `Decoded<C>` and `AttributeOf<C>` — plus the equations between terms, which are checked in
 * `codec.laws.spec.ts`.
 */
export type CodecDef =
    | { readonly kind: 'string' }
    | {
          readonly kind: 'literal'
          readonly allowed: readonly (string | number)[]
      }
    | { readonly kind: 'decimal' }
    | { readonly kind: 'number' }
    | { readonly kind: 'boolean' }
    | { readonly kind: 'binary' }
    | { readonly kind: 'null' }
    | { readonly kind: 'opaque'; readonly numbers: opaque.Numbers }
    | { readonly kind: 'set'; readonly element: AnyCodec }
    | { readonly kind: 'array'; readonly element: AnyCodec }
    | {
          readonly kind: 'tuple'
          readonly elements: readonly AnyCodec[]
          /** The codec for everything past `elements`, where the tuple has a tail. */
          readonly tail?: AnyCodec
      }
    | { readonly kind: 'record'; readonly value: AnyCodec }
    | {
          readonly kind: 'attributes'
          readonly of: Attributes
          /**
           * The codec for what the spec does not name, where there is one.
           *
           * Recorded because a definition that left it out did not determine the codec: two objects
           * differing only in their rest policy had the same definition, and a harness reading it
           * generated only the declared attributes — so an open entity's round-trip law was checked
           * on its closed part and nowhere else. `drop` and `refuse` need no entry: neither puts
           * anything in the entity, so there is nothing to generate.
           */
          readonly rest?: AnyCodec
      }
    | {
          readonly kind: 'tagged'
          readonly discriminator: string
          readonly variants: Attributes
      }
    | { readonly kind: 'untagged'; readonly variants: readonly AnyCodec[] }
    | {
          readonly kind: 'refine'
          readonly inner: AnyCodec
          readonly refined: Refinement
      }
    | { readonly kind: 'optional'; readonly inner: AnyCodec }
    | { readonly kind: 'nullable'; readonly inner: AnyCodec }
    | {
          readonly kind: 'fallback'
          readonly inner: AnyCodec
          /** The stand-in, produced per read so a mutable default cannot leak between entities. */
          readonly value: () => unknown
      }
    | { readonly kind: 'legacy'; readonly current: AnyCodec }
    | { readonly kind: 'restOf'; readonly inner: AnyCodec }
    | {
          readonly kind: 'held'
          readonly inner: AnyCodec
          /** The two halves of the isomorphism, erased — see {@link held}. */
          readonly adapt: {
              readonly encode: (value: never) => unknown
              readonly decode: (held: never) => unknown
          }
      }
    | { readonly kind: 'lazy'; readonly get: () => AnyCodec }
    /**
     * A codec written by hand, saying so.
     *
     * What {@link custom} stamps when it is not told otherwise. It answers nothing to {@link writes},
     * {@link carries} or {@link deeper}, which is the truth about a pair of functions this library did
     * not write: the member could be any of them, the value could be anything, and there is no shape
     * beneath it to walk into. There is no way to claim otherwise: {@link custom} stamps this and
     * takes no definition at all. The library's own marshallers describe themselves as `opaque`, and
     * reach the construction site directly to do it — which is a thing only this package can do.
     */
    | { readonly kind: 'custom' }

/* ── §4's stratification, as three named strata over a flat `kind` ─────────────────── */

/**
 * `CodecDef['kind']` is flat, and the calculus is not.
 *
 * §4 of `docs/codec-calculus.md` puts three different things at three different levels — a **codec**
 * denotes a `Term`, a **field** denotes a `Field`, and a **rest policy** denotes a `Rest` — and says
 * so normatively: "`optional` and `fallback` are fields, not codecs. If your library lets
 * `optional(c)` appear where a codec is expected, C3 fails at that constructor." This library does
 * enforce that, but with branded markers and `NotAboutAbsence` guards at each site that could go
 * wrong, so the level a kind belongs to was never written down anywhere.
 *
 * These are that, written down. They are also what C3's mapping is stated over: a `TermDef` has a
 * `Term`, a `FieldDef` and a `RestDef` deliberately do not, and reporting the last two as "no
 * corresponding term" would be reporting the stratification as a gap.
 */

/** §3's terms: the kinds that denote a codec. */
type TermKind =
    | 'string'
    | 'literal'
    | 'decimal'
    | 'number'
    | 'boolean'
    | 'binary'
    | 'null'
    | 'set'
    | 'array'
    | 'tuple'
    | 'record'
    | 'attributes'
    | 'tagged'
    | 'untagged'
    | 'refine'
    | 'nullable'
    | 'legacy'
    | 'held'
    | 'lazy'
    | 'opaque'
    | 'custom'

/** §4's fields: a *position* in an item — whether a name may be absent — and not a codec. */
type FieldKind = 'optional' | 'fallback'

/** §4's rest policy: what a tuple's tail is, which is likewise a position and not a codec. */
type RestKind = 'restOf'

/**
 * Every kind is classified, and the lists above are written out rather than derived so that adding
 * one is a decision rather than a default.
 *
 * A new `CodecDef` member that no stratum claims stops the build here. That is the same move as
 * `#assert_axioms` in the formalization: a fact the documents assert, turned into a build error
 * instead of something a reader is asked to re-derive.
 */
type Classified<Whole, Parts> = [Whole] extends [Parts]
    ? [Parts] extends [Whole]
        ? true
        : never
    : never
const _everyKindHasALevel: Classified<
    CodecDef['kind'],
    TermKind | FieldKind | RestKind
> = true
void _everyKindHasALevel

/** A definition that denotes a §3 `Term`. */
export type TermDef = Extract<CodecDef, { readonly kind: TermKind }>

/** A definition that denotes a §4 `Field`. */
export type FieldDef = Extract<CodecDef, { readonly kind: FieldKind }>

/** A definition that denotes a §4 `Rest`. */
export type RestDef = Extract<CodecDef, { readonly kind: RestKind }>

/**
 * The member this codec writes, when it writes exactly one.
 *
 * Read from the definition rather than stored beside it. A stored field has to be set by every
 * constructor and carried by every wrapper, and the ones that forgot were silent: `refine` lost it
 * for a while, and `item`, `map`, `tagged` and `untagged` all left it blank while writing an `M`.
 * There is nothing to forget in a function.
 */
export const writes = (codec: AnyCodec): AttributeName | undefined => {
    const def = codec.def
    if (!def) return undefined
    switch (def.kind) {
        // a wrapper writes what it wraps
        case 'refine':
        case 'optional':
        case 'fallback':
            return writes(def.inner)
        case 'legacy':
            return writes(def.current)
        // an adapter changes what the value is *held* as and leaves what it is *stored* as alone,
        // which is the whole of it — so the member is the inner codec's, unchanged
        case 'held':
        // a marked element writes and takes exactly what it wraps; the mark is about position
        case 'restOf':
            return writes(def.inner)
        /**
         * A set's member follows from its element, which the definition carries — so this is derived
         * rather than absent.
         *
         * It used to answer `undefined`, on the grounds that the *kind* `set` does not decide between
         * `SS`, `NS` and `BS`. True, and beside the point: the element decides, and the element is
         * right here. Leaving it unanswered cost a union the ability to tell a set option apart by
         * what it writes, which is the one thing that distinguishes it from a list in the table.
         */
        /**
         * A union writes one member only if every option writes the same one.
         *
         * `'M'` was the answer while a union could only hold objects, and it survived the change that
         * let it hold anything — so a `union([string, boolean])` claimed to write `M`, and nesting one
         * inside another union then filtered it out of every attribute it could actually read. The
         * mirror of {@link carries}, which was already derived this way.
         */
        case 'untagged': {
            let one: AttributeName | undefined
            for (const variant of def.variants) {
                const member = writes(variant)
                if (!member) return undefined
                if (!one) one = member
                else if (one !== member) return undefined
            }
            return one
        }
        // a literal's member follows from its values: digits are `N`, text is `S`, and an empty
        // admissible set admits any string
        case 'literal':
            return typeof def.allowed[0] === 'number' ? 'N' : 'S'
        case 'set': {
            const element = writes(def.element)
            return element === 'S' || element === 'N' || element === 'B'
                ? (`${element}S` as AttributeName)
                : undefined
        }
        // `nullable` writes `NULL` as well, `opaque` writes whatever the value turns out to be, and
        // asking a `lazy` would force the resolution it exists to defer — all three answer
        // `undefined`, which the table gives by not naming them
        default:
            return writtenBy[def.kind]
    }
}

/** Which member each kind of codec puts a value in, where the kind alone decides. */
const writtenBy: { readonly [K in TermKind]?: AttributeName } = {
    string: 'S',
    decimal: 'N',
    number: 'N',
    boolean: 'BOOL',
    binary: 'B',
    null: 'NULL',
    array: 'L',
    tuple: 'L',
    record: 'M',
    attributes: 'M',
    tagged: 'M',
}

/**
 * The kind of JavaScript value this codec encodes from, where the kind alone decides.
 *
 * The mirror of {@link writes}, and it exists for a reason worth stating: **encoding does not
 * validate**. A codec's input is typed, so `number` given `'x'` writes `{ N: 'x' }` rather than
 * failing — which means "it encoded" is no evidence that an option was the right one, and a union
 * cannot be resolved by trying each option and seeing what sticks.
 *
 * What it *can* be resolved by is this, first: `union([string, number])` given `'x'` has one option
 * that takes a string. Trying is still needed after it, because two options can take the same kind of
 * value and still be disjoint — `literal('A')` and `literal('B')` both take a string, and exactly one
 * of them accepts `'A'`.
 *
 * `undefined` means the kind does not decide: `opaque` takes anything, and asking a `lazy` would
 * force the resolution it exists to defer.
 */
export const carries = (codec: AnyCodec): readonly Shape[] | undefined => {
    const def = codec.def
    if (!def) return undefined
    switch (def.kind) {
        case 'refine':
        case 'optional':
        case 'fallback':
        case 'restOf':
            return carries(def.inner)
        case 'legacy':
            return carries(def.current)
        // and this one deliberately does *not* read through. An adapter exists precisely to change
        // the kind of value held — `held(set(string), ...)` takes an array where `set(string)` takes
        // a `Set` — so the inner codec's answer would be the wrong one. Nothing about the definition
        // says what the outer kind is, so it says so by not answering, and a union falls back to
        // trying it
        case 'held':
            return undefined
        case 'nullable': {
            const inner = carries(def.inner)
            return inner && [...inner, 'null']
        }
        case 'untagged': {
            const shapes = new Set<Shape>()
            for (const variant of def.variants) {
                const of = carries(variant)
                if (!of) return undefined
                for (const shape of of) shapes.add(shape)
            }
            return [...shapes]
        }
        // the same fact from the other side of the pair: a numeric literal takes a number
        case 'literal':
            return [typeof def.allowed[0] === 'number' ? 'number' : 'string']
        default: {
            const one = carriedBy[def.kind]
            return one && [one]
        }
    }
}

/** The kinds of value a codec can be given, as coarsely as a runtime check can tell them apart. */
export type Shape =
    | 'string'
    | 'number'
    | 'boolean'
    | 'binary'
    | 'set'
    | 'array'
    | 'map'
    | 'null'

/** Which kind of value each kind of codec takes, where the kind alone decides. */
const carriedBy: { readonly [K in TermKind]?: Shape } = {
    string: 'string',
    // a decimal is stored as `N` and *held* as a string, which is the whole point of it
    decimal: 'string',
    number: 'number',
    boolean: 'boolean',
    binary: 'binary',
    null: 'null',
    set: 'set',
    array: 'array',
    tuple: 'array',
    record: 'map',
    attributes: 'map',
    tagged: 'map',
}

/** The kind of a value, read as coarsely as {@link carries} declares it. */
export const shapeOf = (value: unknown): Shape | undefined =>
    typeof value === 'string'
        ? 'string'
        : typeof value === 'number'
          ? 'number'
          : typeof value === 'boolean'
            ? 'boolean'
            : value === null
              ? 'null'
              : value instanceof Uint8Array
                ? 'binary'
                : value instanceof Set
                  ? 'set'
                  : Array.isArray(value)
                    ? 'array'
                    : asRecord(value)
                      ? 'map'
                      : undefined

/**
 * The only value this codec can carry, when there is exactly one.
 *
 * Deliberately *not* recursive through the wrappers that {@link writes} descends: a constant is a
 * claim about the value, and `refine` can reject it, `legacy` can decode an older encoding into
 * something else, and `optional` admits absence, which is not the value. `fallback` is the one that
 * keeps it — it always writes the attribute, and its replacement is typed to the same value.
 */
export const decides = (codec: AnyCodec): unknown => {
    const def = codec.def
    switch (def?.kind) {
        case 'literal':
            // two admissible values narrow what may be stored without deciding it
            return def.allowed.length === 1 ? def.allowed[0] : undefined
        case 'fallback':
            return decides(def.inner)
        default:
            return undefined
    }
}

/**
 * The codec one segment deeper, or `undefined` where the path runs past the schema.
 *
 * How {@link ItemCodec.at} walks. Defined here beside {@link writes} and {@link decides} because it
 * is the same fact in a different direction: what the definition says is beneath this.
 */
export const deeper = (
    codec: AnyCodec,
    segment: string | number,
): AnyCodec | undefined => {
    const [only, ...rest] = childrenOf(codec, segment)
    // a segment several variants declare *differently* is not one codec, and there is no honest
    // single answer to give for it. `ItemCodec.at` carries the disagreement along instead, because
    // a path may pass through such a segment and arrive somewhere the variants agree
    return rest.length === 0 ? only : undefined
}

/**
 * Every codec a segment can reach, which is more than one exactly where a union's variants
 * disagree about it.
 *
 * A union is the only definition that branches, and what it branches into is a *set of codecs* —
 * not a codec. This used to be a `CodecDef` kind, a pseudo-codec whose `encode` and `decode` both
 * threw, which meant every reader of a definition had to know about a definition that was not one.
 * The disagreement belongs to the walk, so it is the walk that carries it.
 */
const childrenOf = (
    codec: AnyCodec,
    segment: string | number,
): readonly AnyCodec[] => {
    const def = codec.def
    if (!def) return []
    const one = (child: AnyCodec | undefined) => (child ? [child] : [])
    switch (def.kind) {
        case 'attributes':
            return one(def.of[String(segment)])
        case 'record':
            return one(def.value)
        case 'array':
            return one(def.element)
        // a set is unordered, so no document path addresses a member of one — `set` never offered
        // a child either, and refusing here is what keeps a meaningless path from compiling
        case 'tuple':
            // a position past the fixed part is a tail element, where there is a tail
            return one(def.elements[Number(segment)] ?? def.tail)
        case 'tagged':
            return acrossVariants(Object.values(def.variants), segment)
        case 'untagged':
            return acrossVariants(def.variants, segment)
        case 'refine':
        case 'optional':
        case 'fallback':
        case 'nullable':
            return childrenOf(def.inner, segment)
        case 'legacy':
            return childrenOf(def.current, segment)
        case 'lazy':
            return childrenOf(def.get(), segment)
        default:
            return []
    }
}

/** What the variants reach, deduplicated — `Set` keeps insertion order, so the first declared wins. */
const acrossVariants = (
    variants: readonly AnyCodec[],
    segment: string | number,
): readonly AnyCodec[] => [
    ...new Set(variants.flatMap((variant) => childrenOf(variant, segment))),
]

/**
 * A path several variants declare differently, which is still a path.
 *
 * `path()` and `segments` are as well defined here as anywhere — knowing where an attribute lives
 * does not require knowing what writes it, and that is what `at` is most often for. Only the codec
 * half is missing, so only the codec half fails.
 *
 * It carries **no definition**, and that is the whole of the fix: this used to be a `CodecDef` kind
 * called `branch`, so a definition language for codecs contained an entry that was not a codec, and
 * every reader of a definition had to know about it. Now `writes`, `carries` and `deeper` are asked
 * what this is and give the honest answer, which is nothing.
 */
const unresolvedAt = (path: string): AnyCodec => {
    const unresolved = () => {
        throw new CodecError(
            `'${path}' is declared differently in different variants, so this path cannot say which codec to encode with. Reach for the variant you mean — \`variant(...)\` is an item codec with its own \`at\` — or narrow the entity so only one variant declares it.`,
        )
    }
    return codec<never, AttributeValue>({
        encode: unresolved,
        decode: unresolved,
    })
}

/** A map of attribute name to codec — what `item`, `map` and each `tagged` variant hold. */
export type Attributes = Readonly<Record<string, AnyCodec>>

/** What {@link refine} narrowed with, for a generator that has to satisfy it. */
export type Refinement = {
    readonly is: (value: never) => boolean
    readonly what: string
    readonly arbitrary?: (rng: Rng, size: number) => unknown
    readonly onThinSearch?: (what: string, rate: number) => void
}

/**
 * A codec built from another, inheriting what a wrapper does not change.
 *
 * `arbitrary` and `shrink` are the two: they describe what the inner codec can carry, and a wrapper
 * that narrows or defers is usually still carrying it. Everything else is the wrapper's own —
 * `def` in particular, because a wrapper is a *different* codec from the one it wraps.
 *
 * A spread rather than the list of names it used to be, so overriding with an explicit `undefined`
 * still opts out: the key is present, so it wins. What is not mentioned is not there to win with.
 */
const derive = <T, A extends AttributeValue>(
    inner: AnyCodec,
    over: Codec<T, A>,
): AttributeCodec<T, A> =>
    codec({
        arbitrary: inner.arbitrary,
        shrink: inner.shrink,
        ...over,
    } as Codec<T, A>)

/** The same codec, described differently — all a marker wrapper ever does. */
const described = <C>(inner: C, def: CodecDef): C => ({ ...inner, def })

/**
 * Many attributes, as the one `M` that carries them.
 *
 * What `item`, `tagged` and `untagged` each expose as `.attribute` so they can nest inside another
 * entity. All three wrapped themselves identically and differed only in how a path descends, so
 * that difference is the parameter and the rest is written once — including the `'M'`, which all
 * three used to leave unsaid.
 */
const asOneAttribute = <T>(self: {
    encode: (value: T) => Result<AttributeMap>
    decode: (item: AttributeMap) => Result<T>
    def: CodecDef
}): AttributeCodec<T, Attribute<'M'>> =>
    codec({
        encode: (value) =>
            andThen(self.encode(value), (ok) => carrying('M', ok)),
        decode: (attribute) => andThen(expect('M', attribute), self.decode),
        def: self.def,
    })

const expect = <K extends AttributeName>(
    name: K,
    attribute: AttributeValue,
): Result<AttributeCarriesOf<K>> => {
    const carried = (attribute as Record<string, unknown>)[name]
    return carried === undefined
        ? new CodecError(
              `expected attribute member '${name}', found '${memberOf(attribute) ?? 'none'}'`,
          )
        : (carried as AttributeCarriesOf<K>)
}

type AttributeCarriesOf<K extends AttributeName> = Attribute<K>[K]

/**
 * A codec built by hand, at the level of the attribute itself.
 *
 * **Try the combinators first, and expect them to win.** Three attempts at a small example for this
 * were each expressible without it, which is not a coincidence — between them they cover the cases
 * that compose:
 *
 * - the same stored attribute held as something else — {@link held}
 * - several encodings read, one written — {@link legacy}
 * - the member following from the value, where the options can be told apart — {@link union}
 *
 * So there is no illustrative example here on purpose. What is left when those are exhausted is not a
 * small thing: a codec that is *total* over every attribute there is, and configurable in how it
 * treats them. That is a marshaller, and {@link opaque} and `native` are the only two in this library
 * — built through this, deliberately, so that the SDK's marshaller is a codec written the way a
 * consumer would write one. If what you are writing is not one of those, one of the three above is
 * very likely the answer.
 *
 * Three smaller capabilities are also only here:
 *
 * 1. **Its own failure.** Both directions return a {@link Result}, so the error says what was wrong
 *    with the value. An adapter's halves are total, so a failure there arrives wrapped — `refine` the
 *    inner codec instead when the message matters.
 * 2. **Its own generation.** `arbitrary` *and* `shrink`. `held` derives both from the codec
 *    underneath, and `refine` offers only `arbitrary`.
 * 3. **Throws escape.** Unlike `held`, an exception is not caught here: writing a codec is owning it,
 *    where writing a conversion is handing over two functions this library calls, sometimes
 *    speculatively.
 *
 * The two directions are given as the `Result` pair, the same way every codec in this file is built,
 * and the throwing pair is derived — so a hand-written codec cannot end up with the two disagreeing.
 */
export const custom = <T, A extends AttributeValue = AttributeValue>(raw: {
    readonly encode: (value: T) => Result<A>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly arbitrary?: (rng: Rng, size: number) => T
    readonly shrink?: (value: T) => readonly T[]
}): AttributeCodec<T, A> =>
    codec({
        encode: raw.encode,
        decode: raw.decode,
        // stamped, not taken: a hand-written codec says it is one. With no definition to hand in,
        // `writes`, `carries` and `deeper` cannot be told a member, a kind of value or a shape
        // beneath that a pair of foreign functions does not actually have
        def: { kind: 'custom' },
        arbitrary: raw.arbitrary,
        shrink: raw.shrink,
    })

// ── scalars ─────────────────────────────────────────────────────────

/** A string, as `S`. Exact in both directions: DynamoDB does not normalise strings. */
export const string: AttributeCodec<string, Attribute<'S'>> = codec({
    def: { kind: 'string' },
    encode: (value) => carrying('S', value),
    decode: (attribute) => expect('S', attribute),
})

/**
 * A literal with exactly one admissible value.
 *
 * Its own type records the value, which is what lets a caller that has no entity in hand — a key
 * being rebuilt, say — read the value off the schema rather than be handed it. A literal of two
 * or more values is an ordinary {@link AttributeCodec}: it narrows what is admissible without
 * deciding it.
 */
/**
 * Where a literal is stored, which follows from what it holds.
 *
 * Non-distributive on purpose: `'A' | 'B'` is `S`, `0 | 1` is `N`, and a set mixing the two is
 * `never` — a codec cannot write two members, and the type says so before the constructor has to.
 */
export type LiteralAttribute<T> = [T] extends [string]
    ? Attribute<'S'>
    : [T] extends [number]
      ? Attribute<'N'>
      : never

export type ConstantCodec<T extends string | number> = AttributeCodec<
    T,
    LiteralAttribute<T>
> & { readonly constant: T }

/** A string literal union, as `S`. */
export function literal<const T extends string | number>(
    only: T,
): ConstantCodec<T>
export function literal<const T extends string | number>(
    ...allowed: readonly T[]
): AttributeCodec<T, LiteralAttribute<T>>
export function literal<const T extends string | number>(
    ...allowed: readonly T[]
): AttributeCodec<T, LiteralAttribute<T>> {
    /**
     * Numbers are stored as `N`, strings as `S`, and a mix is refused.
     *
     * A literal is the one ground term whose member follows from its *values* rather than from its
     * name, which is what makes it the tool for an enum indexed by number: the held type is the
     * literal union `0 | 1 | 2`, the stored member is `N`, and the admissible set is checked in both
     * directions. Mixing kinds would ask one codec to write two members, which no codec can.
     */
    const numeric = typeof allowed[0] === 'number'
    // quoted as it was written: text in quotes, digits bare
    const named = (one: string | number) =>
        typeof one === 'number' ? String(one) : `'${one}'`
    if (allowed.some((one) => (typeof one === 'number') !== numeric)) {
        throw new CodecError(
            `a literal is stored as 'S' or as 'N' and cannot be both, and these mix strings with numbers: ${allowed
                .map(named)
                .join(', ')}`,
        )
    }
    const member = numeric ? 'N' : 'S'

    /**
     * **`ℓ ⊆ D`** — §3's premise on `(literal-N)`, checked where the rule checks it.
     *
     * `number` refuses `NaN`, `Infinity` and anything past 38 significant digits or the magnitude
     * range; `literal` was writing all of them. `literal(NaN)` produced `{ N: 'NaN' }` and
     * `literal(1e400)` produced `{ N: 'Infinity' }`, both reachable with no cast and both rejected
     * by DynamoDB — an attribute outside §1's `Numerals`, which is the one thing a term is never
     * allowed to write.
     *
     * At the declaration and not per encode, because that is what the premise is: a fact about the
     * admissible set, which this library owns, decidable when the codec is built. The same place
     * the mixed-kind refusal above lives, and for the same reason.
     *
     * This **does** discharge the write side, and the distinction is worth keeping: `ℓ` is frozen
     * at construction, so every value `encode` will ever accept has already been checked here.
     * It does not discharge the read side, because a stored attribute is not drawn from `ℓ` — see
     * `decode` below, which learned that the expensive way.
     */
    if (numeric) {
        const outside = (allowed as readonly number[]).filter(
            (one) => !isNumeral(String(one)),
        )
        if (outside.length) {
            throw new CodecError(
                `a numeric literal is stored as 'N', and ${outside
                    .map(named)
                    .join(', ')} ${outside.length === 1 ? 'is not a number' : 'are not numbers'} DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN or Infinity`,
            )
        }
    }

    /**
     * Checked both ways. An unchecked `encode` makes {@link ConstantCodec.constant} a lie — claim
     * one value, write another — which the type misses where the entity is a union and the codec
     * describes one variant of it.
     */
    const admits = (carried: string | number): Result<T> =>
        allowed.length && !allowed.includes(carried as T)
            ? new CodecError(
                  `${named(carried)} is not one of ${allowed.map(named).join(', ')}`,
              )
            : (carried as T)

    // `N` carries digits, so a numeric literal is written as text and read back as the number it is
    return codec<T, LiteralAttribute<T>>({
        def: { kind: 'literal', allowed },
        encode: (value) =>
            andThen(
                admits(value),
                (ok) =>
                    carrying(
                        member,
                        numeric ? String(ok) : (ok as string),
                    ) as LiteralAttribute<T>,
            ),
        /**
         * **The same gate `number` reads through, and for the same reason.**
         *
         * `Number` is far more permissive than an `N`: it reads `''`, whitespace, `0x10` and
         * `0b11`, none of which DynamoDB will ever hand back. Membership in `ℓ` does not filter
         * them out — it only rejects the ones whose numeric value happens to miss the set, so
         * `literal(0, 1, 2)` read `{ N: '' }` as `0` and `literal(0, 16)` read `{ N: '0x10' }`
         * as `16`. An attribute no store wrote, decoded to a value the type says is legitimate.
         *
         * The premise `ℓ ⊆ D` does not cover this and it was wrong to say it did. A premise
         * bounds the values **this library owns**; a stored attribute is outside anything it
         * owns, which is the whole reason `decode` re-checks what `encode` was trusted on.
         *
         * `number`'s *second* gate — the round-tripped value, not the digits — is genuinely
         * subsumed here, and that one is safe to say: a numeral that rounds past the maximum
         * lands outside `D`, and `ℓ ⊆ D`, so `admits` refuses it. That is a claim about a value
         * landing in a set this library fixed at construction, not about an attribute.
         */
        decode: (attribute) =>
            andThen(expect(member, attribute), (carried) => {
                if (!numeric) return admits(carried as string)
                const text = carried as string
                return isNumeral(text)
                    ? admits(Number(text))
                    : new CodecError(
                          `'${text}' is not a numeral, so this attribute was not written by DynamoDB`,
                      )
            }),
    }) as ConstantCodec<T>
}

/**
 * What DynamoDB **accepts** in an `N`: optional sign, digits, optional point, optional exponent;
 * at most 38 significant digits; magnitude zero or `1e-130 … 9.9…e125`. §1's `Numerals`, and the
 * same predicate as `Numeral.WF` in `formal/Calculus/Domain.lean`.
 */
const NUMERAL = /^[+-]?(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/

const isNumeral = (s: string): boolean => {
    const m = NUMERAL.exec(s)
    if (!m) return false
    const int = m[1] as string
    const frac = m[2] ?? ''
    const mantissa = int + frac
    const lead = mantissa.length - mantissa.replace(/^0+/, '').length
    const significant = mantissa.replace(/^0+/, '').replace(/0+$/, '')
    if (significant.length > 38) return false
    if (significant.length === 0) return true // zero, however it is spelled
    const exponent = int.length - 1 - lead + Number(m[3] ?? '0')
    return exponent >= -130 && exponent <= 125
}

/**
 * What DynamoDB **hands back**, which is a smaller set: it normalises every `N` it accepts —
 * trimming leading and trailing zeros, dropping `+`, expanding exponents, and keeping one spelling
 * of zero. Measured, not assumed: `codec.dynamodb.spec.ts` puts each form into a real table and reads it
 * back, and `Numeral.Stored` in `formal/Calculus/Domain.lean` is the same set.
 */
const isStoredNumeral = (s: string): boolean =>
    s !== '-0' && /^-?(?:0|[1-9]\d*)(?:\.\d*[1-9])?$/.test(s) && isNumeral(s)

/**
 * A decimal held as a string, stored as `N`. The codec for money — nothing becomes a JS number, so
 * nothing rounds.
 *
 * **Only the form DynamoDB stores.** It normalises what it accepts — `'1.50'` becomes `'1.5'`,
 * `'007'` becomes `'7'`, `'1e5'` becomes `'100000'` — and this codec's `decode` is the identity on
 * the digits, so anything else would come back as a different string from the one written. That is
 * a round trip failing across the database, where neither the type nor the law suite can see it, so
 * it is refused at the point where it is still local: `encode` rejects a denormal numeral rather
 * than quietly rewriting it, because rewriting is how you lose track of which value was meant.
 *
 * `'1.50'` is not a price this codec will write. `'1.5'` is. Where exact digits matter more than
 * numeric ordering — trailing zeros that mean something — use {@link string}.
 */
export const decimal: AttributeCodec<string, Attribute<'N'>> = codec({
    def: { kind: 'decimal' },
    encode: (value) =>
        isStoredNumeral(value)
            ? carrying('N', value)
            : new CodecError(
                  `'${value}' is not a numeral DynamoDB stores unchanged; it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
              ),
    decode: (attribute) =>
        andThen(expect('N', attribute), (carried) =>
            isStoredNumeral(carried)
                ? carried
                : new CodecError(
                      `'${carried}' is not a numeral in the form DynamoDB stores, so this attribute was not written by it`,
                  ),
        ),
})

/**
 * A JS number, stored as `N`. Lossy by construction — `N` carries 38 digits, `number` about 15.
 * Right for enums, counts and flags; wrong for money, which is {@link decimal}.
 */
export const number: AttributeCodec<number, Attribute<'N'>> = codec({
    def: { kind: 'number' },
    encode: (value) =>
        isNumeral(value.toString())
            ? carrying('N', value.toString())
            : new CodecError(
                  `${value} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN or Infinity`,
              ),
    /**
     * Both gates, and the second is not redundant. `Number('9.9999999999999999999999999999999999999E+125')`
     * rounds *up* to `1e126`, which is past the maximum — so a numeral DynamoDB stores can read
     * back as a number this codec cannot write. Checking only the stored digits would leave `decode`
     * accepting a value `encode` refuses, which is `(C)` failing.
     */
    decode: (attribute) =>
        andThen(expect('N', attribute), (carried) => {
            if (!isNumeral(carried)) {
                return new CodecError(
                    `'${carried}' is not a numeral, so this attribute was not written by DynamoDB`,
                )
            }
            const read = Number(carried)
            return isNumeral(read.toString())
                ? read
                : new CodecError(
                      `'${carried}' reads back as ${read}, which is outside the range DynamoDB stores`,
                  )
        }),
})

/** A boolean, as `BOOL`. */
export const boolean: AttributeCodec<boolean, Attribute<'BOOL'>> = codec({
    def: { kind: 'boolean' },
    encode: (value) => carrying('BOOL', value),
    decode: (attribute) => expect('BOOL', attribute),
})

/**
 * The `NULL` point: the one value `null`, stored as `⟨NULL, ∗⟩`.
 *
 * Named `nullValue` because `null` is a keyword and `NULL` is already the attribute type. It says
 * what it holds, which is the whole of it — one value.
 *
 * What it is for: a tombstone, and a payload-free option of a discriminated union. Before it, a
 * schema could say "this attribute is a string" or "this attribute is optional", and could not say
 * "this attribute is exactly `NULL`" — the value language had `null` and the attribute domain had
 * `NULL`, and no codec denoted either. That gap was found by asking whether `nullable(c)` could be
 * written as `union(c, nullValue)`; it could not, because the right-hand side was not expressible.
 *
 * Distinct from {@link nullable}, which *adds* `null` to another codec's held set. This holds
 * nothing else.
 */
export const nullValue: AttributeCodec<null, Attribute<'NULL'>> = codec({
    def: { kind: 'null' },
    // checked, though the type already says so: the admissible set is one value and this library
    // owns it, so an unchecked `encode` would write `NULL` for anything that reached it — a pair
    // whose `e` is defined outside its own held set. {@link literal} checks for the same reason
    encode: (value) =>
        value === null
            ? carrying('NULL', true)
            : new CodecError(
                  `${JSON.stringify(value)} is not null, and this codec holds nothing else`,
              ),
    decode: (attribute) => andThen(expect('NULL', attribute), () => null),
})

/** Binary, as `B`. */
export const binary: AttributeCodec<Uint8Array, Attribute<'B'>> = codec({
    def: { kind: 'binary' },
    encode: (value) => carrying('B', value),
    decode: (attribute) => expect('B', attribute),
})

// ── collections ─────────────────────────────────────────────────────

/**
 * A non-empty array, stored as the native set its members belong to.
 *
 * Which set follows from the element's {@link AttributeCodec.member}: `SS`, `NS` or `BS`. Taking a
 * codec rather than being fixed to strings is what makes `set(price)` decode back as prices.
 *
 * **Order is not preserved.** A DynamoDB set comes back in an order the service chooses, so both
 * directions sort. `decode ∘ encode = id` therefore holds only for canonical values; for the rest
 * the law is {@link checkStable}. If order carries meaning use `array(...)`.
 *
 * **Empty is not representable** — encode throws rather than writing what the service refuses.
 */
export const set = <const C extends AnyCodec>(
    element: C & NotAboutAbsence<C>,
): AttributeCodec<ReadonlySet<Decoded<C>>, SetOf<C>> => {
    type T = Decoded<C>
    const inner = element as unknown as AttributeCodec<T>
    const member = writes(inner)
    if (member !== 'S' && member !== 'N' && member !== 'B') {
        throw new CodecError(
            `a set holds strings, numbers or binary, and this element writes ${member ? `'${member}'` : 'no single member'}`,
        )
    }
    const setMember = `${member}S` as 'SS' | 'NS' | 'BS'

    const carried = (value: T): Result<string | Uint8Array> =>
        andThen(
            inner.encode(value),
            (written) =>
                (written as Record<string, unknown>)[member] as
                    | string
                    | Uint8Array,
        )

    // the member is decided above, from the element; the cast carries that decision into the type
    return codec<ReadonlySet<T>, SetOf<C>>({
        def: { kind: 'set', element: inner },
        encode: (value) =>
            value.size === 0
                ? new CodecError(
                      `DynamoDB has no empty ${setMember}; omit the attribute or use array(...)`,
                  )
                : andThen(
                      every([...value], carried),
                      (written) =>
                          // sorted so what is stored does not depend on insertion order; deduplicated
                          // already, because a `Set` is
                          carrying(
                              setMember,
                              [...new Set(written)].sort() as never,
                          ) as SetOf<C>,
                  ),
        // the empty set is refused in *both* directions, and the read side is the one that
        // matters: DynamoDB never stores an empty `SS`, so an item carrying one was written by
        // something else. Decoding it would hand back a value this codec's own `encode` refuses —
        // the pair's two halves disagreeing about what it holds, which is (C) failing
        decode: (attribute) =>
            andThen(
                andThen(expect(setMember, attribute), (members) =>
                    (members as readonly unknown[]).length === 0
                        ? new CodecError(
                              `DynamoDB has no empty ${setMember}, so this attribute was not written by it; a set this codec would refuse to write is not one it can read`,
                          )
                        : every(members as readonly unknown[], (raw) =>
                              inner.decode(carrying(member, raw as never)),
                          ),
                ),
                (read) => new Set(read) as ReadonlySet<T>,
            ),
    })
}

export const array = <const C extends AnyCodec>(
    element: C & NotAboutAbsence<C>,
): AttributeCodec<readonly Decoded<C>[], L<AttributeOf<C>>> => {
    type T = Decoded<C>
    const items = element as unknown as AttributeCodec<T>
    return codec<readonly T[], L<AttributeOf<C>>>({
        def: { kind: 'array', element: items },
        // the codec's own methods rather than a wrapper around them: a closure per call to encode
        // a list is a closure per list in every item written
        encode: (value) =>
            andThen(
                every(value, items.encode),
                (written) => carrying('L', written) as L<AttributeOf<C>>,
            ),
        decode: (attribute) =>
            andThen(expect('L', attribute), (carried) =>
                every(carried, items.decode),
            ),
    })
}

/**
 * A fixed-length, heterogeneous list, as `L`.
 *
 * `list` gives `readonly T[]`, which cannot say that a route is one step or exactly two. Decode
 * checks the length, because a tuple whose arity is wrong is not the type it claims to be.
 */
export const tuple = <const Cs extends readonly AnyCodec[]>(
    // asked of the union of the elements rather than mapped over them: one instantiation instead of
    // one per position, and the diagnostic lands on the call either way. Mapping cost +10% across
    // this repo, measured. `rest` is exempt, and checked for position separately
    ...elements: Cs &
        NotAboutAbsence<
            // matched on the marker alone, never on `RestCodec<unknown, …>`: `AttributeCodec` names
            // its value on both sides, so it is invariant and the wider one does not match
            Exclude<Cs[number], { readonly [restMarker]: true }>
        > &
        RestGoesLast<Cs>
): AttributeCodec<TupleOf<Cs>, L<TupleWrites<Cs>>> => {
    const all = elements.map(
        (element) => element as unknown as AnyCodec,
    ) as readonly AnyCodec[]

    /**
     * The tail is split off once, here, rather than asked for per row.
     *
     * `RestGoesLast` has already refused it anywhere but the end, so the last element is the only one
     * that can be marked and looking at it is enough.
     */
    const last = all[all.length - 1]
    const tail =
        last?.def?.kind === 'restOf' ? (last.def.inner as AnyCodec) : undefined
    const items = tail ? all.slice(0, -1) : all

    return codec({
        def: { kind: 'tuple', elements: items, tail },
        encode: (value) => {
            const held = value as readonly unknown[]
            if (!tail && held.length !== items.length) {
                return new CodecError(
                    `expected ${items.length} elements, found ${held.length}`,
                )
            }
            if (tail && held.length < items.length) {
                return new CodecError(
                    `expected at least ${items.length} elements, found ${held.length}`,
                )
            }
            return andThen(
                every(held, (one, index) =>
                    (items[index] ?? (tail as AnyCodec)).encode(one as never),
                ),
                (written) => carrying('L', written),
            )
        },
        decode: (attribute) =>
            andThen(expect('L', attribute), (carried) => {
                if (!tail && carried.length !== items.length) {
                    return new CodecError(
                        `expected a list of ${items.length}, found ${carried.length}`,
                    )
                }
                if (tail && carried.length < items.length) {
                    return new CodecError(
                        `expected a list of at least ${items.length}, found ${carried.length}`,
                    )
                }
                return every(carried, (one, index) =>
                    (items[index] ?? (tail as AnyCodec)).decode(
                        one as AttributeValue,
                    ),
                ) as never
            }),
        // as with `record` and `map`, the cast keeps the shape each position writes, which
        // `Attribute<'L'>` would flatten to "some list"
    }) as unknown as AttributeCodec<TupleOf<Cs>, L<TupleWrites<Cs>>>
}

/**
 * What a tuple holds: the fixed positions, and then the tail if it has one.
 *
 * Split by peeling the last element, which is the only one a rest may be — so a tuple without one
 * maps position for position exactly as it always did.
 */
export type TupleOf<Cs extends readonly unknown[]> = Cs extends readonly [
    ...infer Head,
    infer Last,
]
    ? Last extends { readonly [restMarker]: true }
        ? readonly [
              ...{ [I in keyof Head]: Decoded<Head[I]> },
              ...Decoded<Last>[],
          ]
        : { readonly [I in keyof Cs]: Decoded<Cs[I]> }
    : { readonly [I in keyof Cs]: Decoded<Cs[I]> }

/**
 * The same split, on the stored side.
 *
 * Both sides match the *marker* and then extract with {@link Decoded} and {@link AttributeOf}, rather
 * than inferring through `RestCodec<…>`. Inferring is the trap: `AttributeCodec` names its value on
 * both sides, so `RestCodec<unknown, infer A>` matches nothing and this fell to the fixed-arity branch
 * — a tuple with a tail typed as though its tail were one element. Silently, because a fixed `[S, N,
 * N]` *is* assignable to `readonly [S, N, ...N[]]`, so an assignment could not tell.
 */
export type TupleWrites<Cs extends readonly unknown[]> = Cs extends readonly [
    ...infer Head,
    infer Last,
]
    ? Last extends { readonly [restMarker]: true }
        ? readonly [
              ...{ [I in keyof Head]: AttributeOf<Head[I]> },
              ...(AttributeOf<Last> & AttributeValue)[],
          ]
        : { readonly [I in keyof Cs]: AttributeOf<Cs[I]> }
    : { readonly [I in keyof Cs]: AttributeOf<Cs[I]> }

/**
 * Nothing, or why a marker cannot wrap another marker.
 *
 * `optional` and `fallback` are both statements about a *name*, so one wrapping the other says the
 * same thing twice — and said it wrongly. Only the outermost mark was read: `optional(fallback(c, v))`
 * dropped the stand-in entirely and left the attribute simply absent, while
 * `fallback(optional(c), v)` stood in on the way out and then *required* the value on the way back.
 * Both spellings mean `fallback(c, v)`, which is the one that works.
 *
 * `rest` is refused for the same reason from the other direction: it marks a position, and a name is
 * not one.
 */
type NotAlreadyMarked<C> = [Extract<C, AboutAbsence>] extends [never]
    ? unknown
    : ErrorMessage<'this codec is already marked: `optional`, `fallback` and `rest` each mark a declaration once, and nesting them reads only the outermost — `fallback(c, v)` is the attribute that may be absent and has a stand-in'>

/**
 * Nothing, or why a tuple's tail is not an attribute.
 *
 * An item's members are reached by *name*, so `optional` and `fallback` belong here — both are
 * statements about a name. `rest` is a statement about a *position*, and there are no positions in a
 * map, so it is the one marker an object member cannot be.
 */
type NoTail<Spec> = [
    Extract<Spec[keyof Spec], { readonly [restMarker]: true }>,
] extends [never]
    ? unknown
    : ErrorMessage<"`rest(...)` is a tuple's tail, not an attribute: an item has names and not positions">

/**
 * Nothing, or why a rest element is not where it has to be.
 *
 * "The rest" is only a thing to be once, and only at the end. Checked by asking whether any element
 * *but* the last is marked, which is one instantiation over the head rather than one per position.
 */
export type RestGoesLast<Cs extends readonly unknown[]> = Cs extends readonly [
    ...infer Head,
    unknown,
]
    ? [Extract<Head[number], { readonly [restMarker]: true }>] extends [never]
        ? unknown
        : ErrorMessage<'`rest(...)` is the tail of a tuple, so it goes last and only once — every earlier position is a fixed element'>
    : unknown

/**
 * A tuple's trailing elements: *and then any number of these*.
 *
 * The counterpart of `...T[]` in a tuple type, and restricted the same way — it is meaningful only as
 * the last element of a {@link tuple}, because "the rest" is only a thing to be once. Every other
 * position refuses it, and the type says so rather than a runtime check discovering it.
 *
 * @example
 * ```ts
 * tuple(string, number, rest(decimal))   // readonly [string, number, ...string[]]
 * tuple(rest(string))                    // readonly string[], but stored as L with no minimum
 * ```
 */
export const rest = <const C extends AnyCodec>(
    element: C & NotAboutAbsence<C>,
): RestCodec<Decoded<C>, AttributeOf<C> & AttributeValue> =>
    ({
        ...(element as object),
        def: { kind: 'restOf', inner: element as unknown as AnyCodec },
    }) as unknown as RestCodec<Decoded<C>, AttributeOf<C> & AttributeValue>

/** A codec marked for a tuple's tail. Carries what it holds and what it writes, unchanged. */
export type RestCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = AttributeCodec<T, A> & { readonly [restMarker]: true }

/** A homogeneous string-keyed record, as `M`. */
export const record = <const C extends AnyCodec>(
    element: C & NotAboutAbsence<C>,
): AttributeCodec<
    Readonly<Record<string, Decoded<C>>>,
    M<{ readonly [key: string]: AttributeOf<C> }>
> => {
    const values = element as unknown as AttributeCodec<Decoded<C>>
    // the cast keeps the *shape* the values write, which `Attribute<'M'>` would flatten to
    // "some map" — the same reason `map` casts
    return codec({
        def: { kind: 'record', value: values },
        encode: (value: Record<string, Decoded<C>>) =>
            andThen(everyEntry(value, values.encode), (written) =>
                carrying('M', written),
            ),
        decode: (attribute) =>
            andThen(expect('M', attribute), (carried) =>
                everyEntry(carried, values.decode),
            ),
    }) as unknown as AttributeCodec<
        Readonly<Record<string, Decoded<C>>>,
        M<{ readonly [key: string]: AttributeOf<C> }>
    >
}

// ── narrowing ───────────────────────────────────────────────────────

/**
 * Narrows what a codec decodes to, checking it on the way in.
 *
 * Where a brand gets applied. `decimal` cannot stand in for a `Price` because `decode` returns a
 * bare `string` — and a row is data somebody else wrote, so running the brand's own predicate is
 * the right way to get one back, rather than asserting.
 *
 * @example
 * ```ts
 * const price = refine(decimal, isPrice, {
 *     // `decimal` generates negatives, which are not Prices; say what a valid one looks like
 *     arbitrary: (rng) => pick(rng, ['0', '1', '0.5']) as Price,
 * })
 * const petId = refine(string, isPetId)
 * ```
 *
 * **The obligation is `is`, and it is yours.** Like `held`'s pair and `custom`'s two functions,
 * `refine` is sound *iff* the predicate honestly decides `Narrow` — nothing here can check that,
 * because `Narrow` is a type and `is` is a claim about it. What follows from the claim is why the
 * two directions are checked differently:
 *
 * - **`decode` runs `is`.** A stored value was never type-checked — a row is data somebody else
 *   wrote — so the predicate is the only thing between the database and `Narrow`.
 * - **`encode` does not.** Its argument is already a `Narrow`, and TypeScript is what says so.
 *   Re-running `is` would assert nothing the call site had not already asserted.
 *
 * The asymmetry tracks how far the type system's guarantee reaches. Past that edge — `unsafeEncode`
 * still runs `encode`, but an `as` upstream of it is not checked by anything — `refine` will write
 * a value it would refuse to read. {@link literal} checks both directions for exactly that reason:
 * a union can widen a field's type, so the guarantee is not available, and its admissible set is
 * data this library owns, which gives the check an authority a caller's predicate cannot have.
 */
export const refine = <Wide, Narrow extends Wide, A extends AttributeValue>(
    inner: AttributeCodec<Wide, A>,
    is: (value: Wide) => value is Narrow,
    options: {
        /**
         * Values satisfying `is`.
         *
         * Optional, but supply it when the inner codec's values rarely pass: generation falls back
         * to filtering, and a predicate that rejects most of what it sees wastes the search.
         */
        readonly arbitrary?: (rng: Rng, size: number) => Narrow
        /** Named in the error when a stored value fails the check. */
        readonly describe?: string
        /**
         * Told when filtering keeps less than half of what it generates, instead of `console.warn`.
         *
         * Only ever called from a generator, so only ever during a property run.
         */
        readonly onThinSearch?: (what: string, rate: number) => void
    } = {},
): AttributeCodec<Narrow, A> => {
    const what = options.describe ?? 'the expected form'

    /**
     * Generation falls back to filtering the inner codec's values, and reports when that thins the
     * search badly.
     *
     * `decimal` generates negatives, which are not prices, and fractions, which are not sequence numbers —
     * so a run of a hundred cases can quietly be a run of forty. The declaration is not the place to
     * fix that: a predicate is what a brand *is*, and demanding an example of one beside it would
     * tax every codec for something only a property run cares about. But a run that has been halved
     * without saying so is worth a word, and this can only be reached from a generator, so the word
     * only ever lands in a test.
     */
    // `writes` reads through a refinement, which is what lets `set(price)` work; `decides` does
    // not, because the predicate may be exactly what rejects the constant
    return derive<Narrow, A>(inner, {
        def: {
            kind: 'refine',
            inner: inner as AnyCodec,
            refined: {
                is: is as (value: never) => boolean,
                what,
                arbitrary: options.arbitrary as
                    | ((rng: Rng, size: number) => unknown)
                    | undefined,
                onThinSearch: options.onThinSearch,
            },
        },
        encode: (value) => inner.encode(value),
        decode: (attribute) =>
            andThen(inner.decode(attribute), (decoded) =>
                is(decoded)
                    ? decoded
                    : new CodecError(
                          `${JSON.stringify(decoded)} is not ${what}`,
                      ),
            ),
    })
}

// ── reading what is already there ───────────────────────────────────

/** Type-level only, for the same reason as {@link optionalMarker}: the def carries the fact. */

/** A codec that stands in a value where the attribute is absent. */
export type FallbackCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = AttributeCodec<T, A> & { readonly [fallbackMarker]: () => T }

/**
 * Reads a missing attribute as a value, and writes the attribute always.
 *
 * Not {@link optional}: the entity always has it, the *data* may not — a row written before the
 * attribute existed. Replaces `item.channel ?? 'IN_STORE'` at every read site. The value is
 * produced per read, so a mutable default cannot leak between entities.
 */
export const fallback = <const C extends AnyCodec>(
    // the *argument's own* type, not a re-declared `AttributeCodec<T, A>`: the guard has to see the
    // marker the caller passed, and a parameter written in terms of inferred `T` and `A` reconstructs
    // a plain codec that never carries one
    inner: C & NotAlreadyMarked<C>,
    // `NoInfer` so the codec is the only thing that says what it holds. Inferring from both sites
    // unified them, and a thunk returning `'A'` widens to `string`, which then refused the very
    // codec it stands in for — invisible while the entity was declared first and pinned it itself
    value: () => NoInfer<Decoded<C>>,
): FallbackCodec<Decoded<C>, AttributeOf<C> & AttributeValue> =>
    described(inner as unknown as AttributeCodec<Decoded<C>>, {
        kind: 'fallback',
        inner: inner as unknown as AnyCodec,
        value,
    }) as unknown as FallbackCodec<Decoded<C>, AttributeOf<C> & AttributeValue>

const fallbackOf = (codec: AnyCodec): (() => unknown) | undefined =>
    codec.def?.kind === 'fallback' ? codec.def.value : undefined

/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart: an attribute is **stored** as `S`, `N`, `SS` — and it is
 * **held**, in your code, as a `string`, a `Date`, an array. Every other combinator changes the first
 * or narrows the second. This one changes only the second, by naming the two halves of the
 * conversion, and leaves what the table holds exactly as it was.
 *
 * Which makes it the answer to "my values arrive as an array and `set(...)` wants a `Set`": nothing
 * about the *table* has to change for that, so nothing about the codec does either. It is also the
 * one to reach for before {@link custom} — the member, the generation and the definition all keep
 * coming from the codec underneath, where a hand-written codec has to restate them.
 *
 * @example
 * ```ts
 * // stored as SS, held as an array
 * const tags = held(set(string), {
 *     encode: (tags: readonly string[]) => new Set(tags),
 *     decode: (tags) => [...tags],
 * })
 *
 * // stored as S, held as a Date
 * const when = held(string, {
 *     encode: (at: Date) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * **Both halves are total.** A conversion that can fail is two things at once, and they compose
 * better apart: narrow the inner codec first, so the failure is reported where the value is actually
 * wrong and with a message about it.
 *
 * ```ts
 * held(refine(string, isIsoDate, { describe: 'an ISO timestamp' }), {
 *     encode: (at: Date) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * The pair must round-trip — `decode(encode(x))` equal to `x`, and `encode(decode(y))` equal to `y` —
 * or the codec's own law does not hold either. `checkRoundTrip` over a spec holding one is what
 * establishes it, and generation reaches through: values are generated for the inner codec and
 * handed out through `decode`, so what is generated is always something the pair produced.
 */
export const held = <T, const C extends AnyCodec>(
    inner: C,
    adapt: {
        /** The value, as the inner codec holds it. Runs on the way to the table. */
        readonly encode: (value: T) => NoInfer<Decoded<C>>
        /** What the inner codec read, as you hold it. Runs on the way back. */
        readonly decode: (held: Decoded<C>) => NoInfer<T>
    },
): AttributeCodec<T, AttributeOf<C>> => {
    const held = inner as unknown as AttributeCodec<Decoded<C>>

    /**
     * The two halves are the one place in a codec where code this library did not write runs.
     *
     * So the throw is contained here. A conversion is ordinary code and ordinary code throws — `new
     * Set(4)` for an adapter typed to take an array, a `.toISOString()` on something that is not a
     * `Date` — and a codec that let that escape would make every caller defensive about it. One of
     * them already was: a union tries an option to find out whether it is the right one, and had to
     * catch, which meant it also swallowed failures that were nothing to do with an adapter.
     *
     * A `CodecError` is what every caller already handles, so that is what a throw becomes.
     */
    const guarded =
        <A, B>(convert: (value: A) => B, direction: 'writing' | 'reading') =>
        (value: A): Result<B> => {
            try {
                return convert(value)
            } catch (thrown) {
                return new CodecError(
                    `the conversion for ${direction} this attribute threw: ${
                        thrown instanceof Error
                            ? thrown.message
                            : String(thrown)
                    }`,
                )
            }
        }

    const into = guarded(adapt.encode, 'writing')
    const outOf = guarded(adapt.decode, 'reading')

    return codec<T, AttributeOf<C>>({
        def: {
            kind: 'held',
            inner: inner as unknown as AnyCodec,
            adapt: adapt as CodecDefHeldAdapt,
        },
        encode: (value) =>
            andThen(into(value), held.encode) as Result<AttributeOf<C>>,
        decode: (attribute) => andThen(held.decode(attribute), outOf),
    })
}

/** The erased shape {@link CodecDef} carries for a {@link held} adapter. */
type CodecDefHeldAdapt = {
    readonly encode: (value: never) => unknown
    readonly decode: (held: never) => unknown
}

/**
 * One direction, which is all an older encoding is ever asked for.
 *
 * `legacy` never writes through `older` — that is the whole of what makes it a migration rather than
 * a union — so asking for a whole codec there asked for a half nobody calls. It also *forced* one:
 * an older encoding whose held type differs from the current one has to be adapted, and {@link held}
 * requires both halves, so adapting a reader meant writing an encode path that is dead by
 * construction. Every `AttributeCodec<T>` is one of these, so nothing that worked stops working.
 *
 * @example
 * ```ts
 * // stored as N now; some rows still hold the digits as B, from a migration nobody finished
 * legacy({
 *     current: decimal,
 *     older: { decode: (at) => andThen(binary.decode(at), (b) => decoder.decode(b)) },
 * })
 * ```
 */
export type Reader<T> = {
    readonly decode: (attribute: AttributeValue) => Result<T>
}

/**
 * Reads any of several encodings, writes only `current`.
 *
 * A table holds every shape it has ever held. Reading tolerantly and writing canonically converges:
 * old rows stay readable and every write moves one closer. `decode ∘ encode = id` survives because
 * encode only ever produces `current`.
 *
 * Deliberately breaks {@link checkMembersStable} — changing what is stored *is* the migration — so
 * an index key cannot use it: DynamoDB rejects a write whose index key has the wrong type.
 *
 * @example
 * **One older encoding.** A table that has held three needs two of these, nested — and `legacy` is
 * itself a {@link Reader}, so it nests directly:
 *
 * ```ts
 * legacy({ current: decimal, older: legacy({ current: string, older: fromBytes }) })
 * ```
 *
 * Not a union: {@link union} requires its options to read back as *different* types so that a value
 * says which one it is, and every encoding of one attribute reads back as the same type by
 * definition. Which is the whole difference between the two — a union asks "which of these is it",
 * a migration asks "can any of these still read it".
 *
 * ```ts
 * // stored as N today, and as S in rows written before that; always written as N
 * rate: legacy({ current: decimal, older: string })
 * ```
 */
export const legacy = <T, A extends AttributeValue>({
    current,
    older,
}: {
    readonly current: AttributeCodec<T, A>
    readonly older: Reader<T>
}): AttributeCodec<T, A> =>
    // `writes` reads through to `current`, the encoding every write produces; `decides` does not,
    // because an older reader can decode this attribute into something else entirely
    derive<T, A>(current, {
        def: { kind: 'legacy', current: current as AnyCodec },
        encode: (value) => current.encode(value),
        decode: (attribute) => {
            // the current encoding is tried first and on its own, so the path every row written
            // since the migration takes allocates nothing: no `[current, ...older]` to walk and no
            // list of reasons to collect for a failure that did not happen
            const read = current.decode(attribute)
            if (!failed(read)) return read
            const older_ = older.decode(attribute)
            if (!failed(older_)) return older_ as T
            return new CodecError(
                `no encoding could read this attribute; tried the current one and one older: ${read} | ${older_}`,
            )
        },
    })

/**
 * A codec resolved on first use, so an entity can contain itself.
 *
 * `item()` evaluates its spec eagerly, so a category whose children are categories cannot name
 * itself — the constant is not initialised yet. A thunk defers that to the first encode, decode or
 * path walk, by which time it is.
 *
 * Resolved once and kept. Declares no {@link AttributeCodec.member}: reading one would force
 * resolution at construction, which is the cycle this exists to break, so a lazy codec cannot be a
 * set's element — no loss, since a set holds strings, numbers or binary and none of those recurse.
 *
 * @example
 * ```ts
 * type Category = { name: string; children?: readonly Category[] }
 *
 * const Category: AttributeCodec<Category, Attribute<'M'>> = lazy(() =>
 *     object({ name: string, children: optional(array(Category)) }),
 * )
 * ```
 */
export const lazy = <T, A extends AttributeValue = AttributeValue>(
    get: () => Nestable<T>,
): AttributeCodec<T, A> => {
    let resolved: AttributeCodec<T> | undefined
    const inner = (): AttributeCodec<T> => {
        resolved ??= get()
        return resolved
    }
    return codec<T, A>({
        def: { kind: 'lazy', get: () => inner() as AnyCodec },
        encode: (value) => inner().encode(value) as Result<A>,
        decode: (attribute) => inner().decode(attribute),
    })
}

// ── presence ────────────────────────────────────────────────────────

/**
 * An attribute that may be absent — which is not the same as null. `{ NULL: true }` is an attribute
 * DynamoDB *has*; use {@link nullable} for that.
 *
 * `undefined` is not injective in: `{ a: undefined }` and `{}` both encode without `a`.
 */
export const optional = <const C extends AnyCodec>(
    inner: C & NotAlreadyMarked<C>,
): OptionalCodec<Decoded<C>, AttributeOf<C>> => {
    const attribute = inner as unknown as AttributeCodec<Decoded<C>>
    return described(attribute, {
        kind: 'optional',
        inner: attribute as AnyCodec,
    }) as OptionalCodec<Decoded<C>, AttributeOf<C>>
}

/** A value that may be null, stored as `NULL` when it is. */
export const nullable = <T, A extends AttributeValue>(
    inner: AttributeCodec<T, A>,
): AttributeCodec<T | null, A | Attribute<'NULL'>> =>
    derive<T | null, A | Attribute<'NULL'>>(inner, {
        def: { kind: 'nullable', inner: inner as AnyCodec },
        encode: (value) =>
            value === null
                ? (carrying('NULL', true) as A | Attribute<'NULL'>)
                : (inner.encode(value) as Result<A | Attribute<'NULL'>>),
        decode: (attribute) =>
            memberOf(attribute) === 'NULL' ? null : inner.decode(attribute),
    })

const isOptional = (codec: AnyCodec): boolean => codec.def?.kind === 'optional'

// ── the escape hatch ────────────────────────────────────────────────

/**
 * Any attribute, decoded to `unknown`.
 *
 * The honest default. Where no schema states which member a value takes, the decoded type is not
 * knowable, so this returns `unknown` and the cast is yours to write — visibly, at the one place it
 * is needed, rather than hidden inside a marshaller applied to every field of every table.
 *
 * The domain is exactly the values whose type is recoverable, so `decode ∘ encode = id` holds for
 * everything accepted and everything else is named and refused. See {@link opaque.Numbers} for the
 * one case that cannot be decided without being told.
 */
const withNumbers = (numbers: opaque.Numbers): AttributeCodec<unknown> =>
    codec({
        def: { kind: 'opaque', numbers },
        encode: (value) => encodeUnknown(value, numbers),
        decode: (attribute) => decodeUnknown(attribute, numbers),
    })

/**
 * Any attribute, with numbers refused — which guesses nothing.
 *
 * One entry point with its only parameter optional, the shape {@link native} takes: `opaque` *is* the
 * refusing codec, so `opaque.encode(value)` needs no call, and calling it chooses the other policy.
 * It was three names for two codecs — `opaqueOf(numbers)`, `opaque` and `opaque.lossy` — which is a
 * constructor, a default and a sibling for a decision with exactly two answers.
 *
 * ```ts
 * opaque.encode(value)            // a number is refused
 * opaque('lossy').encode(value)   // `number` ⇄ `N`, digits only while a float holds them
 * ```
 *
 * Callable *and* a codec, which is what lets `opaque.encode` and {@link opaque.Encode} keep the same
 * name.
 */
export const opaque: AttributeCodec<unknown> & {
    (numbers?: opaque.Numbers): AttributeCodec<unknown>
} = Object.assign(
    (numbers: opaque.Numbers = 'refuse') => withNumbers(numbers),
    withNumbers('refuse'),
)

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
 * back as a `Set`, and an `N` under `'refuse'` is a refusal rather than a value — and it is not a
 * mirror of {@link native.Decode}.
 */
export namespace opaque {
    /**
     * What an unknown attribute does with `N`.
     *
     * There is no third option. `N` is a decimal string and no JS scalar carries it faithfully: decoding
     * to `number` rounds anything wider than a float, and decoding to `string` re-encodes as `S` —
     * silently changing the attribute's *stored type* on the next write, which breaks numeric sort keys
     * and comparisons downstream. Without a schema there is nothing to decide it with, so the decision
     * belongs to the caller and has to be made out loud.
     *
     * - `'refuse'` — numbers are not written, and reading an `N` throws. Nothing is guessed.
     * - `'lossy'` — `number` ⇄ `N`. The member always survives a read-modify-write; the digits survive
     *   only while they fit in a float.
     */
    export type Numbers = 'refuse' | 'lossy'

    /**
     * What {@link opaque} writes for a value of type `T`, or why it refuses to.
     *
     * The counterpart of {@link native.Encode} for *this* package's marshaller, and they are not the
     * same function. `opaque` refuses a number unless told what to do with `N`, refuses a `bigint`, refuses a
     * set of numbers, refuses a `Map`, and refuses a class instance — because each of those decodes back
     * as something else, and its whole domain is the values whose type survives a round trip. The SDK's
     * marshaller accepts all of them. So a team whose in-house marshaller resembles `opaque` needs this
     * type to diff against, not that one.
     *
     * Every branch mirrors one in `encodeUnknown`, refusals included: where the runtime returns a
     * {@link CodecError}, this resolves to an {@link ErrorMessage} carrying the same reason. A shape
     * containing a refused value therefore fails to *describe*, rather than describing a write that
     * throws.
     *
     * One place it is more permissive than the runtime, and deliberately: a class instance is refused at
     * runtime by checking the prototype, which no type can do. `Date` is named because it is the one the
     * runtime's own error message names, but a type cannot tell an arbitrary instance from a plain
     * object — so `Encode<SomeClass>` describes it as `M` where `encode` would refuse it.
     */
    export type Encode<T, Of extends Numbers = 'refuse'> = [T] extends [never]
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
                        : ErrorMessage<"[opaque] a number is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`. Declare it with `number` or `decimal`, or opt in with `opaque('lossy')`">
                    : T extends bigint
                      ? ErrorMessage<'[opaque] a bigint shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`'>
                      : T extends ReadonlySet<infer Member>
                        ? [Member] extends [string]
                            ? SS
                            : [Member] extends [Uint8Array]
                              ? BS
                              : ErrorMessage<'[opaque] `NS` decodes as strings, because its members are decimal strings. Use a set of strings, or `array(number)` if the order does not matter'>
                        : T extends ReadonlyMap<unknown, unknown>
                          ? ErrorMessage<'[opaque] DynamoDB has one map member, `M`, and it decodes as a plain object. Pass an object, or use `record(...)` to state the value type'>
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
    export type ItemEncode<T, Of extends Numbers = 'refuse'> = show<
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
     * - `NS` is a **refusal**, where the SDK's answers `Set<number | bigint>`. Its members are
     *   decimal strings and nothing without a schema can say which of them a JS number holds
     *   faithfully — so this codec will not *write* a set of numbers, and a member it cannot
     *   write is one it cannot read. It read back as `Set<string>` until that was noticed:
     *   re-encoding turned an `NS` into an `SS`, changing the attribute's stored type on a
     *   read-modify-write. See `Calculus.Lawful.no_read_without_write`.
     * - `N` under the default policy is a *refusal*, where the SDK's always reads a number.
     * - `L` and `M` carry a refused member out with them, the way {@link opaque.Encode} does, so a
     *   list of `N` under `'refuse'` is the refusal itself rather than a list of nothing.
     *
     * A bare {@link AttributeValue} distributes, which is the useful answer: it resolves to every
     * value a stored attribute could be read as, the refusal for `N` among them.
     */
    export type Decode<A, Of extends Numbers = 'refuse'> = [A] extends [never]
        ? never
        : A extends NULL
          ? null
          : A extends BOOL
            ? boolean
            : A extends N
              ? Of extends 'lossy'
                  ? number
                  : ErrorMessage<"[opaque] a stored number is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`. Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`">
              : A extends S
                ? string
                : A extends B
                  ? Uint8Array
                  : A extends SS
                    ? Set<string>
                    : A extends NS
                      ? // a member this codec cannot write is a member it cannot read: `NS`
                        // has no write path here, so reading one would re-encode as `SS` and
                        // change the attribute's stored type — (MP), which `μ = ⊤` leaves as
                        // the only law watching
                        ErrorMessage<'[opaque] a stored set of numbers has no counterpart this codec can write, so reading it would re-encode as `SS`. Declare the attribute with `set(number)` or `set(decimal)`'>
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
    export type ItemDecode<Item, Of extends Numbers = 'refuse'> = show<{
        [K in keyof Item]: Decode<Exclude<Item[K], undefined>, Of>
    }>
}

/** Only plain objects round-trip; anything with a prototype loses it. */
const isPlainObject = (value: object) => {
    const prototype = Object.getPrototypeOf(value)
    return prototype === Object.prototype || prototype === null
}

const unrecoverable = (what: string, instead: string) =>
    new CodecError(
        `${what} cannot be stored as an unknown attribute, because decoding could not tell it apart from what it decodes to. ${instead}`,
    )

/**
 * Encodes a value whose type is recoverable from what is stored, and refuses one whose is not.
 *
 * The domain is deliberately narrow, so that `decode ∘ encode = id` holds for everything accepted.
 * Accepted: `null`, `string`, `boolean`, `Uint8Array`, a non-empty `Set` of strings or of binary,
 * arrays, and plain objects — recursively. A `number` only under `'lossy'`; see
 * {@link opaque.Numbers} for why that one cannot be decided here.
 */
const encodeUnknown = (
    value: unknown,
    numbers: opaque.Numbers,
): Result<AttributeValue> => {
    if (value === null) return carrying('NULL', true)
    if (typeof value === 'string') return carrying('S', value)
    if (typeof value === 'boolean') return carrying('BOOL', value)
    if (value instanceof Uint8Array) return carrying('B', value)

    if (typeof value === 'number') {
        if (!Number.isFinite(value)) {
            return new CodecError(`DynamoDB has no number for ${value}`)
        }
        if (numbers === 'refuse') {
            return unrecoverable(
                'a number',
                "Reading it back is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`, changing the attribute's stored type. Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`.",
            )
        }
        /**
         * **Writing an `N` means writing a numeral.** `Number.isFinite` is not that test: §1's
         * `Carries('N')` is `Numerals`, bounded by 38 significant digits and magnitude
         * `1e-130 … 9.9…e125`, and `5e-324` is a perfectly finite double outside it — the
         * specification's own example of the bound going unchecked.
         *
         * `number` has gated on this since the numeral domain was tightened and `literal` since
         * its `ℓ ⊆ D` premise. `opaque` is the third term that writes an `N` from a JS number and
         * it was checking only that the number existed, which let it write an attribute §1's `𝔸`
         * has no point for. Same obligation, same gate: `ran(e) ⊆ 𝔸`.
         */
        return isNumeral(String(value))
            ? carrying('N', String(value))
            : new CodecError(
                  `${value} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125`,
              )
    }

    if (typeof value === 'bigint') {
        return unrecoverable(
            'a bigint',
            'It shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`.',
        )
    }

    if (Array.isArray(value)) {
        return andThen(
            every(value, (x) => encodeUnknown(x, numbers)),
            (written) => carrying('L', written),
        )
    }

    if (value instanceof Set) {
        const members = [...value]
        if (members.length === 0) {
            return new CodecError('DynamoDB has no empty set')
        }
        if (members.every((x) => typeof x === 'string')) {
            return carrying('SS', (members as string[]).sort())
        }
        if (members.every((x) => x instanceof Uint8Array)) {
            return carrying('BS', members as Uint8Array[])
        }
        return unrecoverable(
            'a set of numbers',
            'NS decodes as strings, because its members are decimal strings. Use a set of strings, or `array(number)` if the order does not matter to you.',
        )
    }

    if (value instanceof Map) {
        return unrecoverable(
            'a Map',
            'DynamoDB has one map member, `M`, and it decodes as a plain object. Pass an object, or use `record(...)` to state the value type.',
        )
    }

    if (typeof value === 'object') {
        if (!isPlainObject(value)) {
            return unrecoverable(
                `an instance of ${value.constructor?.name ?? 'a class'}`,
                'Only plain objects survive: `M` carries the own enumerable properties and nothing that says how to rebuild the instance. Convert it first — a `Date`, for example, is faithful as an ISO string.',
            )
        }
        return andThen(
            everyEntry(value as Record<string, unknown>, (v, k) =>
                v === undefined
                    ? new CodecError(
                          `'${k}' is undefined, and DynamoDB has no attribute holding undefined. Omit the key, or use \`optional(...)\` on a declared attribute.`,
                      )
                    : encodeUnknown(v, numbers),
            ),
            (written) => carrying('M', written),
        )
    }

    return unrecoverable(`a ${typeof value}`, 'No DynamoDB member carries it.')
}

const decodeUnknown = (
    attribute: AttributeValue,
    numbers: opaque.Numbers,
): Result<unknown> => {
    const member = memberOf(attribute)
    switch (member) {
        case 'NULL':
            return null
        case 'S':
            return attribute[member]

        /**
         * A number exactly when the stored digits are that number's own shortest form, and the raw
         * string otherwise.
         *
         * `String(n)` is the shortest representation that reads back as `n`, so everything this
         * codec wrote comes back as the number it was. Anything wider — `'1.50'`, a
         * thirty-eight-digit decimal, `'9007199254740993'` — was written by something else with more
         * precision than a float holds, and is handed back untouched rather than quietly rounded.
         */
        case 'N': {
            const carried = attribute.N as string
            if (numbers === 'refuse') {
                return unrecoverable(
                    `the stored number '${carried}'`,
                    "Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`.",
                )
            }
            /**
             * The same two gates `number` reads through, and the second is not redundant for
             * the same reason: `Number('9.9…E+125')` rounds *up* past the maximum, so a numeral
             * the store holds can read back as a value nothing here can write.
             *
             * Without them this decoded `{ N: 'abc' }` to `NaN` and `{ N: '1e400' }` to
             * `Infinity` — values its own `encode` refuses, which is **(C)** failing. `Number`
             * reads far more than an `N` carries: `''` and whitespace are `0`, `'0x10'` is `16`.
             */
            if (!isNumeral(carried)) {
                return new CodecError(
                    `'${carried}' is not a numeral, so this attribute was not written by DynamoDB`,
                )
            }
            const read = Number(carried)
            return isNumeral(String(read))
                ? read
                : new CodecError(
                      `'${carried}' reads back as ${read}, which is outside what DynamoDB stores, so it cannot be written again`,
                  )
        }
        case 'B':
        case 'BOOL':
            return attribute[member]

        /**
         * **A member this codec cannot write is a member it cannot read.**
         *
         * `opaque` has no `NS` write path at all — a numeric `Set` is refused, because reading
         * one back is undecidable without a schema. Reading `NS` anyway produced a
         * `Set<string>`, and re-encoding that wrote `SS`: a numeric set attribute silently
         * becoming a string one on a read-modify-write, which is **(MP)** — the law `opaque`'s
         * `N` refusal already exists to protect, one member over.
         *
         * The general form is a corollary of §2 and is proved in the model
         * (`Calculus.Lawful.no_read_without_write`): a codec is a *pair*, and (MP) holds the
         * halves together, so if `e` never produces a member then no attribute carrying it can
         * be in `dom(p)`. Note which law does the work — (C) is satisfied here, the value
         * round-trips, and only the stored type changes. `μ = ⊤` is exactly where (MP) is the
         * only law left watching.
         */
        case 'NS':
            return unrecoverable(
                'a stored set of numbers',
                "`NS` has no counterpart this codec can write — a set of numbers is refused on the way in, because nothing without a schema says which of its members a JS number holds faithfully. Reading it would mean re-encoding it as `SS` and changing the attribute's stored type. Declare the attribute with `set(number)` or `set(decimal)`.",
            )
        case 'SS':
        case 'BS': {
            // as in `set`: encode has no empty set to offer, so decode has none to return
            const members = attribute[member] as readonly unknown[]
            return members.length === 0
                ? new CodecError(
                      `DynamoDB has no empty ${member}, so this attribute was not written by it`,
                  )
                : new Set(members)
        }
        case 'L':
            return every(attribute.L ?? [], (x) => decodeUnknown(x, numbers))
        case 'M':
            return everyEntry(attribute.M ?? {}, (v) =>
                decodeUnknown(v, numbers),
            )
        default:
            return new CodecError('an AttributeValue carrying no member')
    }
}

/**
 * An attribute path, which is a string and exists whether or not the attribute does.
 *
 * Optionality is stripped at every level, and that is the point: `deliveredAt?` describes whether
 * a *value* is there, and a path to it is well formed regardless — writing the path is how you ask
 * whether it exists. Typing the proxy as the entity leaks that value-level optionality into path
 * construction and forces a `!` at every optional hop, which is a non-null assertion about something
 * that was never a value.
 *
 * `at(i)` indexes a list. Bracket syntax works too, but under `noUncheckedIndexedAccess` a variable
 * index yields `| undefined` — again about a value, not a path — so `at` is the form that stays
 * clean. An entity with its own attribute named `at` should use brackets for that one hop.
 */
export type PathOf<T> = PathTerminal<T> & PathBody<NonNullable<T>>

type PathBody<T> = [T] extends [readonly unknown[]]
    ? PathList<T[number]>
    : [T] extends [object]
      ? {
            readonly [K in UnionKeys<T>]: PathOf<ValueAt<T, K>>
        } & PathRecord<T> &
            PathNarrowing<T>
      : Record<never, never>

/**
 * Every key any member of a union states, not only the shared ones.
 *
 * The reasoning that strips optionality: `priceIn` is a union whose CASH member has a `cardId` and
 * whose STORE_CREDIT member does not, but the path is well formed either way — writing it is how
 * you ask. The shared keys are never the interesting ones. Every key here belongs to some member,
 * so no path this admits is impossible for every variant.
 */
type UnionKeys<T> = T extends unknown ? keyof T : never

type ValueAt<T, K extends PropertyKey> = T extends unknown
    ? K extends keyof T
        ? T[K]
        : never
    : never

/**
 * Picking one member of a union before walking further.
 *
 * Merging every member's keys works while the members are objects, and stops working where they
 * disagree about *kind* — a key holding an object in one and a string in another merges to neither.
 *
 * `when` adds nothing to the path: narrowing is a statement about the type. Only present on a union.
 *
 * @example
 * ```ts
 * p.priceIn.when<Tender<'CASH'>>().cardId   // → 'priceIn.cardId'
 * ```
 */
type PathNarrowing<T> = IsUnion<T> extends true
    ? {
          /**
           * Narrows to the members matching `Filter`.
           *
           * A type rather than a discriminant and a value, because not every union has one. The
           * checked form of the cast otherwise written here: `when<Pet<'DOG'>>()` must match a
           * member or it does not compile.
           *
           * Narrows the *type* only. Where two members put different codecs at one attribute,
           * {@link ItemCodec.at} still cannot choose — types are gone by the time anything runs.
           * Reach for `tagged.variant(name)`, which is an item codec with its own `at`.
           */
          when<Filter extends Partial<T>>(): [Extract<T, Filter>] extends [
              never,
          ]
              ? ErrorMessage<'[when] no member of this union matches that filter'>
              : PathOf<Extract<T, Filter>>
      }
    : unknown

/**
 * A map whose keys are not known ahead of time, indexed by `at`.
 *
 * `requirements[someId]` is an index signature access, and under `noUncheckedIndexedAccess` that
 * yields `| undefined` — a statement about whether a *value* is there, which a path does not care
 * about. Only present when the type actually has a string index signature, so an object with known
 * keys is untouched and `.foo` stays the way to reach `foo`.
 */
type PathRecord<T> = string extends UnionKeys<T>
    ? { at(key: string): PathOf<ValueAt<T, string>> }
    : unknown

/**
 * A list, indexed by `at`.
 *
 * Deliberately not a mapped tuple. Preserving the tuple would let a literal index work in brackets,
 * but it also inherits `Array.prototype.at`, whose signature returns `| undefined` and shadows this
 * one — reintroducing at every index the assertion this type exists to remove.
 */
type PathList<Element> = {
    readonly [index: number]: PathOf<Element>
    at(index: number): PathOf<Element>
}

/**
 * The end of a path, carrying what lives there as a phantom.
 *
 * The phantom is what lets {@link ItemCodec.at} recover the type from a path expression: a selector
 * returns `PathTerminal<Adoption>`, and `Adoption` is inferred straight back out. Optional, so it costs
 * nothing at runtime and nothing to construct.
 */
export type PathTerminal<T> = {
    toString(): string
    readonly [pathValue]?: T
}

declare const pathValue: unique symbol

// ── items ───────────────────────────────────────────────────────────

/**
 * What an item codec does with an attribute its spec does not declare.
 *
 * - `'drop'` (default) — ignored in, absent out. What `PutItem` and `UpdateItem` already mean: a
 *   spec describes the item, and what it does not say is not there.
 * - `'refuse'` — decoding one throws. For a service that owns its table, where an unexpected
 *   attribute means schema and data have drifted.
 * - a codec — extra keys are part of the type, decoding through it and encoding back out. What an
 *   open entity needs.
 */
export type RestPolicy<V = never> = 'drop' | 'refuse' | AttributeCodec<V>

/**
 * The same three answers, stated so a spec can be read *first*.
 *
 * {@link RestPolicy} names the value the codec must handle, which only an entity with an index
 * signature can say. Declaring the spec first means there is no entity yet to ask, so the codec is
 * taken as given and the entity's index signature is derived from it instead — the same fact,
 * flowing the other way.
 */
export type RestDeclaration = 'drop' | 'refuse' | AnyCodec

/**
 * The entity a spec describes.
 *
 * `drop` and `refuse` both say the row holds nothing else, so the entity is closed. A rest codec
 * says it holds anything that codec can read, which is exactly an index signature — the mirror of
 * what {@link EncodedBy} does to the stored shape.
 */
export type DerivedItem<Spec, Rest> = [Rest] extends ['drop' | 'refuse']
    ? show<ObjectOf<Spec>>
    : show<ObjectOf<Spec>> & { readonly [name: string]: Decoded<Rest> }

/**
 * The keys a type states, without an index signature's.
 *
 * The value is `0` and not `T[K]`: only the keys are read back out, and naming the property type
 * instantiates one per key of every entity every spec is checked against, to be thrown away.
 */
type KnownKeys<T> = keyof {
    [K in keyof T as string extends K ? never : number extends K ? never : K]: 0
}

/**
 * The codecs an item needs: one per attribute, optional exactly where the entity is.
 *
 * Total coverage replaces the `key satisfies never` of a hand-written marshaller — a new field is a
 * compile error here, not a field that silently stops being written.
 */
export type ItemSpec<T> = T extends unknown
    ? {
          // distributed explicitly: `KnownKeys` is computed, so the mapped type is no longer
          // homomorphic and a union entity would otherwise collapse to the keys its members share
          [K in KnownKeys<T>]-?: undefined extends T[K]
              ? OptionalCodec<Exclude<T[K], undefined>>
              : Nestable<T[K]>
      }
    : never

/**
 * Reading and writing a whole item.
 *
 * The four item-shaped codecs — this, {@link Tagged}, {@link Untagged} and {@link TaggedCodec} —
 * each spell these members out rather than sharing one record. Factoring them out is the obvious
 * move and measurably the wrong one: as an intersection the result costs more to instantiate than
 * the flat object type, and stops being *comparable* to a hand-written shape, so the `as` a caller
 * writes to bypass a declaration-time check no longer compiles.
 */
export type ObjectCodec<
    Spec extends Record<string, AnyCodec>,
    Rest = 'drop',
> = {
    // spelled out rather than intersected with `AttributeCodec`, for the reason recorded on
    // {@link ItemCodec}: as an intersection the same type costs more to instantiate and stops being
    // *comparable* to a hand-written shape. Measured at +14k instantiations across this repo
    readonly encode: (
        value: DerivedItem<Spec, Rest>,
    ) => Result<M<Encoded<Spec>>>
    readonly decode: (
        attribute: AttributeValue,
    ) => Result<DerivedItem<Spec, Rest>>
    readonly unsafeEncode: (value: DerivedItem<Spec, Rest>) => M<Encoded<Spec>>
    readonly unsafeDecode: (
        attribute: AttributeValue,
    ) => DerivedItem<Spec, Rest>
    readonly def?: CodecDef
    /**
     * The same declaration, read as a whole item: the same two directions without the top-level map,
     * and the things only a top-level codec can offer — `encodePartial`, `field`, `at`, `path`.
     *
     * A DynamoDB item is a map that is never written as one; `PutItem` takes the attributes bare.
     * That is the *only* thing that separated an item codec from a nested one, and it is a fact about
     * where a codec is used rather than about what it declares — so it is a reading of one codec
     * rather than a second constructor. The marshaller draws the same line, under
     * `convertTopLevelContainer`.
     */
    readonly item: ItemCodec<DerivedItem<Spec, Rest>, Spec, Rest>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
}

/**
 * A union of objects, and the same union read as a whole item.
 *
 * Only a union of *objects* has an item reading: an item is a map, so a union that could also be an
 * `S` or an `L` is an attribute and nothing else. Which is why this is what the two union
 * constructors return, rather than what `union` is constrained to accept.
 */
export type DiscriminatedCodec<T, D extends string, Spec> = {
    readonly encode: (value: T) => Result<Attribute<'M'>>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (value: T) => Attribute<'M'>
    readonly unsafeDecode: (attribute: AttributeValue) => T
    readonly def?: CodecDef
    readonly item: Tagged<T, D, Spec>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
}

export type UnionCodec<T, Options extends readonly unknown[]> = {
    readonly encode: (value: T) => Result<WrittenBy<Options>>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (value: T) => WrittenBy<Options>
    readonly unsafeDecode: (attribute: AttributeValue) => T
    readonly def?: CodecDef
    /**
     * The same union read as a whole item — only where every option is an object.
     *
     * An item is a map, so a union that can also be an `S` has no top-level reading. Saying so with a
     * message rather than with an absent property is what makes reaching for it report *why* instead
     * of "property does not exist".
     */
    readonly item: AllObjects<Options> extends true
        ? Untagged<T, SpecsOf<Options>>
        : ErrorMessage<'[union] this union can hold an attribute that is not a map, so it has no whole-item reading — an item is always a map'>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<SpecsOf<Options>>
}

export type ItemCodec<T, Spec = unknown, Rest = 'drop'> = {
    /** Every attribute, or why one could not be written. For `PutItem`. */
    readonly encode: (item: T) => Result<EncodedBy<Spec, Rest>>
    readonly unsafeEncode: (item: T) => EncodedBy<Spec, Rest>
    /**
     * The attributes a patch names, or why one could not be written. For `UpdateItem`, which
     * addresses attributes individually — the reason a whole-value codec does not fit DynamoDB and
     * this is a record of per-attribute ones.
     */
    readonly encodePartial: <const Patch extends Partial<T>>(
        patch: Patch,
    ) => Result<EncodedPatch<Spec, Patch>>
    readonly unsafeEncodePartial: <const Patch extends Partial<T>>(
        patch: Patch,
    ) => EncodedPatch<Spec, Patch>
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /** One attribute's codec, for building `ExpressionAttributeValues` by hand. */
    readonly field: <K extends keyof Spec>(name: K) => Spec[K]
    /**
     * The codec at a path, together with the path.
     *
     * A nested update needs both halves and they must agree: the document path to write at, and the
     * codec declared for what lives there. Deriving them from one expression is what keeps them
     * agreeing — reaching for the generic marshaller at a nested path, which is the alternative,
     * drops out of the schema for that subtree and loses every guarantee it makes.
     *
     * @example
     * ```ts
     * const delivered = Adoption.at((p) => p.shipment.legs.at(i).deliveredAt)
     * delivered.path()            // 'shipment.legs[1].deliveredAt'
     * delivered.encode(stamp)     // through the codec declared for it
     * ```
     */
    readonly at: <X>(
        select: (path: PathOf<T>) => PathTerminal<X>,
    ) => LocatedCodec<X>
    /**
     * A builder for document paths into this item.
     *
     * One instance builds any number of independent paths: every hop returns a new builder carrying
     * its own segments, so nothing accumulates and nothing is consumed. Hoist it.
     */
    readonly path: () => PathOf<T>
    readonly spec: Spec
    /** What this codec does with an attribute the spec does not declare. */
    readonly rest: RestPolicy<unknown>
    /** What this codec is — see {@link CodecDef}. */
    readonly def: CodecDef
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
}

/** An {@link AttributeCodec} that also knows where it lives. */
export type LocatedCodec<T> = AttributeCodec<T> & {
    /** The document path, as DynamoDB expression syntax. */
    readonly path: () => string
    readonly segments: readonly (string | number)[]
}

/**
 * One declared attribute, with the questions about its declaration already answered.
 *
 * Whether an attribute may be absent and what stands in for it are facts about the spec, not about
 * the row being read, so they are settled once when the codec is built.
 */
type Declared = {
    readonly name: string
    readonly codec: AnyCodec
    readonly optional: boolean
    readonly absent: (() => unknown) | undefined
}

/**
 * Declares how an entity is stored, once, in both directions.
 *
 * The spec is the declaration, and the entity is derived from it. Nothing has to be named twice, and
 * there is no type argument to get wrong.
 *
 * Whatever else is worth checking is asked of the codec afterwards, and asked separately, because
 * they are separate questions:
 *
 * - `satisfies ItemCodec<Entity>` — the entity, exactly. `ItemCodec` is invariant in it, sitting in
 *   `encode`'s parameter and `decode`'s return, so a missing attribute, an extra one, and one that
 *   decodes to the wrong type are all caught. This is the totality the entity-first form used to
 *   check by construction.
 * - `satisfies Writes<Row>` — the stored shape. Covariant on its own, hence {@link Writes}.
 *
 * Which is the whole reason the entity is no longer a type parameter: it never needed to be one.
 *
 * @example
 * ```ts
 * const Pet = item({
 *     PK: string,
 *     SK: string,
 *     ownerId: string,
 *     price: decimal,               // money, never a float
 *     tags: set(string),            // SS, not L
 *     adopted: boolean,
 *     soldAt: optional(string),
 * })
 *
 * // and the two questions worth asking of it, each on its own, chainable
 * const Checked = item(spec) satisfies ItemCodec<PetEntry> satisfies Writes<PetItem>
 * ```
 */
export const object = <
    const Spec extends Record<string, AnyCodec>,
    const Rest extends RestDeclaration = 'drop',
>(
    spec: Spec & NoTail<Spec>,
    rest: Rest = 'drop' as Rest,
): ObjectCodec<Spec, Rest> => {
    // one pass, and the presence rules resolved with it. `isOptional` and `fallbackOf` are
    // answers about the *declaration*, so asking them per attribute per item — which is what
    // walking bare entries meant — asks the same question once per row for the life of the table
    const attributes: Record<string, AnyCodec> = {}
    const declared: Declared[] = []
    const declaredSpec = spec as unknown as Record<string, Nestable<never>>
    const restCodec = typeof rest === 'string' ? undefined : (rest as AnyCodec)
    for (const name in declaredSpec) {
        const attribute = declaredSpec[name] as AnyCodec
        attributes[name] = attribute
        declared.push({
            name,
            codec: attribute,
            optional: isOptional(attribute),
            absent: fallbackOf(attribute),
        })
    }

    type T = DerivedItem<Spec, Rest>
    const self: ItemCodec<T, Spec, Rest> = {
        encode: (item) => {
            const held = item as Record<string, unknown>
            const out: Record<string, AttributeValue> = {}
            for (const { name, codec: attribute, optional } of declared) {
                const value = held[name]
                if (value === undefined) {
                    if (optional) continue
                    return new CodecError(
                        `'${name}' is required and was not given`,
                    )
                }
                const written = attribute.encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
            }
            if (restCodec) {
                for (const name in held) {
                    const value = held[name]
                    if (name in attributes || value === undefined) continue
                    const written = restCodec.encode(value as never)
                    if (failed(written)) return written.under(name)
                    out[name] = written
                }
            }
            return out as EncodedBy<Spec, Rest>
        },

        encodePartial: (patch) => {
            const held = patch as Record<string, unknown>
            const out: Record<string, AttributeValue> = {}
            for (const name in held) {
                const value = held[name]
                if (value === undefined) continue
                const attribute = attributes[name]
                if (!attribute) {
                    return new CodecError(`'${name}' is not an attribute`)
                }
                const written = attribute.encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
            }
            return out as never
        },

        /**
         * Attributes the spec does not mention are dropped. A row written before a field existed
         * decodes without it, which is why `encode ∘ decode` is not identity on items.
         */
        decode: (item) => {
            const out: Record<string, unknown> = {}
            for (const {
                name,
                codec: attributeCodec,
                optional,
                absent,
            } of declared) {
                const attribute = item[name]
                if (attribute === undefined) {
                    if (optional) continue
                    if (absent) {
                        out[name] = absent()
                        continue
                    }
                    return new CodecError(
                        `'${name}' is required and the item has no such attribute`,
                    )
                }
                const read = attributeCodec.decode(attribute)
                if (failed(read)) return read.under(name)
                out[name] = read
            }

            if (rest === 'drop') return out as T
            for (const name in item) {
                if (name in attributes) continue
                if (!restCodec) {
                    return new CodecError(
                        `'${name}' is not an attribute this codec declares; the schema and the data have drifted apart`,
                    )
                }
                const read = restCodec.decode(item[name] as AttributeValue)
                if (failed(read)) return read.under(name)
                out[name] = read
            }
            return out as T
        },

        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        unsafeEncodePartial: (patch) => orThrow(self.encodePartial(patch)),

        path: () => pathBuilder<T>(),
        at: <X>(select: (path: PathOf<T>) => PathTerminal<X>) => {
            const segments = segmentsOf(select(pathBuilder<T>()))
            const path = asPath(segments)

            /**
             * The walk carries a *set* of codecs, not one.
             *
             * A path may pass through a segment the variants declare differently and still arrive
             * where they agree — `legs` is a one-tuple in `SINGLE_LEG` and a two-tuple in
             * `MULTI_LEG`, but indexing either reaches the same leg codec. So the disagreement is
             * carried along and reported only if it survives to the end, where using it would mean
             * encoding with a codec nobody declared.
             */
            let frontier: readonly AnyCodec[] = [self as unknown as AnyCodec]
            for (const segment of segments) {
                const next = [
                    ...new Set(frontier.flatMap((c) => childrenOf(c, segment))),
                ]
                if (next.length === 0) {
                    throw new CodecError(
                        `no attribute is declared at '${path}'`,
                    )
                }
                frontier = next
            }
            const [first, ...ambiguous] = frontier as [AnyCodec, ...AnyCodec[]]
            const here =
                ambiguous.length === 0 ? first : unresolvedAt(String(path))

            return {
                ...(here as AttributeCodec<X>),
                path: () => path,
                segments,
            }
        },
        field: (name) => (attributes as Spec)[name],
        spec: attributes as Spec,
        rest: rest as RestPolicy<unknown>,
        def: {
            kind: 'attributes',
            of: attributes as unknown as Attributes,
            rest: restCodec,
        },
    }

    // the `M` is what this codec writes; `.item` is the same two directions with the wrapper taken
    // off. Named member by member rather than spread so the cast keeps the *shape* the map carries —
    // `Attribute<'M'>` would flatten it to "some map" — and so that a call to `object` stays a plain
    // object literal, which is what lets a bundler drop an unused one
    const nested = asOneAttribute(self) as unknown as AttributeCodec<
        DerivedItem<Spec, Rest>,
        M<Encoded<Spec>>
    >
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        item: self as ItemCodec<DerivedItem<Spec, Rest>, Spec, Rest>,
    }
}

/**
 * A builder for document paths into `T`.
 *
 * The one implementation behind both `item(...).path()` and `tableEntry(...).path()`. They must
 * agree about what a path means — `at` resolves a codec by walking the same segments this records —
 * and the surest way for two implementations to agree is for there to be one.
 */
export const pathBuilder = <T>(): PathOf<T> => recordPath([]) as PathOf<T>

/** A segment addressing a list position, as opposed to an attribute named in digits. */
const asIndex = /^\d+$/

/** What each recorder recorded — read back by {@link segmentsOf}. */
const recorded = new WeakMap<object, readonly (string | number)[]>()

/** Nothing, shared: every `get` is trapped, so the target is only an identity to hang one on. */
const nothing = {}

/**
 * Records what a path expression walks through.
 *
 * Every hop returns a *new* recorder carrying its own segments, rather than pushing into a shared
 * array. Accumulating in place would be shorter and wrong: a selector that names an intermediate
 * node and reads more than one attribute off it — `const step = p.route.at(0); step.id; return
 * step.status` — would record both reads as one path. It also makes a recorder reusable, which is
 * what `path()` has always been.
 */
const recordPath = (segments: readonly (string | number)[]): unknown => {
    const recorder = new Proxy(nothing, {
        get: (_target, prop) => {
            if (typeof prop !== 'string') return undefined
            if (prop === 'toString') return () => asPath(segments)
            if (prop === 'at') {
                return (index: number) => recordPath([...segments, index])
            }
            // narrowing is a statement about the type; the document path is unchanged
            if (prop === 'when') return () => recordPath(segments)
            // digits all the way through, or it is an attribute name: `parseInt` accepted a
            // leading number and dropped the rest, so `'1abc'` recorded `[NaN]`
            return recordPath([
                ...segments,
                asIndex.test(prop) ? Number(prop) : prop,
            ])
        },
    })
    recorded.set(recorder, segments)
    return recorder
}

/**
 * The path a selector built.
 *
 * Read from a side table keyed on the recorder, because the two alternatives are both worse. A
 * property would have to be a key the `get` trap carves out of the entity's own namespace, which is
 * what a private symbol was for. A callable target — recovering the path by calling it — carves
 * nothing out, but it makes `typeof path` be `'function'`, and a recorder answers `.then` with
 * another recorder: a path whose target is callable *is a thenable*, so `await path` and
 * `Promise.resolve(path)` hang forever, silently. The target stays inert and the segments live
 * beside it.
 */
const segmentsOf = (path: unknown): readonly (string | number)[] => {
    // no `typeof` guard: `WeakMap.prototype.get` answers `undefined` for a key that cannot be held
    // weakly, so a selector that returned a string or a number falls into the same branch
    const segments = recorded.get(path as object)
    if (!segments) {
        throw new CodecError(
            'a path selector must return a path — an attribute, `at(...)` or `when()`',
        )
    }
    return segments
}

/**
 * Type-level only, and a function *pair* rather than a value, for one reason: invariance.
 *
 * A property whose type is `Written` is covariant, so a codec writing a subset of the pinned shape
 * would be accepted — which is the whole thing the pin exists to refuse. Naming `Written` in both a
 * parameter and a return position makes the comparison mutual, and mutual is what "the same shape"
 * means. `in out` is not an alternative: it constrains instantiations of one generic against each
 * other, and a `satisfies` compares two different types.
 */
declare const writesMarker: unique symbol

/**
 * The shape a codec puts in the table, asked of the codec itself.
 *
 * ```ts
 * const Pet = item(spec) satisfies Writes<PetItem>
 * ```
 *
 * Kept off {@link ItemCodec} and intersected onto what a constructor returns instead. On `ItemCodec`
 * the phantom would be invariant there too, and `satisfies ItemCodec<Pet>` — which leaves `Spec` at
 * its default — would then refuse every real codec. The two questions are separate and ask
 * separately: `satisfies ItemCodec<Pet>` is the entity, `satisfies Writes<PetItem>` is the row, and
 * they chain.
 */
export type Writes<Written> = {
    readonly [writesMarker]?: (written: Written) => Written
}

/**
 * The pin as {@link ItemCodec} carries it: inert until something asks.
 *
 * `unknown` is what the phantom is when no shape is named, and every function is assignable to
 * `unknown` — so `satisfies ItemCodec<Pet>`, which leaves `Spec` at its default, is untouched by
 * this and stays a question about the entity alone.
 *
 * Carried on the codec rather than intersected onto what `item` returns, which is where this
 * started: `tableEntry` infers `CodecSpec` and `CodecRest` from the codec it is handed, and an
 * intersection is a source those inferences do not survive — `Rest` fell back to its default, and a
 * row that really does carry an open policy's attributes typed as though it did not.
 */
type WritesPin<Spec, Rest> = unknown extends Spec
    ? unknown
    : (written: EncodedBy<Spec, Rest>) => EncodedBy<Spec, Rest>

/**
 * The same pin for a union, whose row is one variant's attributes or another's.
 *
 * A union has no single encoded shape to name — `encode` returns "some attribute map", because which
 * attributes are written depends on which variant the value is. So the phantom is the only place the
 * shape appears at all, which makes it the only thing a pin can be asked of.
 */
type WritesVariantsPin<Spec> = unknown extends Spec
    ? unknown
    : (written: EncodedVariants<Spec>) => EncodedVariants<Spec>

/**
 * What a union of variants writes: one variant's attributes, or another's.
 *
 * A row of a tagged or untagged entity is exactly one variant, so the shape is the union rather than
 * the merge — which is what lets a pin catch a variant that has drifted while the others have not.
 * Handles a record of variants (`tagged`) and a list of them (`untagged`); the two differ only in
 * how they are keyed.
 */
export type EncodedVariants<Variants> = Variants extends readonly unknown[]
    ? { [V in keyof Variants]: Encoded<Variants[V]> }[number]
    : { [V in keyof Variants]: Encoded<Variants[V]> }[keyof Variants]

/**
 * Which set an element reaches, from what the element writes.
 *
 * The runtime asks {@link writes}; this is the same question of the type, so a spec can pin `SS`
 * and be told when the element stops being a string. `L` and `SS` are the distinction a marshaller
 * that guesses gets wrong, so a shape that could not tell them apart would pin very little.
 */
export type SetOf<C> = AttributeOf<C> extends Attribute<'S'>
    ? SS
    : AttributeOf<C> extends Attribute<'N'>
      ? NS
      : AttributeOf<C> extends Attribute<'B'>
        ? BS
        : never

/**
 * The attribute a codec writes, as a type.
 *
 * The mirror of {@link Decoded}: that side says what the entity holds, this side says what the
 * *table* holds. A codec has carried both since the beginning — `AttributeCodec<T, A>` — so this
 * reads the half nobody was reading.
 */
export type AttributeOf<C> = C extends {
    readonly attribute: AttributeCodec<infer _Nested, infer Nesting>
}
    ? Nesting
    : C extends AttributeCodec<infer _Held, infer Written>
      ? Written
      : never

/**
 * The item a spec writes, as a shape you could have written by hand.
 *
 * The fixed point. `Encoded<typeof Pet>` is what the codec puts in the table; a `PetItem` written
 * out by hand is what the table is believed to hold; pinning one against the other is what makes a
 * migration checkable rather than hoped for. Optional attributes are optional keys, because an
 * attribute a codec may omit is one the item may not have.
 */
/**
 * What an item writes: the attributes the spec declares, plus whatever a rest policy adds.
 *
 * {@link Encoded} alone is a *lower bound* rather than the answer. Under `'drop'` and `'refuse'`
 * nothing else is written and the two agree; a rest codec emits attributes the spec never named, so
 * claiming `Encoded<Spec>` exactly would be a promise the compiler then enforces against the
 * caller — refusing to read an attribute the codec really did write.
 *
 * The two string policies are named rather than the codec matched: an {@link AttributeCodec} is
 * invariant in its value, so `Rest extends AttributeCodec<unknown, infer A>` fails for every codec
 * of a narrower value and quietly takes the wrong branch.
 */
/**
 * The attributes a patch writes, read off the patch rather than off the whole spec.
 *
 * `Partial<Encoded<Spec>>` is the weaker answer and it loses the thing a patch knows: which
 * attributes are being written. Naming them means an `UpdateItem` built from this is checked
 * against the attributes it actually sets, not against every attribute the entity could have.
 *
 * Optional exactly where the patch's own value admits `undefined`, because that is the value the
 * implementation skips — a key present with no value writes no attribute.
 *
 * Based on {@link Encoded} and *not* {@link EncodedBy}: a patch never reaches a rest policy. The
 * implementation looks each name up among the declared attributes and refuses one it does not
 * find, so a type carrying the rest policy's index signature would promise a write that is an
 * error at runtime.
 */
export type EncodedPatch<Spec, Patch> = Encoded<Spec> extends infer Full
    ? show<
          {
              [K in keyof Patch as K extends keyof Full
                  ? undefined extends Patch[K]
                      ? never
                      : K
                  : never]: Written<Full, K>
          } & {
              [K in keyof Patch as K extends keyof Full
                  ? undefined extends Patch[K]
                      ? K
                      : never
                  : never]?: Written<Full, K>
          }
      >
    : never

/**
 * The attribute at `K`, without the `undefined` that optionality adds.
 *
 * Indexing an optional key of {@link Encoded} yields `Attribute<'S'> | undefined`, which is a fact
 * about whether the attribute is *there* rather than about what it carries — and a patch that names
 * it has settled that question. Carrying the `undefined` through would put it back, so every read
 * of a patched attribute would need a `?.` for a value the patch just supplied.
 */
type Written<Full, K> = Exclude<Full[K & keyof Full], undefined>

export type EncodedBy<Spec, Rest> = [Rest] extends ['drop' | 'refuse']
    ? Encoded<Spec>
    : Encoded<Spec> & { readonly [name: string]: AttributeValue }

export type Encoded<Spec> = show<
    {
        [K in keyof Spec as Spec[K] extends {
            readonly [optionalMarker]: true
        }
            ? never
            : K]: AttributeOf<Spec[K]>
    } & {
        [K in keyof Spec as Spec[K] extends {
            readonly [optionalMarker]: true
        }
            ? K
            : never]?: AttributeOf<Spec[K]>
    }
>

export type ObjectOf<Spec> = {
    [K in keyof Spec as Spec[K] extends { readonly [optionalMarker]: true }
        ? never
        : K]: Decoded<Spec[K]>
} & {
    [K in keyof Spec as Spec[K] extends { readonly [optionalMarker]: true }
        ? K
        : never]?: Decoded<Spec[K]>
}

// ── unions ─────────────────────────────────────────────────────────

export type IsUnion<T, U = T> = T extends unknown
    ? [U] extends [T]
        ? false
        : true
    : never

/**
 * The member a tag selects.
 *
 * `Extract<T, { [D]: V }>` is not enough: a variant may span several tags — a `Vendor` member
 * typed `vendorId: 'ACME' | 'GLOBEX'` does not extend `{ vendorId: 'ACME' }`. Asking whether the
 * tag is *among* the member's tags does reach it.
 */
export type VariantOf<T, D extends keyof T, V> = T extends unknown
    ? V extends T[D]
        ? T
        : never
    : never

/**
 * A tagged codec, structural so a signature can ask for one without naming its discriminator —
 * `Tagged` carries `D` contravariantly, so naming it would accept only the one guessed.
 */
export type TaggedCodec<T, Spec = unknown> = {
    readonly encode: (item: T) => Result<AttributeMap>
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeEncode: (item: T) => AttributeMap
    readonly unsafeDecode: (item: StoredItem) => T
    readonly discriminator: keyof T & string
    readonly spec: Spec
    readonly variant: (name: keyof Spec) => unknown
}

/**
 * The codecs a discriminated entity needs: every variant, and every attribute of each.
 *
 * Coverage is total on two axes. Missing a variant is a compile error, and so is missing an
 * attribute of one — a variant that gains a field cannot silently stop being written.
 */
export type TaggedSpec<T, D extends keyof T> = {
    [V in T[D] & (string | number)]: ItemSpec<VariantOf<T, D, V>>
}

export type Tagged<T, D extends string = keyof T & string, Spec = unknown> = {
    /** Every attribute, or why one could not be written. */
    readonly encode: (item: T) => Result<AttributeMap>
    readonly unsafeEncode: (item: T) => AttributeMap
    /**
     * The attributes a patch names, or why one could not be written.
     *
     * The discriminator is required in a patch, because it is what chooses the codec. This is a type
     * error, not a runtime one: `Partial<T> & Pick<T, D>`.
     */
    readonly encodePartial: (
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /** One variant's codec, with everything {@link item} gives. */
    readonly variant: <V extends keyof Spec>(
        name: V,
    ) => ItemCodec<VariantOf<T, D & keyof T, V>, Spec[V]>
    readonly discriminator: D
    readonly spec: Spec
    /** What this codec is — see {@link CodecDef}. */
    readonly def: CodecDef
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
}

const readTag = (item: StoredItem, discriminator: string): Result<string> => {
    const attribute = item[discriminator]
    if (attribute === undefined) {
        return new CodecError(
            `'${discriminator}' chooses the variant and the item has no such attribute`,
        )
    }
    const member = memberOf(attribute)
    if (member !== 'S' && member !== 'N') {
        return new CodecError(
            `'${discriminator}' chooses the variant, so it must be carried as 'S' or 'N', not '${member ?? 'none'}'`,
        )
    }
    return attribute[member] as string
}

/**
 * How an entity that is a union of objects is stored.
 *
 * **Discriminated, not a bare `oneOf`.** Trying each member until one parses is ambiguous, order-
 * dependent, and can return a different variant than the one encoded — breaking
 * `decode ∘ encode = id`. A discriminator makes decode a lookup.
 *
 * Mirrors `tableEntry`'s discriminated key schema, so a union spells its discriminator the same way
 * for keys and for attributes.
 *
 * @example
 * ```ts
 * const Visit = tagged<Visit>()('type', {
 *     CHECKUP: { type: literal('CHECKUP'), petId: string, vetId: string },
 *     VACCINATION: { type: literal('VACCINATION'), petId: string, vaccine: string },
 * })
 * ```
 */
const tagged = <T extends Record<string, unknown>>(
    discriminator: string,
    byVariant: Record<string, ItemCodec<Record<string, unknown>, unknown>>,
): DiscriminatedCodec<T, string, Record<string, unknown>> => {
    const pick = (tag: string): Result<ItemCodec<T, unknown>> =>
        (byVariant[tag] as ItemCodec<T, unknown> | undefined) ??
        new CodecError(
            `'${tag}' is not a variant of '${discriminator}'; expected ${Object.keys(
                byVariant,
            )
                .map((x) => `'${x}'`)
                .join(', ')}`,
        )

    const tagOf = (item: Partial<T>): Result<string> => {
        const tag = item[discriminator]
        return tag === undefined
            ? new CodecError(
                  `'${String(discriminator)}' chooses the variant and was not given`,
              )
            : String(tag)
    }

    const self: Tagged<T, string, Record<string, unknown>> = {
        encode: (item) =>
            andThen(andThen(tagOf(item), pick), (variant) =>
                variant.encode(item as never),
            ),
        encodePartial: (patch) =>
            andThen(andThen(tagOf(patch), pick), (variant) =>
                variant.encodePartial(patch as never),
            ),
        decode: (item) =>
            andThen(
                andThen(readTag(item, discriminator), pick),
                (variant) => variant.decode(item) as Result<T>,
            ),
        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeEncodePartial: (patch) => orThrow(self.encodePartial(patch)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        variant: (name) => byVariant[name as string] as never,
        discriminator,
        // keyed by tag, holding what each variant declares — the keys are the variant names,
        // which is what a caller walking the variants reads
        spec: Object.fromEntries(
            Object.entries(byVariant).map(([tag, variant]) => [
                tag,
                variant.spec,
            ]),
        ),
        def: {
            kind: 'tagged',
            discriminator,
            variants: byVariant as unknown as Attributes,
        },
    }

    const nested = asOneAttribute(self)
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        item: self as Tagged<T, string, Record<string, unknown>>,
    }
}

// ── unions with no discriminator ────────────────────────────────────

/**
 * Whether two variants can ever hold the same set of attribute names.
 *
 * A variant admits every name set between its required keys and its declared keys. Two such
 * intervals intersect exactly when each variant's required keys are all declared by the other —
 * which makes collision decidable at declaration, before any item exists.
 *
 * Prior art: degenerate's `VariantOverlapAnalyzer` runs the same check while generating Dart from
 * an OpenAPI spec and warns "consider adding a discriminator". It has to be conservative — it works
 * from a spec it did not write and can only report what it can *prove* — and it cannot refuse,
 * because real specs violate `oneOf` constantly. A hand-written codec is not so constrained: the
 * rule below is exact rather than one-sided, and a collision is an error rather than a warning.
 */
type Collides<A, B> = [Exclude<RequiredKeysOf<A>, keyof B>] extends [never]
    ? [Exclude<RequiredKeysOf<B>, keyof A>] extends [never]
        ? true
        : false
    : false

type RequiredKeysOf<Spec> = {
    [K in keyof Spec]-?: Spec[K] extends { readonly [optionalMarker]: true }
        ? never
        : K
}[keyof Spec]

type CollisionsFrom<
    Head,
    Rest extends readonly unknown[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (Collides<Head, Next> extends true
                ? `variants ${At} and ${Cursor['length']}`
                : never)
          | CollisionsFrom<Head, Tail, At, [...Cursor, unknown]>
    : never

type Collisions<
    Specs extends readonly unknown[],
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | CollisionsFrom<Head, Rest, Cursor['length'], [...Cursor, unknown]>
          | Collisions<Rest, [...Cursor, unknown]>
    : never

/**
 * Rejects a declaration whose variants cannot be told apart, at the declaration rather than on the
 * first item that collides in production.
 */
export type ValidateVariants<Specs extends readonly unknown[]> = [
    Collisions<Specs>,
] extends [never]
    ? unknown
    : ErrorMessage<`[untagged] ${Collisions<Specs>} can hold the same attributes and cannot be told apart; give them a discriminator and use tagged`>

/**
 * Whether two options read back as types a value could not choose between.
 *
 * One direction is enough to be ambiguous: if everything of A's type is also a valid B, a value of
 * that type matches both. `string` and `decimal` both read back as `string`, so *every* value is
 * ambiguous — which is also why the union is ill-formed rather than merely risky: its entity type is
 * `string`, so nothing about a value says which option produced it and `decode ∘ encode = id` cannot
 * hold. `literal('A')` and `literal('B')` read back as `'A'` and `'B'`, which no value satisfies
 * both of.
 */
type Overlaps<A, B> = [Decoded<A>] extends [Decoded<B>]
    ? true
    : [Decoded<B>] extends [Decoded<A>]
      ? true
      : false

/**
 * Object options are exempt, because a different rule already covers them.
 *
 * Two object options are told apart by their exact set of attribute names, which is *stricter* than
 * their types: `{ a, b }` is assignable to `{ a }`, and yet an item carrying both attributes is
 * admitted by only one of them. Judging those by type would refuse declarations that work, so they
 * are judged by {@link Collisions} instead.
 */
type BothObjects<A, B> = A extends AnyObjectCodec
    ? B extends AnyObjectCodec
        ? true
        : false
    : false

type OverlapsFrom<
    Head,
    Rest extends readonly unknown[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (BothObjects<Head, Next> extends true
                ? never
                : Overlaps<Head, Next> extends true
                  ? `options ${At} and ${Cursor['length']}`
                  : never)
          | OverlapsFrom<Head, Tail, At, [...Cursor, unknown]>
    : never

type Overlapping<
    Options extends readonly unknown[],
    Cursor extends readonly unknown[] = [],
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | OverlapsFrom<Head, Rest, Cursor['length'], [...Cursor, unknown]>
          | Overlapping<Rest, [...Cursor, unknown]>
    : never

/**
 * Both rules, in the order that gives the more specific message.
 *
 * An overlap is the deeper problem — the union cannot round-trip at all — so it is reported first.
 * A name collision between two object options is reported by {@link ValidateVariants}.
 */
export type ValidateOptions<Options extends readonly unknown[]> = [
    Overlapping<Options>,
] extends [never]
    ? ValidateVariants<ObjectSpecsOf<Options>>
    : ErrorMessage<`[union] ${Overlapping<Options>} read back as the same type, so nothing about a value says which one it came from — give them a discriminator and use discriminatedUnion`>

/**
 * An object codec with its spec forgotten — the constraint form, as {@link AnyCodec} is for codecs.
 *
 * Structural, and deliberately: it asks for the one member that says "I am an object codec and this
 * is what I declare". A bare spec record does not have it, so passing one where an option is expected
 * is refused rather than silently read as a codec.
 */
export type AnyObjectCodec = {
    readonly item: {
        // `never` in and `unknown` out, the same erasure {@link AnyCodec} uses, so every object codec
        // fits and none of them has to be named
        readonly encode: (item: never) => unknown
        readonly decode: (item: StoredItem) => unknown
        readonly spec: Record<string, AnyCodec>
    }
}

/**
 * Whether every option is an object codec, which decides whether the union has an item reading.
 */
export type AllObjects<Options extends readonly unknown[]> =
    Options extends readonly [
        infer Head,
        ...infer Rest extends readonly unknown[],
    ]
        ? Head extends AnyObjectCodec
            ? AllObjects<Rest>
            : false
        : true

/**
 * The specs of the object options, with the others dropped.
 *
 * Only object options can collide on attribute names, so only they are checked. Positions in the
 * message {@link ValidateVariants} produces therefore count object options — the same thing for the
 * all-object union that is the common case.
 */
export type ObjectSpecsOf<Options extends readonly unknown[]> =
    Options extends readonly [
        infer Head,
        ...infer Rest extends readonly unknown[],
    ]
        ? Head extends { readonly item: { readonly spec: infer S } }
            ? [S, ...ObjectSpecsOf<Rest>]
            : ObjectSpecsOf<Rest>
        : []

/** The entity a list of options describes: whatever any one of them reads back. */
export type DerivedUnion<Options extends readonly unknown[]> = {
    [I in keyof Options]: Decoded<Options[I]>
}[number]

/** What a union writes: whatever the option it chose writes. */
export type WrittenBy<Options extends readonly unknown[]> = Extract<
    { [I in keyof Options]: AttributeOf<Options[I]> }[number],
    AttributeValue
>

/** What each option declares, read off the options. */
export type SpecsOf<Options extends readonly unknown[]> = {
    [I in keyof Options]: Options[I] extends {
        readonly item: { readonly spec: infer S }
    }
        ? S
        : never
}

/** The variants of an untagged union. There is no tag, so there is nothing to key them by. */
export type UntaggedSpec<T> = readonly ItemSpec<T>[]

/**
 * The entity a list of variant specs describes: one variant, or another.
 *
 * The union and not the merge, which is the same distinction {@link EncodedVariants} makes about the
 * stored side — a row is exactly one variant, so an attribute only one of them declares is not an
 * attribute the entity always has.
 */
export type DerivedVariants<Specs extends readonly unknown[]> = {
    [I in keyof Specs]: show<ObjectOf<Specs[I]>>
}[number]

export type Untagged<T, Specs extends readonly unknown[] = UntaggedSpec<T>> = {
    /** Every attribute, or why one could not be written. */
    readonly encode: (item: T) => Result<AttributeMap>
    readonly unsafeEncode: (item: T) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /**
     * One variant by position.
     *
     * Indexing a list with a `number` yields `| undefined` under `noUncheckedIndexedAccess`, which is
     * a statement about a position that may not exist — and it landed on the *codec*, so reaching a
     * variant written as a literal one line below its declaration needed a `!`. Getting the index
     * right is the caller's job, as with any list; what comes back is a codec.
     */
    readonly variant: <I extends number>(
        index: I,
    ) => ItemCodec<show<ObjectOf<NonNullable<Specs[I]>>>, NonNullable<Specs[I]>>
    readonly spec: Specs
    /** What this codec is — see {@link CodecDef}. */
    readonly def: CodecDef
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Specs>
}

/**
 * One option of a union, reduced to what matching it actually asks.
 *
 * Two kinds, and the difference is the whole matcher. An **object** option declares a set of
 * attribute names, so the names of a value identify it before anything is encoded — and a failure
 * *after* it has been identified is a real error, not a reason to try the next one. Any **other**
 * codec declares nothing a name could match, so the only question that can be asked of it is whether
 * it can carry the value at all, and a failure means "not this one".
 *
 * Which is why an object option is never tried and rejected: `object({ a })` with `rest: 'drop'`
 * would happily encode `{ a, b }` and silently lose `b`, so "it encoded" is not evidence that it is
 * the right option. Its names are.
 */
type Option = {
    readonly codec: AnyCodec
    /** The member it writes, where the kind alone decides — a cheap filter on decode. */
    readonly member: AttributeName | undefined
    /** The kinds of value it takes, where the kind alone decides — the same filter on encode. */
    readonly carries: readonly Shape[] | undefined
    /** The whole-item reading, for object options only. */
    readonly item: ItemCodec<Record<string, unknown>, unknown> | undefined
    /** The names it declares, for object options only. */
    readonly declares: ReadonlySet<string> | undefined
    readonly requires: readonly string[]
    /** How it is named in a message — written the way it was declared. */
    readonly describe: string
}

/**
 * Whether a term knows which values are its own.
 *
 * A `literal` does, by construction: it checks the value against its admissible set in *both*
 * directions, so being able to encode a value is real evidence the value was meant for it. Almost
 * nothing else does — encoding does not validate — which is why a union cannot generally resolve by
 * trying.
 *
 * It **propagates through containers**, and it has to. `set(literal(1))` refuses a set of strings,
 * because the element refuses each one — so `union(set(literal('a')), set(literal(1)))` is perfectly
 * resolvable, and reading the property off the option alone refused it. The same for a wrapper that
 * encodes straight through its inner codec.
 *
 * `nullable` is left out on purpose: two nullable literals both accept `null`, so the wrapper admits
 * a value neither literal decides. `held` is left out because the conversion is a caller's function
 * and there is nothing to read.
 */
const identifies = (option: Option) => identifying(option.codec)

const identifying = (codec: AnyCodec): boolean => {
    const def = codec.def
    switch (def?.kind) {
        case 'literal':
        // a tag lookup fails for a value carrying no tag it knows, which is the same evidence
        case 'tagged':
            return true
        case 'set':
        case 'array':
            return identifying(def.element)
        case 'tuple':
            return def.elements.every(identifying)
        case 'record':
            return identifying(def.value)
        case 'untagged':
            return def.variants.every(identifying)
        case 'refine':
        case 'optional':
        case 'fallback':
            return identifying(def.inner)
        case 'legacy':
            return identifying(def.current)
        default:
            return false
    }
}

const optionOf = (codec: AnyCodec): Option => {
    /**
     * Read from the definition, not from the presence of `.item`.
     *
     * A nested union has an `.item` too, and its `spec` is the *list* of its options rather than a
     * record of attributes — so testing for the member classified a union as an object and then walked
     * that list as though `0` and `1` were attribute names. `attributes` is the definition of an
     * object codec and of nothing else.
     */
    const asObject =
        codec.def?.kind === 'attributes'
            ? (codec as unknown as Partial<AnyObjectCodec>).item
            : undefined
    const spec = asObject?.spec
    if (!spec) {
        return {
            codec,
            member: writes(codec),
            carries: carries(codec),
            item: undefined,
            declares: undefined,
            requires: [],
            describe: codec.def?.kind ?? 'a codec',
        }
    }
    const declares = new Set<string>()
    const requires: string[] = []
    for (const name in spec) {
        declares.add(name)
        if (!isOptional(spec[name] as AnyCodec)) requires.push(name)
    }
    return {
        codec,
        member: 'M',
        carries: ['map'],
        item: asObject as unknown as ItemCodec<
            Record<string, unknown>,
            unknown
        >,
        declares,
        requires,
        describe: `{ ${[...declares]
            .map((name) =>
                isOptional(spec[name] as AnyCodec) ? `${name}?` : name,
            )
            .join(', ')} }`,
    }
}

/**
 * Whether an object option can describe exactly this set of attribute names.
 *
 * Two conditions, and both matter for the law: every name present must be one the option declares
 * (otherwise encoding would drop data), and every attribute it requires must be present (otherwise
 * it is simply not this one).
 */
const admits = (option: Option, names: ReadonlySet<string>) => {
    const declares = option.declares
    if (!declares) return false
    for (const name of names) if (!declares.has(name)) return false
    for (const name of option.requires) if (!names.has(name)) return false
    return true
}

/**
 * A value read as a bare record of attributes, or nothing.
 *
 * Only a plain object can be an object option's value. An array, a `Set`, a `Uint8Array` and a class
 * instance all have keys `Object.keys` will happily list, and matching an object option on those
 * would pick one that cannot encode them.
 */
const asRecord = (value: unknown): Record<string, unknown> | undefined => {
    if (typeof value !== 'object' || value === null) return undefined
    const proto = Object.getPrototypeOf(value) as object | null
    return proto === Object.prototype || proto === null
        ? (value as Record<string, unknown>)
        : undefined
}

/**
 * The names a value has, which is all the object matcher reads.
 *
 * A key whose value is `undefined` is not a name. That is the same rule in both directions —
 * `{ gift: undefined }` encodes without `gift`, and an item with no `gift` attribute decodes without
 * it — so matching an option on it would pick one the other direction cannot reach.
 */
const namesOf = (held: Record<string, unknown>) => {
    const names = new Set<string>()
    for (const name in held) {
        if (held[name] !== undefined) names.add(name)
    }
    return names
}

/**
 * A union of objects with no discriminator — `{ petId, price } | { petIds }`.
 *
 * **A unique structural match; ambiguity is refused rather than scored.** A variant admits a set of
 * attribute names when it declares all of them and requires none that are missing. Exactly one
 * match is used; none or several throw.
 *
 * That is what keeps `decode ∘ encode = id`, which first-match-wins does not: the matcher reads only
 * names, never positions, so both directions reach the same variant. Scoring widest or narrowest
 * would preserve the law too, but every candidate declares all the names present, so it would be an
 * arbitrary tie-break silently committing to a shape nobody named.
 *
 * Prefer {@link tagged} wherever a discriminator exists.
 *
 * @example
 * ```ts
 * const LineItem = union([
 *     { gift: optional(boolean), petId: string, price: decimal },
 *     { petIds: array(string) },
 * ])
 * ```
 */
/**
 * The tag values a variant answers to — its discriminator's whole admissible set, not one value.
 *
 * A variant may span several tags, and this codebase relies on it: a carrier declared
 * `carrierId: literal('ACME', 'GLOBEX')` is *one* variant covering two stored values, which is why
 * {@link VariantOf} asks whether a tag is *among* a member's tags rather than equal to it.
 */
type TagsOf<Spec, D extends PropertyKey> = Spec extends unknown
    ? // distributed over the *variants*: the conditional below is on `Spec[D]`, so a union of specs
      // handed in whole would ask about a union of codecs and answer nothing
      D extends keyof Spec
        ? Spec[D] extends AttributeCodec<infer Tag, AttributeValue>
            ? // a tag is stored as `S` or as `N`, so a numeric enum indexes variants as readily as
              // a string one — `readTag` reads either member and keys on the text it carries
              Tag extends string | number
                ? Tag
                : never
            : never
        : never
    : never

/**
 * The options keyed by their own tag, which is what a lookup needs.
 *
 * Derived rather than declared. A record keyed by tag value repeats what the option's own `literal`
 * already says, so `{ SHOT: { type: literal('CHECKUP') } }` is expressible and the two can disagree.
 * Reading the tag off the option makes that unrepresentable — and it is how `zod` does it.
 */
type ByTag<Specs extends readonly unknown[], D extends PropertyKey> = {
    [Spec in Specs[number] as TagsOf<Spec, D>]: Spec
}

/**
 * Nothing, or the fact that some option does not say which variant it is.
 *
 * A discriminator only discriminates if every option names it with a `literal`. One that does not
 * cannot be found by a lookup, and would decode as whichever option happened to match instead.
 */
type EveryOptionTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
> = [TagsOf<Specs[number], D>] extends [never]
    ? ErrorMessage<'[discriminatedUnion] every option must name the discriminator with `literal(...)`, or a lookup cannot find it'>
    : unknown

/**
 * A union of objects told apart by one attribute — `zod`'s `discriminatedUnion`, over an item.
 *
 * The stored value of the discriminator chooses the option, and each option says which value it is by
 * naming that attribute with `literal(...)`. A lookup rather than a search: it cannot be ambiguous,
 * and it is the only union that can encode a *patch*, because a subset of the attributes does not say
 * which option it belongs to.
 *
 * The options are *codecs*, not bare specs, so an option that already has a name can be handed over
 * by it and a nested union reads the same as a nested anything else. What the union needs of an
 * option — its attributes, and what its discriminator admits — an object codec already carries.
 *
 * @example
 * ```ts
 * discriminatedUnion('type', [
 *     object({ type: literal('CHECKUP'), petId: string, vetId: string }),
 *     object({ type: literal('SHOT'), petId: string, vaccine: string }),
 * ])
 * ```
 */
export const discriminatedUnion = <
    const D extends string,
    const Options extends readonly AnyObjectCodec[],
>(
    discriminator: D,
    options: Options & EveryOptionTagged<SpecsOf<Options>, D>,
): DiscriminatedCodec<
    DerivedVariants<SpecsOf<Options>>,
    D,
    ByTag<SpecsOf<Options>, D>
> => {
    const byTag: Record<
        string,
        ItemCodec<Record<string, unknown>, unknown>
    > = {}
    for (const option of options as readonly AnyObjectCodec[]) {
        if (!option?.item?.spec) {
            throw new CodecError(
                `every option must be an object codec, and one of them is not — a bare spec has no variant to select, so pass \`object(...)\` around it`,
            )
        }
        // the whole admissible set, not one value: an option may answer to several tags
        const def = option.item.spec[discriminator]?.def
        const tags = def?.kind === 'literal' ? def.allowed : undefined
        if (!tags?.length) {
            throw new CodecError(
                `every option must name '${discriminator}' with \`literal(...)\`, and one of them does not — without it a lookup cannot find the variant`,
            )
        }
        // the option is already built, so the variant is the codec it came with rather than a
        // second one built from the same spec
        for (const tag of tags) {
            byTag[tag] = option.item as unknown as ItemCodec<
                Record<string, unknown>,
                unknown
            >
        }
    }
    return tagged(discriminator, byTag) as never
}

/**
 * A union told apart by what each option holds, with no tag to switch on — `zod`'s `union`.
 *
 * Options are codecs of any kind, and the rule is the same for all of them: **exactly one** option
 * must match, or it is an error. What "match" means is the only thing that differs, and it differs
 * because the options do — see {@link Option}. An object option is chosen by the attribute *names*
 * present; anything else is chosen by being the only option that can carry the value.
 *
 * Ambiguity is reported rather than resolved by declaration order. Two object options that can hold
 * the same attributes are refused at the declaration; two attribute options that can both carry one
 * particular value cannot be known until that value turns up, because `literal('A')` and
 * `literal('B')` both write `S` and are never ambiguous — so that one is reported when it happens.
 *
 * @example
 * ```ts
 * union([object({ petId: string, price: decimal }), object({ petIds: array(string) })])
 * union([string, number])                    // an attribute that is either
 * union([object({ at: string }), string])     // a map or a bare string
 * ```
 */
export const union = <const Options extends readonly AnyCodec[]>(
    options: Options &
        ValidateOptions<Options> &
        NotAboutAbsence<Options[number]>,
): UnionCodec<DerivedUnion<Options>, Options> => {
    const all = (options as readonly AnyCodec[]).map(optionOf)

    /**
     * Two options that no *value* can choose between, refused where the declaration is.
     *
     * `ValidateOptions` refuses the pairs that no stored attribute can choose between, at compile
     * time, by asking whether they read back as the same type. This is the other direction, and the
     * types cannot see it: `array(string)` and `array(number)` read back as different types and are
     * handed the same array — and neither checks what is in it, because **encoding does not validate**
     * (see {@link carries}). So they are ambiguous for every value, which makes it a fact about the
     * declaration rather than about a row, and reporting it per-encode reported it once per write
     * forever instead of once at import.
     *
     * Two exemptions, and both are options that identify themselves:
     *
     * - an **object** option is chosen by the attribute names present, never by being tried
     * - a **literal** knows which values are its own, so trying it is a real question — which is why
     *   `union([literal('A'), literal('B')])` is not ambiguous and never was
     *
     * An option whose kind is unknown — an adapter, an `opaque` — is not compared: it could be
     * anything, and refusing it against everything would refuse unions that work.
     */
    for (let i = 0; i < all.length; i++) {
        for (let j = i + 1; j < all.length; j++) {
            const first = all[i] as Option
            const second = all[j] as Option
            if (first.declares || second.declares) continue
            if (identifies(first) || identifies(second)) continue
            const shared = first.carries?.find((kind) =>
                second.carries?.includes(kind),
            )
            if (shared) {
                throw new CodecError(
                    `${first.describe} and ${second.describe} both take the same kind of value — ${shared} — and neither checks what it is given, so no value can choose between them; give the entity a discriminator and use discriminatedUnion`,
                )
            }
        }
    }

    /** Every option, for a message that says what was available. */
    const listed = () => all.map((option) => option.describe).join(' | ')

    const ambiguous = (first: Option, second: Option, what: string) =>
        new CodecError(
            `${first.describe} and ${second.describe} both admit ${what}; these options cannot be told apart, so give them a discriminator and use discriminatedUnion`,
        )

    const unmatched = (what: string) =>
        new CodecError(`no option admits ${what}; options are ${listed()}`)

    /**
     * What was being matched, named by the names it had.
     *
     * The names are the actionable half of both messages — "no option admits this item" says nothing
     * a reader can act on, while the set of attributes it turned up with says exactly which option
     * was expected to declare them. A value that is not a record has no names, and then there is
     * nothing to add.
     */
    const naming = (label: string, names: ReadonlySet<string> | undefined) =>
        names
            ? `${label} with attributes ${[...names].map((x) => `'${x}'`).join(', ') || '(none)'}`
            : label

    /**
     * The one option this could be, or why there is not exactly one.
     *
     * Two steps, and both are needed. The **kind** filter comes first and is the only step that can
     * be trusted on its own: an option that takes a string cannot be the one for a number, and an
     * option that writes `S` cannot read an `N`. If it leaves one option, that option *is* the answer
     * — so a failure past that point is its error, reported as itself rather than swallowed into "no
     * option matched".
     *
     * If it leaves several, they are **tried**, and exactly one must succeed. That step alone would
     * not do: encoding does not validate (see {@link carries}), so several permissive options would
     * all "succeed" on a value only one of them means. And the first step alone would not do either:
     * `literal('A')` and `literal('B')` take the same kind of value and are never ambiguous.
     */
    const only = <A>(
        survives: (option: Option) => boolean,
        named: string,
        through: (option: Option) => Result<A>,
    ): Result<A> => {
        const candidates = all.filter(survives)
        if (candidates.length === 0) return unmatched(named)
        if (candidates.length === 1) return through(candidates[0] as Option)

        let first: Option | undefined
        let carried: Result<A> | undefined
        for (const option of candidates) {
            const attempt = through(option)
            if (failed(attempt)) continue
            if (first) return ambiguous(first, option, named)
            first = option
            carried = attempt
        }
        return first ? (carried as Result<A>) : unmatched(named)
    }

    /** Which options a value could be for: an object option by its names, anything else by kind. */
    const forValue =
        (shape: Shape | undefined, names: ReadonlySet<string> | undefined) =>
        (option: Option) =>
            option.declares
                ? shape === 'map' && !!names && admits(option, names)
                : !option.carries || !shape || option.carries.includes(shape)

    type T = DerivedUnion<Options>

    /** The same, from the stored side, where the member carried is what filters. */
    const read = (attribute: AttributeValue): Result<T> => {
        const member = memberOf(attribute)
        const carriedMap =
            member === 'M'
                ? (attribute as { readonly M: AttributeMap }).M
                : undefined
        const names = carriedMap ? namesOf(carriedMap) : undefined
        return only(
            (option) =>
                option.declares
                    ? member === 'M' && !!names && admits(option, names)
                    : option.member === undefined ||
                      member === undefined ||
                      option.member === member,
            naming('this attribute', names),
            (option) => option.codec.decode(attribute) as Result<T>,
        )
    }

    /** The item reading's own matcher: the value is always a record, so only names filter. */
    const readItem = (item: StoredItem): Result<T> => {
        const names = namesOf(item)
        return only(
            (option) => admits(option, names),
            naming('this item', names),
            (option) =>
                (
                    option.item as ItemCodec<Record<string, unknown>, unknown>
                ).decode(item) as Result<T>,
        )
    }

    const writeItem = (item: T): Result<AttributeMap> => {
        const names = namesOf(item as Record<string, unknown>)
        return only(
            (option) => admits(option, names),
            naming('this entity', names),
            (option) =>
                (
                    option.item as ItemCodec<Record<string, unknown>, unknown>
                ).encode(item as Record<string, unknown>),
        )
    }

    /**
     * The same union read as a whole item, which only an all-object union has.
     *
     * An item is a map, so an option that writes anything else has nothing to contribute at the top
     * level. The type says so — {@link UnionCodec} replaces this with a message where it does not
     * apply — and the runtime is built either way rather than branching, because an option that could
     * not be reached here also cannot be selected here: `declares` is what selects, and only an
     * object option has it.
     */
    const self: Untagged<T, SpecsOf<Options>> = {
        encode: writeItem,
        decode: readItem,
        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        variant: (index) => (all[index] as Option).item as never,
        spec: (options as readonly AnyCodec[]).map(
            (option) =>
                (option as unknown as Partial<AnyObjectCodec>).item?.spec,
        ) as never,
        def: {
            kind: 'untagged',
            variants: all.map((option) => option.codec),
        },
    }

    // the option chosen writes what it writes; `WrittenBy` is the union of those, which no single
    // call can be narrowed to from inside
    const write = (value: T): Result<WrittenBy<Options>> => {
        const held = asRecord(value)
        return only(
            forValue(shapeOf(value), held ? namesOf(held) : undefined),
            naming('this value', held ? namesOf(held) : undefined),
            (option) => option.codec.encode(value as never),
        ) as Result<WrittenBy<Options>>
    }

    return {
        encode: write,
        decode: read,
        unsafeEncode: (value) => orThrow(write(value)),
        unsafeDecode: (attribute) => orThrow(read(attribute)),
        def: {
            kind: 'untagged',
            variants: all.map((option) => option.codec),
        },
        item: self as never,
    }
}

/**
 * How a union of objects is declared: with a tag, or by the attributes each variant has.
 *
 * One parameter and one signature. Overloads would read the same at the call and cost the
 * diagnostic — `No overload matches this call` at the call site instead of a message on the
 * argument, which is what two signatures on `tableEntry` were measured to do. A union in one
 * inference slot would cost worse: a string and an array sharing a slot is how `tableEntry` came to
 * infer a codec from a separator.
 */
