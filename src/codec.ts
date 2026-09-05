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
import {
    carrying,
    isNumeral,
    isStoredNumeral,
    memberOf,
    tooDeeplyNested,
} from './attribute'
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
     * survives, and `string.set()` must not be empty. `size` bounds recursion.
     */
    readonly arbitrary?: (rng: Rng, size: number) => Out
    /**
     * Values simpler than `value`, cheapest first. Must be finite and never yield `value` itself.
     */
    readonly shrink?: (value: In) => readonly Out[]
    /** What this codec is — see {@link CodecDef}. */
    readonly def: CodecDef
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

/**
 * Anything a {@link rest} produced, whatever it marks — {@link AnyCodec}'s counterpart for the one
 * thing that is a position rather than a codec, and the only element type {@link tuple} accepts that
 * is not a codec.
 *
 * Written as the marked shape rather than as `RestCodec<unknown, AttributeValue>`, for the reason
 * {@link TupleWrites} records: `AttributeCodec` names its value on both sides, so it is invariant
 * and the `unknown` instantiation matches no real one.
 */
export type AnyRest = { readonly [restMarker]: true; readonly rest: AnyCodec }

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
          /**
           * Which ground term the alternatives belong to — **named, not inferred**.
           *
           * This used to be absent, and every reader worked it out from `typeof allowed[0]`: digits
           * were `N`, text was `S`. That guess is exactly what `decimal('1')` refutes — its
           * alternatives are text and it stores `N` — so the base is recorded rather than recovered.
           * `formal/Calculus/Domain.lean:539` carries the same decision as `GroundKind`, an *index*
           * on `Term.literal` rather than a premise read off the values.
           */
          readonly base: LiteralBase
          readonly allowed: readonly LiteralValue[]
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
          /** The declared attributes, each with its presence mark — see {@link Field}. */
          readonly of: Readonly<Record<string, Field>>
          /**
           * The policy for what the spec does not name — the constructor's own argument, verbatim.
           *
           * Recorded because a definition that left it out did not determine the codec: two objects
           * differing only in their rest policy had the same definition, and a harness reading it
           * generated only the declared attributes — so an open entity's round-trip law was checked
           * on its closed part and nowhere else.
           *
           * This used to record the rest *codec* alone, and `undefined` for either string policy, on
           * the argument that neither puts anything in the entity so a generator has nothing to make
           * of them. That argument is about the *write* half only. `drop` and `refuse` disagree about
           * whether an undeclared name is an error, which is the read half — §4's `p` — so a
           * consumer reading a definition to reconstruct the codec could not reconstruct that, and
           * `src/lean.ts` was silently writing `Rest.drop` for both. The field now carries the
           * policy itself, so the three cases are three values rather than two.
           */
          readonly rest: RestDeclaration
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
          /**
           * The stand-in. A value, not a thunk: §3 `(fallback)` asks that it be *writable* by the
           * inner term, which is decidable at the declaration, and a thunk defers the only question
           * worth asking about it. One value is held here and a *copy* is handed to each read that
           * needs one, so the check happens once and nothing is shared — see `copiedPerRead`.
           */
          readonly value: unknown
      }
    | { readonly kind: 'legacy'; readonly current: AnyCodec }
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
    | {
          readonly kind: 'custom'
          /**
           * The pair itself, erased — `Term.custom` carries `ce` and `cp` as data and this is that.
           *
           * It used to carry nothing, on the ground that a definition should not claim a member, a
           * kind of value or a shape beneath that a pair of foreign functions does not have. That
           * ground is intact and this does not touch it: the two functions *are* the term, not a
           * description of one, so `writes`, `carries` and `deeper` still answer nothing here.
           * What it buys is that the definition now determines the codec at every constructor —
           * `admits` asks the pair the definition carries rather than the codec beside it.
           */
          readonly encode: (value: never) => Result<AttributeValue>
          /**
           * Erased as {@link held}'s adapter is. Not `Result<unknown>`, which *is* `unknown` —
           * `Result<T>` is `T | CodecError` — so the annotation would say nothing. A caller asks
           * {@link failed} of what comes back, exactly as it does of the codec's own `decode`.
           */
          readonly decode: (attribute: AttributeValue) => unknown
      }

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
 * `Term` and a `FieldDef` deliberately does not, so reporting a field as "no corresponding term"
 * would be reporting the stratification as a gap.
 *
 * **There are two levels here and §4 has three, which is the point rather than an omission.** A
 * rest policy denotes a `Rest`, and a `Rest` is not something a *codec* can be: it is a payload of
 * the two things that have one, a tuple's `tail` and an object's `rest`, exactly as `Body` carries
 * it in the model. `rest(c)` is a marker those two unwrap at construction and never a codec, so
 * there is no definition kind for it and nothing for a third stratum to classify.
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
const _everyKindHasALevel: Classified<CodecDef['kind'], TermKind | FieldKind> =
    true
void _everyKindHasALevel

/** A definition that denotes a §3 `Term`. */
export type TermDef = Extract<CodecDef, { readonly kind: TermKind }>

/** A definition that denotes a §4 `Field`. */
export type FieldDef = Extract<CodecDef, { readonly kind: FieldKind }>

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
        // a literal's member follows from its **base**, which the definition now names. It used to
        // follow from `typeof allowed[0]`, and that reading has a counterexample: `decimal('1')`
        // holds text and stores `N`
        case 'literal':
            return literalMember[def.base]
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
 * value and still be disjoint — `string('A')` and `string('B')` both take a string, and exactly one
 * of them accepts `'A'`.
 *
 * `undefined` means the kind does not decide: `opaque` takes anything, and asking a `lazy` would
 * force the resolution it exists to defer.
 */
export const carries = (codec: AnyCodec): readonly Shape[] | undefined => {
    const def = codec.def
    switch (def.kind) {
        case 'refine':
        case 'optional':
        case 'fallback':
            return carries(def.inner)
        case 'legacy':
            return carries(def.current)
        // and this one deliberately does *not* read through. An adapter exists precisely to change
        // the kind of value held — `held(string.set(), ...)` takes an array where `string.set()` takes
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
        // the same fact from the other side of the pair, and the two sides do not agree base for
        // base: `decimal(...)` takes a string and writes an `N`, exactly as bare `decimal` does
        case 'literal':
            return [literalShape[def.base]]
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
    switch (def.kind) {
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
 * Which of the four set bases this codec's elements sit at, or `undefined` if it is not one.
 *
 * The companion of {@link writes} for {@link set}, and the two answer different questions. `writes`
 * is a fact about the *attribute*: `decimal.set()` and `number.set()` both write `NS`, so the member
 * cannot tell them apart. This is a fact about the *term*, and it can — which is exactly why
 * `formal/Calculus/Domain.lean:602` indexes a set by a base rather than by a `Member`.
 *
 * Reads through `refine` and a literal, and through nothing else. Both of those are *restrictions*
 * of a base, so the set they build is a restriction of the base's set — `setCodec_restrict`. An
 * adapter (`held`), a read widening (`legacy`) or a union is not a restriction of anything, has no
 * base, and gets `undefined`.
 */
export const setBase = (codec: AnyCodec): SetBase | undefined => {
    const def = codec.def
    switch (def.kind) {
        case 'string':
        case 'number':
        case 'decimal':
        case 'binary':
            return def.kind
        // a literal at `boolean` is the one that has no set: there is no `BOOLS`
        case 'literal':
            return def.base === 'boolean' ? undefined : def.base
        case 'refine':
            return setBase(def.inner)
        default:
            return undefined
    }
}

/**
 * Whether this codec admits this value — §3's `Adm : Term → Value → Bool`, ported.
 *
 * The sixth reader of a definition, beside {@link writes}, {@link carries}, {@link decides},
 * {@link setBase} and {@link deeper}, and it is a *function of the term* rather than a field of the
 * codec for the same reason they all are: there is nothing to forget in a function. The model
 * proved this exact at all 21 constructors (`Adm_exact`), which is what makes the port sound rather
 * than a second description of the same thing drifting from it.
 *
 * **This is exactly "encode succeeds", both ways**, and it was not always. Encoding did not
 * validate — a codec's input is typed, so `string.encode(5)` wrote `{ S: 5 }` — and the law held
 * one way round, failing at twenty-three of the thirty-two codecs in `codec.laws.spec.ts`'s table.
 * Every row runs the predicate this function runs now, so `admits(c, v) ⟺ !isError(c.encode(v))`
 * is the law that file states, over the whole table and pool.
 *
 * **The predicates live here and `encode` calls them, rather than the reverse**, at every row but
 * the two below. That direction is forced: `admits` reaches `opaque` and `custom` *by* calling
 * `encode`, so an `encode` that consulted `admits` there would not terminate. Those two need no
 * consulting — asking a codec cannot disagree with its answer — and the carve-out is the whole of
 * it.
 *
 * **Two rows ask their codec instead of describing it**, which is the model's own move (`adm
 * (.custom ce _) = fun v => (ce v).isSome`, and `opaque`'s rows were converted to match):
 *
 * - `custom` carries the pair itself, which is not a description of a set but the thing that
 *   decides it, so asking is the only option.
 * - `opaque` carries only `numbers`, and its domain is everything else it checks: nesting depth,
 *   plain-object-ness, no empty set, no `NS`, no `Map`, no `bigint`. A hand-written recursion
 *   stating that a second time is a description that must be kept in agreement with what it
 *   describes; a question cannot drift. The brief for this asked for a closed form here and it
 *   would have been the weaker choice.
 *
 * `lazy` terminates because it recurses on the **value**, not on the term: `def.get()` is forced
 * once per level of the value, and a value is finite.
 */
export const admits = (codec: AnyCodec, value: unknown): boolean => {
    const def = codec.def
    switch (def.kind) {
        case 'string':
        case 'boolean':
        case 'binary':
            return shapeOf(value) === def.kind
        // the gate already inside `encode`, lifted out: writing an `N` means writing a numeral, and
        // `Number.isFinite` is not that test
        case 'number':
            return typeof value === 'number' && isNumeral(String(value))
        // `isStoredNumeral` stringifies what it is given — `isStoredNumeral(['1'])` is `true` — so
        // the kind is checked first rather than relying on the regexp to do it
        case 'decimal':
            return typeof value === 'string' && isStoredNumeral(value)
        case 'null':
            return value === null
        // dispatched on the base, because the base is what says which JS kind the alternatives are;
        // `sameLiteral` is what compares binary by its octets rather than by reference
        case 'literal':
            return (
                shapeOf(value) === literalShape[def.base] &&
                def.allowed.some((one) =>
                    sameLiteral(one, value as LiteralValue),
                )
            )
        // non-emptiness is part of it: DynamoDB has no empty `SS`, so `encode` refuses one and this
        // has to as well or the implication fails at the empty set
        case 'set':
            return (
                value instanceof Set &&
                value.size > 0 &&
                [...value].every((member) => admits(def.element, member))
            )
        // and `[]` **is** admitted, which is the mirror of that and is correct: `L` has an empty
        // inhabitant where the set members do not
        case 'array':
            return (
                Array.isArray(value) &&
                value.every((element) => admits(def.element, element))
            )
        case 'tuple': {
            if (!Array.isArray(value)) return false
            const fixed = def.elements.length
            const tail = def.tail
            if (tail ? value.length < fixed : value.length !== fixed) {
                return false
            }
            return value.every((one, at) =>
                admits((def.elements[at] ?? tail) as AnyCodec, one),
            )
        }
        case 'record': {
            const held = asRecord(value)
            return (
                held !== undefined &&
                Object.values(held).every((one) => admits(def.value, one))
            )
        }
        /**
         * §4's field table, read the way `encode` reads it: a declared name must be there and be
         * admitted unless the field is `optional`, and an undeclared name is checked only where
         * there is a rest codec to check it with — `drop` and `refuse` both ignore it on the way
         * in, which is what `encode` does.
         *
         * A `fallback` field is **not** absence-tolerant here, and that matches `encode`: the
         * stand-in is what a *read* supplies when the attribute is missing, not what a write may
         * leave out.
         */
        case 'attributes': {
            const held = asRecord(value)
            if (!held) return false
            for (const name in def.of) {
                const field = def.of[name]
                if (field === undefined) continue
                const at = held[name]
                if (at === undefined) {
                    if (field.mark === 'optional') continue
                    return false
                }
                if (!admits(field.codec, at)) return false
            }
            const rest = def.rest
            if (typeof rest === 'string') return true
            for (const name in held) {
                if (name in def.of || held[name] === undefined) continue
                if (!admits(rest, held[name])) return false
            }
            return true
        }
        /** The tag lookup, `Object.hasOwn` for the reason {@link discriminatedUnion} gives. */
        case 'tagged': {
            const held = asRecord(value)
            const tag = held?.[def.discriminator]
            if (tag === undefined) return false
            const name = String(tag)
            return (
                Object.hasOwn(def.variants, name) &&
                admits(def.variants[name] as AnyCodec, value)
            )
        }
        /**
         * The disjunction, which is what the *value* side of a union is: an option admits it or
         * none does. Left as a disjunction on purpose — the resolver `union` actually runs is a
         * different question (it counts, and refuses where two options both admit), and rewiring
         * it to this is a behaviour change out of scope here.
         */
        case 'untagged':
            return def.variants.some((variant) => admits(variant, value))
        case 'refine':
            return (
                admits(def.inner, value) &&
                def.refined.is(value as never) === true
            )
        /**
         * An adapter is asked about the value it *holds*, so the value is put through the adapter
         * first — and the adapter is a caller's function, which throws on a value it does not own
         * (`(value as readonly string[]).join` on a number). A throw is not an admission.
         */
        case 'held':
            try {
                return admits(def.inner, def.adapt.encode(value as never))
            } catch {
                return false
            }
        // a read widening writes what it currently is, and the older readings are read-side only
        case 'legacy':
            return admits(def.current, value)
        // the same ownership question the constructor asks: where the inner term owns the null
        // point, `nullable` is that term and `null` is admitted only if the term admits it
        case 'nullable':
            return ownsNull(def.inner)
                ? admits(def.inner, value)
                : value === null || admits(def.inner, value)
        // §4's fields: the mark is about the name, and what may be held is the inner term's
        case 'optional':
        case 'fallback':
            return admits(def.inner, value)
        case 'lazy':
            return admits(def.get(), value)
        // the two that ask — see the note above. They ask different things, and the difference
        // is where the pair lives: `custom`'s two functions are data the definition carries, so
        // the definition answers; `opaque`'s codec is this library's own, reached through the
        // codec beside the definition because `numbers` is all the definition needs to carry
        case 'custom':
            try {
                return !failed(def.encode(value as never))
            } catch {
                return false
            }
        case 'opaque':
            try {
                return !failed(codec.encode(value as never))
            } catch {
                return false
            }
    }
}

/**
 * Whether this codec reads this attribute at all — §3's `AdmA`, and **not** ported the way
 * {@link admits} ports `Adm`.
 *
 * `admits` is a reader of the *definition*, one row per constructor, because the write side was
 * loose: `encode` trusted its argument's type, so "would this be written?" and "does the row
 * admit it?" were different questions and the row was the honest one. **The read side never had
 * that licence.** It parses data somebody else wrote, so it validates, and a differential over
 * 864 (codec, attribute) pairs found the model's `AdmA` and this library's read agreeing at all
 * 861 checkable ones (`a41f874`, `formal/ARCHITECTURE.md` §10). A twenty-one-row reader here
 * would be a second description of something already exact — so this **asks the codec**, which is
 * the same move `admits` itself makes at its two exact rows.
 *
 * A throw is not a reading: an adapter is a caller's function and may throw on an attribute it
 * does not own, exactly as it may on a value.
 *
 * **Internal.** Like the six definition readers, it is not on the published surface — see
 * `Rotorise.ts`'s export list. It exists because two places had already written it: `testing.ts`
 * had it as `reads`, and `lean.ts`'s read-verdict generator had the same six lines inlined, and
 * neither could see the other's.
 */
export const admitsAttribute = (
    codec: AnyCodec,
    attribute: AttributeValue,
): boolean => {
    try {
        return !failed(codec.decode(attribute as never))
    } catch {
        return false
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
    const one = (child: AnyCodec | undefined) => (child ? [child] : [])
    switch (def.kind) {
        case 'attributes':
            return one(def.of[String(segment)]?.codec)
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
 * It says **`custom`**, which is the definition for a pair of functions with no structure beneath
 * them, and that is what this is. It used to be a `CodecDef` kind of its own called `branch`, so a
 * definition language for codecs contained an entry that was not a codec and every reader had to
 * know about it; and it used to carry no definition at all, which stopped being available when
 * `def` became required. `custom` costs no reader a case and changes no answer: `writes`, `carries`
 * and `deeper` say nothing at a `custom`, exactly as they said nothing at a missing definition, and
 * `admits` reaches the same `false` by attempting the pair and catching the throw rather than by
 * declining to claim.
 */
const unresolvedAt = (path: string): AnyCodec => {
    const unresolved = () => {
        throw new CodecError(
            `'${path}' is declared differently in different variants, so this path cannot say which codec to encode with. Reach for the variant you mean — \`variant(...)\` is an item codec with its own \`at\` — or narrow the entity so only one variant declares it.`,
        )
    }
    return codec<never, AttributeValue>({
        def: { kind: 'custom', encode: unresolved, decode: unresolved },
        encode: unresolved,
        decode: unresolved,
    })
}

/** A map of attribute name to codec — what `item`, `map` and each `tagged` variant hold. */
export type Attributes = Readonly<Record<string, AnyCodec>>

/**
 * One declared attribute of an object, with the mark that says when it may be absent.
 *
 * §4's `Field`, and the model's `Field` is these same three cases. **Not {@link FieldDef}**, which
 * is a different thing one level up: `FieldDef` is the *definition of a codec* that marks a field —
 * what `optional(string)` is when a caller holds it on its own — while this is a *position in a
 * body*, which is what §4 means by a field and what has a mark at all.
 *
 * **The mark used to be the wrapping codec's definition kind, and reading a field meant walking
 * two definitions**: `def.of[name].def.kind === 'optional'`, at six sites, each of which had to
 * know that `optional` and `fallback` are the only two kinds that count as marks. The mark sits
 * beside the codec now, so the walk is one lookup and the set of marks is closed by this type.
 * `object` unwraps the marker at construction, which is where it already resolved the presence
 * rules for its own encode and decode.
 */
export type Field =
    | { readonly mark: 'required'; readonly codec: AnyCodec }
    | { readonly mark: 'optional'; readonly codec: AnyCodec }
    | {
          readonly mark: 'fallback'
          readonly codec: AnyCodec
          /** The stand-in — see {@link fallback}, which checks it is writable at construction. */
          readonly value: unknown
      }

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
 *
 * **What the caller owes, and it is the whole of §2.** Every other constructor here has its laws
 * *proved* from the terms it is built out of; this one takes two foreign functions, so the model
 * discharges it by assumption — `Lawful (denote t)` as a premise
 * (`formal/Calculus/Soundness.lean:74`). No gate is possible and none is attempted: the pair is
 * arbitrary code, and there is no definition to read. The four:
 *
 * 1. **(R)** retraction — `decode(encode(t))` is `t`, exactly, for every `t` you write.
 * 2. **(C)** canonizability — everything `decode` accepts, `encode` can write back.
 * 3. **(W)** member-naming — every `encode` writes the same member, or the codec names none.
 * 4. **(MP)** — reading an attribute and writing it back never changes its member.
 *
 * They are checkable, just not from here. `checkRoundTrip` is (R) over generated values,
 * `checkDecodesAreWritable` is (C) against attributes nobody would write — which is the direction
 * a round trip cannot reach, and where three of this library's shipped defects lived — and
 * `checkMembersStable` is (W) and (MP). All three are in `./testing`, and a `custom` without them
 * is a codec whose laws nobody has asserted.
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
        // the pair, as data: a hand-written codec's definition *is* its two functions. `writes`,
        // `carries` and `deeper` are still told nothing, because two foreign functions have no
        // member, no kind of value and no shape beneath to tell them about
        def: {
            kind: 'custom',
            encode: raw.encode as (value: never) => Result<AttributeValue>,
            decode: raw.decode,
        },
        arbitrary: raw.arbitrary,
        shrink: raw.shrink,
    })

// ── scalars ─────────────────────────────────────────────────────────

/**
 * The ground terms a literal can sit at.
 *
 * **Named by the caller, never guessed.** `literal(...)` read its carrier off the JS type of its
 * arguments — digits meant `N`, text meant `S` — and that was the one place in this library where a
 * term's member followed from its *values* rather than from its name. That constructor is now
 * removed, not merely deprecated: a literal is a capability of the primitive that names the base,
 * so `string('A')`, `number(1)` and `decimal('1')` each say which ground term they narrow.
 *
 * The list is §3's `GroundKind` **minus `null`**. It read "plus `decimal`" while `GroundKind` was
 * `string | number | boolean | binary | null`; `decimal` is a ground base in the model now, so the
 * difference is the other way round and it is a stratification one — `nullValue` is a codec and
 * `nullValue()` is not a literal anyone can write, because the only nonempty subset of `Unit` is
 * `Unit`.
 */
export type LiteralBase = 'string' | 'number' | 'decimal' | 'boolean' | 'binary'

/** An alternative, at whichever base carries it. */
export type LiteralValue = string | number | boolean | Uint8Array

/**
 * Which member each base stores a literal in.
 *
 * Not injective: `number` and `decimal` both store `N`. That is exactly why the base has to be
 * recorded — the member cannot recover it, and neither can the JS type of the values, since a
 * `decimal` literal's alternatives are text.
 */
const literalMember: { readonly [B in LiteralBase]: AttributeName } = {
    string: 'S',
    number: 'N',
    decimal: 'N',
    boolean: 'BOOL',
    binary: 'B',
}

/** Which kind of JS value each base's alternatives are — the mirror, and not the same partition. */
const literalShape: { readonly [B in LiteralBase]: Shape } = {
    string: 'string',
    number: 'number',
    // a decimal is held as a string and stored as `N`, which is the whole point of it
    decimal: 'string',
    boolean: 'boolean',
    binary: 'binary',
}

/**
 * The bases a native set can be built from — `formal/Calculus/Domain.lean:602`'s `SetBase`.
 *
 * `boolean` is the one base with no set: DynamoDB has `SS`, `NS` and `BS`, and no `BOOLS`. Four
 * bases onto three wire members, because `number` and `decimal` are both real and neither is a
 * legacy spelling of the other.
 */
export type SetBase = Exclude<LiteralBase, 'boolean'>

/** Two alternatives, compared the way the base compares them: bytes for `binary`, `===` otherwise. */
const sameLiteral = (one: LiteralValue, other: LiteralValue): boolean =>
    one instanceof Uint8Array
        ? other instanceof Uint8Array &&
          one.length === other.length &&
          one.every((byte, at) => byte === other[at])
        : one === other

/** An alternative as a message names it: text in quotes, digits bare, bytes in hex. */
const namedLiteral = (one: LiteralValue): string =>
    typeof one === 'string'
        ? `'${one}'`
        : one instanceof Uint8Array
          ? `0x${[...one].map((byte) => byte.toString(16).padStart(2, '0')).join('')}`
          : String(one)

/**
 * A literal at a named base — the one builder every literal in this library goes through.
 *
 * The premises §3 states on `(literal)`, checked where the rule states them:
 *
 * - **`ℓ` is non-empty.** Checked by each caller, because the message wants to name the
 *   constructor the caller actually wrote.
 * - **`ℓ` is homogeneous at the base.** Free in the model — `NEFinset k.Carrier` — and not free
 *   here, because a spread of a plain array defeats the type. So it is a construction-time refusal.
 * - **`ℓ ⊆ D`** at the two bases that write an `N`. `number` reads through `Number.prototype
 *   .toString`; `decimal` is text already and has to be in the form the service returns, or the
 *   literal is one this codec could write and never read back.
 *
 * All three are decided when the codec is built, because `ℓ` is data this library owns.
 */
const literalCodec = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): AttributeCodec<T, AttributeValue> => {
    const member = literalMember[base]

    const wrong = allowed.filter((one) => shapeOf(one) !== literalShape[base])
    if (wrong.length) {
        throw new CodecError(
            `\`${base}(...)\` admits ${literalShape[base]} values, and ${wrong
                .map(namedLiteral)
                .join(', ')} ${wrong.length === 1 ? 'is' : 'are'} not one`,
        )
    }

    /**
     * **`ℓ ⊆ D`** — the premise on the numeric bases, and the defect that made it more than
     * bookkeeping. `literal(NaN)` produced `{ N: 'NaN' }` and `literal(1e400)` produced
     * `{ N: 'Infinity' }`, both reachable with no cast and both rejected by the service.
     */
    if (base === 'number') {
        const outside = (allowed as readonly number[]).filter(
            (one) => !isNumeral(String(one)),
        )
        if (outside.length) {
            throw new CodecError(
                `a numeric literal is stored as 'N', and ${outside
                    .map(namedLiteral)
                    .join(
                        ', ',
                    )} ${outside.length === 1 ? 'is not a number' : 'are not numbers'} DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN or Infinity`,
            )
        }
    }

    /**
     * The same premise at `decimal`, and it is *narrower* than `number`'s, for the reason
     * {@link decimal} gives: the service normalises what it accepts, and this codec's read side is
     * the identity on the digits, so an alternative in any other form is one that could be written
     * and would come back as a different string.
     */
    if (base === 'decimal') {
        const outside = (allowed as readonly string[]).filter(
            (one) => !isStoredNumeral(one),
        )
        if (outside.length) {
            throw new CodecError(
                `a decimal literal is stored as 'N' in the form DynamoDB returns, and ${outside
                    .map(namedLiteral)
                    .join(
                        ', ',
                    )} ${outside.length === 1 ? 'is' : 'are'} not: it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
            )
        }
    }

    return codecOfTerm<T, AttributeValue>({ kind: 'literal', base, allowed })
}

/** `ℓ` non-empty, refused where the caller can see which constructor named nothing. */
const someAlternatives = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): readonly T[] => {
    if (allowed.length === 0) {
        throw new CodecError(
            `a literal admits one of a non-empty set of values, and \`${base}()\` names none; pass the values, or use \`${base}\` itself if anything is admissible`,
        )
    }
    return allowed
}

/**
 * Where a literal is stored, which follows from what it holds.
 *
 * Non-distributive on purpose: `'A' | 'B'` is `S`, `0 | 1` is `N`, and a set mixing the two is
 * `never` — a codec cannot write two members, and the type says so before the constructor has to.
 *
 * The default of {@link ConstantCodec}'s second parameter, and only the default. `decimal('1')`
 * holds a string and stores `N`, so it passes its attribute explicitly: this type is the *guess*
 * the new surface exists to stop making, kept because {@link literal} still makes it.
 */
export type LiteralAttribute<T> = [T] extends [string]
    ? Attribute<'S'>
    : [T] extends [number]
      ? Attribute<'N'>
      : never

/**
 * A literal with exactly one admissible value.
 *
 * Its own type records the value, which is what lets a caller that has no entity in hand — a key
 * being rebuilt, say — read the value off the schema rather than be handed it. A literal of two
 * or more values is an ordinary {@link AttributeCodec}: it narrows what is admissible without
 * deciding it.
 *
 * `constant` is a **type-level** brand and carries no runtime property; {@link decides} is what
 * reads the value back at runtime.
 */
export type ConstantCodec<
    T extends LiteralValue,
    A extends AttributeValue = LiteralAttribute<T>,
> = AttributeCodec<T, A> & { readonly constant: T }

/**
 * The `.set()` capability, on the four bases that have one.
 *
 * `base.set()` is the whole base; `base.set(...values)` is a set of a literal at it. Both are the
 * same {@link set} underneath, which is what keeps there being one set combinator rather than two.
 */
const setCapability =
    (base: SetBase, ground: () => AnyCodec) =>
    (...allowed: readonly LiteralValue[]) =>
        // the *public* codec, reached through a thunk because it is the constant being defined:
        // `string.set()` and the set of that same base should be the same codec, definition
        // included, and a second element object built from the same closures would compare unequal
        set(
            (allowed.length
                ? literalCodec(base, allowed)
                : ground()) as AnyCodec,
        )

/** The literal capability, on every base. */
const literalCapability =
    (base: LiteralBase) =>
    (...allowed: readonly LiteralValue[]) =>
        literalCodec(base, someAlternatives(base, allowed))

/**
 * A string, as `S`. Exact in both directions: DynamoDB does not normalise strings.
 *
 * ```ts
 * string              // any string
 * string('A')         // exactly 'A', and its type says so
 * string('A', 'B')    // one of two
 * string.set()        // SS
 * string.set('A', 'B')// SS whose members are checked
 * ```
 *
 * Callable *and* a codec, the same {@link opaque} trick and for the same reason: `string.encode`
 * and `string('A')` are one name for one ground term, rather than a codec and a constructor that
 * have to be kept in step.
 */
export type StringCodec = AttributeCodec<string, Attribute<'S'>> & {
    <const T extends string>(only: T): ConstantCodec<T, Attribute<'S'>>
    <const T extends string>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'S'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<string>, SS>
        <const T extends string>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, SS>
    }
}

/**
 * A value's kind, for a message about a value that should not have arrived.
 *
 * The five ground `encode`s all refuse the same way and want to say the same thing about what they
 * were handed. `shapeOf` answers `undefined` for what it cannot place — a `bigint`, a `Map`, a
 * function — and `typeof` is the honest fallback there rather than a guess.
 */
const describeShape = (value: unknown): string =>
    `${shapeOf(value) ?? typeof value} \`${String(value)}\``

/* ── §3's terms, denoted ──────────────────────────────────────────────────────────────── */

/**
 * The two halves a term denotes, with neither half's type known.
 *
 * A term does not carry the TypeScript type its codec has — `{ kind: 'string' }` says `S` and says
 * nothing about `string` — so {@link denote} answers in the erased pair and {@link codecOfTerm}
 * puts the type back on, once, where the constructor knows it.
 */
type Pair = {
    readonly encode: (value: never) => Result<AttributeValue>
    readonly decode: (attribute: AttributeValue) => Result<unknown>
}

/**
 * §3's ground terms, as one construction — the model's `pointCodec` under this library's word.
 *
 * A prism pair, which `src/` has no name of its own for; §3 calls what it builds a *ground term*,
 * so that is the word here.
 *
 * A payload carried between a value constructor and an attribute constructor, both prisms. The
 * prism laws are §2's laws in disguise, which is why `lawful_pointCodec` needs no hypothesis about
 * either side beyond the member it stamps: `out_into` is the round trip **(R)** and `into_out` is
 * canonizability **(C)**.
 *
 * The shape test is {@link admits}', not a second one: `shapeOf` is the function that row calls, so
 * the two cannot drift into disagreeing about what a string is.
 */
const groundCodec = (
    shape: Shape,
    member: AttributeName,
    noun: string,
    writes: string,
): Pair => ({
    encode: (value) =>
        shapeOf(value) === shape
            ? carrying(member, value as never)
            : new CodecError(
                  `${describeShape(value)} is not ${noun}, and \`${shape}\` writes ${writes} — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
              ),
    decode: (attribute) => expect(member, attribute),
})

/**
 * **A pair between a value shape and a member, with the payload transformed on the way.**
 *
 * The model calls this `carriedCodec`, and so does this file: `carrying` is already the word here
 * for building an attribute out of a payload, and this is the codec that word describes.
 * {@link groundCodec} is the degenerate case, where the payload passes through untouched.
 *
 * The transform is the whole of what distinguishes the products from each other. `array` and
 * `record` hand it {@link every}, a traversal — the model's `entrywise` — and differ only in what
 * they traverse. `tuple` aligns first. `object` guards and filters first. `set` is the one product
 * that is not an instance, because its attribute side is a choice among three wire sets rather than
 * one member.
 */
const carriedCodec = <Payload, Written, Read>(
    holds: (value: unknown) => value is Payload,
    member: AttributeName,
    refuse: (value: unknown) => CodecError,
    into: (payload: Payload) => Result<Written>,
    outOf: (carried: Read) => Result<unknown>,
): Pair => ({
    // two casts, one reason: `member` is a *value* here, so the type checker cannot tie it to the
    // payload types either side of it. The model takes the two prisms as arguments and gets that
    // tie for free; this takes a member and a pair of transforms, and the row is what says they
    // agree — `'L'` with a list, `'M'` with a map
    encode: (value: unknown) =>
        holds(value)
            ? andThen(into(value), (written) =>
                  carrying(member, written as never),
              )
            : refuse(value),
    decode: (attribute) =>
        andThen(expect(member, attribute), (carried) => outOf(carried as Read)),
})

/**
 * §4's body: the declared fields and the policy for everything else, as one pair over a bare item.
 *
 * The model's `objectCodecCore`, and `objectCodecCore_eq` is the lemma. It is *not* a
 * {@link carriedCodec} instance on its own — it writes a bare map rather than an `M` — which is
 * exactly the distinction `.item` exposes: §5 says a codec writes the attributes of that codec, and
 * `object` writes the members of `object` like any other, offering `.item` for the one place that
 * writes no map. So `denote`'s row wraps this in the member and `.item` takes it as it is.
 *
 * **A field's mark is read here and nowhere else.** `fieldSem` in the model is the function that
 * turns `Field` into a presence rule; here it is the three-way `mark`, read once per field per
 * direction, and there is no second place that asks what `optional` means.
 *
 * Whether a stand-in must be *copied* per read is settled once, at the declaration, rather than
 * asked per item: {@link copiedPerRead} is a fact about this runtime and not about the term, which
 * is why it lives in the compiled form and not in {@link Field}.
 */
const bodySem = (
    of: Readonly<Record<string, Field>>,
    rest: RestDeclaration,
): {
    readonly encode: (
        held: Record<string, unknown>,
    ) => Result<Record<string, AttributeValue>>
    readonly decode: (
        item: Readonly<Record<string, AttributeValue>>,
    ) => Result<Record<string, unknown>>
} => {
    const declared: Declared[] = []
    for (const name in of) {
        const field = of[name]
        if (field === undefined) continue
        declared.push({
            name,
            codec: field.codec,
            optional: field.mark === 'optional',
            absent:
                field.mark === 'fallback'
                    ? {
                          value: field.value,
                          copy: copiedPerRead(field.value),
                      }
                    : undefined,
        })
    }
    const restCodec = typeof rest === 'string' ? undefined : rest
    return {
        encode: (held) => {
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
                    if (name in of || value === undefined) continue
                    const written = restCodec.encode(value as never)
                    if (failed(written)) return written.under(name)
                    out[name] = written
                }
            }
            return out
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
                        out[name] = absent.copy
                            ? structuredClone(absent.value)
                            : absent.value
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
            if (rest === 'drop') return out
            for (const name in item) {
                if (name in of) continue
                if (!restCodec) {
                    return new CodecError(
                        `'${name}' is not an attribute this codec declares; the schema and the data have drifted apart`,
                    )
                }
                const read = restCodec.decode(item[name] as AttributeValue)
                if (failed(read)) return read.under(name)
                out[name] = read
            }
            return out
        },
    }
}

/**
 * §3 `(held)`: a pair reached through an adapter — the model's `Codec.through`.
 *
 * The word is `held`'s, because that is what this library calls the term. `f` sits in front of `e`
 * and `g` sits behind `p`, so the adapter changes what the value is *held* as and leaves what it is
 * *stored* as alone. §5 turns on the asymmetry: the readable side sees through it and the writable
 * one cannot, which is the one row where the two sides of a term part in that direction.
 *
 * **A throw is a refusal like any other.** The two functions are the caller's, so either may throw
 * rather than return, and the guard is what makes that a value the way §2's error channel is one
 * rather than an exception escaping a codec.
 */
const heldThrough = (
    inner: AnyCodec,
    adapt: {
        readonly encode: (value: never) => unknown
        readonly decode: (held: never) => unknown
    },
): Pair => {
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
    return {
        encode: (value) =>
            andThen(into(value), (held) => inner.encode(held as never)),
        decode: (attribute) => {
            // `failed` rather than `andThen`, because a {@link Pair}'s read answers `unknown` and
            // `Result<unknown>` *is* `unknown` — the failure channel is not visible in that type,
            // so the test has to be made rather than inferred
            const read = inner.decode(attribute)
            return failed(read) ? read : outOf(read as never)
        },
    }
}

/**
 * **What a term means**, as one function on the definition.
 *
 * Every constructor's pair comes from here, so there is one description of what a term denotes
 * rather than one per constructor beside a definition that says the same thing. The model's
 * `denote` is this function and the rows below answer to its combinators one for one.
 *
 * **The `default` is temporary and this is the exit condition.** Rows arrive one constructor per
 * commit, each deleting that constructor's hand-written halves as it lands, and the branch is
 * unreachable from any constructor that has been switched. The pass that switches the last one
 * deletes the branch and adds the guard that makes a row-less kind a build error, the way
 * `_everyKindHasALevel` makes an unclassified kind one.
 */
const denote = (def: TermDef): Pair => {
    switch (def.kind) {
        case 'string':
            return groundCodec('string', 'S', 'a string', "an 'S'")
        case 'boolean':
            return groundCodec('boolean', 'BOOL', 'a boolean', "a 'BOOL'")
        case 'binary':
            return groundCodec('binary', 'B', 'a `Uint8Array`', "a 'B'")
        /**
         * §3 `(array)`: a list carried into an `L`, with the element's pair run entrywise.
         * `arrayCodec_eq` is the lemma, and the traversal is `every` here where the model writes
         * `entrywise` — one word for one concept, and this file already had it.
         *
         * The element's own methods are handed over rather than a closure around them: a closure
         * per call to encode a list is a closure per list in every item written. And `every`
         * iterates whatever is iterable, so a string arrived as its characters until the shape was
         * asked first — which is what `admits`' `array` row asks, and now what this asks too.
         */
        case 'array': {
            const items = def.element
            return carriedCodec(
                (value): value is readonly never[] => Array.isArray(value),
                'L',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not an array, and \`array\` writes an 'L' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (list) => every(list, items.encode),
                (carried: readonly AttributeValue[]) =>
                    every(carried, items.decode),
            )
        }
        /**
         * §3 `(record)`: the same construction as `array` at the other product.
         * `recordCodec_e_eq` is the lemma, and the two rows differ in exactly three things — the
         * shape they test, the member they carry, and whether the traversal walks positions or
         * entries. `every` and `everyEntry` are the two traversals; the model writes `entrywise`
         * once and instantiates it twice.
         *
         * `Object.entries('abc')` is `[['0','a'], …]`, so a string was written as a map keyed by
         * index until the shape was asked first. `asRecord` is the test `admits`' `record` row
         * uses, so the two cannot drift about what a plain object is.
         */
        case 'record': {
            const values = def.value
            return carriedCodec(
                (value): value is Record<string, never> =>
                    asRecord(value) !== undefined,
                'M',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not a plain object, and \`record\` writes an 'M' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (held) => everyEntry(held, values.encode),
                (carried: Readonly<Record<string, AttributeValue>>) =>
                    everyEntry(carried, values.decode),
            )
        }
        /**
         * §3 `(tuple)` and `(tuple-tail)` in one row, which is what the constructor carries.
         * `tupleCodec_eq` is the lemma and `align_eq_some` is what settles the tail: the arity
         * test comes **before** the positions, because a list of the wrong length has no
         * entrywise reading at all. `align` is the model's name for that step; here it is the two
         * length tests, and they are the same fact — a tuple with a tail aligns at *at least* its
         * fixed arity, one without at exactly it.
         *
         * A `Uint8Array` of the right length has the right `length` and is not a tuple, which is
         * what the length tests alone could not say. `admits`' `tuple` row asks `Array.isArray`
         * before it counts, and so does this, which is what makes the arity messages mean what
         * they say.
         */
        case 'tuple': {
            const items = def.elements
            const tail = def.tail
            /** `align`: the arity test, which comes before any position is read. */
            const aligned = (
                length: number,
                say: (arity: number) => string,
            ): CodecError | undefined =>
                (tail ? length < items.length : length !== items.length)
                    ? new CodecError(`${say(items.length)}, found ${length}`)
                    : undefined
            const atLeast = tail ? 'at least ' : ''
            const at = (index: number) => items[index] ?? (tail as AnyCodec)
            return carriedCodec(
                (value): value is readonly never[] => Array.isArray(value),
                'L',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not an array, and \`tuple\` writes an 'L' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (held) =>
                    aligned(
                        held.length,
                        (arity) => `expected ${atLeast}${arity} elements`,
                    ) ?? every(held, (one, index) => at(index).encode(one)),
                (carried: readonly AttributeValue[]) =>
                    aligned(
                        carried.length,
                        (arity) => `expected a list of ${atLeast}${arity}`,
                    ) ?? every(carried, (one, index) => at(index).decode(one)),
            )
        }
        /**
         * §3 `(set)`, and the one product that is **not** a {@link carriedCodec}. The model says
         * why: its attribute side is a choice among three wire sets rather than one member, so
         * there is no single `A` prism to carry a payload into. `setCodec_restrict` is the lemma
         * that keeps `refine` and a literal readable through — a restriction of the elements is a
         * restriction of the set, and the two write the same attribute.
         *
         * Which set follows from the element's member, so the row asks {@link writes} rather than
         * being told. §3 `(set)`'s premise is checked at the declaration, in {@link set}, where a
         * caller can see which element failed it.
         *
         * **Empty is refused in both directions, and the read side is the one that matters.**
         * DynamoDB never stores an empty `SS`, so an item carrying one was written by something
         * else; decoding it would hand back a value this codec's own `encode` refuses, which is
         * the pair's two halves disagreeing about what it holds — **(C)** failing.
         *
         * `value.size` is `undefined` on anything that is not a `Set`, so `=== 0` was false for a
         * string and `[...value]` then spread it into its characters: `string.set()` wrote
         * `{ SS: ['a','b','c'] }` for `'abc'`. `admits`' `set` row asks `instanceof Set` first.
         */
        case 'set': {
            const inner = def.element
            const member = writes(inner)
            if (member !== 'S' && member !== 'N' && member !== 'B') {
                throw new CodecError(
                    `a set holds strings, numbers or binary, and this element writes ${member ? `'${member}'` : 'no single member'}`,
                )
            }
            const setMember = `${member}S` as 'SS' | 'NS' | 'BS'
            const carried = (value: unknown): Result<string | Uint8Array> =>
                andThen(
                    inner.encode(value as never),
                    (written) =>
                        (written as Record<string, unknown>)[member] as
                            | string
                            | Uint8Array,
                )
            return {
                encode: (value: unknown) =>
                    !(value instanceof Set)
                        ? new CodecError(
                              `${describeShape(value)} is not a \`Set\`, and a ${setMember} is written from one — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                          )
                        : value.size === 0
                          ? new CodecError(
                                `DynamoDB has no empty ${setMember}; omit the attribute or use array(...)`,
                            )
                          : andThen(every([...value], carried), (written) =>
                                // sorted so what is stored does not depend on insertion order;
                                // deduplicated already, because a `Set` is
                                carrying(
                                    setMember,
                                    [...new Set(written)].sort() as never,
                                ),
                            ),
                decode: (attribute) =>
                    andThen(
                        andThen(expect(setMember, attribute), (members) =>
                            (members as readonly unknown[]).length === 0
                                ? new CodecError(
                                      `DynamoDB has no empty ${setMember}, so this attribute was not written by it; a set this codec would refuse to write is not one it can read`,
                                  )
                                : every(members as readonly unknown[], (raw) =>
                                      inner.decode(
                                          carrying(member, raw as never),
                                      ),
                                  ),
                        ),
                        (read) => new Set(read),
                    ),
            }
        }
        /**
         * §4's object: {@link bodySem} carried into an `M`. The row is the wrapper and the body is
         * the content, which is the split §5 states — a codec writes the attributes of that codec,
         * and `.item` is the one place that writes no map.
         */
        case 'attributes': {
            const body = bodySem(def.of, def.rest)
            return carriedCodec(
                (value): value is Record<string, unknown> =>
                    asRecord(value) !== undefined,
                'M',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not a plain object, and an object writes an 'M' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                body.encode,
                (carried: Readonly<Record<string, AttributeValue>>) =>
                    body.decode(carried),
            )
        }
        /** §3 `(held)`. `lawful_through` is the lemma; the adapter is data the term carries. */
        case 'held':
            return heldThrough(def.inner, def.adapt)
        /**
         * §3 `(literal)`, and it is **not** a sixth ground term: `literalCodec k ls` is
         * `(baseCodec k).restrict (inL k ls)`, the base's pair narrowed to membership of `ℓ`. The
         * base is the index, so the row reaches it by denoting `{ kind: base }` — the five bases
         * are exactly five term kinds.
         *
         * **What the base's own read gate buys, stated where it is now free.** The hand-written
         * row re-checked `isNumeral` before consulting `ℓ`, because `Number` is far more permissive
         * than an `N` — it reads `''`, whitespace, `0x10` and `0b11`, none of which DynamoDB hands
         * back, and membership in `ℓ` does not filter them out: `number(0, 1, 2)` read `{ N: '' }`
         * as `0`. Going through the base means that gate is the base's, asked once, and the row no
         * longer restates it.
         *
         * **At `number` the predicate is on the read value and not on the stored text**, which is
         * the model's `inL` at that base and the one place §5's two literal rules part: a string
         * literal's stored text *is* its value, a numeric literal's is not.
         */
        case 'literal': {
            const allowed = def.allowed
            /**
             * `inL`, answering with the **member of `ℓ`** rather than with `true`.
             *
             * The model's is a `Bool` and it does not need to be more: Lean has no reference
             * identity, so two `ByteArray`s with the same octets *are* one value and `p` returning
             * "the value" is unambiguous. JS has two objects for that one value, and returning the
             * declared one is how this language spells the model's answer — a `decode` that handed
             * back the array off the wire would answer with a value the type says is one of `ℓ`
             * and `===` says is not.
             */
            const member = (value: unknown): LiteralValue | undefined =>
                allowed.find((one) => sameLiteral(one, value as LiteralValue))
            const refuse = (value: unknown) =>
                new CodecError(
                    `${namedLiteral(value as LiteralValue)} is not one of ${allowed
                        .map(namedLiteral)
                        .join(', ')}`,
                )
            const base = denote({ kind: def.base })
            return {
                encode: (value: unknown) =>
                    member(value) === undefined
                        ? refuse(value)
                        : base.encode(value as never),
                decode: (attribute) =>
                    andThen(base.decode(attribute), (read) => {
                        const found = member(read)
                        return found === undefined ? refuse(read) : found
                    }),
            }
        }
        /**
         * §3 `(decimal)`. The held set is §1's `Numerals` and not every string: the grammar, the
         * 38 significant digits and the magnitude range are checked on **both** halves.
         * `lawful_decimalCodec` is its own lemma, and the model gives the read side's check the
         * same reason this one has — an ill-formed numeral admitted by `p` would name a value `e`
         * then refuses, and that is **(C)** failing.
         *
         * This is the term whose *value* is text and whose *member* is `N`, which is why §5 has it
         * writing `.str` while storing `N`, and why the write occupancy of `set(decimal)` is a set
         * of strings. The row carries the value across unchanged; only the member differs.
         *
         * `isStoredNumeral` stringifies what it is given — `isStoredNumeral(['1'])` is `true` — so
         * the kind is checked first, which is what `admits`' `decimal` row says and what this row
         * did not say before it moved here.
         */
        case 'decimal':
            return {
                encode: (value: unknown) =>
                    typeof value === 'string' && isStoredNumeral(value)
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
            }
        /**
         * §3 `(number)`. The held set is `D` — §1's numeral domain — and not every double, so
         * both halves gate. `lawful_numberCodec` is its own lemma rather than the ground one's,
         * and the model's row is written out for the same reason this one is.
         *
         * **The second gate is not redundant**, and the model records the same fact from the same
         * direction: `p` gates on the **round-tripped** value rather than on the stored digits,
         * because `ofDec` rounds and a numeral at the top of the range can round *up* past it.
         * Gating on the digits would admit a value `e` then refuses, which is **(C)** failing.
         * `Number('9.9999999999999999999999999999999999999E+125')` is that numeral here.
         */
        case 'number':
            return {
                // `value.toString()` is defined on everything, so the numeral gate alone accepted
                // the *string* `'5'` as readily as the number `5`. `admits`' `number` row asks the
                // kind first; so does this
                // annotated `unknown` rather than left to infer `never` from {@link Pair}: the
                // erased pair says a caller may pass anything, and this row narrows what it is
                encode: (value: unknown) =>
                    typeof value === 'number' && isNumeral(value.toString())
                        ? carrying('N', value.toString())
                        : new CodecError(
                              `${value} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN or Infinity`,
                          ),
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
            }
        /**
         * **The `NULL` point, and it is not a {@link groundCodec} here.** The reason is this
         * library's and not the model's: `lawful_nullCodec` *is* `lawful_pointCodec`, at the
         * prisms `nullV` and `nullA`, whose payload is `Unit` — "a prism with a trivial payload,
         * which is what makes `null` an instance of the same shape as the three that carry data".
         * So the model has one construction for all four.
         *
         * `groundCodec` is not that construction. It is a shape test and a `carrying`, which
         * carries the *value* into the member — and `NULL`'s payload is the constant `true`, which
         * no value supplies. Being generic over it would mean taking the prism pair as arguments
         * rather than a shape and a member, which is a larger construction than four rows.
         *
         * `encode` checks, though the type already says so: the admissible set is one value and
         * this library owns it, so an unchecked `encode` would write `NULL` for anything that
         * reached it — a pair whose `e` is defined outside its own held set. A literal checks for
         * the same reason.
         */
        case 'null':
            return {
                encode: (value) =>
                    value === null
                        ? carrying('NULL', true)
                        : new CodecError(
                              `${JSON.stringify(value)} is not null, and this codec holds nothing else`,
                          ),
                decode: (attribute) =>
                    andThen(expect('NULL', attribute), () => null),
            }
        default:
            throw new CodecError(
                `\`${def.kind}\` is not ported to \`denote\` yet — this is reachable only from a constructor that has not been switched, and no such constructor calls it`,
            )
    }
}

/**
 * A term, as the codec it denotes — the one place the erased pair gets its type back.
 *
 * `denote` answers about the term, and a term does not carry the type its codec has, so exactly one
 * cast stands between the two. It is here rather than at each constructor because twenty-one casts
 * with one reason between them is one reason nobody reads. `build.ts`'s `codec` is still the single
 * construction site: this hands it a pair instead of two hand-written halves.
 */
const codecOfTerm = <T, A extends AttributeValue>(
    def: TermDef,
): AttributeCodec<T, A> =>
    codec<T, A>({
        def,
        ...(denote(def) as Pick<Codec<T, A>, 'encode' | 'decode'>),
    })

const stringCodec: AttributeCodec<string, Attribute<'S'>> = codecOfTerm({
    kind: 'string',
})

/** @see {@link StringCodec} */
export const string: StringCodec = Object.assign(
    literalCapability('string'),
    stringCodec,
    { set: setCapability('string', () => string) },
) as unknown as StringCodec

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
 *
 * **`decimal('1')` is the literal the old surface could not spell.** The removed `literal(...)`
 * guessed `S` from the JS type for `literal('1')` and went through the host's `number` for
 * `literal(1)`; neither says "stored as `N`, exactly this text".
 *
 * It is modelled. This docstring said for a while that it was "the one thing on this surface with
 * no counterpart in the calculus", because `GroundKind` was `string | number | boolean | binary |
 * null`. `decimal` is a `GroundKind` now, carrying `StoredNumeral` — the same gate this codec runs
 * — and `GroundKind.toValue` sends it to a `.str`, which is why the *value* side needed no change.
 * `src/lean.ts` emits `Term.literal GroundKind.decimal`, and both `decimal('1')` and
 * `decimal.set()` are covered by kernel-checked vectors.
 */
export type DecimalCodec = AttributeCodec<string, Attribute<'N'>> & {
    <const T extends string>(only: T): ConstantCodec<T, Attribute<'N'>>
    <const T extends string>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'N'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<string>, NS>
        <const T extends string>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, NS>
    }
}

const decimalCodec: AttributeCodec<string, Attribute<'N'>> = codecOfTerm({
    kind: 'decimal',
})

/** @see {@link DecimalCodec} */
export const decimal: DecimalCodec = Object.assign(
    literalCapability('decimal'),
    decimalCodec,
    { set: setCapability('decimal', () => decimal) },
) as unknown as DecimalCodec

/**
 * A JS number, stored as `N`. Lossy by construction — `N` carries 38 digits, `number` about 15.
 * Right for enums, counts and flags; wrong for money, which is {@link decimal}.
 *
 * `number.set()` and `decimal.set()` are **both first-class**, and neither is the other's legacy
 * spelling: `number.set()` is what a caller who means their platform's numbers means, and
 * `decimal.set()` is the host-independent one. They write the same member, `NS`, and hold different
 * things — which is why `formal/Calculus/Domain.lean:602` indexes a set by a base rather than by
 * `Member`.
 */
export type NumberCodec = AttributeCodec<number, Attribute<'N'>> & {
    <const T extends number>(only: T): ConstantCodec<T, Attribute<'N'>>
    <const T extends number>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'N'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<number>, NS>
        <const T extends number>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, NS>
    }
}

const numberCodec: AttributeCodec<number, Attribute<'N'>> = codecOfTerm({
    kind: 'number',
})

/** @see {@link NumberCodec} */
export const number: NumberCodec = Object.assign(
    literalCapability('number'),
    numberCodec,
    { set: setCapability('number', () => number) },
) as unknown as NumberCodec

/**
 * A boolean, as `BOOL`.
 *
 * `boolean(true)` is a literal at `BOOL`, which nothing on the old surface could spell —
 * `literal(...)` took a string or a number and there was no third option. There is deliberately no
 * `boolean.set()`: DynamoDB has `SS`, `NS` and `BS`, and no set of booleans.
 */
export type BooleanCodec = AttributeCodec<boolean, Attribute<'BOOL'>> & {
    <const T extends boolean>(only: T): ConstantCodec<T, Attribute<'BOOL'>>
    <const T extends boolean>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'BOOL'>>
}

const booleanCodec: AttributeCodec<boolean, Attribute<'BOOL'>> = codecOfTerm({
    kind: 'boolean',
})

/** @see {@link BooleanCodec} */
export const boolean: BooleanCodec = Object.assign(
    literalCapability('boolean'),
    booleanCodec,
) as unknown as BooleanCodec

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
 *
 * Not callable, and there is nothing for it to be: the model's `GroundKind.null` has carrier `Unit`,
 * so `literal .null` can say nothing this codec does not already say.
 */
export const nullValue: AttributeCodec<null, Attribute<'NULL'>> = codecOfTerm({
    kind: 'null',
})

/**
 * Binary, as `B`.
 *
 * `binary(bytes)` compares **by bytes**, not by reference — two `Uint8Array`s holding the same
 * octets are the same alternative, and a decoded value comes back as the member of `ℓ` rather than
 * as the array that was read off the wire.
 */
export type BinaryCodec = AttributeCodec<Uint8Array, Attribute<'B'>> & {
    (only: Uint8Array): ConstantCodec<Uint8Array, Attribute<'B'>>
    (
        ...allowed: readonly Uint8Array[]
    ): AttributeCodec<Uint8Array, Attribute<'B'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<Uint8Array>, BS>
        (
            ...allowed: readonly Uint8Array[]
        ): AttributeCodec<ReadonlySet<Uint8Array>, BS>
    }
}

const binaryCodec: AttributeCodec<Uint8Array, Attribute<'B'>> = codecOfTerm({
    kind: 'binary',
})

/** @see {@link BinaryCodec} */
export const binary: BinaryCodec = Object.assign(
    literalCapability('binary'),
    binaryCodec,
    { set: setCapability('binary', () => binary) },
) as unknown as BinaryCodec

// ── collections ─────────────────────────────────────────────────────

/**
 * A non-empty set, stored as the native set its members belong to.
 *
 * **The one set builder, and it is internal.** Every set in the surface comes through here:
 * `string.set()` and the other three bases via {@link setCapability}, and everything that reduces
 * to a base via {@link setCapable} — `amount.set()` where `amount = refine(decimal, isAmount)`.
 * It was exported as `set(element)` and is not any more: the capability propagates, so a
 * free-standing form said nothing `.set()` cannot, and having two spellings of one combinator on
 * the surface meant two things to keep in step. It stays a function rather than being inlined
 * because it is where both halves of §3 `(set)`'s premise are checked, and they are checked once.
 *
 * Which set follows from the element's member: `SS`, `NS` or `BS`. Taking a codec rather than being
 * fixed to strings is what makes `price.set()` decode back as prices.
 *
 * **Order is not preserved.** A DynamoDB set comes back in an order the service chooses, so both
 * directions sort. `decode ∘ encode = id` therefore holds only for canonical values; for the rest
 * the law is {@link checkStable}. If order carries meaning use `array(...)`.
 *
 * **Empty is not representable** — encode throws rather than writing what the service refuses.
 */
const set = <const C extends AnyCodec>(
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
    /**
     * …and the element reduces to one of the four bases a stored set is built from.
     *
     * The member check above is §3 `(set)`'s premise as it *was* — `setMember μ = some μS` — and it
     * is not enough, because `writes` reads through wrappers that a set has no way to record.
     * a set of `held(string, f, g)` passed it: `held` writes where its inner term does, so the member
     * was `'S'`, and the adapter's two functions then ran per member of an attribute that stores no
     * such thing. The model closed this by indexing `Term.set` with a `SetBase`
     * (`formal/Calculus/Term.lean:60`) and says outright what that gives up — a set of a `held` and
     * of a `legacy`, neither of which has a set-level spelling and neither of which appears in
     * `src/`. This is the same refusal, at the same place the other one lives.
     *
     * `refine` and a literal are **not** given up: a restriction of the elements is a restriction of
     * the set, and `setCodec_restrict` (`formal/Calculus/Combinators.lean`) proves the two write the
     * same attribute. So {@link setBase} reads through those two and nothing else.
     */
    if (!setBase(inner)) {
        throw new CodecError(
            `a set's element must be one of the four bases a stored set is built from — \`string\`, \`number\`, \`decimal\` or \`binary\`, narrowed by \`refine\` or by a literal — and this element is a \`${inner.def?.kind ?? 'codec with no definition'}\`, which writes '${member}' by reading through to something else. A set of it has nothing DynamoDB stores`,
        )
    }
    // the member is decided above, from the element; the cast carries that decision into the type
    return codecOfTerm<ReadonlySet<T>, SetOf<C>>({
        kind: 'set',
        element: inner,
    })
}

export const array = <const C extends AnyCodec>(
    element: C & NotAboutAbsence<C>,
): AttributeCodec<readonly Decoded<C>[], L<AttributeOf<C>>> => {
    type T = Decoded<C>
    return codecOfTerm<readonly T[], L<AttributeOf<C>>>({
        kind: 'array',
        element: element as unknown as AttributeCodec<T>,
    })
}

/**
 * A fixed-length, heterogeneous list, as `L`.
 *
 * `list` gives `readonly T[]`, which cannot say that a route is one step or exactly two. Decode
 * checks the length, because a tuple whose arity is wrong is not the type it claims to be.
 */
export const tuple = <const Cs extends readonly (AnyCodec | AnyRest)[]>(
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
    const all = elements as readonly unknown[]

    /**
     * `RestGoesLast` refuses a misplaced `rest` in the *type*, and a cast defeats the type.
     *
     * Past one, nothing looked: the split below reads only the last element, so a `rest` anywhere
     * else was read as a fixed element and written as one — `tuple(rest(string) as any, number)`
     * encoded `['a', 1]` as a two-element tuple and reported nothing. This is §8 case (b): the
     * condition is decidable from the declaration, so it is refused where the declaration is,
     * beside `set`'s two refusals for the same reason.
     */
    const misplaced = all.findIndex(
        (element, at) => at < all.length - 1 && isTail(element),
    )
    if (misplaced !== -1) {
        throw new CodecError(
            `\`rest\` is at position ${misplaced} of ${all.length} elements and a tuple's rest must be last — everything after it would have no fixed position. The type says so too; this call reached here past a cast`,
        )
    }

    /**
     * The tail is split off once, here, rather than asked for per row.
     *
     * `RestGoesLast` has already refused it anywhere but the end, so the last element is the only one
     * that can be marked and looking at it is enough.
     */
    const last = all[all.length - 1]
    const tail = isTail(last) ? last.rest : undefined
    const items = (tail ? all.slice(0, -1) : all) as readonly AnyCodec[]

    // as with `record` and `map`, the cast keeps the shape each position writes, which
    // `Attribute<'L'>` would flatten to "some list"
    return codecOfTerm({
        kind: 'tuple',
        elements: items,
        tail,
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
    ? Last extends { readonly [restMarker]: true; readonly rest: infer R }
        ? readonly [...{ [I in keyof Head]: Decoded<Head[I]> }, ...Decoded<R>[]]
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
    ? Last extends { readonly [restMarker]: true; readonly rest: infer R }
        ? readonly [
              ...{ [I in keyof Head]: AttributeOf<Head[I]> },
              ...(AttributeOf<R> & AttributeValue)[],
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
    ({ rest: element as unknown as AnyCodec }) as unknown as RestCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue
    >

/**
 * Whether this is a tail marker rather than an element — the runtime half of `restMarker`.
 *
 * `restMarker` is a `declare const` symbol, so it exists in the type and nowhere else, and
 * {@link tuple} needs an answer at run time. One own property, checked by name.
 */
const isTail = (element: unknown): element is { readonly rest: AnyCodec } =>
    typeof element === 'object' &&
    element !== null &&
    'rest' in element &&
    // and it is not a codec, which is decidable now that every codec carries a definition. An
    // `ItemCodec` has a `rest` of its own — its open-part policy — so the first test alone would
    // take one for a tail
    !('def' in element)

/**
 * A tuple's tail: the element codec, marked for a position.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A> & { …marker }`, which
 * claimed a rest has an `encode` and a `decode` — true only because `rest(c)` was built by spreading
 * `c`, so a bare rest encoded as its element by accident. A rest is a *position*, `Rest` in §4's
 * third stratum, and the only two things that have one are a tuple's tail and an object's open part.
 * Both unwrap it at construction. Nothing else may be given one, and the type no longer offers a
 * caller the two halves to call.
 */
export type RestCodec<T, A extends AttributeValue = AttributeValue> = {
    readonly [restMarker]: true
    readonly rest: AttributeCodec<T, A>
}

/** A homogeneous string-keyed record, as `M`. */
export const record = <const C extends AnyCodec>(
    element: C & NotAboutAbsence<C>,
): AttributeCodec<
    Readonly<Record<string, Decoded<C>>>,
    M<{ readonly [key: string]: AttributeOf<C> }>
> => {
    // the cast keeps the *shape* the values write, which `Attribute<'M'>` would flatten to
    // "some map" — the same reason `map` casts
    return codecOfTerm({
        kind: 'record',
        value: element as unknown as AttributeCodec<Decoded<C>>,
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
export type Refined<T, A extends AttributeValue> = AttributeCodec<T, A> &
    SetCapable<T, A>

/**
 * `.set()`, where the codec it sits on can be a set's element.
 *
 * The capability {@link setBase} decides at runtime, stated at the type as far as the type can see
 * it — which is not all the way. A codec's *type* is not generic in its definition — every codec
 * carries a `CodecDef`, and none of them carries *which* one at the type — so `refine(...)`'s type
 * knows the attribute and never the base it reduced through. So the gate here is the attribute — `S`, `N` or `B`, the three a stored set is built
 * from — and `refine(held(string, f, g), p).set()` type-checks and throws, because `held` writes
 * `S` and reduces to no base. That gap closes only by making the codec type generic in its
 * definition, which was measured at 481 of 968 signatures and rejected; the runtime refusal in
 * {@link set} is what stands in for it, and is tested at each of the six kinds that reach it.
 *
 * **One member at a time, and each test non-distributive.** Two shorter spellings were tried and
 * both admit `refine(union([string, number]), p).set()`, which is a set of an element writing two
 * members and cannot exist:
 *
 * - `[A] extends [Attribute<'S'> | Attribute<'N'> | Attribute<'B'>]` — a union of admissible
 *   attributes is assignable to a union of them, so it passes.
 * - the same without the tuples, distributing — each arm passes on its own, and the result is
 *   `{ set: () => SS } | { set: () => NS }`, a union whose members all have a `set`, so calling it
 *   is allowed.
 *
 * Asking each member separately, with `[A] extends [...]` so the question is about `A` whole, is
 * what refuses the union: it is not `Attribute<'S'>`, not `Attribute<'N'>` and not
 * `Attribute<'B'>`, so it falls through.
 *
 * `Record<never, never>` rather than `{}` in the last branch: an intersection with it is the codec
 * unchanged, and `{}` means "anything but null", which would make the intersection accept a `.set`
 * this type is declining to give.
 */
export type SetCapable<T, A extends AttributeValue> = [A] extends [
    Attribute<'S'>,
]
    ? { readonly set: () => AttributeCodec<ReadonlySet<T>, SS> }
    : [A] extends [Attribute<'N'>]
      ? { readonly set: () => AttributeCodec<ReadonlySet<T>, NS> }
      : [A] extends [Attribute<'B'>]
        ? { readonly set: () => AttributeCodec<ReadonlySet<T>, BS> }
        : Record<never, never>

/**
 * The `.set()` capability, attached to a codec that is not one of the four bases.
 *
 * The thunk closes over the codec **it returns**, not the one it was handed, and that is the whole
 * of the care needed here: `.set()` records its element in `def`, so a thunk closing over the
 * argument would make `amount.set().def` and `amount.set().def` two definitions that differ by a
 * `set` property nobody can see. Same reason {@link setCapability} reaches its base through a thunk
 * rather than naming the constant it is defining.
 */
const setCapable = <T, A extends AttributeValue>(
    self: AttributeCodec<T, A>,
): Refined<T, A> => {
    const capable = {
        ...self,
        set: () => set(capable as unknown as AnyCodec),
    }
    return capable as unknown as Refined<T, A>
}

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
): Refined<Narrow, A> => {
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
    // `writes` reads through a refinement, which is what lets a set of a brand work; `decides`
    // does not, because the predicate may be exactly what rejects the constant.
    //
    // `setCapable` is what carries `.set()` across the refinement, and it is the whole of why the
    // brand survives: `amount.set()` decodes as `ReadonlySet<Price>` because the set is built from
    // `amount`, where the predicate that produces a `Price` already lives.
    return setCapable(
        derive<Narrow, A>(inner, {
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
            /**
             * **The predicate runs on the way in too**, which is what closed the last row of
             * `admits ⟺ encode`.
             *
             * It used to run on `decode` only, on the argument that a row is data somebody else
             * wrote while an argument is typed — and the type is `Narrow`, so a value failing `is`
             * arrived past it. That is true of every gate added here and was not a reason to skip
             * this one: a brand whose predicate is not checked is a brand that can be forged by a
             * cast, and `admits(refine(c, is), v)` said so all along by running `is` itself.
             */
            encode: (value) =>
                is(value as Wide)
                    ? inner.encode(value)
                    : new CodecError(`${JSON.stringify(value)} is not ${what}`),
            decode: (attribute) =>
                andThen(inner.decode(attribute), (decoded) =>
                    is(decoded)
                        ? decoded
                        : new CodecError(
                              `${JSON.stringify(decoded)} is not ${what}`,
                          ),
                ),
        }),
    )
}

// ── reading what is already there ───────────────────────────────────

/** Type-level only, for the same reason as {@link optionalMarker}: the def carries the fact. */

/** A codec that stands in a value where the attribute is absent. */
export type FallbackCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = AttributeCodec<T, A> & { readonly [fallbackMarker]: T }

/**
 * Reads a missing attribute as a value, and writes the attribute always.
 *
 * Not {@link optional}: the entity always has it, the *data* may not — a row written before the
 * attribute existed. Replaces `item.channel ?? 'IN_STORE'` at every read site.
 *
 * **The stand-in must be writable by the codec it stands in for**, and that is checked here, at the
 * declaration. §3 `(fallback)` carries it as a premise (`formal/Calculus/Soundness.lean:89`) and it
 * exists because the proof failed without it: a row missing the attribute reads back as the
 * stand-in, and if the inner codec cannot write that value the item cannot be written back —
 * **(C)** broken at the read, with the refusal surfacing on some later write rather than at the
 * declaration responsible for it. `fallback(string('A'), 'B')` is the whole of it.
 *
 * The stand-in is a **value and not a thunk**, which is what makes the check possible here rather
 * than on whichever read happens to need it first. It does not become shared state for that: the
 * declaration holds one value and each read that needs one gets a `structuredClone` of it, so a
 * mutable stand-in still cannot leak between entities. Primitives are handed over as they are,
 * being unable to leak anything.
 */
export const fallback = <const C extends AnyCodec>(
    // the *argument's own* type, not a re-declared `AttributeCodec<T, A>`: the guard has to see the
    // marker the caller passed, and a parameter written in terms of inferred `T` and `A` reconstructs
    // a plain codec that never carries one
    inner: C & NotAlreadyMarked<C>,
    // `NoInfer` so the codec is the only thing that says what it holds. Inferring from both sites
    // unified them, and a stand-in written `'A'` widens to `string`, which then refused the very
    // codec it stands in for — invisible while the entity was declared first and pinned it itself
    value: NoInfer<Decoded<C>>,
): FallbackCodec<Decoded<C>, AttributeOf<C> & AttributeValue> => {
    // §3 `(fallback)`: the stand-in must be *writable*, or a row missing the name decodes to a
    // value the item cannot be written back as — (C) broken at the read, with the refusal arriving
    // on the next write instead of at the declaration that caused it. Decidable here, from the
    // declaration alone, which is why the stand-in is a value and not a thunk.
    if (!admits(inner as unknown as AnyCodec, value)) {
        throw new CodecError(
            `\`fallback\`'s stand-in must be a value the codec it stands in for can write, and ${describeShape(value)} is not one this \`${(inner as unknown as AnyCodec).def?.kind ?? 'codec'}\` writes. A row missing the attribute would read back as it and then refuse on the way out`,
        )
    }
    return described(inner as unknown as AttributeCodec<Decoded<C>>, {
        kind: 'fallback',
        inner: inner as unknown as AnyCodec,
        value,
    }) as unknown as FallbackCodec<Decoded<C>, AttributeOf<C> & AttributeValue>
}

/**
 * Whether this stand-in has to be *copied* on each read that uses it, decided once.
 *
 * The declaration holds **one** value — that is what makes §3 `(fallback)`'s premise checkable
 * where the declaration is — so handing that object out is handing every row the same object, and
 * one caller's `.push` becomes every other caller's default. `structuredClone` is the platform's,
 * so a copy costs no dependency.
 *
 * Two reasons not to copy, and both are settled here rather than per read.
 *
 * A **primitive** cannot be mutated, so sharing one is safe and copying it is waste — and most
 * stand-ins are primitives.
 *
 * And a value `structuredClone` **refuses**. Ordinarily there is none: a stand-in is a value the
 * inner codec `admits`, so it comes from the value language — arrays, plain objects, `Set`,
 * `Uint8Array` — and all of those clone. {@link custom} is the exception, because its `admits` row
 * asks the caller's own pair, so a hand-written codec can legitimately admit a class instance with
 * methods or anything else holding a function. Rather than throw a `DataCloneError` out of a
 * `decode` months later, the clone is attempted once at the declaration; where it fails the value
 * is shared, which is the old behaviour confined to the one case that forces it.
 */
const copiedPerRead = (value: unknown): boolean => {
    if (typeof value !== 'object' || value === null) return false
    try {
        structuredClone(value)
        return true
    } catch {
        return false
    }
}

/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart: an attribute is **stored** as `S`, `N`, `SS` — and it is
 * **held**, in your code, as a `string`, a `Date`, an array. Every other combinator changes the first
 * or narrows the second. This one changes only the second, by naming the two halves of the
 * conversion, and leaves what the table holds exactly as it was.
 *
 * Which makes it the answer to "my values arrive as an array and `.set()` wants a `Set`": nothing
 * about the *table* has to change for that, so nothing about the codec does either. It is also the
 * one to reach for before {@link custom} — the member, the generation and the definition all keep
 * coming from the codec underneath, where a hand-written codec has to restate them.
 *
 * @example
 * ```ts
 * // stored as SS, held as an array
 * const tags = held(string.set(), {
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
 *
 * **Nothing here checks it, and nothing here can.** The model carries it as `IsoCancels`
 * (`formal/Calculus/Codec.lean:157`) — a premise, in both directions: `g(f v) = v` wherever `f v`
 * lands writable, and `f(g v) = v` on the writable values themselves. It is a premise there for
 * the same reason it is unchecked here. One direction quantifies over the *held* type, which has
 * no generator except `decode` itself, so every value this library could make is already in the
 * pair's image; and probing the other at construction is worse than not probing it, because a
 * legitimate adapter is an isomorphism on the values its inner codec describes and *throws* off
 * them — `held(string, dateAdapter)` would be refused for `new Date('<anything>')`, which is
 * exactly the narrowing the example above asks for rather than a defect.
 *
 * So this is a written obligation, and `checkIso` is how a caller discharges it: it generates for
 * the inner codec and checks `encode(decode(y))`, which is the half a table depends on. The
 * failure mode it catches, unrefused today and pinned in `codec.laws.spec.ts`, is an adapter that
 * *normalises* — `{ encode: v => v.toUpperCase(), decode: v => v }` reads `'a'` back as `'A'`,
 * and every read-modify-write on that row rewrites the value.
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
    return codecOfTerm<T, AttributeOf<C>>({
        kind: 'held',
        inner: inner as unknown as AnyCodec,
        adapt: adapt as CodecDefHeldAdapt,
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
 *
 * **Two things §3 asks of the older reader** (`ReadsCoherently`,
 * `formal/Calculus/Codec.lean:163`), and only one of them is checkable.
 *
 * `ran(r) ⊆ dom(e)` — a migration lands on values the current encoding can *write*. This is
 * checked, per read, as soon as the older reader has answered, because that is the earliest
 * anything can know what it returns. Unchecked it read a row and refused on the way out, which is
 * **(C)** broken at the migrated row and reported at some later write.
 *
 * Coherence — where both readers read an attribute, they agree — is **not** checkable, and the
 * reason is sharper than that. The current encoding is tried first and the older one only on its
 * failure, here and in the model (`Codec.extendRead`), so on `dom(p_current)` the older reader is
 * never consulted and a disagreement has no observable consequence at all. What the premise buys
 * is that the *ordering does not matter*: with it, this presentation equals the order-free
 * `p ∪ r`. Without it the reading depends on declaration order, which is the one thing §5 says
 * resolution never does. So it is a written obligation, and the thing to check is that two
 * readers of one attribute agree — nothing in this library will tell you they do not.
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
            if (!failed(older_)) {
                // §3 `(legacy)`'s first premise, `ran(r) ⊆ dom(e)`: a migration must land on
                // values the *current* encoding can write. Decidable here and nowhere earlier —
                // `older` is a function, so what it returns is known only once it has answered.
                // Without this the row decodes and the write-back refuses, which is (C) broken at
                // the migrated row and reported at the next write instead of at this read.
                if (!admits(current as unknown as AnyCodec, older_)) {
                    return new CodecError(
                        `an older encoding read this attribute as ${describeShape(older_)}, which the current encoding cannot write. A migration has to land on values that can be written back, or the row reads and then refuses on the way out`,
                    )
                }
                return older_ as T
            }
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

/**
 * Does `inner` already reach the null point, at *either* end?
 *
 * `null ∈ dom(e)` or `⟨NULL, ∗⟩ ∈ dom(p)`, which is the specification's `owns(c)`. The
 * disjunction is not a convenience: asked per side, a codec could decline to write `null` while
 * still reading `⟨NULL, ∗⟩`, the point's two ends would belong to different codecs, and a round
 * trip would go out through one and back through the other with nothing looking ambiguous on
 * either side taken alone.
 *
 * Two probes at two points. A throw is a refusal like any other — {@link held}'s adapter is
 * arbitrary user code and may throw rather than return a `CodecError`, which is the same reason
 * {@link admits} wraps its `held` row.
 */
const ownsNull = (inner: AnyCodec): boolean =>
    reaches(() => inner.encode(null as never)) ||
    reaches(() => inner.decode(carrying('NULL', true)))

const reaches = (probe: () => unknown): boolean => {
    try {
        return !failed(probe())
    } catch {
        return false
    }
}

/**
 * A value that may be null, stored as `NULL` when it is — **unless `inner` already owns the null
 * point**, in which case this is `inner`'s own pair, untouched.
 *
 * Without the guard the wrapper's `NULL` branch shadows the inner codec, and **(R)** fails on a
 * term the specification proves lawful: `nullable(held(nullable(string), adapter))`, where the
 * adapter maps `'SENTINEL'` to `null`, writes `{ NULL: true }` for `'SENTINEL'` and reads back
 * `null`. The value written is not the value read. No declaration in this repository builds that
 * term and `held` is unemittable, so no generated vector could ever have found it.
 *
 * Where the guard does *not* fire, null-honesty is a theorem rather than an assumption: an
 * `inner` that wrote `⟨NULL, ∗⟩` would read it straight back by **(R)** and so would own the
 * point, and one that read some attribute to `null` would write the point by **(C)** and own it
 * again. Both hypotheses are refuted by the guard rather than required of the caller.
 *
 * **The question is asked once, at first use rather than at construction.** `owns` is a property
 * of the pair and the probes are two calls, so asking repeatedly would be a walk with a known
 * answer. It is not asked *at* construction because {@link lazy} exists: a recursive declaration
 * forces its thunk when probed, and at module-evaluation time that is a reference to a binding
 * that does not exist yet. Deferring costs one boolean test per call and is the difference
 * between answering the question and catching an error from having asked it too early.
 */
export const nullable = <T, A extends AttributeValue>(
    inner: AttributeCodec<T, A>,
): AttributeCodec<T | null, A | Attribute<'NULL'>> => {
    let owns: boolean | undefined
    const ownsInner = () => (owns ??= ownsNull(inner as AnyCodec))
    return derive<T | null, A | Attribute<'NULL'>>(inner, {
        def: { kind: 'nullable', inner: inner as AnyCodec },
        encode: (value) =>
            value === null && !ownsInner()
                ? (carrying('NULL', true) as A | Attribute<'NULL'>)
                : (inner.encode(value as T) as Result<A | Attribute<'NULL'>>),
        decode: (attribute) =>
            memberOf(attribute) === 'NULL' && !ownsInner()
                ? null
                : inner.decode(attribute),
    })
}

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
    /** How many `L`/`M` this value already sits inside. See {@link MAX_DOCUMENT_NESTING}. */
    enclosing = 0,
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
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            every(value, (x) => encodeUnknown(x, numbers, enclosing + 1)),
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
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            everyEntry(value as Record<string, unknown>, (v, k) =>
                v === undefined
                    ? new CodecError(
                          `'${k}' is undefined, and DynamoDB has no attribute holding undefined. Omit the key, or use \`optional(...)\` on a declared attribute.`,
                      )
                    : encodeUnknown(v, numbers, enclosing + 1),
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
                "`NS` has no counterpart this codec can write — a set of numbers is refused on the way in, because nothing without a schema says which of its members a JS number holds faithfully. Reading it would mean re-encoding it as `SS` and changing the attribute's stored type. Declare the attribute with `number.set()` or `decimal.set()`.",
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
    readonly def: CodecDef
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
    readonly def: CodecDef
    readonly item: Tagged<T, D, Spec>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
}

export type UnionCodec<T, Options extends readonly unknown[]> = {
    readonly encode: (value: T) => Result<WrittenBy<Options>>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (value: T) => WrittenBy<Options>
    readonly unsafeDecode: (attribute: AttributeValue) => T
    readonly def: CodecDef
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
    readonly absent:
        | { readonly value: unknown; readonly copy: boolean }
        | undefined
}

/**
 * The marker taken off, once, at the declaration.
 *
 * A marker is `described(inner, …)` — the inner codec with a different definition — so the two
 * halves are the inner's and unwrapping changes nothing about what the field encodes or decodes.
 * What it changes is that the mark is *named* rather than left to be recovered from a definition
 * kind, which is what {@link Field} is for.
 */
const fieldOf = (codec: AnyCodec): Field => {
    const def = codec.def
    if (def.kind === 'optional') return { mark: 'optional', codec: def.inner }
    if (def.kind === 'fallback')
        return { mark: 'fallback', codec: def.inner, value: def.value }
    return { mark: 'required', codec }
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
 *     tags: string.set(),           // SS, not L
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
    // the marker off each declared attribute, once — the term. What the two directions walk is
    // the *compiled* form of it, which `bodySem` builds and which carries one thing the term does
    // not: whether a stand-in has to be copied per read, a fact about this runtime and not about
    // the declaration.
    const fields: Record<string, Field> = {}
    const declaredSpec = spec as unknown as Record<string, Nestable<never>>
    for (const name in declaredSpec) {
        fields[name] = fieldOf(declaredSpec[name] as AnyCodec)
    }
    const body = bodySem(fields, rest as RestDeclaration)
    const itemDef = {
        kind: 'attributes',
        of: fields,
        rest: rest as RestDeclaration,
    } as const

    type T = DerivedItem<Spec, Rest>
    const self: ItemCodec<T, Spec, Rest> = {
        encode: (item) =>
            body.encode(item as Record<string, unknown>) as Result<
                EncodedBy<Spec, Rest>
            >,

        encodePartial: (patch) => {
            const held = patch as Record<string, unknown>
            const out: Record<string, AttributeValue> = {}
            for (const name in held) {
                const value = held[name]
                if (value === undefined) continue
                const field = fields[name]
                if (!field) {
                    return new CodecError(`'${name}' is not an attribute`)
                }
                const written = field.codec.encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
            }
            return out as never
        },

        decode: (item) =>
            body.decode(
                item as Readonly<Record<string, AttributeValue>>,
            ) as Result<T>,

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
        field: (name) => spec[name],
        spec: spec as Spec,
        rest: rest as RestPolicy<unknown>,
        def: itemDef,
    }

    // the `M` is what this codec writes; `.item` is the same two directions with the wrapper taken
    // off. Named member by member rather than spread so the cast keeps the *shape* the map carries —
    // `Attribute<'M'>` would flatten it to "some map" — and so that a call to `object` stays a plain
    // object literal, which is what lets a bundler drop an unused one
    const nested = codecOfTerm(itemDef) as unknown as AttributeCodec<
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
 *     CHECKUP: { type: string('CHECKUP'), petId: string, vetId: string },
 *     VACCINATION: { type: string('VACCINATION'), petId: string, vaccine: string },
 * })
 * ```
 */
const tagged = <T extends Record<string, unknown>>(
    discriminator: string,
    byVariant: Record<string, ItemCodec<Record<string, unknown>, unknown>>,
): DiscriminatedCodec<T, string, Record<string, unknown>> => {
    const pick = (tag: string): Result<ItemCodec<T, unknown>> => {
        // `Object.hasOwn` and not a truthiness test: `byVariant` is a plain object, so a tag of
        // `toString` or `constructor` reaches `Object.prototype` and comes back as a variant that
        // has no `decode`. The tag is read off the *stored* item, so that is reachable from data
        // this library does not control, and it surfaced as a raw `TypeError` — the one thing
        // every other failure here is careful not to be.
        const variant = Object.hasOwn(byVariant, tag)
            ? (byVariant[tag] as ItemCodec<T, unknown> | undefined)
            : undefined
        return (
            variant ??
            new CodecError(
                `'${tag}' is not a variant of '${discriminator}'; expected ${Object.keys(
                    byVariant,
                )
                    .map((x) => `'${x}'`)
                    .join(', ')}`,
            )
        )
    }

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
 * hold. `string('A')` and `string('B')` read back as `'A'` and `'B'`, which no value satisfies
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
 * nothing else did — encoding did not validate — which was why a union could not generally resolve
 * by trying.
 *
 * **Every row validates now and the resolver decides by {@link admits}, so this is no longer about
 * trying.** What it is still about is the *declaration*: whether two options can be told apart at
 * all, asked with no value in hand. That question is why `admits` cannot replace this function —
 * `admits` takes a value, and there is none at import time — and it is the shape of the answer
 * HANDOFF's fourth item expected and did not get.
 *
 * It **propagates through containers**, and it has to. `number.set(1)` refuses a set of strings,
 * because the element refuses each one — so `union([string.set('a'), number.set(1)])` is perfectly
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
 *
 * Named for what it is, which used to be `admits` — and it is emphatically **not** {@link admits},
 * §3's `Adm`. It is a test on *names* alone, the `keysOk` the model's `optionSemOf` uses for object
 * options, and it says nothing about whether the values at those names are admissible. Two things
 * called `admits` in one file was one name for two questions.
 */
const namesFit = (option: Option, names: ReadonlySet<string>) => {
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
 * `carrierId: string('ACME', 'GLOBEX')` is *one* variant covering two stored values, which is why
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
 * already says, so `{ SHOT: { type: string('CHECKUP') } }` is expressible and the two can disagree.
 * Reading the tag off the option makes that unrepresentable — and it is how `zod` does it.
 */
type ByTag<Specs extends readonly unknown[], D extends PropertyKey> = {
    [Spec in Specs[number] as TagsOf<Spec, D>]: Spec
}

/**
 * Which pairs of options answer to a tag in common, as `options i and j`.
 *
 * A discriminated union is a *lookup*, so two options claiming one tag is not an ambiguity to be
 * resolved when a value turns up — it is a table with one key written twice, and the second write
 * wins in silence. Decidable from the declaration, so it is refused there, the way
 * {@link Overlapping} refuses an untagged union's.
 */
type SharedTagsFrom<
    Head,
    Rest extends readonly unknown[],
    D extends PropertyKey,
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | ([TagsOf<Head, D> & TagsOf<Next, D>] extends [never]
                ? never
                : `options ${At} and ${Cursor['length']}`)
          | SharedTagsFrom<Head, Tail, D, At, [...Cursor, unknown]>
    : never

/**
 * Whether a tag set has more than one member.
 *
 * The intersection of a union of distinct literals is `never`, and of a single literal is itself —
 * so this is the one distinction a conditional cannot make directly, because `extends` on a naked
 * type parameter distributes and every branch then sees one member.
 */
type TagIntersection<Tags> = (
    Tags extends unknown
        ? (x: Tags) => void
        : never
) extends (x: infer One) => void
    ? One
    : never

/**
 * The options whose discriminator literal admits more than one value.
 *
 * Indexed by position like {@link SharedTags}, and one option at a time rather than a pair: this is
 * a defect in a single option, so naming its neighbour would say nothing.
 */
type MultiTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | ([TagsOf<Head, D>] extends [TagIntersection<TagsOf<Head, D>>]
                ? never
                : `option ${Cursor['length']}`)
          | MultiTagged<Rest, D, [...Cursor, unknown]>
    : never

type SharedTags<
    Specs extends readonly unknown[],
    D extends PropertyKey,
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | SharedTagsFrom<
                Head,
                Rest,
                D,
                Cursor['length'],
                [...Cursor, unknown]
            >
          | SharedTags<Rest, D, [...Cursor, unknown]>
    : never

/**
 * Nothing, or the fact that the options cannot be looked up.
 *
 * Three ways that happens, in the order that gives the more specific message. An option that does
 * not name the discriminator with a `literal` cannot be found at all, and would decode as whichever
 * option happened to match instead. An option whose literal admits *several* values is arity one's
 * refusal — one variant, one tag. Two options that name the *same* value can each be found, and
 * only one of them ever is.
 *
 * The arity check comes before the sharing check because it is a defect in one option rather than
 * in a pair, and because an option with two tags has to lose one before the sharing question is
 * even well posed.
 */
type EveryOptionTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
> = [TagsOf<Specs[number], D>] extends [never]
    ? ErrorMessage<'[discriminatedUnion] every option must name the discriminator with a literal at `string`, `number` or `decimal`, or a lookup cannot find it'>
    : [MultiTagged<Specs, D>] extends [never]
      ? [SharedTags<Specs, D>] extends [never]
          ? unknown
          : ErrorMessage<`[discriminatedUnion] ${SharedTags<Specs, D>} answer to the same discriminator value, and a lookup reaches only one of them — give them distinct values`>
      : ErrorMessage<`[discriminatedUnion] ${MultiTagged<Specs, D>} names the discriminator with a literal admitting several values, and a variant answers to exactly one tag — split it into one option per value`>

/**
 * A union of objects told apart by one attribute — `zod`'s `discriminatedUnion`, over an item.
 *
 * The stored value of the discriminator chooses the option, and each option says which value it is by
 * naming that attribute with a literal — `string('CHECKUP')`, `number(1)`, `decimal('1')`. A
 * lookup rather than a search: it cannot be ambiguous,
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
 *     object({ type: string('CHECKUP'), petId: string, vetId: string }),
 *     object({ type: string('SHOT'), petId: string, vaccine: string }),
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
        // one value, not the whole admissible set: a variant answers to exactly one tag, so the
        // `allowed` set below is read for its single member and refused if it has more
        const def = option.item.spec[discriminator]?.def
        /**
         * A tag is read back by {@link readTag}, which accepts `S` or `N` and nothing else — so the
         * bases that can carry one are exactly the three that write those two members. A literal at
         * `boolean` or `binary` is a perfectly good literal and cannot be a discriminator: `BOOL`
         * and `B` name no variant a lookup could find, and the value is not a key.
         */
        const tags =
            def?.kind === 'literal' &&
            def.base !== 'boolean' &&
            def.base !== 'binary'
                ? (def.allowed as readonly (string | number)[])
                : undefined
        if (!tags?.length) {
            throw new CodecError(
                `every option must name '${discriminator}' with a literal at \`string\`, \`number\` or \`decimal\`, and one of them does not — a tag is carried as 'S' or 'N', and without one a lookup cannot find the variant`,
            )
        }
        if (tags.length > 1) {
            throw new CodecError(
                `'${discriminator}' names ${tags.length} values at one option (${tags.join(', ')}), and a variant answers to exactly one tag — split it into one option per value`,
            )
        }
        const [tag] = tags as readonly [string | number]
        // Two options answering to one tag is a table with a key written twice: the second
        // write wins and the first option becomes unreachable, which shows up later as a
        // required attribute of the *other* variant going missing. `union` refuses its own
        // ambiguity at the declaration; so does this.
        if (Object.hasOwn(byTag, tag)) {
            throw new CodecError(
                `two options answer to '${discriminator}' = '${tag}', and a lookup reaches only one of them — give them distinct values`,
            )
        }
        // the option is already built, so the variant is the codec it came with rather than a
        // second one built from the same spec
        byTag[tag] = option.item as unknown as ItemCodec<
            Record<string, unknown>,
            unknown
        >
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
 * particular value cannot be known until that value turns up, because `string('A')` and
 * `string('B')` both write `S` and are never ambiguous — so that one is reported when it happens.
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
     * handed the same array.
     *
     * **The reason they are ambiguous has changed, and narrowed.** It used to be that neither
     * checked what was in it, because encoding did not validate. Both check now, and the pair is
     * still refused — over exactly one value, `[]`, the one array carrying nothing to tell them
     * apart. `set` has no such value and separates; see {@link separatedByElements}, which is the
     * exemption that follows. Reporting any of this per-encode would report it once per write
     * forever instead of once at import.
     *
     * Two exemptions, and both are options that identify themselves:
     *
     * - an **object** option is chosen by the attribute names present, never by being tried
     * - a **literal** knows which values are its own, so trying it is a real question — which is why
     *   `union([string('A'), string('B')])` is not ambiguous and never was
     *
     * An option whose kind is unknown — an adapter, an `opaque` — is not compared: it could be
     * anything, and refusing it against everything would refuse unions that work.
     *
     * **Both directions, because the condition has two sides.** This loop compared `carries` — value
     * kinds — and nothing compared `writes`, so `union([decimal, number])` was accepted: `decimal`
     * takes a string and `number` takes a number, no shared kind, declaration allowed. Both store
     * `'N'`. It encoded `'1.5'` to `{ N: '1.5' }` and then *could not read back what it had
     * written* — the decode filter kept both options and reported "decimal and number both admit
     * this attribute". A union that writes a row no reader can resolve is worse than one that is
     * refused, and it was invisible only because the mirror `union([string, decimal])` *is* refused,
     * by the kind check, one line up.
     */
    /**
     * Whether two options of the same container kind are told apart by what they hold — and the
     * answer turns on whether the container has an **empty inhabitant**.
     *
     * The loop below refuses a pair sharing a carried kind, on the stated ground that "neither
     * checks what it is given". That was true and is not: every row validates now, so
     * `array(string)` refuses `[1]` and `array(number)` refuses `['a']`. Measured, the pairs that
     * used to be refused wholesale share these values and no others:
     *
     *     array(string) / array(number)     `[]`
     *     record(string) / record(number)   `{}`
     *     set(string) / set(number)         nothing
     *
     * So `array` and `record` stay refused, and the reason is sharper than the old one: it is not
     * that neither checks, it is the one value that carries nothing to check. `set` separates,
     * because **DynamoDB has no empty set** — the asymmetry `admits`' own rows record, where `[]`
     * is admitted and an empty `Set` is not, deciding a question about declarations.
     *
     * **A sufficient condition, deliberately.** "No value can choose between these two" is not
     * decidable from two definitions in general, so this answers `false` wherever it cannot show
     * separation and the pair stays refused. Widening it is a matter of adding a container that
     * provably has no empty inhabitant, not of weakening what is here.
     *
     * **And this is not `identifying` being retired.** HANDOFF's fourth item expected `admits` to
     * replace it; it cannot. `admits` answers a question about a *value*, and both `identifying`
     * and this function answer a question about a *declaration* — there is no value in hand at
     * import time to ask about. The resolver is where `admits` replaced trying; the declaration
     * guard is where it structurally cannot.
     */
    const separatedByElements = (first: Option, second: Option): boolean => {
        const one = first.codec.def
        const other = second.codec.def
        if (one?.kind !== 'set' || other?.kind !== 'set') return false
        const held = carries(one.element)
        const alsoHeld = carries(other.element)
        return (
            !!held &&
            !!alsoHeld &&
            !held.some((kind) => alsoHeld.includes(kind))
        )
    }

    for (let i = 0; i < all.length; i++) {
        for (let j = i + 1; j < all.length; j++) {
            const first = all[i] as Option
            const second = all[j] as Option
            if (first.declares || second.declares) continue
            if (identifies(first) || identifies(second)) continue
            if (separatedByElements(first, second)) continue
            const shared = first.carries?.find((kind) =>
                second.carries?.includes(kind),
            )
            if (shared) {
                throw new CodecError(
                    `${first.describe} and ${second.describe} both take the same kind of value — ${shared} — and neither checks what it is given, so no value can choose between them; give the entity a discriminator and use discriminatedUnion`,
                )
            }
            if (first.member !== undefined && first.member === second.member) {
                throw new CodecError(
                    `${first.describe} and ${second.describe} both store '${first.member}', and neither checks what it reads, so no stored attribute can choose between them; give the entity a discriminator and use discriminatedUnion`,
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
     * If it leaves several, they are **tried**, and exactly one must succeed. The first step alone
     * would not do: `string('A')` and `string('B')` take the same kind of value and are never
     * ambiguous.
     *
     * **This is the read side only now.** Attempting was once the only thing available on both
     * sides, because encoding did not validate and a permissive option would "succeed" on a value
     * only its neighbour meant. The write side decides instead — {@link onlyAdmitting} — and this
     * one still attempts because there is no `AdmA` in `src/` to decide a stored attribute with.
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

    /**
     * The same, **decided rather than attempted** — the write side only.
     *
     * `only` finds its answer by encoding through every survivor and keeping the one that did not
     * fail. That was the only thing available while `encode` did not validate, and it is why this
     * union used to report ambiguity that was not there: a resolver that decides by *trying*
     * inherits every looseness of everything it tries, and then reports the result as a property of
     * the declaration. `union([held(decimal, dateAdapter), string])` could not encode a `Date` for
     * exactly that reason, and the fix was `string` refusing one.
     *
     * `admits` is the decision. It is §3's `Adm`, proved exact at all 21 constructors, and
     * `codec.laws.spec.ts` now holds `admits(c, v) ⟺ !failed(c.encode(v))` over its whole table —
     * so on the values in play this selects the same option `only` would have found by attempting,
     * and says *why* rather than discovering it. Two differences that are improvements rather than
     * equivalences: a `held` option whose adapter **throws** on a value it does not own is filtered
     * out here instead of propagating, and an ambiguity is reported without first writing one of
     * the two answers.
     *
     * **The read side keeps attempting**, because there is nothing to decide with: the model has
     * `AdmA` on the attribute side and `src/` has no port of it. That asymmetry is the reason this
     * is a second function rather than a flag on the first.
     */
    const onlyAdmitting = <A>(
        survives: (option: Option) => boolean,
        named: string,
        value: unknown,
        through: (option: Option) => Result<A>,
    ): Result<A> => {
        const candidates = all.filter(
            (option) => survives(option) && admits(option.codec, value),
        )
        if (candidates.length === 0) return unmatched(named)
        if (candidates.length > 1) {
            return ambiguous(
                candidates[0] as Option,
                candidates[1] as Option,
                named,
            )
        }
        return through(candidates[0] as Option)
    }

    /** Which options a value could be for: an object option by its names, anything else by kind. */
    const forValue =
        (shape: Shape | undefined, names: ReadonlySet<string> | undefined) =>
        (option: Option) =>
            option.declares
                ? shape === 'map' && !!names && namesFit(option, names)
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
                    ? member === 'M' && !!names && namesFit(option, names)
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
            (option) => namesFit(option, names),
            naming('this item', names),
            (option) =>
                (
                    option.item as ItemCodec<Record<string, unknown>, unknown>
                ).decode(item) as Result<T>,
        )
    }

    const writeItem = (item: T): Result<AttributeMap> => {
        const names = namesOf(item as Record<string, unknown>)
        return onlyAdmitting(
            (option) => namesFit(option, names),
            naming('this entity', names),
            item,
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
        return onlyAdmitting(
            forValue(shapeOf(value), held ? namesOf(held) : undefined),
            naming('this value', held ? namesOf(held) : undefined),
            value,
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
