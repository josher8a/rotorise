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
import { DynamoNumber, isStoredNumeral } from './attribute'
import { codec } from './build'
import type { Pair } from './denote'
import {
    altSem,
    byTagSem,
    codecAtLevel,
    codecOfTerm,
    guard,
    itemSem,
    judged,
    literalCodec,
    literalShape,
    membersOf,
    membersTooDeeply,
    opaqueTerms,
    optionOfTerm,
    termOf,
} from './denote'
import type {
    CycleEntryOf,
    DecodeFrame,
    DecodeTerm,
    EncodedFrame,
    FirstFrame,
    HoldsFree,
    HoldsNoValue,
    KindOfFrames,
    NarrowFrames,
    OffersAt,
    ScopeWallCycle,
    StepFrames,
} from './pathModel'
import {
    andThen,
    asPath,
    CodecError,
    failed,
    orThrow,
    type Result,
} from './result'
import { childAt, flatOf, guardAt, sideOf, storedApart } from './scoped'
import type { Body, Field, NameForm, NonEmpty, Term } from './term'
import {
    alwaysWritten,
    clauseForm,
    holdsNoValue,
    member as memberOf,
    openRefusal,
    ownsNullOf,
    pinnedForm,
    refuseSlots,
    resolvedTerm,
    sameAdapter,
    sameTerm,
    targetOf,
    unanimous,
    unboundRefs,
    usedTargetOf,
    whenBound,
} from './term'

/**
 * Forwarded for the consumers that still name them here.
 *
 * They are `denote.ts`'s now — each answers about a term's *pair* — and this keeps the move to one
 * pass. Six of the eight go in the pass that deletes the readers; `codecOfTerm` and `termOf` stay,
 * and their callers move to the module that owns them there.
 */
export { codecOfTerm, termOf, valueKinds } from './denote'

import type { ErrorMessage, show } from '../utils'
import type { StandardOutput, StandardSchemaV1 } from './standard'
import {
    describeShape,
    namedLiteral,
    namesOf,
    readTags,
    sameLiteral,
} from './value'

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
 * Type-level only. Whether an attribute may be absent is read at runtime from the field's
 * {@link Field} — `optional` is one of the two marks — so there is nothing for a symbol to carry
 * and nothing for a wrapper to forget to copy. The declaration stays because the *type* needs a
 * brand: {@link ItemSpec} and {@link ObjectOf} decide required from optional by it.
 */
declare const optionalMarker: unique symbol

/** Type-level only, for the same reason as {@link optionalMarker}: the term carries the fact. */
declare const fallbackMarker: unique symbol

/** Type-level only, for the same reason as {@link optionalMarker}. */
declare const undefinableMarker: unique symbol

/**
 * Marks a codec that a literal constructor built: `string('a')`, `number(1)`, `decimal('1')`,
 * `boolean(true)`, and each form with more than one value.
 *
 * Type-level only. A clause pins a key only where the term pins a literal, and only a literal
 * constructor builds such a term. The decoded type cannot say which constructor built a codec: a
 * caller's adapter can decode to a literal type over a term that pins nothing. So the readers that
 * ask whether a key is pinned read this mark, and no adapter sets the mark.
 */
declare const literalMarker: unique symbol

/** The mark of {@link literalMarker}, on a codec that a literal constructor built. */
type LiteralMark = { readonly [literalMarker]: true }

/** The mark where each codec of `C` carries the mark, and nothing otherwise. */
type LiteralMarkOf<C> = [C] extends [LiteralMark] ? LiteralMark : unknown

/*
 * **The model's term of a codec, in its type.** Optional, so no value carries it and no
 * constructor body changes. A codec with no term in its type, as a thunk with an annotation, is an
 * unbound `ref`.
 */
declare const termMarker: unique symbol
/**
 * **The options of a dissection, in declared order**, which a product distributes over. The tag
 * table of a dissection keys its members by tag and keeps no order. Optional and type-level only.
 */
declare const optionsMarker: unique symbol
type OptionsMark<Os> = { readonly [optionsMarker]?: Os }
/**
 * **The element codecs of a list, in declared order**, which a pattern reaches by position. The term
 * of a list keeps the terms of its elements, and a slice at a position rebuilds the codec there.
 * Optional and type-level only.
 */
declare const elementsMarker: unique symbol
type ElementsMark<Cs> = { readonly [elementsMarker]?: Cs }
/** The declared positions of a list with no spread, or `never`. */
type FixedElements<C> = C extends {
    readonly [elementsMarker]?: infer Cs extends readonly unknown[]
}
    ? true extends HasSpreadIn<Cs>
        ? never
        : Cs
    : never
type HasSpreadIn<Cs extends readonly unknown[]> = Cs[number] extends infer E
    ? E extends AnySpread
        ? true
        : false
    : false
type TermMark<T> = { readonly [termMarker]?: T }
type FreeTerm = ['ref', '#free']
/**
 * The default of the term and of the decoded type of {@link ObjectCodec}, {@link ItemCodec} and
 * {@link UnionCodec}: the type that the spec or the options give, computed where a member reads it.
 */
declare const ofParts: unique symbol
type OfParts = typeof ofParts
type TermOf<C> = C extends { readonly [termMarker]?: infer T }
    ? unknown extends T
        ? FreeTerm
        : T
    : FreeTerm
type TermsOf<Cs> = { -readonly [I in keyof Cs]: TermOf<Cs[I]> }

/*
 * **The free names of a codec, in its type**: the names that its term reads through a `ref` and
 * that no scope binds. Optional, so no value carries it. Wrapped in a tuple, because a reader
 * infers an optional `never` as `string`. A field carries the names of the codec that it marks.
 */
declare const freeMarker: unique symbol
type Free<F extends string> = { readonly [freeMarker]?: [F] }
export type FreeOf<C> = C extends {
    readonly [freeMarker]?: [infer F extends string]
}
    ? F
    : C extends { readonly codec: infer Marked }
      ? FreeOf<Marked>
      : never
/** The free names of an object: the names of its spec and its rest. An entry of a scope has none. */
type ObjectFree<Spec, Rest, Tm> = [Tm] extends [OfParts]
    ? FreeOf<Spec[keyof Spec]> | FreeOf<Rest>
    : never
/**
 * The `this` of each use: **a use needs a closed codec**, with no free name. `encode` is a
 * member of each codec, and keeps the type from being weak, so a codec with no mark is closed.
 */
export type Closed = {
    readonly encode: unknown
    readonly [freeMarker]?: [never]
}
type BaseT<K extends string> = ['prim', ['base', K]]
type LitT<K extends string, V> = ['prim', ['literal', K, V]]
type LitsT<
    K extends string,
    L extends readonly unknown[],
> = L extends readonly [infer One]
    ? LitT<K, One>
    : ['union', { -readonly [I in keyof L]: LitT<K, L[I]> }]
type HeldT<I, O, G> = ['held', false, I, O, [G, false], []]
type NumText<N> = N extends DynamoNumber<infer S> ? S : string
type NumTexts<L extends readonly unknown[]> = {
    -readonly [I in keyof L]: NumText<L[I]>
}
type FloatTexts<L extends readonly unknown[]> = {
    -readonly [I in keyof L]: `${L[I] & number}`
}
type DecimalT = HeldT<BaseT<'number'>, BaseT<'string'>, 'decimalText'>
type FloatT<I> = HeldT<I, BaseT<'number'>, ['caller', 'asFloat']>
type EveryButNumberT = [
    'union',
    [
        BaseT<'string'>,
        BaseT<'boolean'>,
        BaseT<'binary'>,
        BaseT<'null'>,
        ['set', BaseT<'string'>],
        ['set', BaseT<'number'>],
        ['set', BaseT<'binary'>],
        ['list', [], ['some', ['opaq']], []],
        ['object', ['mk', Record<never, never>, ['some', ['opaq']]]],
    ],
]
/** A field carries its slot as its term; a codec is a required slot. */
type SlotOf<F> = F extends { readonly codec: unknown }
    ? TermOf<F>
    : ['req', TermOf<F>]
type ObjectTermOf<Spec, Rest> = [
    'object',
    [
        'mk',
        { -readonly [K in keyof Spec]: SlotOf<Spec[K]> },
        [Rest] extends [undefined] ? ['none'] : ['some', TermOf<Rest>],
    ],
]
type ListTermOf<Items, Pre extends unknown[] = []> = Items extends readonly [
    infer H,
    ...infer R,
]
    ? H extends AnySpread
        ? ['list', Pre, ['some', TermOf<H>], TermsOf<R>]
        : ListTermOf<R, [...Pre, TermOf<H>]>
    : ['list', Pre, ['none'], []]

/**
 * Marks the codec for a list's repeating positions.
 *
 * Type-level only, and read at runtime from the definition, for the same reason as
 * {@link optionalMarker}. Like `optional`, it is a marker for a *position* rather than a codec in its
 * own right — it says "and then any number of these" — so it is meaningful in exactly one place:
 * among the elements of a {@link list}.
 */
declare const spreadMarker: unique symbol

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
    readonly encode: (this: Closed, value: In) => Result<A>
    /** The value this attribute holds, or why it cannot be read. */
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<Out>
    /**
     * The same, throwing.
     *
     * What every codec calls to compose with another: a nested decode that returned a union would
     * have to be unwrapped at each of the fifty-odd places one codec reaches into the next, and the
     * unwrapping is the part that gets forgotten. So composition throws and the boundary converts,
     * which is why these are the ones the composites are built from.
     */
    readonly unsafeEncode: (this: Closed, value: In) => A
    /** The same, throwing. */
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => Out
    /**
     * What this codec is — see {@link Term}.
     *
     * A term and not a declaration: the two field kinds denote a field, a field is not a codec,
     * and so no codec's definition is one. It is what makes each reader total over the kinds it can
     * be handed rather than over the kinds that exist.
     */
    readonly def: Term
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

/**
 * An attribute that may be absent from the item entirely.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A>` intersected with the
 * marker, so it claimed a field has an `encode` and a `decode` — true only because {@link optional}
 * built its answer by spreading the codec it marks. The field stratum refuses it: a field is a statement about a
 * *name*, the name belongs to the object, and the pair a member is read and written through is the
 * one the field marks. `rest` stopped making the same claim at `931c29c`.
 *
 * The definition is carried because {@link fieldOf} reads the mark off `def.kind` at run time, and a
 * type that did not name it would be a type that does not say what the value holds.
 */
export type OptionalCodec<
    T,
    A extends AttributeValue = AttributeValue,
    C = AttributeCodec<T, A>,
> = {
    readonly [optionalMarker]: true
    readonly codec: C
    // the mark's own case and not the whole of `Field`, so a reader that must tell the two marks
    // apart can, without the symbols — which are `declare const` and reach no consumer
    readonly def: Extract<Field, { readonly mark: 'optional' }>
}

/**
 * Carries {@link optionalMarker} as well as its own: the attribute is omitted either way, so every
 * reader that asks about the stored row is correct for this mark by being unchanged. The second
 * marker is what {@link ObjectOf} reads to keep the key required.
 */
export type UndefinableCodec<
    T,
    A extends AttributeValue = AttributeValue,
    C = AttributeCodec<T, A>,
> = {
    readonly [optionalMarker]: true
    readonly [undefinableMarker]: true
    readonly codec: C
    readonly def: Extract<Field, { readonly mark: 'undefinable' }>
}

/** Any codec, both directions erased — `never` in and `unknown` out, so every codec fits. */
export type AnyCodec = CodecShape<never, unknown, AttributeValue>

/**
 * Anything a {@link spread} produced, whatever it marks — {@link AnyCodec}'s counterpart for the one
 * thing that is a position rather than a codec, and the only element type {@link list} accepts that
 * is not a codec.
 *
 * Written as the marked shape rather than as `SpreadCodec<unknown, AttributeValue>`, for the reason
 * {@link ListWrites} records: `AttributeCodec` names its value on both sides, so it is invariant
 * and the `unknown` instantiation matches no real one.
 */
export type AnySpread = {
    readonly [spreadMarker]: true
    readonly spread: AnyCodec
}

/**
 * Anything an object member can be declared as: a codec, or a field that marks one.
 *
 * `optional` and `withLegacyRead` state that the attribute at a *name* may be absent, and the name belongs
 * to the object rather than to the thing declared at it. So a field is not a codec, and the pair a
 * member is read and written through is the one the field marks.
 *
 * Written as the definition alone, because the definition is the whole of what both cases carry that
 * an object reads: `fieldOf` takes the mark off `def.mark` and the child term out of the same record.
 */
export type ObjectSlot = AnyCodec | { readonly def: Field }

/**
 * The codec a declaration marks, and the declaration itself where it is already one.
 *
 * A body hands out codecs and never fields. The mark is a statement about a name, the name is the
 * body's, and a caller that asked for the attribute at a name wants the thing that reads and writes
 * it — so this is what {@link ItemCodec.field} answers with.
 */
export type Marks<C> = C extends { readonly codec: infer Marked } ? Marked : C

export type Decoded<C> = C extends {
    readonly attribute: AttributeCodec<infer T>
}
    ? T
    : // a field marks a codec and has none of its own, so the value it carries is the marked one's
      C extends { readonly codec: AttributeCodec<infer T> }
      ? T
      : C extends AttributeCodec<infer T, AttributeValue>
        ? T
        : never

/* ── the readers ──────────────────────────────────────────────────────────────────────── */

/*
 * A reader here answers from the **term** and nothing else, which is what makes the term determine
 * the codec rather than describe it. `constantOf` is the one left in this file; `member`, `occV`,
 * `occA`, `specOf`, `tagsOf` and `agrees` are `term.ts`'s, and
 * `carries`, `accepts` and `readsBack` ask the pair in `denote.ts`.
 *
 * They take a *codec* and read its term rather than taking the term, and that is the decision
 * rather than a leftover. A child position holds a term, so a reader recursing into one calls
 * `codecOfTerm`, which memoises on the frozen term and answers the codec that was already built.
 * A `Term` parameter instead moves the `.def` read from one place inside each of them out to
 * every call site.
 *
 * This is a section note and deliberately not a docstring: it binds to no declaration, so it
 * opens with one star rather than two. `docstring_anchor.py` is the check a doc comment here
 * would trip.
 */

/**
 * The kinds of value a codec can be given, as coarsely as a runtime check can tell them apart.
 *
 * **The codomain of {@link shapeOf}, which classifies a *value*.** That is what fixes the alphabet
 * and why it cannot be finer: `shapeOf` sees a `Set` and answers `'set'`, because telling `strSet`
 * from `numSet` means inspecting the elements, and **an empty `Set` belongs to no family at all**.
 * The same asymmetry decides which containers separate at `union`.
 *
 * {@link SetSlot} is the finer alphabet and is not a replacement. A term knows its base, so `occV`
 * can answer `strSet`; a value does not carry one, so no total function takes a value to a `SetSlot`.
 * The two are the codomains of two different functions rather than two spellings of one, which is
 * the answer to the question `1060c01` left open.
 */
export type Shape =
    | 'string'
    | 'number'
    | 'boolean'
    | 'binary'
    | 'set'
    | 'array'
    | 'map'
    | 'null'

/**
 * The `Value` **constructor** a term can write — {@link Shape} with the three set families split.
 *
 * The model's `SetSlot`, and the split is the whole of its content: `Kind` collapses `strSet`, `numSet`
 * and `binSet` to one label, so `set(string)` and `set(number)` are indistinguishable to it, while
 * the ten constructors tell them apart. `union(set(string), set(number))` is certified by this and
 * was not by the coarser label.
 *
 * **The codomain of `occV`, which reads a *term*.** The split is available here precisely because a
 * term carries its base. {@link Shape} is the value side's alphabet and stays coarse for the reason
 * written there, so this does not replace it: the two answer different questions.
 */
export type SetSlot = Exclude<Shape, 'set'> | 'strSet' | 'numSet' | 'binSet'

/**
 * What one declared attribute decides, read where the field is held.
 *
 * The two presence marks answer differently and neither is the codec's answer. A name that may be absent
 * decides nothing about a key, because a key built from it would have no value to build from in the
 * rows that omit it. A stand-in is written always, so what it stands in for still decides.
 *
 * A reader of the term alone does not answer this. A term is what a codec has, a field is not a
 * codec, and the body is what holds a field — so this reads the mark first and the term second.
 */
export const constantOf = (declared: ObjectSlot): unknown => {
    const def = declared.def
    if (
        'mark' in def &&
        (def.mark === 'optional' || def.mark === 'undefinable')
    )
        return undefined
    const t = 'mark' in def ? def.t : def
    // **A single-valued literal decides; two admissible values narrow without deciding.** This was
    // `decides`, a reader that walked the definition to answer it, and the term answers the same
    // row — deliberately *not* through the wrappers `member` descends: a constant is a claim about
    // the value, and `refine` can reject it, `withLegacyRead` can decode an older encoding into something
    // else, and `optional` admits absence, which is not the value. `withLegacyRead` is the one that keeps
    // it, always writing the attribute at a value typed to the same alternative.
    //
    // **An adapter is the second that keeps it**, and it has to be: `number` and `decimal` are
    // adapters over the one numeric base now, so a numeric discriminator is a literal under a
    // `held` and reading only the bare row would have lost every one of them. The value is the
    // caller's rather than the carrier's, so it is the inner literal's put back through the
    // adapter — well defined because `held` owes that the pair cancels.
    if (t.kind === 'held' && t.inner.kind === 'literal') {
        return (t.g as (held: unknown) => unknown)(t.inner.v)
    }
    return t.kind === 'literal' ? t.v : undefined
}

/* ── the seam: a definition, as the term it denotes ───────────────────────────────────── */

/**
 * Every codec a segment can reach, which is more than one exactly where a union's variants
 * disagree about it.
 *
 * A union is the only definition that branches, and what it branches into is a *set of codecs* —
 * not a codec. This used to be a `Def` kind, a pseudo-codec whose `encode` and `decode` both
 * threw, which meant every reader of a definition had to know about a definition that was not one.
 * The disagreement belongs to the walk, so it is the walk that carries it.
 *
 * **A segment has three answers**, as the model's `childD` has. The codecs at the segment. No
 * codec, where the term stores a member that is not the container of the segment: the store
 * refuses the segment on every attribute of the term, so the term leaves the frontier. And
 * {@link absent}, where the container admits no value at the segment: a closed object that lacks
 * the name, or a list with no spread past its prefix. A write there leaves an item that the codec
 * does not read, so `absent` stays on the frontier and the frontier refuses on use.
 *
 * `cycles` holds the entries of the flat scope of the root of the walk, which {@link printedMember}
 * reads.
 */
const childrenOf = (
    codec: AnyCodec,
    segment: string | number,
    cycles: Cycles,
): readonly AnyCodec[] | CodecError => {
    const def = codec.def
    // a position enters a list, and a name enters a map
    const container = typeof segment === 'number' ? 'L' : 'M'
    let stored = memberOf(def)
    if (def.kind === 'held' || def.kind === 'refine' || def.kind === 'legacy')
        stored = printedMember(def.inner, cycles)
    const apart = stored !== undefined && stored !== container
    switch (def.kind) {
        // a name the body does not declare falls in the open block, where there is one
        case 'object': {
            if (apart) return []
            const { fields, rest } = def.body
            const field = fields[segment]
            return [
                field
                    ? codecOfTerm(field.t)
                    : rest
                      ? codecOfTerm(rest)
                      : absent,
            ]
        }
        // a set is unordered, so no document path addresses a member of one — `set` never offered
        // a child either, and refusing here is what keeps a meaningless path from compiling
        case 'list': {
            if (apart || typeof segment !== 'number') return []
            // **A suffix refuses every position past the prefix.** Which codec holds position `n`
            // depends on how long the value is, because the suffix aligns from the right, and a
            // path is written without a length. The prefix is the part a path can address whatever
            // the value, so that is the part addressed here
            const at = def.pre[segment]
            if (at) return [codecOfTerm(at)]
            if (def.suf.length > 0) {
                return new CodecError(
                    `a path cannot go to position ${segment} of a list with a suffix: the codec at a position past the prefix depends on the length of the value, and a path carries no length. Address a position in the prefix, or the list itself`,
                )
            }
            return [def.spread ? codecOfTerm(def.spread) : absent]
        }
        case 'union':
            return acrossVariants(
                def.options.map((option) => codecOfTerm(option)),
                segment,
                cycles,
            )
        // **A path stops at an adapter that reads the whole value.** A write at a path writes one
        // part of the attribute, and the attribute is checked as a whole nowhere on that write
        case 'refine':
            if (apart) return []
            throw new CodecError(
                `a path cannot go into \`refine\` at '${segment}': the predicate reads the whole value, and a write at the path writes one part of the value without the predicate. Address the refined attribute itself`,
            )
        case 'legacy':
            if (apart) return []
            throw new CodecError(
                `a path cannot go into \`withLegacyRead\` at '${segment}': an older encoding of the attribute has another shape, and a path addresses the current shape only. Address the attribute itself`,
            )
        case 'held':
            if (apart) return []
            return new CodecError(
                `a path cannot go into an adapter at '${segment}': the adapter converts the whole value, and a write at the path writes one part of the stored value without the conversion. Address the attribute itself`,
            )
        case 'ref':
            return childrenOf(codecOfTerm(usedTargetOf(def)), segment, cycles)
        // `opaque` admits every value, so the codec at each segment is `opaque` again
        case 'opaq':
            return [codec]
        // a primitive, a literal and a set each store a member that no segment enters
        default:
            return []
    }
}

/**
 * The entries of the flat scope of the root of a walk, as {@link flatOf} numbers them. **The map
 * holds every entry, not only the entry on the stack of the walk.** An entry that the walk reads
 * before its cycle closes is a reference in the print as well, and a read of the stack alone gave
 * a member there, which the type and the model refuse.
 */
type Cycles = ReadonlyMap<Term, number>

/**
 * **The member that a wrapper's inner term stores, as the model reads the printed term.** The
 * emitter prints a `ref` that closes no cycle as its target, so the walk reads the target. The
 * emitter prints an entry of a cycle as a reference, `Scoped.Term.ref`, inside a closed codec. The
 * model's `μG` answers no member at a reference, so this answers `undefined` at an entry.
 * The emitter refuses a `ref` with no target, and this answers `undefined` there too.
 *
 * {@link memberOf} answers `undefined` at every `ref`, and the set constructor relies on that
 * answer. A set holds no `ref` on the path that `member` reads, so the last row reads a set
 * exactly.
 */
const printedMember = (t: Term, cycles: Cycles): AttributeName | undefined => {
    if (cycles.has(t)) return undefined
    switch (t.kind) {
        case 'ref': {
            const target = targetOf(t)
            return target === undefined
                ? undefined
                : printedMember(target, cycles)
        }
        case 'held':
        case 'refine':
        case 'legacy':
            return printedMember(t.inner, cycles)
        case 'union':
            return unanimous(t.options.map((one) => printedMember(one, cycles)))
        default:
            return memberOf(t)
    }
}

/** A frontier with one codec added, where no codec of the frontier has an equal term. */
const including = (
    frontier: readonly AnyCodec[],
    codec: AnyCodec,
): readonly AnyCodec[] =>
    frontier.some((one) => sameTerm(one.def, codec.def))
        ? frontier
        : [...frontier, codec]

/**
 * **The codec where a container admits no value at a segment**: one `never`, so a frontier that
 * holds it agrees with no writer, and the walk refuses on use. One term, so the frontier keeps one
 * copy.
 */
const absent: AnyCodec = codecOfTerm({ kind: 'never' })

/**
 * **A codec that admits no value at a path**: its term is `never`, the model's frame whose head is
 * `never` (`frameNever`). A declared `never` and {@link absent} are one term, so the test reads the
 * term and not the identity of {@link absent}: the frontier keeps the first codec of a term, and an
 * identity test made the verdict depend on the order of the options.
 *
 * **The test reads through no `ref`.** The walk reads a `ref` only to step through it. So a `ref`
 * whose target is `never` reads as a codec here, where the model, which prints the target, reads
 * `never`.
 */
const admitsNothing = (codec: AnyCodec): boolean => codec.def.kind === 'never'

/**
 * What the variants reach, one codec for each term ({@link sameTerm}), so the first declared wins.
 * Two calls of one constructor build two codecs of one term, and the model reads one term. A
 * variant that refuses makes the whole answer a refusal, because the reach of that variant is
 * unknown.
 */
const acrossVariants = (
    variants: readonly AnyCodec[],
    segment: string | number,
    cycles: Cycles,
): readonly AnyCodec[] | CodecError => {
    let reached: readonly AnyCodec[] = []
    for (const variant of variants) {
        const children = childrenOf(variant, segment, cycles)
        if (children instanceof CodecError) return children
        for (const child of children) reached = including(reached, child)
    }
    return reached
}

/**
 * **The frontier after a clause**, the model's `narrow`. A union gives each option whose stored
 * view {@link storedApart} does not separate from the stored view of the clause. Any other member
 * stays where the clause does not separate the member. A clause that separates every member is a
 * refusal that names the keys of the clause. A `ref` resolves as {@link childrenOf} resolves it.
 *
 * **The test reads the stored views**, because a path addresses a stored attribute. An adapter is
 * apart only from the bottom, so a test on the terms separates nothing at a `number` tag. The
 * stored view of an adapter is its inner term, which the test reads.
 */
const narrowAcross = (
    frontier: readonly AnyCodec[],
    clause: Clause,
): readonly AnyCodec[] | CodecError => {
    const apart = (t: Term) => storedApart(clause, t)
    let kept: readonly AnyCodec[] = []
    for (const one of frontier) {
        let t = one.def
        while (t.kind === 'ref') t = usedTargetOf(t)
        if (t.kind !== 'union') {
            if (!apart(t)) kept = including(kept, one)
            continue
        }
        for (const option of t.options) {
            if (!apart(option)) kept = including(kept, codecOfTerm(option))
        }
    }
    if (kept.length > 0) return kept
    const keys = Object.keys(clause.body.fields)
        .map((key) => `'${key}'`)
        .join(', ')
    return new CodecError(
        `the clause on ${keys} separates every option that the path reaches, so no codec stands at the path`,
    )
}

/** The stored value of a literal: the members a literal stores, and no set, list or map. */
export type StoredLiteral =
    | Attribute<'S'>
    | Attribute<'N'>
    | Attribute<'BOOL'>
    | Attribute<'B'>

/**
 * **A stored fact at a path that a condition expression tests**: the stored attribute at
 * `segments` holds one of the values in `in`, holds the member `type`, or exists. The three forms
 * are DynamoDB's `IN`, `attribute_type` and `attribute_exists`. Rotorise states the fact, and the
 * caller's expression library renders the fact.
 */
export type Precondition =
    | {
          readonly segments: readonly (string | number)[]
          readonly in: NonEmpty<StoredLiteral>
      }
    | {
          readonly segments: readonly (string | number)[]
          readonly type: AttributeName
      }
    | { readonly segments: readonly (string | number)[]; readonly exists: true }

/**
 * **The preconditions of the clauses on a path**, a conjunction. The preconditions of a clause are
 * the stored admission of the clause term at the position of the narrowed union. The narrowing
 * drops each option that the stored view of the clause separates. So an item that satisfies the
 * preconditions is no item of a dropped option, and a write at the path is safe under the
 * preconditions.
 *
 * A precondition is exact or absent. A condition weaker than the admission admits an item of a
 * dropped option, so a clause key with no exact precondition is a refusal that names the key.
 *
 * **An empty clause below the root is a refusal.** The clause term is then an open object with no
 * key: the narrowing drops each option that stores no `M`, and no key carries the precondition of
 * that member.
 */
const preconditionsOf = (
    steps: readonly Step[],
): Result<readonly Precondition[]> => {
    const preconditions: Precondition[] = []
    const prefix: (string | number)[] = []
    for (const step of steps) {
        if (typeof step !== 'object') {
            prefix.push(step)
            continue
        }
        const fields = Object.entries(step.body.fields)
        if (fields.length === 0 && prefix.length > 0) {
            return new CodecError(
                `the clause at '${asPath(prefix)}' names no key, so no precondition states that the attribute is a map`,
            )
        }
        const side = sideOf(step, 'raw')
        if (side === undefined && fields.length > 0) {
            return new CodecError(
                `the clause at '${asPath(prefix)}' has no scoped form, so no precondition reads it`,
            )
        }
        for (const [key, field] of fields) {
            if (side === undefined) break
            const at = guardAt(
                side,
                childAt(side, field.t, false),
                [...prefix, key],
                side.bodies.length + 1,
            )
            if (at.inexact) {
                return new CodecError(
                    `'${asPath(at.inexact.segments)}' gives no exact precondition: the clause stores ${at.inexact.what} there, and a condition on the path would admit more than the clause`,
                )
            }
            preconditions.push(...at.conjuncts)
        }
    }
    return preconditions
}

/**
 * The codec at a path whose walk refused. Both halves return the refusal, so
 * no value is written and no attribute is read, and the term is **`never`** for the reason that
 * {@link unresolvedAt} gives. Each call returns a new `CodecError`, because `under` changes the
 * error that it receives.
 */
const refusedAt = (refusal: CodecError): AnyCodec => {
    const refused = () => new CodecError(refusal.message)
    return codec<never, AttributeValue>({
        def: { kind: 'never' },
        encode: refused,
        decode: refused,
    })
}

/**
 * A path several variants declare differently, which is still a path.
 *
 * `path()` and `segments` are as well defined here as anywhere — knowing where an attribute lives
 * does not require knowing what writes it, and that is what `at` is most often for. Only the codec
 * half is missing, so only the codec half fails.
 *
 * It says **`never`**, the term that admits no value, and that is what this is: both halves return
 * the refusal, so no value is written and no attribute is read. It used to be a `Def` kind of its own called
 * `branch`, so a definition language for codecs contained an entry that was not a codec and every
 * reader had to know about it; and it used to carry no definition at all, which stopped being
 * available when `def` became required. It then said `custom`, a pair of functions with no
 * structure beneath them, which is gone: a caller reaches `held` over the codec the values really
 * sit on, and the term left with the constructor. `never` costs no reader a case and states the
 * fact rather than hiding it behind a throw — `member` and `carries` say nothing here, exactly as
 * they said nothing at a missing definition, and `accepts` declines to claim instead of reaching
 * the same `false` by catching.
 *
 * **`partial` is a frontier that holds a codec that admits nothing** ({@link admitsNothing}): some option admits no value at the path,
 * so a write there leaves an item of that option unreadable. A clause that drops the option settles
 * the path, so the refusal names `narrow`.
 */
const unresolvedAt = (path: string, partial: boolean): AnyCodec =>
    refusedAt(
        new CodecError(
            partial
                ? `'${path}' is declared by some variants only, so a write at this path would leave an item of another variant that no variant reads. Call \`narrow({...})\` to keep the variants that declare it.`
                : `'${path}' is declared differently in different variants, so this path cannot say which codec to encode with. Call \`narrow({...})\` to keep the variants that agree, for example \`narrow({ type: string('A') })\` where \`type\` is the discriminator.`,
        ),
    )

/** A map of attribute name to codec — what `item`, `map` and each `tagged` variant hold. */
export type Attributes = Readonly<Record<string, AnyCodec>>

/** What {@link refine} narrowed with, for an arbitrary that has to satisfy it. */
export type Refinement = {
    readonly is: (value: never) => boolean
    readonly what: string
    readonly arbitrary?: (rng: Rng, size: number) => unknown
    readonly onThinSearch?: (what: string, rate: number) => void
}

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
 * The list is the model's `GroundKind` **minus `null`**. It read "plus `decimal`" while `GroundKind` was
 * `string | number | boolean | binary | null`; `decimal` is a ground base in the model now, so the
 * difference is the other way round and it is a stratification one — `nullValue` is a codec and
 * `nullValue()` is not a literal anyone can write, because the only nonempty subset of `Unit` is
 * `Unit`.
 */
export type LiteralBase = 'string' | 'number' | 'boolean' | 'binary'

/** An alternative, at whichever base carries it. */
export type LiteralValue = string | DynamoNumber | boolean | Uint8Array

/**
 * The bases a native set can be built from — `SetBase`.
 *
 * `boolean` is the one base with no set: DynamoDB has `SS`, `NS` and `BS`, and no `BOOLS`. Four
 * bases onto three wire members, because `number` and `decimal` are both real and neither is a
 * legacy spelling of the other.
 */
export type SetBase = Exclude<LiteralBase, 'boolean'>

/**
 * The rule `(literal)`'s `ℓ`, checked: non-empty and pairwise distinct.
 *
 * **The model gets three guarantees from a type and the host's type gives two.** `ls` is a
 * `NEFinset k.Carrier`, so the base indexes the alternatives, `n ≥ 1` holds, and no two are equal —
 * all three from `NEFinset`. `term.ts`'s {@link Literal} buys the first from a discriminated union
 * over the base and the second from a tuple head. **TypeScript cannot say the third**, so it is a
 * refusal at construction, and this is where it lives.
 *
 * Distinctness is not tidiness. `NEFinset` is a *set*, so `literal(k, {'A','A'})` and
 * `literal(k, {'A'})` are one term in the model and two definitions here — and the second names a
 * cardinality the first does not, which is what {@link constantOf} reads to answer whether a literal
 * has exactly one value. A repeated alternative makes a two-element `ls` that admits one value,
 * and the constant would go unrecognised.
 *
 * Compared with {@link sameLiteral}, which compares the way the base compares: bytes for `binary`,
 * `===` otherwise.
 */
const someAlternatives = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): readonly T[] => {
    if (allowed.length === 0) {
        throw new CodecError(
            `a literal admits one of a non-empty set of values, and \`${base}()\` names none; pass the values, or use \`${base}\` itself if anything is admissible`,
        )
    }
    // the values rather than the indices, so the pair is two `T`s and not two lookups the checker
    // has to be told about; `at` recovers the position the message names
    for (const [i, one] of allowed.entries()) {
        for (const [after, other] of allowed.slice(i + 1).entries()) {
            if (sameLiteral(one, other)) {
                const at = i + 1 + after
                throw new CodecError(
                    `a literal's alternatives are a *set*, and \`${base}()\` names the same value at positions ${i} and ${at}; the model's \`NEFinset\` cannot hold it twice, and a repeat makes a two-value literal that admits one — which stops it reading as a constant`,
                )
            }
        }
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
 * `constant` is a **type-level** brand and carries no runtime property; {@link constantOf} is what
 * reads the value back at runtime.
 */
export type ConstantCodec<
    T,
    A extends AttributeValue = T extends LiteralValue
        ? LiteralAttribute<T>
        : AttributeValue,
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
export type StringCodec = AttributeCodec<string, Attribute<'S'>> &
    TermMark<BaseT<'string'>> & {
        <const T extends string>(
            only: T,
        ): ConstantCodec<T, Attribute<'S'>> &
            LiteralMark &
            TermMark<LitT<'string', T>>
        <const L extends readonly string[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'S'>> &
            LiteralMark &
            TermMark<LitsT<'string', L>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<string>, SS> &
                TermMark<['set', BaseT<'string'>]>
            <const L extends readonly string[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, SS> &
                TermMark<['set', LitsT<'string', L>]>
        }
    }

/* ── the terms, denoted ───────────────────────────────────────────────────────────────── */

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
 * **`N` itself, and the one native numeric term.** DynamoDB's own number, held as
 * {@link DynamoNumber}: exact to 38 significant digits, validated once at construction, and
 * already in the spelling the store returns.
 *
 * ```ts
 * dynamoNumber                       // an exact number
 * dynamoNumber(DynamoNumber.from('1.5'))   // …and a literal at it
 * dynamoNumber.set()                 // NS
 * ```
 *
 * **Three carriers write `N`, and the other two are adapters over this one.** They are no longer
 * terms of their own: a JS float and a decimal string are two ways a caller may hold this, not two
 * things the service stores.
 *
 * | codec | holds | exact | what it costs |
 * | --- | --- | --- | --- |
 * | `dynamoNumber` | {@link DynamoNumber} | yes, 38 digits | the caller builds one |
 * | {@link decimal} | `string` | yes, 38 digits | text the caller re-validates, and refuses a denormal spelling |
 * | {@link number} | JS `number` | no, about 15 digits | rounding, by construction |
 */
export const dynamoNumber: AttributeCodec<DynamoNumber, Attribute<'N'>> &
    TermMark<BaseT<'number'>> & {
        <const T extends DynamoNumber>(
            only: T,
        ): ConstantCodec<T, Attribute<'N'>> &
            LiteralMark &
            TermMark<LitT<'number', NumText<T>>>
        // a tuple, because inference unions no two object candidates: `readonly T[]` reads `T` off
        // the first numeral, and refuses a second numeral with another text
        <const T extends readonly DynamoNumber[]>(
            ...allowed: T
        ): AttributeCodec<T[number], Attribute<'N'>> &
            LiteralMark &
            TermMark<LitsT<'number', NumTexts<T>>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<DynamoNumber>, NS> &
                TermMark<['set', BaseT<'number'>]>
            <const T extends readonly DynamoNumber[]>(
                ...allowed: T
            ): AttributeCodec<ReadonlySet<T[number]>, NS> &
                TermMark<['set', LitsT<'number', NumTexts<T>>]>
        }
    } = Object.assign(
    literalCapability('number'),
    codecOfTerm({ kind: 'number' }) as AttributeCodec<
        DynamoNumber,
        Attribute<'N'>
    >,
    { set: setCapability('number', () => dynamoNumber) },
) as never

/** The held side of an adapter over a finite set of numerals: the texts it hands the caller. */
const textsOf = (texts: readonly string[]): Term => {
    const options: Term[] = [...new Set(texts)].map((v) => ({
        kind: 'literal',
        base: 'string',
        v,
    }))
    return options.length === 1
        ? (options[0] as Term)
        : { kind: 'union', options }
}

/**
 * An adapter over {@link dynamoNumber}, one conversion wide, on both halves. `held` is defined
 * further down this file, so the term is built directly; the two are the same construction.
 *
 * `outer` is the base the adapter hands to the caller, as a write occupancy. The conversion
 * checks the held side itself: `storedOnly` refuses a value that is not a string, and the carrier
 * refuses a value that is not a number. The term of `number` holds a `DynamoNumber`, so the term
 * cannot be the membership test for a JS float.
 */
const numericAdapter = <T>(
    inner: Term,
    outer: Term,
    into: (value: T) => Result<DynamoNumber>,
    outOf: (held: DynamoNumber) => Result<T>,
    via?: 'decimalText',
): AttributeCodec<T, Attribute<'N'>> =>
    codecOfTerm<T, Attribute<'N'>>({
        kind: 'held',
        inner,
        outer,
        f: into as (value: never) => unknown,
        g: outOf as (held: never) => unknown,
        ...(via ? { via } : {}),
    })

/**
 * The digits a caller wrote, refused rather than re-spelled.
 *
 * **The type is checked here and not by `isStoredNumeral`.** That predicate tests a pattern, and a
 * pattern coerces: `['1']` and any object whose `toString` spells a numeral both match it, so
 * `decimal` admitted values its own type excludes and wrote them as `N`. The predicate is right to
 * stay a predicate on `string` — the emitter recognises it by reference — so the boundary is here.
 */
const storedOnly = (value: string): Result<DynamoNumber> =>
    typeof value !== 'string'
        ? new CodecError(
              `${describeShape(value)} is not a string, and \`decimal\` holds the digits as text — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
          )
        : isStoredNumeral(value)
          ? DynamoNumber.from(value)
          : new CodecError(
                `'${value}' is not a numeral DynamoDB stores unchanged; it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
            )

/**
 * A decimal held as a string, stored as `N`. The codec for money — nothing becomes a JS number, so
 * nothing rounds.
 *
 * **An adapter over {@link dynamoNumber}, not a base of its own.** `decimal` was a second ground
 * base at `N` and is a change of carrier now: the same number, handed to the caller as text.
 *
 * **Only the form DynamoDB stores.** It normalises what it accepts — `'1.50'` becomes `'1.5'`,
 * `'007'` becomes `'7'`, `'1e5'` becomes `'100000'` — and this codec hands back the digits, so
 * anything else would come back as a different string from the one written. That is a round trip
 * failing across the database, where neither the type nor the law suite can see it, so it is
 * refused at the point where it is still local: `encode` rejects a denormal numeral rather than
 * quietly rewriting it, because rewriting is how you lose track of which value was meant.
 *
 * That refusal is this codec's and not the carrier's. {@link DynamoNumber} normalises, because it
 * holds a number; this hands back text, so it refuses instead.
 *
 * `'1.50'` is not a price this codec will write. `'1.5'` is. Where exact digits matter more than
 * numeric ordering — trailing zeros that mean something — use {@link string}.
 */
export const decimal: AttributeCodec<string, Attribute<'N'>> &
    TermMark<DecimalT> & {
        <const T extends string>(
            only: T,
        ): ConstantCodec<T, Attribute<'N'>> &
            LiteralMark &
            TermMark<HeldT<LitT<'number', T>, LitT<'string', T>, 'decimalText'>>
        <const L extends readonly string[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'N'>> &
            LiteralMark &
            TermMark<
                HeldT<LitsT<'number', L>, LitsT<'string', L>, 'decimalText'>
            >
        readonly set: {
            (): AttributeCodec<ReadonlySet<string>, NS> &
                TermMark<['set', DecimalT]>
            <const L extends readonly string[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, NS> &
                TermMark<
                    [
                        'set',
                        HeldT<
                            LitsT<'number', L>,
                            LitsT<'string', L>,
                            'decimalText'
                        >,
                    ]
                >
        }
    } = Object.assign(
    (...allowed: readonly string[]) => {
        const stored = allowed.map((one) => orThrow(storedOnly(one)))
        return numericAdapter<string>(
            termOf(literalCapability('number')(...stored) as AnyCodec),
            // the held side is the texts the adapter hands the caller, so the view is exact
            textsOf(stored.map((held) => held.toString())),
            storedOnly,
            (held) => held.toString(),
            'decimalText',
        )
    },
    numericAdapter<string>(
        { kind: 'number' },
        { kind: 'string' },
        storedOnly,
        (held) => held.toString(),
        'decimalText',
    ),
    {
        // the set of the adapter itself: the conversion rides at the element
        set: (...allowed: readonly string[]) =>
            set((allowed.length ? decimal(...allowed) : decimal) as AnyCodec),
    },
) as never

/** A JS number, as the carrier refuses it. */
const asFloat = (value: number): Result<DynamoNumber> =>
    DynamoNumber.fromNumber(value)

/**
 * The alternatives a numeric literal names, refused at the caller's level first.
 *
 * **Two refusals, and the adapter owes both.** A value that is not a number at all is
 * `literalTerm`'s sentence one base down, and it is about the caller's type. A number outside what
 * `N` holds is the carrier's. The conversion runs before the native literal is built, so without
 * this the carrier would answer for the type and `number(0, 'A')` would report a `NaN` rule.
 *
 * **Every value outside the range is named, not the first.** A caller who writes three bad
 * alternatives fixes three. One bad alternative keeps the carrier's own sentence, which already
 * says which rule it broke.
 */
const numericAlternatives = (
    allowed: readonly number[],
): readonly DynamoNumber[] => {
    const held: DynamoNumber[] = []
    const outside: number[] = []
    let firstRefusal: CodecError | undefined
    for (const one of allowed) {
        if (typeof one !== 'number') {
            throw new CodecError(
                `\`number(...)\` admits ${literalShape.number} values, and ${namedLiteral(one)} is not one`,
            )
        }
        const carried = asFloat(one)
        if (failed(carried)) {
            outside.push(one)
            firstRefusal ??= carried
        } else {
            held.push(carried)
        }
    }
    if (outside.length === 1 && firstRefusal) throw firstRefusal
    if (outside.length > 1) {
        throw new CodecError(
            `${outside.map(namedLiteral).join(', ')} are not numbers DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN and no Infinity`,
        )
    }
    return held
}

/**
 * …and back, refused where the rounding leaves the range `N` holds.
 *
 * `N` carries 38 significant digits and a JS `number` about 15, so reading rounds. Rounding is this
 * codec's declared cost and not a failure. Rounding *out of the range DynamoDB stores* is a
 * different fact: the value read back is one this same codec would refuse to write, so the round
 * trip breaks on a numeral the service genuinely returns. The write half already refuses it, and
 * this half says the same thing rather than hand back a number that cannot go home.
 */
const asJsNumber = (held: DynamoNumber): Result<number> => {
    const value = held.toNumber()
    return failed(DynamoNumber.fromNumber(value))
        ? new CodecError(
              `'${held.toString()}' rounds to ${String(value)}, which is outside what DynamoDB stores, so \`number\` cannot write it back; read this attribute with \`dynamoNumber\` or \`decimal\`, which do not round`,
          )
        : value
}

/**
 * A JS number, stored as `N`. Lossy by construction — `N` carries 38 digits, `number` about 15.
 * Right for enums, counts and flags; wrong for money, which is {@link decimal}.
 *
 * **An adapter over {@link dynamoNumber}, not a base of its own**, and the conversion is where the
 * loss is: the float has already rounded before this codec sees it. `number.set()` and
 * `decimal.set()` are two carriers over one wire set: each is the set of its adapter.
 */
export const number: AttributeCodec<number, Attribute<'N'>> &
    TermMark<FloatT<BaseT<'number'>>> & {
        <const T extends number>(
            only: T,
        ): ConstantCodec<T, Attribute<'N'>> &
            LiteralMark &
            TermMark<FloatT<LitT<'number', `${T}`>>>
        <const L extends readonly number[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'N'>> &
            LiteralMark &
            TermMark<FloatT<LitsT<'number', FloatTexts<L>>>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<number>, NS> &
                TermMark<['set', FloatT<BaseT<'number'>>]>
            <const L extends readonly number[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, NS> &
                TermMark<['set', FloatT<LitsT<'number', FloatTexts<L>>>]>
        }
    } = Object.assign(
    (...allowed: readonly number[]) =>
        numericAdapter<number>(
            termOf(
                literalCapability('number')(
                    ...numericAlternatives(allowed),
                ) as AnyCodec,
            ),
            { kind: 'number' },
            asFloat,
            asJsNumber,
        ),
    numericAdapter<number>(
        { kind: 'number' },
        { kind: 'number' },
        asFloat,
        asJsNumber,
    ),
    {
        // the set of the adapter itself: the conversion rides at the element
        set: (...allowed: readonly number[]) =>
            set((allowed.length ? number(...allowed) : number) as AnyCodec),
    },
) as never

/**
 * A boolean, as `BOOL`.
 *
 * `boolean(true)` is a literal at `BOOL`, which nothing on the old surface could spell —
 * `literal(...)` took a string or a number and there was no third option. There is deliberately no
 * `boolean.set()`: DynamoDB has `SS`, `NS` and `BS`, and no set of booleans.
 */
export type BooleanCodec = AttributeCodec<boolean, Attribute<'BOOL'>> &
    TermMark<BaseT<'boolean'>> & {
        <const T extends boolean>(
            only: T,
        ): ConstantCodec<T, Attribute<'BOOL'>> &
            LiteralMark &
            TermMark<LitT<'boolean', T>>
        <const L extends readonly boolean[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'BOOL'>> &
            LiteralMark &
            TermMark<LitsT<'boolean', L>>
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
export const nullValue: AttributeCodec<null, Attribute<'NULL'>> &
    TermMark<BaseT<'null'>> = codecOfTerm({
    kind: 'null',
})

/**
 * Binary, as `B`.
 *
 * `binary(bytes)` compares **by bytes**, not by reference — two `Uint8Array`s holding the same
 * octets are the same alternative, and a decoded value comes back as the member of `ℓ` rather than
 * as the array that was read off the wire.
 */
export type BinaryCodec = AttributeCodec<Uint8Array, Attribute<'B'>> &
    TermMark<BaseT<'binary'>> & {
        // a `Uint8Array` has no literal type: the bytes are unknown text at the type level
        (
            only: Uint8Array,
        ): ConstantCodec<Uint8Array, Attribute<'B'>> &
            LiteralMark &
            TermMark<LitT<'binary', string>>
        (
            ...allowed: readonly Uint8Array[]
        ): AttributeCodec<Uint8Array, Attribute<'B'>> &
            LiteralMark &
            TermMark<['union', LitT<'binary', string>[]]>
        readonly set: {
            (): AttributeCodec<ReadonlySet<Uint8Array>, BS> &
                TermMark<['set', BaseT<'binary'>]>
            (
                ...allowed: readonly Uint8Array[]
            ): AttributeCodec<ReadonlySet<Uint8Array>, BS> &
                TermMark<['set', ['union', LitT<'binary', string>[]]]>
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
 * because it is where both halves of the rule `(set)`'s premise are checked, and they are checked once.
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
    element: C,
): AttributeCodec<ReadonlySet<Decoded<C>>, SetOf<C>> => {
    type T = Decoded<C>
    const inner = element as unknown as AttributeCodec<T>
    // the element is the element's own term, so a restriction, a literal and an adapter each ride
    // at the element, and the set is its finite-powerset lift
    const term: Term = { kind: 'set', elem: inner.def }
    return codecOfTerm<ReadonlySet<T>, SetOf<C>>(term)
}

/**
 * A homogeneous positional container, as `L`.
 *
 * `list(spread(c))` says the same thing, and this says it in one word for the common case. A
 * `never` element is admitted rather than refused: the spread is not a slot, so an array of
 * nothing is the empty list, which is a value.
 */
export const array = <const C extends AnyCodec>(
    element: C,
): AttributeCodec<readonly Decoded<C>[], L<AttributeOf<C>>> &
    TermMark<['list', [], ['some', TermOf<C>], []]> &
    Free<FreeOf<C>> => {
    type T = Decoded<C>
    return codecOfTerm<readonly T[], L<AttributeOf<C>>>({
        kind: 'list',
        pre: [],
        spread: termOf(element as unknown as AnyCodec),
        suf: [],
    })
}

/**
 * A declaration that fills a **slot** with a term holding no value.
 *
 * A slot is a position a value must fill: a declared element of a list, and a `req` or `withLegacyRead`
 * field. `optional` and `undefinable` are not slots, because the key may be absent. A list's
 * spread is not one either, because a value of the declared length omits it.
 */
type IsNeverSlot<D> = [D] extends [{ readonly [optionalMarker]: true }]
    ? false
    : [D] extends [
            { readonly codec: { readonly def: { readonly kind: 'never' } } },
        ]
      ? true
      : [D] extends [{ readonly def: { readonly kind: 'never' } }]
        ? true
        : // the node that a `ref` names, and each other form that holds no value
          HoldsNoValue<
                TermOf<D extends { readonly codec: infer C } ? C : D>
            > extends true
          ? true
          : false

/**
 * Whether any **declared** position of a list is `never`.
 *
 * The spread is not asked, because the spread is not a slot: a value of exactly the declared
 * length omits every spread position, so a spread at the bottom is the list of its declared
 * positions and that is a value. The model's `Term.list` admits a value of exactly the declared
 * length for the same reason, so a spread at `never` leaves its held set non-empty.
 */
type ListNeverSlot<Cs extends readonly unknown[]> = Cs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? H extends AnySpread
        ? ListNeverSlot<T>
        : IsNeverSlot<H> extends true
          ? true
          : ListNeverSlot<T>
    : false

/**
 * Nothing, or why this list can hold no value.
 *
 * **The model types a list with a `never` position and gives it an empty held set, which is
 * correct there.** The host refuses it instead, because a position nothing fills makes the whole
 * list unconstructible and `never` already names that term: a declaration with two spellings, one
 * of them a trap, is the shape a constructor should not have.
 *
 * The spread is exempt, and that is the same rule read the other way: it is not a slot, so a list
 * whose spread is `never` is the list of its declared positions, and that is a value.
 */
type NoNeverSlot<Cs extends readonly unknown[]> = ListNeverSlot<Cs> extends true
    ? ErrorMessage<'[list] a declared position is `never`, so nothing fills it and the list holds no value at all. Use `never` itself if that is what you meant'>
    : unknown

/**
 * A positional container: the elements in order, with at most one {@link spread} among them.
 *
 * The call reads as the type it builds. `list(string, spread(decimal), boolean)` is
 * `readonly [string, ...string[], boolean]`, position for position, so a reader checks the
 * declaration against the type without splitting it into parts first.
 *
 * **A spread may sit anywhere, and only once.** It used to have to go last, because the only
 * container that took one was a tuple and a tuple had no suffix. A list has one, so "last" was
 * never the rule: the rule is *once*, and {@link SpreadOnce} states it. Every position after the
 * spread is a fixed element aligned from the right.
 *
 * A value of length `n` is held when `n` is at least the declared positions: the prefix aligns
 * from the left, the suffix from the right, and the middle goes through the spread.
 *
 * @example
 * ```ts
 * list(string, decimal, spread(boolean))  // readonly [string, string, ...boolean[]]
 * list(string, spread(decimal), boolean)  // readonly [string, ...string[], boolean]
 * list(string, decimal)                   // readonly [string, string]
 * list(spread(string))                    // readonly string[], as `array` gives
 * ```
 */
export const list = <const Cs extends readonly (AnyCodec | AnySpread)[]>(
    // asked of the union of the elements rather than mapped over them: one instantiation instead
    // of one per position, and the diagnostic lands on the call either way. Mapping cost +10%
    // across this repo, measured
    ...elements: Cs & SpreadOnce<Cs> & NoNeverSlot<Cs>
): ListCodec<Cs> => {
    const all = elements as readonly unknown[]

    /**
     * `SpreadOnce` refuses a second spread in the *type*, and a cast defeats the type.
     *
     * The cast is the path that matters: with two spreads the first was read as the spread and
     * the second as a fixed element, so the declaration held a shape nobody wrote.
     */
    const spreads = all.filter(isSpread)
    if (spreads.length > 1) {
        throw new CodecError(
            'a list has at most one spread, and this one has ' +
                `${spreads.length} — the positions after the spread are fixed elements`,
        )
    }

    const at = all.findIndex(isSpread)
    const marked = at === -1 ? undefined : (all[at] as AnySpread)

    // as with `map`, the cast keeps the shape each position writes, which
    // `Attribute<'L'>` would flatten to "some list"
    return codecOfTerm({
        kind: 'list',
        pre: (at === -1 ? all : all.slice(0, at)).map((c) =>
            termOf(c as AnyCodec),
        ),
        ...(marked ? { spread: termOf(marked.spread) } : {}),
        suf: (at === -1 ? [] : all.slice(at + 1)).map((c) =>
            termOf(c as AnyCodec),
        ),
    }) as unknown as ListCodec<Cs>
}

/** The codec that {@link list} returns, and the one that a slice at a position rebuilds. */
type ListCodec<Cs extends readonly unknown[]> = AttributeCodec<
    ListOf<Cs>,
    L<ListWrites<Cs>>
> &
    TermMark<ListTermOf<Cs>> &
    Free<FreeOf<Cs[number]>> &
    ElementsMark<Cs>

/**
 * The elements split at the one spread: what comes before it, what it marks, and what comes after.
 *
 * Accumulated into `Pre` rather than inferred at a fixed position, because the spread may sit
 * anywhere. The accumulator makes the recursion tail-recursive, which is the form TypeScript
 * unrolls to a thousand elements instead of fifty.
 */
type Split<
    Cs extends readonly unknown[],
    Pre extends readonly unknown[] = [],
> = Cs extends readonly [infer H, ...infer T]
    ? H extends AnySpread
        ? H extends { readonly spread: infer S }
            ? { pre: Pre; spread: S; suf: T }
            : never
        : Split<T, [...Pre, H]>
    : { pre: Pre; spread: undefined; suf: [] }

/**
 * What a list holds: the prefix by position, the spread by repetition, then the suffix by position.
 *
 * Written as two branches on the spread rather than as one type with an empty rest, because
 * `...never[]` in the middle of a tuple type is not the empty middle — it is a tuple no value
 * inhabits.
 */
export type ListOf<Cs extends readonly unknown[]> = Split<Cs> extends {
    pre: infer P extends readonly unknown[]
    spread: infer S
    suf: infer F extends readonly unknown[]
}
    ? S extends AnyCodec
        ? readonly [
              ...{ [I in keyof P]: Decoded<P[I]> },
              ...Decoded<S>[],
              ...{ [I in keyof F]: Decoded<F[I]> },
          ]
        : readonly [
              ...{ [I in keyof P]: Decoded<P[I]> },
              ...{ [I in keyof F]: Decoded<F[I]> },
          ]
    : never

/**
 * The same split, on the stored side.
 *
 * Both sides match the *marker* and then extract with {@link Decoded} and {@link AttributeOf},
 * rather than inferring through `SpreadCodec<…>`. Inferring is the trap: `AttributeCodec` names
 * its value on both sides, so `SpreadCodec<unknown, infer A>` matches nothing and this fell to the
 * fixed-arity branch — a list with a spread typed as though the spread were one element. Silently,
 * because a fixed `[S, N, N]` *is* assignable to `readonly [S, N, ...N[]]`, so an assignment could
 * not tell.
 */
export type ListWrites<Cs extends readonly unknown[]> = Split<Cs> extends {
    pre: infer P extends readonly unknown[]
    spread: infer S
    suf: infer F extends readonly unknown[]
}
    ? S extends AnyCodec
        ? readonly [
              ...{ [I in keyof P]: AttributeOf<P[I]> },
              ...(AttributeOf<S> & AttributeValue)[],
              ...{ [I in keyof F]: AttributeOf<F[I]> },
          ]
        : readonly [
              ...{ [I in keyof P]: AttributeOf<P[I]> },
              ...{ [I in keyof F]: AttributeOf<F[I]> },
          ]
    : never

/**
 * Nothing, or why a spread is not an attribute.
 *
 * An item's members are reached by *name*, so `optional` and `withLegacyRead` belong here — both are
 * statements about a name. `spread` is a statement about a *position*, and there are no positions
 * in a map, so it is the one marker an object member cannot be.
 */
type NoSpreadMember<Spec> = [
    Extract<Spec[keyof Spec], { readonly [spreadMarker]: true }>,
] extends [never]
    ? unknown
    : ErrorMessage<'`spread(...)` is a position in a list, not an attribute: an item has names and not positions'>

/** A field whose mark makes it a slot, declared at a term that holds no value. */
type NoNeverField<Spec> = [
    {
        [K in keyof Spec]: IsNeverSlot<Spec[K]> extends true ? K : never
    }[keyof Spec],
] extends [never]
    ? unknown
    : ErrorMessage<`[object] '${{
          [K in keyof Spec]: IsNeverSlot<Spec[K]> extends true ? K : never
      }[keyof Spec] &
          string}' is declared at \`never\` and the row always writes it, so the object holds no value at all. Mark it \`optional\`, or use \`never\` itself`>

/**
 * Nothing, or why a list carries more than one spread.
 *
 * A spread says "and then any number of these", and a second one has no reading: the positions
 * between the two belong to both. Checked by splitting at the first spread and asking whether
 * anything *after* it is marked, which is one instantiation over the tail rather than one per
 * position.
 */
export type SpreadOnce<Cs extends readonly unknown[]> = Split<Cs> extends {
    suf: infer F extends readonly unknown[]
}
    ? [Extract<F[number], { readonly [spreadMarker]: true }>] extends [never]
        ? unknown
        : ErrorMessage<'a list has at most one `spread(...)` — the positions after it are fixed elements'>
    : unknown

/**
 * A list's repeating positions: *and then any number of these*.
 *
 * The counterpart of `...T[]` in a tuple type, and restricted the same way — it is meaningful only
 * among the elements of a {@link list}, and only once, because the positions between two spreads
 * belong to both. Every other place refuses it, and the type says so rather than a runtime check
 * discovering it.
 *
 * @example
 * ```ts
 * list(string, decimal, spread(boolean))  // readonly [string, string, ...boolean[]]
 * list(string, spread(decimal), boolean)  // readonly [string, ...string[], boolean]
 * list(spread(string))                    // readonly string[], stored as L with no minimum
 * ```
 */
export const spread = <const C extends AnyCodec>(
    element: C,
): SpreadCodec<Decoded<C>, AttributeOf<C> & AttributeValue> &
    TermMark<TermOf<C>> &
    Free<FreeOf<C>> =>
    ({ spread: element as unknown as AnyCodec }) as unknown as SpreadCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue
    >

/**
 * Whether this is a spread marker rather than an element — the runtime half of `spreadMarker`.
 *
 * `spreadMarker` is a `declare const` symbol, so it exists in the type and nowhere else, and
 * {@link list} needs an answer at run time. One own property, checked by name.
 */
const isSpread = (element: unknown): element is AnySpread =>
    typeof element === 'object' &&
    element !== null &&
    'spread' in element &&
    // and it is not a codec, which is decidable now that every codec carries a definition: a
    // marker is a position and has no `encode` to call
    !('def' in element)

/**
 * A list's repeating position: the element codec, marked for a position.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A> & { …marker }`, which
 * claimed a marker has an `encode` and a `decode` — true only because the marker was built by
 * spreading its element, so a bare one encoded as its element by accident. A spread is a
 * *position*, and a list is the only thing that has one. It unwraps the marker at construction.
 * Nothing else may be given one, and the type no longer offers a caller the two halves to call.
 */
export type SpreadCodec<T, A extends AttributeValue = AttributeValue> = {
    readonly [spreadMarker]: true
    readonly spread: AttributeCodec<T, A>
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
export type Refined<
    T,
    A extends AttributeValue,
    Tm = FreeTerm,
> = AttributeCodec<T, A> & SetCapable<T, A, Tm>

/**
 * `.set()`, where the codec it sits on can be a set's element.
 *
 * The capability {@link set} decides at runtime, stated at the type as far as the type can see
 * it, which is not all the way. A codec's *type* is not generic in its definition: every codec
 * carries a `Term`, and none of them carries *which* one at the type. So `refine(...)`'s type
 * knows the attribute and never the term beneath, and the gate here is the attribute: `S`, `N` or
 * `B`, the three a stored set is built from. `refine(withLegacyRead(…), p).set()` type-checks
 * and throws, because a read widening has no set in the model. That gap closes only by making the
 * codec type generic in its definition, which was measured at 481 of 968 signatures and rejected;
 * the runtime refusal in {@link set} is what stands in for it.
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
export type SetCapable<T, A extends AttributeValue, Tm = FreeTerm> = [
    A,
] extends [Attribute<'S'>]
    ? {
          readonly set: () => AttributeCodec<ReadonlySet<T>, SS> &
              TermMark<['set', Tm]>
      }
    : [A] extends [Attribute<'N'>]
      ? {
            readonly set: () => AttributeCodec<ReadonlySet<T>, NS> &
                TermMark<['set', Tm]>
        }
      : [A] extends [Attribute<'B'>]
        ? {
              readonly set: () => AttributeCodec<ReadonlySet<T>, BS> &
                  TermMark<['set', Tm]>
          }
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

/** What {@link refine} takes beside the inner codec and the predicate. */
type RefineOptions<Narrow> = {
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
     * Only ever called from an arbitrary, so only ever during a property run.
     */
    readonly onThinSearch?: (what: string, rate: number) => void
}

/**
 * Two signatures, one codec. A refinement of a literal constructor keeps the mark of the literal
 * ({@link literalMarker}), because the term under the predicate pins the literal: the members of a
 * slice and the walk of `at` read through a refinement.
 */
export function refine<
    Wide,
    Narrow extends Wide,
    A extends AttributeValue,
    Tm = FreeTerm,
    F extends string = never,
>(
    inner: AttributeCodec<Wide, A> & LiteralMark & TermMark<Tm> & Free<F>,
    is: (value: Wide) => value is Narrow,
    options?: RefineOptions<Narrow>,
): Refined<Narrow, A, ['refine', Tm]> &
    LiteralMark &
    TermMark<['refine', Tm]> &
    Free<F>
export function refine<
    Wide,
    Narrow extends Wide,
    A extends AttributeValue,
    Tm = FreeTerm,
    F extends string = never,
>(
    inner: AttributeCodec<Wide, A> & TermMark<Tm> & Free<F>,
    is: (value: Wide) => value is Narrow,
    options?: RefineOptions<Narrow>,
): Refined<Narrow, A, ['refine', Tm]> & TermMark<['refine', Tm]> & Free<F>
export function refine<Wide, Narrow extends Wide, A extends AttributeValue>(
    inner: AttributeCodec<Wide, A>,
    is: (value: Wide) => value is Narrow,
    options: RefineOptions<Narrow> = {},
): Refined<Narrow, A, unknown> {
    const what = options.describe ?? 'the expected form'

    /**
     * Generation falls back to filtering the inner codec's values, and reports when that thins the
     * search badly.
     *
     * `decimal` generates negatives, which are not prices, and fractions, which are not sequence numbers —
     * so a run of a hundred cases can quietly be a run of forty. The declaration is not the place to
     * fix that: a predicate is what a brand *is*, and demanding an example of one beside it would
     * tax every codec for something only a property run cares about. But a run that has been halved
     * without saying so is worth a word, and this can only be reached from an arbitrary, so the word
     * only ever lands in a test.
     */
    // `member` reads through a refinement, which is what lets a set of a brand work; `constantOf`
    // does not, because the predicate may be exactly what rejects the constant.
    //
    // `setCapable` is what carries `.set()` across the refinement, and it is the whole of why the
    // brand survives: `amount.set()` decodes as `ReadonlySet<Price>` because the set is built from
    // `amount`, where the predicate that produces a `Price` already lives.
    return setCapable(
        codecOfTerm<Narrow, A>({
            kind: 'refine',
            inner: termOf(inner as unknown as AnyCodec),
            q: {
                is: is as (value: never) => boolean,
                what,
                arbitrary: options.arbitrary as
                    | ((rng: Rng, size: number) => unknown)
                    | undefined,
                onThinSearch: options.onThinSearch,
            },
        }),
    )
}

// ── reading what is already there ───────────────────────────────────

/**
 * A field that stands in a value where the attribute is absent.
 *
 * Not a codec, for the reason {@link OptionalCodec} records. The stand-in is the marker's payload at
 * the type level and `def.value` at run time, and the run-time side is the one {@link withLegacyRead}
 * checks against the rule `(withLegacyRead)`.
 */
type MissingCodec<
    T,
    A extends AttributeValue = AttributeValue,
    // the codec the mark is about, carried rather than erased to `AttributeCodec<T, A>`. A brand
    // sits on the codec — `constant` is the one that matters here — and erasing to the two type
    // arguments drops it before a derivation over the spec can ask
    C = AttributeCodec<T, A>,
> = {
    readonly [fallbackMarker]: T
    readonly codec: C
    readonly def: Extract<Field, { readonly mark: 'fallback' }>
}

/**
 * Reads a missing attribute as a value, and writes the attribute always.
 *
 * Not {@link optional}: the entity always has it, the *data* may not — a row written before the
 * attribute existed. Replaces `item.channel ?? 'IN_STORE'` at every read site.
 *
 * **The stand-in must be writable by the codec it stands in for**, and that is checked here, at the
 * declaration. The model carries it as the premise `hfill` of `carrier_objectCodec`: the stand-in of a
 * `.fill` slot is in the write domain of its codec. The premise exists because the proof failed
 * without it: a row missing the attribute reads back as the stand-in, and if the inner codec cannot write that value the item cannot be written back —
 * **(C)** broken at the read, with the refusal surfacing on some later write rather than at the
 * declaration responsible for it. `withLegacyRead({ current: string('A'), whenMissing: 'B' })` is the whole of it.
 *
 * The stand-in is a **value and not a thunk**, which is what makes the check possible here rather
 * than on whichever read happens to need it first. A stand-in that the codec writes through a
 * {@link ref} that no scope binds is checked by the {@link scope} that binds the name. It does not become shared state for that: the
 * declaration holds one value and each read that needs one gets a copy of it, so a mutable stand-in
 * still cannot leak between entities. The copy keeps the class of each value, because a decode must
 * be writable: a `DynamoNumber` is shared, being immutable. Primitives are handed over as they are,
 * being unable to leak anything.
 */
const withMissing = <const C extends AnyCodec>(
    // the *argument's own* type, not a re-declared `AttributeCodec<T, A>`: the guard has to see the
    // marker the caller passed, and a parameter written in terms of inferred `T` and `A` reconstructs
    // a plain codec that never carries one
    inner: C,
    // `NoInfer` so the codec is the only thing that says what it holds. Inferring from both sites
    // unified them, and a stand-in written `'A'` widens to `string`, which then refused the very
    // codec it stands in for — invisible while the entity was declared first and pinned it itself
    value: NoInfer<Decoded<C>>,
): MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> => {
    // The rule `(withLegacyRead)`: the stand-in must be *writable*, or a row missing the name decodes to a
    // value the item cannot be written back as — (C) broken at the read, with the refusal arriving
    // on the next write instead of at the declaration that caused it. Decidable from the
    // declaration alone, which is why the stand-in is a value and not a thunk
    const standsFor = inner as unknown as AnyCodec
    const check = (): void => {
        let refusal: CodecError | undefined
        try {
            const written = standsFor.encode(value as never)
            refusal = failed(written) ? written : undefined
        } catch (thrown) {
            // a value outside the codec's type, which the codec reached past that type: as `accepts` reads it
            refusal = new CodecError(
                thrown instanceof Error ? thrown.message : String(thrown),
            )
        }
        if (refusal) {
            throw new CodecError(
                `\`withLegacyRead\`'s stand-in must be a value the codec it stands in for can write, and this \`${standsFor.def.kind}\` refuses the stand-in: ${refusal.message}. A row missing the attribute would read back as it and then refuse on the way out`,
            )
        }
    }
    // **A stand-in that the codec writes through an unbound `ref` waits for the scope** that binds
    // the ref, because the write reads through the ref
    whenBound([termOf(standsFor)], check)
    const attribute = inner as unknown as AttributeCodec<Decoded<C>>
    return {
        codec: attribute,
        def: { mark: 'fallback', t: termOf(inner), v: value },
    } as unknown as MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C>
}

/**
 * The refusal in the type of a wall argument whose term reaches an entry on a cycle. The overload
 * of `withLegacyRead` with a stand-in carries no refusal, because a stand-in alone builds no wall.
 * So an older reader beside a stand-in refuses at run time alone.
 */
type WallOver<W extends string, C> = [CycleEntryOf<TermOf<C>>] extends [never]
    ? unknown
    : ErrorMessage<`\`${W}\` reads '${CycleEntryOf<TermOf<C>> & string}', an entry on a cycle. A wall reaches no cycle`>

/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart: an attribute is **stored** as `S`, `N`, `SS` — and it is
 * **held**, in your code, as a `string`, a `Date`, an array. Every other combinator changes the first
 * or narrows the second. This one changes only the second, by naming the two halves of the
 * conversion, and leaves what the table holds exactly as it was.
 *
 * **Two restrictions, and a conversion between them.** `inner` restricts the stored side and
 * `outer` restricts the held side, which is the shape of `z.codec(in, out, { decode, encode })`.
 * The held type derives from `outer`, and `encode` and `decode` only transform.
 *
 * @example
 * ```ts
 * // stored as SS, held as an array
 * const tags = held(string.set(), array(string), {
 *     encode: (tags) => new Set(tags),
 *     decode: (tags) => [...tags],
 * })
 *
 * // stored as S, held as a Date, restricted by a schema of another library
 * const when = held(string, z.date(), {
 *     encode: (at) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * **The held side is checked on both halves.** `encode` runs only on a value that `outer` admits,
 * and the value that `decode` returns must pass `outer` too. A value outside `outer` is refused by
 * name, as a base codec refuses a value past its type, and the caller's `encode` never runs on it.
 * The model states the same codec: `through` the conversion, then restricted by the write domain of
 * `outer` on both halves, so the codec is lawful for every `outer`.
 *
 * **`outer` has two forms.** A codec of this library admits a value where its `encode` succeeds,
 * which is the admission `accepts` asks, and the term records the codec's term as the held side.
 * A schema of another library implements Standard Schema v1, and admits a value where `validate`
 * returns no issues. `validate` answers synchronously here, because a codec does. A `Promise` or a
 * throw becomes a refusal.
 *
 * **A foreign schema records the top as the held side.** The library cannot read which kinds of
 * value a foreign schema admits, so the write occupancy of this `held` is every kind. A `union`
 * with such an option has no certificate on the write side, and refuses where the other option
 * writes a kind. The runtime check still runs, so the codec refuses what the schema refuses.
 *
 * **Narrow the stored side in `inner`.** A conversion that can fail is two things at once, and
 * they compose better apart: narrow the inner codec first, so the failure is reported where the
 * value is actually wrong and with a message about it.
 *
 * ```ts
 * held(refine(string, isIsoDate, { describe: 'an ISO timestamp' }), z.date(), {
 *     encode: (at) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * The pair must round-trip — `decode(encode(x))` equal to `x`, and `encode(decode(y))` equal to `y` —
 * or the codec's own law does not hold either. `checkRoundTrip` over a spec holding one is what
 * establishes it, and generation reaches through: values are generated for the inner codec and
 * handed out through `decode`, so what is generated is always something the pair produced.
 *
 * **Nothing here checks it, and nothing here can.** The model carries it as `IsoCancels` — a
 * premise, in both directions: `g(f v) = v` wherever `f v` lands writable, and `f(g v) = v` on the
 * writable values themselves. It is a premise there for the same reason it is unchecked here. One
 * direction quantifies over the *held* type, which has no arbitrary except `decode` itself, so
 * every value this library could make is already in the pair's image; and probing the other at
 * construction is worse than not probing it, because a legitimate adapter is an isomorphism on the
 * values its inner codec describes and *throws* off them.
 *
 * So this is a written obligation, and `checkIso` is how a caller discharges it: it generates for
 * the inner codec and checks `encode(decode(y))`, which is the half a table depends on. The
 * failure mode it catches, unrefused today and pinned in `codec.laws.spec.ts`, is an adapter that
 * *normalises* — `{ encode: v => v.toUpperCase(), decode: v => v }` reads `'a'` back as `'A'`,
 * and every read-modify-write on that row rewrites the value.
 */
export const held = <
    const C extends AnyCodec,
    const O extends AnyCodec | StandardSchemaV1,
>(
    inner: C & WallOver<'held', C>,
    outer: O & WallOver<'held', O>,
    adapt: {
        /**
         * The value, as the inner codec holds it. Runs on the way to the table, on a value that
         * `outer` admits.
         *
         * Return a {@link CodecError} where the conversion has nothing to hand over — a value
         * outside the range the inner codec describes, or text that does not parse. That is a
         * refusal like any other and reaches the caller as one.
         */
        readonly encode: (value: HeldOf<O>) => Result<NoInfer<Decoded<C>>>
        /** What the inner codec read, as you hold it. Runs on the way back. Refuses the same way. */
        readonly decode: (held: Decoded<C>) => Result<NoInfer<HeldOf<O>>>
        /**
         * **How to generate one of these, where the pair is partial.**
         *
         * Omit both and the adapter derives them from the inner codec: a value is generated
         * there and handed out through `decode`, and a value is shrunk there and handed back.
         * That is right while the conversion accepts everything the inner codec produces.
         *
         * State them when it does not. A conversion that refuses part of the inner codec's range
         * makes the derived arbitrary offer values the pair never makes, so a property run fails
         * on the arbitrary instead of on the codec.
         */
        readonly arbitrary?: (rng: Rng, size: number) => HeldOf<O>
        /** How to shrink one, where the pair is partial. Derived from the inner codec otherwise. */
        readonly shrink?: (value: HeldOf<O>) => readonly HeldOf<O>[]
    },
): AttributeCodec<HeldOf<O>, AttributeOf<C>> &
    TermMark<
        HeldT<
            TermOf<C>,
            O extends StandardSchemaV1 ? ['opaq'] : TermOf<O>,
            ['caller']
        >
    > &
    Free<FreeOf<C> | FreeOf<O>> => {
    const side = heldSide(outer)
    const innerTerm = termOf(inner as unknown as AnyCodec)
    /**
     * **A half that cannot convert returns a `CodecError`**, and the signature says so. A refusal
     * is a value here, as it is everywhere else on this surface, so nothing about declining a
     * conversion is special and no caller has to catch.
     *
     * The two halves are still the one place in a codec where code this library did not write
     * runs, so the throw stays contained as a backstop rather than as the contract. A conversion
     * is ordinary code and ordinary code throws — `new Set(4)` for an adapter typed to take an
     * array, a `.toISOString()` on something that is not a `Date`. A codec that let that escape
     * would make every caller defensive about it, and one already was: a union tries an option to
     * find out whether it is the right one, and had to catch, which meant it also swallowed
     * failures that were nothing to do with an adapter.
     *
     * The check of `outer` runs inside the two halves, and not in `denote`'s row. The term
     * language carries a number as a `DynamoNumber`, so the term of `number` is a sound write
     * occupancy for the JS float adapter and a wrong membership test for it. A library adapter
     * checks the held side in its own conversion, and this checks the side the caller named.
     */
    return codecOfTerm<HeldOf<O>, AttributeOf<C>>({
        kind: 'held',
        inner: innerTerm,
        outer: side.term,
        f: (value: HeldOf<O>) =>
            side.admit(value, 'encode') ?? adapt.encode(value),
        g: (read: Decoded<C>) => {
            const out = adapt.decode(read)
            return failed(out) ? out : (side.admit(out, 'decode') ?? out)
        },
        arbitrary: adapt.arbitrary,
        shrink: adapt.shrink as
            | ((value: never) => readonly unknown[])
            | undefined,
    })
}

/** The held type of a `held`: the output of a foreign schema, or what a codec decodes. */
export type HeldOf<O> = O extends StandardSchemaV1
    ? StandardOutput<O>
    : Decoded<O>

/**
 * **The held side of a `held`**: the term it records, and the check that runs on each half.
 *
 * `admit` answers `undefined` for a value the side admits, and a refusal that names the side
 * otherwise. `at` names the half, because the value that `decode` returns is the caller's defect
 * and a value handed to `encode` past its type is the defect of the code that called.
 */
const heldSide = (
    outer: AnyCodec | StandardSchemaV1,
): {
    readonly term: Term
    readonly admit: (
        value: unknown,
        at: 'encode' | 'decode',
    ) => CodecError | undefined
} => {
    const refused = (at: 'encode' | 'decode', side: string, why: string) =>
        new CodecError(
            at === 'encode'
                ? `the held side of this \`held\`, ${side}, refuses the value before \`encode\` runs: ${why}`
                : `the held side of this \`held\`, ${side}, refuses the value that \`decode\` returned: ${why}`,
        )
    if (!('~standard' in outer)) {
        return {
            term: termOf(outer),
            // the admission `accepts` asks, encoded once so the refusal keeps the codec's reason.
            // `accepts` catches a throw for the same reason: an object codec reaches for `value.a`
            admit: (value, at) => {
                let written: unknown
                try {
                    written = outer.encode(value as never)
                } catch (thrown) {
                    written = new CodecError(
                        thrown instanceof Error
                            ? thrown.message
                            : String(thrown),
                    )
                }
                return failed(written)
                    ? refused(at, 'a codec of this library', written.reason)
                    : undefined
            },
        }
    }
    const { vendor, validate } = outer['~standard']
    const side = `a ${vendor} schema`
    return {
        /**
         * **The top, because the held side is not this library's to rule.** A foreign schema has
         * a runtime face, `validate`, and no static face: nothing here can read which kinds of
         * value it admits. `opaque` is the term that admits every kind, so the write occupancy is
         * the honest upper bound, and a certificate that needs a smaller one is refused. The
         * runtime check below still restricts the codec to what the schema admits.
         */
        term: { kind: 'opaq' },
        admit: (value, at) => {
            // the boundary: `validate` is code of another library, so a throw and a malformed
            // answer each become a refusal here, and nothing past this line catches
            try {
                const answer = validate(value)
                if (answer instanceof Promise) {
                    return refused(
                        at,
                        side,
                        '`validate` answered with a Promise, and a codec answers synchronously, so the value has no verdict',
                    )
                }
                return answer.issues === undefined
                    ? undefined
                    : refused(
                          at,
                          side,
                          answer.issues
                              .map((issue) => issue.message)
                              .join('; ') ||
                              'the schema reported an issue with no message',
                      )
            } catch (thrown) {
                return refused(
                    at,
                    side,
                    `\`validate\` threw: ${thrown instanceof Error ? thrown.message : String(thrown)}`,
                )
            }
        },
    }
}

/**
 * One direction, which is all an older encoding is ever asked for.
 *
 * `withLegacyRead` never writes through `older` — that is the whole of what makes it a migration rather than
 * a union — so asking for a whole codec there asked for a half nobody calls. It also *forced* one:
 * an older encoding whose held type differs from the current one has to be adapted, and {@link held}
 * requires both halves, so adapting a reader meant writing an encode path that is dead by
 * construction. Every `AttributeCodec<T>` is one of these, so nothing that worked stops working.
 *
 * @example
 * ```ts
 * // stored as N now; some rows still hold the digits as B, from a migration nobody finished
 * withLegacyRead({
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
 * **One older encoding.** A table that has held three needs two of these, nested — and `withLegacyRead` is
 * itself a {@link Reader}, so it nests directly:
 *
 * ```ts
 * withLegacyRead({ current: decimal, older: withLegacyRead({ current: string, older: fromBytes }) })
 * ```
 *
 * Not a union: {@link union} requires its options to read back as *different* types so that a value
 * says which one it is, and every encoding of one attribute reads back as the same type by
 * definition. Which is the whole difference between the two — a union asks "which of these is it",
 * a migration asks "can any of these still read it".
 *
 * ```ts
 * // stored as N today, and as S in rows written before that; always written as N
 * rate: withLegacyRead({ current: decimal, older: string })
 * ```
 *
 * **Two things the rule `(withLegacyRead)` asks of the older reader**, and only one of them is checkable.
 *
 * `ran(r) ⊆ dom(e)` — a migration lands on values the current encoding can *write*. This is
 * checked, per read, as soon as the older reader has answered, because that is the earliest
 * anything can know what it returns. The model reads the same way (`Codec.extendRead`), so there
 * the containment is the construction and not a premise. Unchecked it read a row and refused on
 * the way out, which is **(C)** broken at the migrated row and reported at some later write.
 *
 * Coherence (`ReadsCoherently`) — where both readers read an attribute, and the current encoding
 * can write the older answer, they agree — is **not**
 * checkable, and the reason is sharper than that. The current encoding is tried first and the older one only on its
 * failure, here and in the model (`Codec.extendRead`), so on `dom(p_current)` the older reader is
 * never consulted and a disagreement has no observable consequence at all. What the premise buys
 * is that the *ordering does not matter*: with it, and only with it, this presentation equals the order-free
 * union of `p` and the checked older reading. Without it the reading depends on declaration
 * order, which is the one thing that resolution never does. So it is a written obligation, and the thing to check is that two
 * readers of one attribute agree — nothing in this library will tell you they do not.
 */
export type WithLegacyReadOptions<C extends AnyCodec> = {
    readonly current: C
} & (
    | {
          readonly older: Reader<Decoded<C>>
          readonly whenMissing?: NoInfer<Decoded<C>>
      }
    | {
          readonly older?: Reader<Decoded<C>>
          readonly whenMissing: NoInfer<Decoded<C>>
      }
)

/**
 * Reads an older attribute encoding or a missing object attribute.
 *
 * `older` extends an attribute codec's read side. `whenMissing` declares an object slot, because
 * absence belongs to an object map and no attribute codec can read an absent attribute.
 */
export function withLegacyRead<const C extends AnyCodec>(options: {
    readonly current: C & WallOver<'withLegacyRead', C>
    readonly older: Reader<Decoded<C>>
    readonly whenMissing?: never
}): AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue> &
    TermMark<['legacy', TermOf<C>]> &
    Free<FreeOf<C>>
export function withLegacyRead<const C extends AnyCodec>(options: {
    readonly current: C
    readonly older?: Reader<Decoded<C>>
    readonly whenMissing: NoInfer<Decoded<C>>
}): MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> &
    TermMark<['fill', TermOf<C>]> &
    Free<FreeOf<C>>
export function withLegacyRead<const C extends AnyCodec>(
    options: WithLegacyReadOptions<C>,
):
    | AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue>
    | MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> {
    const { current, older } = options
    const currentCodec = current as unknown as AttributeCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue
    >
    const extended = older
        ? codecOfTerm<Decoded<C>, AttributeOf<C> & AttributeValue>({
              kind: 'legacy',
              inner: termOf(current),
              r: older.decode,
          })
        : currentCodec
    return (
        'whenMissing' in options
            ? withMissing(extended, options.whenMissing as Decoded<C>)
            : extended
    ) as
        | AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue>
        | MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C>
}

/*
 * **A cycle is a name in one declaration.** `ref(name)` is the reference, and its term is the
 * name. `scope(defs)` binds each name of `defs`. The term of an entry is `['scope', D, K]`: the
 * record `D` of the terms of the definitions, and the name `K`. A `ref` resolves by one lookup
 * in `D`, so the type substitutes nothing and copies nothing. The decoded type of an entry is a
 * function of that term, so no caller states the decoded type of a cycle.
 *
 * At run time, a `ref` is a node that carries a slot, and `scope` fills the slot. Each former that
 * runs before `scope` reads the `ref` as unbound. So a cycle of the term graph passes through a `ref`.
 */
type Ref<N extends string> = AttributeCodec<unknown> &
    TermMark<['ref', N]> &
    Free<N>
type ScopeTerms<Defs> = { -readonly [K in keyof Defs]: TermOf<Defs[K]> }
type ScopeTerm<Defs, K> = ['scope', ScopeTerms<Defs>, K]
type ScopeOf<Defs> = {
    readonly [K in keyof Defs]: EntryOf<
        DefOf<Defs, Defs[K]>,
        ScopeTerm<Defs, K>,
        Defs
    >
}
/**
 * **The definition that a codec names in a scope**: the codec, or the definition at the end of its
 * chain of `ref`s. A chain that returns to a name it passed keeps the codec, and the guard refuses
 * the scope.
 */
type DefOf<Defs, C, Seen = never> = TermOf<C> extends [
    'ref',
    infer N extends keyof Defs,
]
    ? [N] extends [Seen]
        ? C
        : DefOf<Defs, Defs[N], Seen | N>
    : C
/**
 * An entry: the codec of the definition that the entry names, read at the term `Tm` of the entry.
 * An object keeps its item, and a union keeps its item and its slices, each typed from the term.
 * Each option of a union is the definition that the option names, so a slice reads a `ref` option
 * as the definition. Any other entry keeps the `.set()` of an element that writes `S`, `N` or `B`,
 * and a dissection keeps its options in declared order, each the definition that the option names.
 */
type EntryOf<C, Tm, Defs> = C extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    infer Rest extends AnyCodec | undefined
>
    ? ObjectCodec<Spec, Rest, DecodeTerm<Tm>, Tm>
    : C extends UnionCodec<infer _T, infer Options extends readonly unknown[]>
      ? UnionCodec<
            DecodeTerm<Tm>,
            { [I in keyof Options]: DefOf<Defs, Options[I]> },
            Tm
        > &
            LiteralMarkOf<C>
      : AttributeCodec<DecodeTerm<Tm>, AttributeOf<C> & AttributeValue> &
            LiteralMarkOf<C> &
            TermMark<Tm> &
            SetCapable<DecodeTerm<Tm>, AttributeOf<C> & AttributeValue, Tm> &
            (C extends OptionsMark<infer Os extends readonly unknown[]>
                ? OptionsMark<{ [I in keyof Os]: DefOf<Defs, Os[I]> }>
                : unknown)
/** A refusal on each definition that reads a name the scope does not declare. */
type ScopeNamed<Defs> = {
    readonly [K in keyof Defs]: [Exclude<FreeOf<Defs[K]>, keyof Defs>] extends [
        never,
    ]
        ? unknown
        : ErrorMessage<`[scope] a ref names '${Exclude<FreeOf<Defs[K]>, keyof Defs> & string}', which this scope does not declare`>
}

/** A refusal on each definition that holds a wall over an entry on a cycle of this scope. */
type ScopeWalls<Defs> = {
    readonly [K in keyof Defs]: [
        ScopeWallCycle<ScopeTerms<Defs>, TermOf<Defs[K]>>,
    ] extends [never]
        ? unknown
        : ErrorMessage<`[scope] a wall in '${K & string}' reads '${ScopeWallCycle<ScopeTerms<Defs>, TermOf<Defs[K]>> & string}', an entry on a cycle. A wall reaches no cycle`>
}

/**
 * A reference of a {@link scope}. The `ref` names an entry of the scope that holds it, and reads as
 * the codec of that entry.
 */
export function ref<const N extends string>(name: N): Ref<N>
export function ref(name: string): unknown {
    return codecOfTerm({ kind: 'ref', slot: { name, waiting: [] } })
}

/**
 * **Codecs that name each other**, each one an entry. A {@link ref} in a definition names an entry,
 * and the decoded type of each entry follows from the definitions, with no annotation. A single
 * cycle is a scope of one entry.
 *
 * Each former ran before the names were bound, so the guard runs here: a recursion with no
 * container on its path, or with an adapter on its path, is refused. A `ref` to a name that `defs`
 * does not declare is refused. Then each check that waits on a bound name runs: the check of a
 * `union` with a `ref` option, which a `nullable` over a `ref` builds, the index of a dissection
 * whose tag reads a `ref`, and the stand-in of a `withLegacyRead` that writes through a `ref`.
 *
 * **A scope binds and closes.** Each entry has no free name, in the type and at run time, so each
 * entry is a codec to use. A scope that refuses binds no name, so each fragment that it held stays
 * open and refuses each use.
 *
 * @example
 * ```ts
 * const { Folder } = scope({
 *     Folder: object({ name: string, children: array(ref('Node')) }),
 *     Node: union([object({ file: string }), ref('Folder')]),
 * })
 * ```
 */
export function scope<const Defs extends Readonly<Record<string, AnyCodec>>>(
    defs: Defs & ScopeNamed<Defs> & ScopeWalls<Defs>,
): ScopeOf<Defs>
export function scope(defs: Readonly<Record<string, AnyCodec>>): unknown {
    const terms = Object.fromEntries(
        Object.entries(defs).map(([name, def]) => [name, termOf(def)]),
    )
    const slots = unboundRefs(Object.values(terms))
    for (const slot of slots)
        if (!Object.hasOwn(defs, slot.name))
            throw new CodecError(
                `[scope] a ref names '${slot.name}', which this scope does not declare`,
            )
    for (const slot of slots) {
        slot.bound = terms
        slot.refused = false
    }
    // **A refused scope binds no name**, so each fragment it held stays open and refuses each use.
    // The refusal of the guard carries the term of the entry, so a checker states the model's
    // guard on that term
    try {
        for (const [name, t] of Object.entries(terms)) {
            const refused = guard(t, name)
            if (refused) throw refused
        }
        for (const check of new Set([...slots].flatMap((slot) => slot.waiting)))
            check()
    } catch (thrown) {
        refuseSlots(slots)
        throw thrown
    }
    // **An entry carries the `.set()` of the node that its chain of `ref`s names**, as its type
    // does. A `ref` and a literal carry no `.set()` of their own, so such an entry builds the set
    // of itself, and the judgment of the set refuses an element that writes no `S`, `N` or `B`. An
    // object and a union write `M` or no single member, so their entries stay as declared
    return Object.fromEntries(
        Object.entries(defs).map(([name, def]) => {
            const kind = terms[name]?.kind
            return [
                name,
                'set' in def || kind === 'object' || kind === 'union'
                    ? def
                    : { ...def, set: () => set(def) },
            ]
        }),
    )
}

// ── presence ────────────────────────────────────────────────────────

/**
 * An attribute that may be absent — which is not the same as null. `{ NULL: true }` is an attribute
 * DynamoDB *has*; use {@link nullable} for that.
 *
 * `undefined` is not injective in: `{ a: undefined }` and `{}` both encode without `a`.
 *
 * **A name is the only thing this can be said of**, so the result goes in an object's spec and
 * nowhere else. A list, a set, a tuple, an open block and a union option have no name at that position for
 * anything to be missing from, and each of those refuses this because a field is not a codec — the
 * member for a value that may be stored as `NULL` in one of them is {@link nullable}. Marking a
 * marked declaration is refused the same way: `withLegacyRead({ current: c, whenMissing: v })` is the attribute that may be absent
 * and has a stand-in, and it is what both nestings meant.
 */
export const optional = <const C extends AnyCodec>(
    inner: C,
): OptionalCodec<Decoded<C>, AttributeOf<C>, C> &
    TermMark<['optional', TermOf<C>]> => {
    // the marked codec beside the definition, not a copy of the codec with a definition stamped on
    // it: a field has no pair of its own, and spreading one gave it the pair of the codec it marks.
    // `inner` itself, so the mark carries the codec the caller passed and not its erasure
    // one assertion, and it cannot come off. `optionalMarker` is a `declare const` symbol, so it
    // exists in the type and nowhere a literal can write it: removing the assertion reports
    // "Property '[optionalMarker]' is missing". It is `rest`'s spelling for `rest`'s reason
    return {
        codec: inner,
        def: { mark: 'optional', t: termOf(inner) },
    } as unknown as OptionalCodec<Decoded<C>, AttributeOf<C>, C>
}

/**
 * A key that is always present, holding `undefined` when the row carries no such attribute.
 *
 * The mark for a model that writes `k: T | undefined` rather than `k?: T`. Both describe the same
 * row, and they are different TypeScript types, which is the whole of the difference from
 * {@link optional}.
 *
 * ```ts
 * object({ tags: undefinable(string.set()) })   // { tags: ReadonlySet<string> | undefined }
 * object({ tags: optional(string.set()) })      // { tags?: ReadonlySet<string> }
 * ```
 *
 * **It stores nothing, and never `NULL`** — {@link nullable} is the codec for a value that *is*
 * null and writes an attribute; this writes none.
 *
 * It is the stricter of the pair: `optional` reads both `{}` and `{ k: undefined }` back as `{}`,
 * so **(R)** holds for it modulo that identification, while here the round trip is an equality. It
 * takes on no premise of its own — unlike {@link withLegacyRead}, which must check its stand-in is
 * writable because it writes one.
 */
export const undefinable = <const C extends AnyCodec>(
    inner: C,
): UndefinableCodec<Decoded<C>, AttributeOf<C>, C> &
    TermMark<['optional', TermOf<C>]> =>
    ({
        codec: inner,
        def: { mark: 'undefinable', t: termOf(inner) },
    }) as unknown as UndefinableCodec<Decoded<C>, AttributeOf<C>, C>

/**
 * A value that may be null, stored as `NULL` when it is — **unless `inner` already owns the null
 * point**, in which case this is `inner`'s own pair, untouched.
 *
 * Without the guard the wrapper's `NULL` branch shadows the inner codec, and **(R)** fails on a
 * term the specification proves lawful: `nullable(held(nullable(string), string, adapter))`, where the
 * adapter maps `'SENTINEL'` to `null`, writes `{ NULL: true }` for `'SENTINEL'` and reads back
 * `null`. The value written is not the value read. No declaration in this repository builds that
 * term and `held` is unemittable, so no generated vector could ever have found it.
 *
 * Where the guard does *not* fire, null-honesty is a theorem rather than an assumption: an
 * `inner` that wrote `⟨NULL, ∗⟩` would read it straight back by **(R)** and so would own the
 * point, and one that read some attribute to `null` would write the point by **(C)** and own it
 * again. Both hypotheses are refuted by the guard rather than required of the caller.
 *
 * **The question is asked once, at construction.** The term answers the question, and an answer
 * that the term does not determine is a refusal. **A {@link ref} that no scope binds yet leaves the
 * question open**: the codec is then the {@link union} with `NULL`, and the {@link scope} that binds
 * the name runs the check of the union. A `ref` to an entry that owns the null point fails the
 * check there, because two options then write `NULL`.
 */
export const nullable = <
    T,
    A extends AttributeValue,
    Tm = FreeTerm,
    F extends string = never,
>(
    inner: AttributeCodec<T, A> & TermMark<Tm> & Free<F>,
): AttributeCodec<T | null, A | Attribute<'NULL'>> &
    TermMark<['union', [Tm, BaseT<'null'>]]> &
    Free<F> => {
    const t = termOf(inner as unknown as AnyCodec)
    const owns = ownsNullOf(t)
    // **An unbound `ref` leaves the answer open**: the codec is the union with `NULL`, an open
    // fragment, and the union's check waits for the scope that binds the names. A `ref` whose
    // entry owns the null point fails that check, as a second option that writes `NULL`
    if (owns === undefined && unboundRefs([t]).size > 0)
        return codecOfTerm<T | null, A | Attribute<'NULL'>>(
            union([inner, nullValue]).def,
        )
    if (owns === undefined) {
        throw new CodecError(
            `nullable: ${t.kind} decides the null point by running a function this cannot read, ` +
                'so whether the union would be certified is unknown. ' +
                'Write the wrapper inside instead, as in held(nullable(inner), outer, adapter).',
        )
    }
    if (owns) return inner as AttributeCodec<T | null, A | Attribute<'NULL'>>
    // a term that holds no value adds no option to the null point, so the union is `NULL` itself,
    // read at the node that the term names
    if (holdsNoValue(t)) {
        return nullValue as AttributeCodec<T | null, A | Attribute<'NULL'>>
    }
    return codecOfTerm<T | null, A | Attribute<'NULL'>>({
        kind: 'union',
        options: [t, { kind: 'null' }],
    })
}

// ── the escape hatch ────────────────────────────────────────────────

const canonicalOpaque = codecOfTerm<unknown, AttributeValue>(
    opaqueTerms.canonical,
)
const opaquePolicies: {
    readonly [Of in opaque.Numbers]: AttributeCodec<unknown>
} = {
    lossy: codecOfTerm<unknown, AttributeValue>(opaqueTerms.lossy),
    refuse: codecOfTerm<unknown, AttributeValue>(opaqueTerms.refuse),
}

function opaqueOf(): AttributeCodec<unknown> & TermMark<['opaq']>
function opaqueOf(
    numbers: 'lossy',
): AttributeCodec<unknown> &
    TermMark<HeldT<['opaq'], ['opaq'], ['caller', 'opaqueLossy']>>
function opaqueOf(
    numbers: 'refuse',
): AttributeCodec<unknown> &
    TermMark<HeldT<['opaq'], EveryButNumberT, ['caller', 'opaqueRefuse']>>
function opaqueOf(numbers?: opaque.Numbers): AttributeCodec<unknown>
function opaqueOf(numbers?: opaque.Numbers): AttributeCodec<unknown> {
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
    export type Numbers = 'refuse' | 'lossy'

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
export type PathOf<T, F = unknown> = PathTerminal<T> &
    PathBody<NonNullable<T>, F>

type PathBody<T, F> = [T] extends [readonly unknown[]]
    ? // a list that holds no value offers no position, as the walk answers a position of it as vacant
      [T[number]] extends [never]
        ? Record<never, never>
        : PathList<T[number]>
    : [T] extends [object]
      ? {
            readonly [K in UnionKeys<T>]: PathOf<ValueAt<T, K>, ChildAt<F, K>>
        } & PathRecord<T> &
            PathNarrowing<T, F>
      : Record<never, never>

/**
 * **The frontier of a path, where the path type knows the codecs**: one record per member, with
 * the spec of the member, its open entry, and its decoded type. `unknown` is a frontier that the
 * type does not know, and `unknown` absorbs every union, so one unknown member makes the frontier
 * unknown. A list, an adapter and a `ref` carry no codec of a child in their types, so the
 * frontier below one is unknown.
 */
type Member = {
    readonly spec: unknown
    readonly rest: unknown
    readonly t: unknown
}

/** The members of a codec: each option of a union, each variant of a tagged union, or the object. */
type MembersOf<C> = C extends UnionCodec<infer _T, infer Options>
    ? MembersOf<Options[number]>
    : C extends DiscriminatedCodec<infer T, infer D, infer Table>
      ? {
            [V in keyof Table]: {
                readonly spec: Table[V]
                readonly rest: undefined
                readonly t: VariantOf<T, D & keyof T, V>
            }
        }[keyof Table]
      : C extends {
              readonly item: {
                  readonly spec: infer Spec
                  readonly rest: infer Rest
              }
          }
        ? { readonly spec: Spec; readonly rest: Rest; readonly t: Decoded<C> }
        : unknown

/** The frontier at the root of an item: the one member that its spec declares. */
type ItemFrontier<T, Spec, Rest> = {
    readonly spec: Spec
    readonly rest: Rest
    readonly t: T
}

/** The codec that a field of a spec marks, or the codec itself. */
type MarkedCodec<C> = C extends { readonly codec: infer Marked } ? Marked : C

/** The codec that a member holds at a key: the declared field, then the open entry. */
type CodecAt<M, K> = M extends Member
    ? K extends keyof M['spec']
        ? MarkedCodec<M['spec'][K]>
        : M['rest'] extends AnyCodec
          ? M['rest']
          : never
    : unknown

/** The frontier one key down. A key that no known member holds gives an unknown frontier. */
type ChildAt<F, K> = unknown extends F
    ? unknown
    : MembersOf<CodecAt<F, K>> extends infer Next
      ? [Next] extends [never]
          ? unknown
          : Next
      : unknown

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
 * Picking the members of a union that a clause does not separate, before walking further.
 *
 * Merging every member's keys works while the members are objects, and stops working where they
 * disagree about *kind* — a key holding an object in one and a string in another merges to neither.
 *
 * `narrow` adds no segment to the path. The walk of {@link ItemCodec.at} narrows its frontier by the
 * clause. Only present on a union.
 *
 * @example
 * ```ts
 * p.priceIn.narrow({ tenderType: string('CASH') }).cardId   // → 'priceIn.cardId'
 * ```
 */
type PathNarrowing<T, F> = IsUnion<T> extends true
    ? {
          /**
           * **Narrows the path at run time and in the type, to the members that the clause does not
           * separate.** The clause is an object
           * of codecs: each key is required at the term of its codec, and every other name is open.
           *
           * A member stays where the clause cannot tell it apart. A pin `'A' | 'B'` stays under the
           * clause `'A'`, and a member with no pin at the key stays too. The walk of `at` separates
           * on the stored views, so `number(1)` and `decimal('1')` meet, and `decimal` and
           * `string` are apart. Where the path knows the codecs, this type separates on the stored
           * attributes too ({@link Kept}). Below a list, an adapter or a `ref`, and in the path of a
           * `tableEntry`, the type knows only the decoded types and is coarser ({@link Narrowed}).
           */
          narrow<const C extends Readonly<Record<string, AnyCodec>>>(
              clause: C & ClauseOn<T, F, C>,
          ): unknown extends F
              ? PathOf<Narrowed<T, C>>
              : PathOf<Kept<F, C>['t'], Kept<F, C>>
      }
    : unknown

/**
 * **The members of a known frontier that a clause does not separate**, as the walk of `at` decides
 * it: on the stored side. A member goes where, at one key of the clause, the member holds no codec,
 * or the codec of the member and the codec of the clause are apart ({@link StoredApart}).
 */
type Kept<F, C> = F extends Member
    ? true extends {
          [K in keyof C]: [CodecAt<F, K>] extends [never]
              ? true
              : StoredApart<CodecAt<F, K>, C[K]>
      }[keyof C]
        ? never
        : F
    : never

/**
 * **Two codecs whose stored attributes cannot meet**: the members of DynamoDB that the two write
 * share none, or each pins literals and the two pins share no stored value. The stored attribute
 * of an adapter is the attribute of its inner codec, so `number` and `decimal` each write `N`, and
 * `number(1)` and `decimal('1')` each store the text `1`. A codec pins literals only where a literal
 * constructor built it ({@link literalMarker}), so a caller's adapter pins nothing here.
 *
 * Coarser than the walk of `at` in two places: two maps or two lists are never apart here, and a
 * caller's adapter over a literal pins nothing here, where the walk reads the literal under it.
 */
type StoredApart<X, Y> = [
    WrittenMembers<AttributeOf<X>> & WrittenMembers<AttributeOf<Y>>,
] extends [never]
    ? true
    : [StoredPin<X>] extends [never]
      ? false
      : [StoredPin<Y>] extends [never]
        ? false
        : [StoredPin<X> & StoredPin<Y>] extends [never]
          ? true
          : false

/** The members of DynamoDB that an attribute type writes: the keys that it requires. */
type WrittenMembers<A> = A extends unknown
    ? {
          [K in keyof A]-?: undefined extends A[K] ? never : K
      }[keyof A]
    : never

/** The stored text of a literal, or `never` where no literal constructor built the codec. */
type StoredPin<C> = C extends LiteralMark ? StoredText<Decoded<C>> : never

/** The stored text of a literal, or `never` where the decoded type is not a literal. */
type StoredText<D> = D extends string | number | boolean
    ? string extends D
        ? never
        : number extends D
          ? never
          : boolean extends D
            ? never
            : `${D}`
    : never

/**
 * **The members that a clause does not separate, on the decoded types**: the filter where the path
 * type knows no codec, as in the path of a `tableEntry`. A member goes where, at one key of the
 * clause, the member declares no such key and holds no index signature, or the value at the key
 * shares no value with what the clause's codec decodes.
 */
type Narrowed<T, C> = T extends unknown
    ? true extends SeparatedAt<T, C>[keyof C]
        ? never
        : T
    : never

/** Whether the clause separates the member at each key of the clause. */
type SeparatedAt<T, C> = {
    [K in keyof C]: K extends keyof T
        ? [T[K] & Decoded<C[K]>] extends [never]
            ? true
            : false
        : true
}

/**
 * Nothing, or why a clause names nothing: a key that no member declares, or a clause that separates
 * every member.
 */
type ClauseOn<T, F, C> = [Exclude<keyof C, UnionKeys<T>>] extends [never]
    ? [unknown extends F ? Narrowed<T, C> : Kept<F, C>] extends [never]
        ? ErrorMessage<'[narrow] the clause separates every member of this union'>
        : unknown
    : ErrorMessage<`[narrow] no member of this union declares '${Exclude<
          keyof C,
          UnionKeys<T>
      > &
          string}'`>

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

/*
 * **The selector of `at`, read from the term.** A node holds the frames of `Term.at` at its path.
 * The node offers each name that a head declares, each name where a head is open, and each
 * position where a head is a list. The decision of the node is `pathKind` of its frames, and the
 * selector admits a node where the decision is one codec. The decoded type at the node is a
 * function of its first frame. `T` and `F` follow the path as the decoded type and the frontier,
 * so a key or an index that is no literal keeps the typing of {@link PathOf}, and so does a
 * `narrow` over a codec whose type carries no term.
 */
declare const pathKindMarker: unique symbol
type PathResolved = { readonly [pathKindMarker]?: 'resolved' }
declare const pathEncoded: unique symbol
/**
 * The attribute that the codec at a node writes, as a phantom: a function of the first frame,
 * where the node resolves. The root of an item is the item codec, which writes a row and no
 * attribute, so the root keeps the wide `AttributeValue`.
 */
type PathEncoded<A> = { readonly [pathEncoded]?: A }
type TermPath<Fs, T, F, Root = false> = PathTerminal<TermPathValue<Fs>> &
    PathEncoded<Root extends true ? AttributeValue : TermPathEncoded<Fs>> & {
        readonly [pathKindMarker]?: KindOfFrames<Fs>
    } & TermPathBody<Fs, NonNullable<T>, F, OffersAt<Fs>, Root>
type TermPathValue<Fs> = KindOfFrames<Fs> extends 'resolved'
    ? DecodeFrame<FirstFrame<Fs>>
    : never
type TermPathEncoded<Fs> = KindOfFrames<Fs> extends 'resolved'
    ? EncodedFrame<FirstFrame<Fs>>
    : never
type TermPathBody<Fs, T, F, O, Root> = {
    readonly [K in Extract<O, ['name', unknown]>[1] & string]: TermPath<
        StepFrames<['name', K], Fs>,
        ValueAt<T, K>,
        ChildAt<F, K>
    >
} & ([Extract<O, ['open']>] extends [never]
    ? unknown
    : { readonly [name: string]: PathOf<ValueAt<T, string>> } & {
          at<const K extends string>(
              key: K,
          ): string extends K
              ? PathOf<ValueAt<T, string>>
              : TermPath<
                    StepFrames<['name', K], Fs>,
                    ValueAt<T, K>,
                    ChildAt<F, K>
                >
          /** An open name, selected by a method, so the step adds no `| undefined`. */
          entry<const K extends string>(
              key: K,
          ): TermPath<StepFrames<['name', K], Fs>, ValueAt<T, K>, ChildAt<F, K>>
      }) &
    ([Extract<O, ['pos']>] extends [never]
        ? unknown
        : { readonly [index: number]: PathOf<ElementOf<T>> } & {
              at<const I extends number>(
                  index: I,
              ): number extends I
                  ? PathOf<ElementOf<T>>
                  : TermPath<StepFrames<['pos', I], Fs>, ElementOf<T>, unknown>
          }) &
    TodayNarrowing<T, F, Fs, Root>
type ElementOf<T> = T extends readonly unknown[] ? T[number] : never
/**
 * `narrow` at a node. A node that holds frames offers {@link TermNarrowing}, whatever its decoded
 * type, because the frames decide the clause. A node whose type carries no term offers
 * {@link PathNarrowing} where {@link PathOf} offers it: on an object type that is no list.
 */
type TodayNarrowing<T, F, Fs, Root> = HoldsFree<Fs> extends true
    ? [T] extends [readonly unknown[]]
        ? unknown
        : [T] extends [object]
          ? PathNarrowing<T, F>
          : unknown
    : TermNarrowing<Fs, Root>
/**
 * {@link PathNarrowing}, where the node holds frames, and read on the terms alone: the narrowed node
 * holds the options that the clause keeps ({@link NarrowFrames}), so its decision is the decision of
 * the walk of `at`. The clause is refused where it keeps no option of the frames, as the walk refuses
 * it. The decoded type of the narrowed node is the decoded type of the kept frames.
 */
type TermNarrowing<Fs, Root> = {
    narrow<
        const C extends Readonly<Record<string, AnyCodec>>,
        K = NarrowFrames<Fs, ClauseTerms<C>>,
    >(
        clause: C & ClauseOnFrames<K>,
    ): TermPath<K, DecodeFrames<K>, unknown, Root>
}
/** The decoded type of the codecs at the frames of a node. */
type DecodeFrames<Fs> = Fs extends unknown[]
    ? { [I in keyof Fs]: DecodeFrame<Fs[I]> }[number]
    : never
type ClauseTerms<C> = { [K in keyof C]: TermOf<C[K]> }
/** Nothing, or why the clause keeps no option: `K` holds the frames that the clause keeps. */
type ClauseOnFrames<K> = K extends []
    ? ErrorMessage<'[narrow] the clause separates every member of this union'>
    : unknown

// ── items ───────────────────────────────────────────────────────────

/** The decoded type `T` of an object codec, or the entity that its spec describes. */
type ItemOf<T, Spec, Rest> = [T] extends [OfParts] ? DerivedItem<Spec, Rest> : T

/**
 * The entity a spec describes.
 *
 * An absent rest says the row holds nothing else, so the entity is closed. A rest codec says it
 * holds anything that codec can read, which is exactly an index signature — the mirror of
 * what {@link EncodedBy} does to the stored shape.
 */
type DerivedItem<Spec, Rest> = [Rest] extends [undefined]
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
    Spec extends Record<string, ObjectSlot>,
    Rest extends AnyCodec | undefined = undefined,
    // the decoded type and the term: an entry of a `scope` reads both from the term of the entry
    T = OfParts,
    Tm = OfParts,
> = {
    // spelled out rather than intersected with `AttributeCodec`, for the reason recorded on
    // {@link ItemCodec}: as an intersection the same type costs more to instantiate and stops being
    // *comparable* to a hand-written shape. Measured at +14k instantiations across this repo
    readonly encode: (
        this: Closed,
        value: ItemOf<T, Spec, Rest>,
    ) => Result<M<EncodedBy<Spec, Rest>>>
    readonly decode: (
        this: Closed,
        attribute: AttributeValue,
    ) => Result<ItemOf<T, Spec, Rest>>
    readonly unsafeEncode: (
        this: Closed,
        value: ItemOf<T, Spec, Rest>,
    ) => M<EncodedBy<Spec, Rest>>
    readonly unsafeDecode: (
        this: Closed,
        attribute: AttributeValue,
    ) => ItemOf<T, Spec, Rest>
    readonly def: Term
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
    readonly item: ItemCodec<ItemOf<T, Spec, Rest>, Spec, Rest, Tm> &
        Free<ObjectFree<Spec, Rest, Tm>>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
    /** The model's term of this codec. Type-level only. */
    readonly [termMarker]?: [Tm] extends [OfParts]
        ? ObjectTermOf<Spec, Rest>
        : Tm
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [ObjectFree<Spec, Rest, Tm>]
}

/**
 * A union of objects, and the same union read as a whole item.
 *
 * Only a union of *objects* has an item reading: an item is a map, so a union that could also be an
 * `S` or an `L` is an attribute and nothing else. Which is why this is what the two union
 * constructors return, rather than what `union` is constrained to accept.
 */
export type DiscriminatedCodec<
    T,
    D extends string,
    Spec,
    F extends string = never,
> = {
    readonly encode: (this: Closed, value: T) => Result<Attribute<'M'>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => Attribute<'M'>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    readonly item: Tagged<T, D, Spec> & Free<F>
    /**
     * **The members a clause keeps**, over the same keys — or `never` where it keeps none.
     *
     * `Spec` does not shrink with `T`. A member the clause dropped is still keyed in the table, and
     * asking for it gives an `ItemCodec<never>`: the entity type is what the slice narrows, and the
     * runtime is what refuses the assignment. Narrowing the table too would need the spec list
     * filtered in step with the entity union, and the two are matched by their decoded types rather
     * than positionally.
     */
    readonly extract: <const P extends AnyCodec>(
        this: Closed,
        pattern: P & ValidatePattern<Spec[keyof Spec], P>,
    ) => DiscriminatedCodec<
        VariantsOf<KeptByTag<Spec, P>>,
        D,
        KeptByTag<Spec, P>
    >
    /** …and the members it rejects, the complement of the same pattern. */
    readonly exclude: <const P extends AnyCodec>(
        this: Closed,
        pattern: P & ValidatePattern<Spec[keyof Spec], P>,
    ) => DiscriminatedCodec<
        VariantsOf<KeptByTag<Spec, P, false>>,
        D,
        KeptByTag<Spec, P, false>
    >
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [F]
}

/**
 * A dissection read as a whole item: the members, chosen by an assignment.
 *
 * {@link Tagged} at several discriminators. One field moves, because there is no single
 * discriminator to name: `keys` holds the key set where `discriminator` held the one name.
 *
 * `spec` is the members' specs as the caller declared them. There is no string to key them by: a
 * key would be a rendering of an assignment, and a rendering is an order.
 */
export type Dissected<
    T,
    Ks extends readonly string[],
    Specs extends readonly unknown[],
> = {
    /** Every attribute, or why one could not be written. */
    readonly encode: (this: Closed, item: T) => Result<AttributeMap>
    readonly unsafeEncode: (this: Closed, item: T) => AttributeMap
    /** The attributes a patch names. Every discriminator is required: they choose the codec. */
    readonly encodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, Ks[number] & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, Ks[number] & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    readonly keys: Ks
    readonly spec: Specs
    /** What this codec is — see {@link Term}. */
    readonly def: Term
}

/** {@link Dissected} with the top-level `M` back on, which is what a `dunion` codec is. */
export type DissectedCodec<
    T,
    Ks extends readonly string[],
    Specs extends readonly unknown[],
    F extends string = never,
> = {
    readonly encode: (this: Closed, value: T) => Result<Attribute<'M'>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => Attribute<'M'>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    readonly item: Dissected<T, Ks, Specs> & Free<F>
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [F]
    /** **The members a pattern keeps**, over the same keys — or `never` where it keeps none. */
    readonly extract: <const P extends AnyCodec>(
        this: Closed,
        pattern: P & ValidatePattern<Specs[number], P>,
    ) => DissectedCodec<
        DerivedVariants<Extracted<Specs, P>>,
        Ks,
        Extracted<Specs, P>
    >
    /** …and the members it rejects, the complement of the same pattern. */
    readonly exclude: <const P extends AnyCodec>(
        this: Closed,
        pattern: P & ValidatePattern<Specs[number], P>,
    ) => DissectedCodec<
        DerivedVariants<Excluded<Specs, P>>,
        Ks,
        Excluded<Specs, P>
    >
}

/**
 * What {@link mdunion} returns, read at the arity the caller wrote.
 *
 * **At one key it is today's type, exactly.** `discriminatedUnion` is `mdunion` at one
 * discriminator, so the two have to be the same type and not merely compatible ones — a caller
 * who swaps the call changes no annotation, and `discriminator`, `spec` and the
 * `Writes` pin all read as they did.
 */
export type Dissection<
    Ks extends readonly string[],
    Options extends readonly unknown[],
> = Ks extends readonly [infer D extends string]
    ? DiscriminatedCodec<
          DerivedVariants<SpecsOf<Options>>,
          D,
          ByTag<SpecsOf<Options>, D>,
          FreeOf<Options[number]>
      >
    : DissectedCodec<
          DerivedVariants<SpecsOf<Options>>,
          Ks,
          SpecsOf<Options>,
          FreeOf<Options[number]>
      >

export type UnionCodec<
    T,
    Options extends readonly unknown[],
    // the term: an entry of a `scope` reads it, and its slices, from the term of the entry
    Tm = OfParts,
> = {
    readonly encode: (this: Closed, value: T) => Result<WrittenBy<Options>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => WrittenBy<Options>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    /**
     * The same union read as a whole item — only where every option is an object.
     *
     * An item is a map, so a union that can also be an `S` has no top-level reading. Saying so with a
     * message rather than with an absent property is what makes reaching for it report *why* instead
     * of "property does not exist".
     */
    readonly item: AllObjects<Options> extends true
        ? Untagged<T, SpecsOf<Options>> & Free<UnionFree<Options, Tm>>
        : ErrorMessage<'[union] this union can hold an attribute that is not a map, so it has no whole-item reading — an item is always a map'>
    /**
     * **The options a pattern keeps**: the options whose values all lie inside what the pattern
     * holds. The pattern is a codec, so the slice of a union takes what a codec takes, a union
     * that holds a string beside objects included.
     *
     * An object pattern names the keys that it needs, and an option may declare more. The slice goes
     * into a field that holds a union of objects, and the result stays compact, as the `Extract` of
     * TypeScript reads it: `{ k, pet: U }` against `{ pet: P }` keeps `{ k, pet: Extract<U, P> }`. So
     * the extraction has no option that the original lacks. The result is rebuilt through
     * {@link union}, so a slice of a certified union is certified.
     */
    readonly extract: <const P extends AnyCodec>(
        this: Closed,
        pattern: P & ValidatePattern<SpecsOf<Options>[number], P>,
    ) => UnionSlice<Tm, KeptOptions<Options, P>>
    /** …and the options it rejects, the complement of the same pattern. */
    readonly exclude: <const P extends AnyCodec>(
        this: Closed,
        pattern: P & ValidatePattern<SpecsOf<Options>[number], P>,
    ) => UnionSlice<Tm, KeptOptions<Options, P, false>>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<SpecsOf<Options>>
    /** The model's term of this codec. Type-level only. */
    readonly [termMarker]?: [Tm] extends [OfParts]
        ? ['union', TermsOf<Options>]
        : Tm
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [UnionFree<Options, Tm>]
}

/** The free names of a union: the names of its options. An entry of a scope has none. */
type UnionFree<Options extends readonly unknown[], Tm> = [Tm] extends [OfParts]
    ? FreeOf<Options[number]>
    : never

/**
 * The options that a clause keeps. A slice of an entry of a `scope` holds the `ref`s of the entry,
 * so the slice is one more entry of that scope, at a key that no `ref` can name.
 */
type UnionSlice<Tm, Kept extends readonly unknown[]> = [Tm] extends [
    ['scope', infer D, unknown],
]
    ? UnionCodec<DecodeTerm<SliceTerm<D, Kept>>, Kept, SliceTerm<D, Kept>>
    : UnionCodec<DerivedUnion<Kept>, Kept>
declare const sliceKey: unique symbol
type SliceTerm<D, Kept extends readonly unknown[]> = [
    'scope',
    {
        [K in keyof D as K extends typeof sliceKey ? never : K]: D[K]
    } & { [sliceKey]: ['union', TermsOf<Kept>] },
    typeof sliceKey,
]

export type ItemCodec<T, Spec = unknown, Rest = undefined, Tm = OfParts> = {
    /** Every attribute, or why one could not be written. For `PutItem`. */
    readonly encode: (this: Closed, item: T) => Result<EncodedBy<Spec, Rest>>
    readonly unsafeEncode: (this: Closed, item: T) => EncodedBy<Spec, Rest>
    /**
     * The attributes a patch names, or why one could not be written. For `UpdateItem`, which
     * addresses attributes individually — the reason a whole-value codec does not fit DynamoDB and
     * this is a record of per-attribute ones.
     */
    readonly encodePartial: <const Patch extends Partial<T>>(
        this: Closed,
        patch: Patch,
    ) => Result<EncodedPatch<Spec, Patch>>
    readonly unsafeEncodePartial: <const Patch extends Partial<T>>(
        this: Closed,
        patch: Patch,
    ) => EncodedPatch<Spec, Patch>
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    /** One attribute's codec, for building `ExpressionAttributeValues` by hand. */
    readonly field: <K extends keyof Spec>(name: K) => Marks<Spec[K]>
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
     *
     * The codec keeps the attribute it writes: `A` is the member that the model reads at the
     * resolved frame, as the one attribute of that member, so `encode` gives `{ S: string }` at a
     * string. A frame where the model reads no one member gives the union of the attributes of
     * its options, and the wide `AttributeValue` where an option has no member the type computes
     * (`opaque`). The root of the item writes a row, and keeps the wide `AttributeValue`.
     */
    readonly at: <X, A extends AttributeValue = AttributeValue>(
        this: Closed,
        select: (
            path: TermPath<
                [[[Tm] extends [OfParts] ? ObjectTermOf<Spec, Rest> : Tm, []]],
                T,
                ItemFrontier<T, Spec, Rest>,
                true
            >,
        ) => PathTerminal<X> & PathResolved & PathEncoded<A>,
    ) => LocatedCodec<X, A>
    /**
     * A builder for document paths into this item.
     *
     * One instance builds any number of independent paths: every hop returns a new builder carrying
     * its own segments, so nothing accumulates and nothing is consumed. Hoist it.
     */
    readonly path: () => PathOf<T, ItemFrontier<T, Spec, Rest>>
    readonly spec: Spec
    /** The codec of an attribute the spec does not declare, or `undefined` for a closed object. */
    readonly rest: Rest
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
}

/** An {@link AttributeCodec} that also knows where it lives, and keeps the attribute it writes. */
export type LocatedCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = AttributeCodec<T, A> & {
    /** The document path, as DynamoDB expression syntax. */
    readonly path: () => string
    readonly segments: readonly (string | number)[]
    /**
     * **The condition under which a write at this path is safe**, as a conjunction of
     * {@link Precondition}s: one group for each `narrow` on the path, empty where the path has no
     * `narrow`. The narrowing drops options, and an item of a dropped option may still be stored.
     * Put the preconditions in the `ConditionExpression` of the write, so the write refuses such
     * an item.
     *
     * A refusal where a clause key stores a term that no exact precondition states.
     */
    readonly preconditions: Result<readonly Precondition[]>
}

/**
 * One declared attribute, with the questions about its declaration already answered.
 *
 * Whether an attribute may be absent and what stands in for it are facts about the spec, not about
 * the row being read, so they are settled once when the codec is built.
 */
export type Declared = {
    readonly name: string
    readonly pair: Pair
    /** The attribute may be omitted — true for both `optional` and `undefinable`. */
    readonly optional: boolean
    /** On decode, an omitted attribute still gets its key, holding `undefined`. */
    readonly keyed: boolean
    readonly absent:
        | { readonly value: unknown; readonly copy: boolean }
        | undefined
}

/**
 * The marker taken off, once, at the declaration.
 *
 * A field names the codec it marks, so the two halves are that codec's and taking the mark off
 * changes nothing about what the member encodes or decodes. What it changes is that the mark is
 * *named* rather than left to be recovered from a definition kind, which is what {@link Field} is
 * for.
 */
const fieldOf = (declared: ObjectSlot): Field => {
    const def = declared.def
    return 'mark' in def ? def : { mark: 'req', t: def }
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
 * - `satisfies ItemCodec<Entity>` — the entity, up to assignability both ways. `ItemCodec` is
 *   invariant in it, sitting in `encode`'s parameter and `decode`'s return, so a required attribute
 *   that is missing or extra, and one that decodes to the wrong type, are caught. An optional key
 *   that is added or dropped is not caught: an object without `k?` is assignable to an object with
 *   it, and back. {@link pin} compares the key paths with their optional marks, and refuses it.
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
const objectFromMap = <
    const Spec extends Record<string, ObjectSlot>,
    const Rest extends AnyCodec | undefined = undefined,
>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
    rest: Rest,
): ObjectCodec<Spec, Rest> => {
    // the marker off each declared attribute, once — the term. What the two directions walk is
    // the *compiled* form of it, which `bodySem` builds and which carries one thing the term does
    // not: whether a stand-in has to be copied per read, a fact about this runtime and not about
    // the declaration.
    const fields: Record<string, Field> = {}
    const declaredSpec = spec as unknown as Record<string, ObjectSlot>
    for (const name in declaredSpec) {
        fields[name] = fieldOf(declaredSpec[name] as ObjectSlot)
    }

    const declaredBody: Body =
        rest === undefined ? { fields } : { fields, rest: termOf(rest) }
    const itemDef = { kind: 'object', body: declaredBody } as const
    // the judgment of the node runs before the item pair is built
    const nested = codecOfTerm(itemDef) as unknown as AttributeCodec<
        DerivedItem<Spec, Rest>,
        M<EncodedBy<Spec, Rest>>
    >
    // the term's item pair, not a second one built beside it — `denote`'s row asks `itemSem` for
    // the same object, so `.item` and the codec run one body rather than two that agree
    /**
     * **The view, and this is where it starts.**
     *
     * The owner's ruling: the top-level map belongs to the view, not to the codec. An `object`
     * codec writes an `M` like any other term, and `.item` is the one reading that writes no map —
     * the same pair, one level in.
     *
     * So the pair is not built here. `denote.ts` builds one item pair per term and this hands out
     * that one, which is what makes `item.encode === codec.encode`'s body the same function. They
     * were two objects before `579ed89`, and nothing said which of them a caller was running.
     */
    const body = itemSem(itemDef)

    type T = DerivedItem<Spec, Rest>
    // a term that reads a name that no scope binds refuses each use
    const self: ItemCodec<T, Spec, Rest> = {
        encode: (item) =>
            openRefusal(itemDef) ??
            (body.encode(item as Record<string, unknown>) as Result<
                EncodedBy<Spec, Rest>
            >),

        encodePartial: (patch) => {
            const open = openRefusal(itemDef)
            if (open) return open
            const held = patch as Record<string, unknown>
            const out: Record<string, AttributeValue> = {}
            for (const name in held) {
                const value = held[name]
                if (value === undefined) continue
                // a name the spec does not declare is written through the open entry, as `encode`
                // writes it
                const term = fields[name]?.t ?? declaredBody.rest
                if (!term) {
                    return new CodecError(`'${name}' is not an attribute`)
                }
                const written = codecOfTerm(term).encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
            }
            return out as never
        },

        decode: (item) =>
            openRefusal(itemDef) ??
            membersTooDeeply(item, 0) ??
            (body.decode(
                item as Readonly<Record<string, AttributeValue>>,
            ) as Result<T>),

        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        unsafeEncodePartial: (patch) => orThrow(self.encodePartial(patch)),

        path: () => pathBuilder<T, ItemFrontier<T, Spec, Rest>>(),
        at: <X, A extends AttributeValue = AttributeValue>(
            select: (
                path: TermPath<
                    [[ObjectTermOf<Spec, Rest>, []]],
                    T,
                    ItemFrontier<T, Spec, Rest>,
                    true
                >,
            ) => PathTerminal<X> & PathResolved & PathEncoded<A>,
        ) => {
            const steps = stepsOf(
                select(
                    rootPath<
                        TermPath<
                            [[ObjectTermOf<Spec, Rest>, []]],
                            T,
                            ItemFrontier<T, Spec, Rest>,
                            true
                        >
                    >(),
                ),
            )
            const segments = segmentsIn(steps)
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
            const walk = (): AnyCodec => {
                const open = openRefusal(itemDef)
                if (open) return refusedAt(open)
                let frontier: readonly AnyCodec[] = [
                    self as unknown as AnyCodec,
                ]
                const flat = flatOf(itemDef)
                if (flat.kind === 'refused')
                    return refusedAt(new CodecError(flat.reason))
                for (const step of steps) {
                    const next =
                        typeof step === 'object'
                            ? narrowAcross(frontier, step)
                            : acrossVariants(frontier, step, flat.cycles)
                    if (next instanceof CodecError) return refusedAt(next)
                    // a frontier where no codec admits a value is a name that no codec declares
                    if (next.every(admitsNothing)) {
                        throw new CodecError(
                            `no attribute is declared at '${path}'`,
                        )
                    }
                    frontier = next
                }
                // a clause at the root narrows the values, and the item codec writes each value
                // of a kept option as that option writes it
                if (segments.length === 0) return self as unknown as AnyCodec
                const [first, ...ambiguous] = frontier as [
                    AnyCodec,
                    ...AnyCodec[],
                ]
                // the item root is no level, and each segment past the first crosses one L or M
                return ambiguous.length === 0
                    ? segments.length <= 1
                        ? first
                        : codecAtLevel(first.def, segments.length - 1)
                    : unresolvedAt(String(path), frontier.some(admitsNothing))
            }
            const here = walk()

            return {
                ...(here as AttributeCodec<X, A>),
                path: () => path,
                segments,
                preconditions: preconditionsOf(steps),
            }
        },
        // the codec the member declares, never the field that marks it: a field has no pair, and a
        // caller that asked for the attribute at a name asked for the thing that reads and writes it
        field: <K extends keyof Spec>(name: K) => {
            const declared = fields[name as string]
            return (declared && codecOfTerm(declared.t)) as Marks<Spec[K]>
        },
        spec: spec as Spec,
        rest,
        def: itemDef,
    }

    // the `M` is what this codec writes; `.item` is the same two directions with the wrapper taken
    // off. Named member by member rather than spread so the cast keeps the *shape* the map carries —
    // `Attribute<'M'>` would flatten it to "some map" — and so that a call to `object` stays a plain
    // object literal, which is what lets a bundler drop an unused one
    const made = {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        item: self as ItemCodec<DerivedItem<Spec, Rest>, Spec, Rest>,
    }
    objectItems.set(nested.def, self)
    return made
}

/** The whole-item reading of an object node: the declared spec, the open block, and the pair. */
type ObjectItem = AnyObjectCodec['item'] & {
    readonly rest: AnyCodec | undefined
}

/**
 * **The whole-item reading of each object node**, so a former that reads the node a `ref` names
 * reaches the declared spec of the node. Each object node comes from {@link objectFromMap}.
 */
const objectItems = new WeakMap<Term, ObjectItem>()

/** The whole-item reading of the node that a term names, or nothing where the node is no object. */
const objectNamed = (t: Term): ObjectItem | undefined => {
    const node = resolvedTerm(t)
    return node === undefined ? undefined : objectItems.get(node)
}

export type ObjectEntry<
    Key extends string = string,
    Value extends ObjectSlot = ObjectSlot,
> = readonly [AttributeCodec<Key, Attribute<'S'>>, Value]

type AnyObjectEntry = readonly [AnyCodec, ObjectSlot]

type OptionalObjectSlot = {
    readonly def: Extract<Field, { readonly mark: 'optional' | 'undefinable' }>
}

type EntryAdmission<Entry> = Entry extends readonly [
    AttributeCodec<infer Key, Attribute<'S'>>,
    infer Value extends ObjectSlot,
]
    ? Key extends string
        ? string extends Key
            ? Value extends OptionalObjectSlot
                ? unknown
                : ErrorMessage<'[object] an open key entry must be optional, because a required wildcard means at least one matching key'>
            : unknown
        : ErrorMessage<'[object] an entry key must be a string codec'>
    : ErrorMessage<'[object] an entry must contain a string codec and an object slot'>

type EntriesAdmission<Entries extends readonly AnyObjectEntry[]> =
    UnionToIntersection<EntryAdmission<Entries[number]>>

type UnionToIntersection<Value> = (
    Value extends unknown
        ? (value: Value) => void
        : never
) extends (value: infer Intersection) => void
    ? Intersection
    : never

type EntrySpec<Entry> = Entry extends readonly [
    AttributeCodec<infer Key extends string, Attribute<'S'>>,
    infer Value extends ObjectSlot,
]
    ? string extends Key
        ? Record<never, never>
        : { readonly [K in Key]: Value }
    : never

type EntrySpecs<Entries extends readonly AnyObjectEntry[]> = show<
    UnionToIntersection<EntrySpec<Entries[number]>>
>

type SlotCodec<Slot> = Slot extends { readonly codec: infer Codec }
    ? Codec
    : Slot

type WildcardEntry<Entries extends readonly AnyObjectEntry[]> =
    Entries[number] extends infer Entry
        ? Entry extends readonly [
              AttributeCodec<infer Key, Attribute<'S'>>,
              infer Value extends ObjectSlot,
          ]
            ? string extends Key
                ? SlotCodec<Value>
                : never
            : never
        : never

type EntryRest<Entries extends readonly AnyObjectEntry[]> = [
    WildcardEntry<Entries>,
] extends [never]
    ? undefined
    : Extract<WildcardEntry<Entries>, AnyCodec>

/**
 * The names an entry key declares, read from the node that the key names, through its `ref`s. The
 * names fix the body at the declaration, so a key that names a `ref` that no scope binds yet is
 * refused rather than waiting.
 */
const entryNames = (key: AnyCodec): string[] => {
    const term = resolvedTerm(termOf(key))
    if (term?.kind === 'literal' && term.base === 'string') return [term.v]
    if (term?.kind === 'union') {
        const names = term.options.flatMap((option) => {
            const one = resolvedTerm(option)
            return one?.kind === 'literal' && one.base === 'string'
                ? [one.v]
                : []
        })
        if (names.length === term.options.length) return names
    }
    if (term?.kind === 'string') return []
    throw new CodecError(
        'an object entry key must be `string` or a string literal key set',
    )
}

const entryCodec = (slot: ObjectSlot): AnyCodec =>
    ('codec' in slot ? slot.codec : slot) as AnyCodec

export function object<const Spec extends Record<string, ObjectSlot>>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
): ObjectCodec<show<Spec>>
export function object<const Entries extends readonly AnyObjectEntry[]>(
    ...entries: Entries & EntriesAdmission<Entries>
): ObjectCodec<EntrySpecs<Entries>, EntryRest<Entries>>
export function object<
    const Spec extends Record<string, ObjectSlot>,
    const FirstEntry extends AnyObjectEntry,
    const Entries extends readonly AnyObjectEntry[],
>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
    firstEntry: FirstEntry & EntriesAdmission<[FirstEntry, ...Entries]>,
    ...entries: Entries
): ObjectCodec<
    show<Spec & EntrySpecs<[FirstEntry, ...Entries]>>,
    EntryRest<[FirstEntry, ...Entries]>
>
export function object(
    first?: Record<string, ObjectSlot> | AnyObjectEntry,
    ...tail: AnyObjectEntry[]
): unknown {
    const isEntry = Array.isArray(first)
    const spec: Record<string, ObjectSlot> =
        !isEntry && first !== undefined
            ? (first as Record<string, ObjectSlot>)
            : {}
    const entries = (isEntry ? [first, ...tail] : tail) as AnyObjectEntry[]
    const fields: Record<string, ObjectSlot> = { ...spec }
    let rest: AnyCodec | undefined
    for (const [key, slot] of entries) {
        const names = entryNames(key)
        if (names.length === 0) {
            const field = fieldOf(slot)
            if (field.mark !== 'optional' && field.mark !== 'undefinable') {
                throw new CodecError(
                    'an open key entry must be optional, because a required wildcard means at least one matching key',
                )
            }
            if (rest !== undefined) {
                throw new CodecError('an object has at most one open key entry')
            }
            rest = entryCodec(slot)
            continue
        }
        for (const name of names) {
            if (name in fields) {
                throw new CodecError(`'${name}' is declared more than once`)
            }
            fields[name] = slot
        }
    }
    return objectFromMap(fields, rest) as ObjectCodec<
        Record<string, ObjectSlot>,
        AnyCodec | undefined
    >
}

/** The options a factor offers, at the type level: a union's, or the factor itself. */
type FactorOptions<F> = F extends UnionCodec<infer _T, infer Os>
    ? Os
    : F extends {
            readonly [optionsMarker]?: infer Os extends readonly unknown[]
        }
      ? Os
      : readonly [F]

/** Every name a factor can declare, across all of its options. */
type DeclaredNames<F> = FactorOptions<F>[number] extends infer O
    ? O extends ObjectCodec<infer S, infer _R, infer _T, infer _Tm>
        ? keyof S & string
        : never
    : never

/** Whether any option of a factor is left open by a rest codec. */
type AnyOpen<F> = FactorOptions<F>[number] extends infer O
    ? O extends ObjectCodec<infer _S, infer R, infer _T, infer _Tm>
        ? [R] extends [undefined]
            ? never
            : true
        : true
    : never

/**
 * One merge at the type level. The merge is closed, because a name neither factor declares is one
 * the product refuses.
 */
type MergeTwo<X, Y> = X extends ObjectCodec<
    infer A,
    infer _RA,
    infer _TA,
    infer _TmA
>
    ? Y extends ObjectCodec<infer B, infer _RB, infer _TB, infer _TmB>
        ? ObjectCodec<show<A & B>>
        : never
    : never

type DistributeOne<X, Ys extends readonly unknown[]> = {
    [I in keyof Ys]: MergeTwo<X, Ys[I]>
}

/** The `flatMap` order: outer first, inner second. */
type Distribute<
    Xs extends readonly unknown[],
    Ys extends readonly unknown[],
> = Xs extends readonly [infer H, ...infer T extends readonly unknown[]]
    ? [...DistributeOne<H, Ys>, ...Distribute<T, Ys>]
    : []

/** One merge needs no union around it; several are one flat union. */
type ProductOfTwo<X, Y> = Distribute<
    FactorOptions<X>,
    FactorOptions<Y>
> extends infer Ms extends readonly unknown[]
    ? Ms extends readonly [infer One]
        ? One
        : UnionCodec<DerivedUnion<Ms>, Ms>
    : never

/** More than two factors fold left. */
type FoldProduct<Fs extends readonly unknown[]> = Fs extends readonly [
    infer A,
    infer B,
    ...infer R extends readonly unknown[],
]
    ? FoldProduct<[ProductOfTwo<A, B>, ...R]>
    : Fs extends readonly [infer A]
      ? A
      : never

/** A name two factors both declare, which is the one thing a product cannot have. */
type SharedAcross<Fs extends readonly unknown[]> = Fs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? (DeclaredNames<H> & DeclaredNames<T[number]>) | SharedAcross<T>
    : never

/** Whether any factor holds no value, read at the node that the factor names. */
type HasNeverFactor<Fs extends readonly unknown[]> = Fs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? // `[H] extends [never]` is true only where `H` *is* `never`, which is how a spec casts a
      // factor past the type. Without this guard that cast matches every shape below it
      [H] extends [never]
        ? HasNeverFactor<T>
        : [H] extends [{ readonly def: { readonly kind: 'never' } }]
          ? true
          : HoldsNoValue<TermOf<H>> extends true
            ? true
            : HasNeverFactor<T>
    : false

/**
 * Nothing, or why these factors have no product.
 *
 * **Three rules, in the order that gives the advice a caller can act on.** A `never` factor comes
 * first: a product against a factor that holds nothing passes no check, because every merge
 * holds nothing and two empty held sets are comparable in both directions. Without this clause the
 * open-factor one fired on it and told the caller to close a rest policy `never` does not have.
 *
 * The shared name is next, because its message names the name. The open factor is last: a `rest`
 * codec holds an undeclared name through a codec of its own, and the product would have to hold it
 * through both.
 *
 * The never clause reads each form that holds no value at the node that a factor names, so a scope
 * entry that names `never`, and `union([])`, get the never reason. A factor can still hold no value
 * through a predicate, and no clause reads that.
 */
export type ValidateProduct<Fs extends readonly unknown[]> =
    HasNeverFactor<Fs> extends true
        ? ErrorMessage<'[product] one factor is `never`, which holds no value — so every product with it holds none either and no value could select between the results. Remove the factor'>
        : [SharedAcross<Fs>] extends [never]
          ? [AnyOpen<Fs[number]>] extends [never]
              ? unknown
              : ErrorMessage<'[product] a factor holds undeclared names through a `rest` codec, and a product declares no meet of two of them. Close every factor: give it no open key entry'>
          : ErrorMessage<`[product] two factors both declare '${SharedAcross<Fs>}', and a product needs disjoint names. Rename it, or drop it from one factor`>

/**
 * **The options a factor offers**: the object node that the factor names, or each option of the
 * union node that the factor names. Each read goes through the `ref`s, so a factor and a `ref` to
 * the factor give one product. The merge is built at the declaration, so a factor that names a
 * `ref` that no scope binds yet is refused rather than waiting.
 */
const optionsOfFactor = (factor: AnyCodec): readonly ObjectItem[] => {
    const node = resolvedTerm(termOf(factor))
    // a product against a factor that holds nothing passes no check: every merge would hold
    // nothing too, and two empty held sets are comparable both ways, so no value tells the options
    // apart. The rule reads each form whose emptiness the term decides. A factor can still hold
    // nothing through a predicate that admits no value, and the product of such a factor builds
    if (holdsNoValue(termOf(factor))) {
        throw new CodecError(
            '`never` holds no value, so every product with it holds none either and no value could select between the results — remove the factor',
        )
    }
    if (node?.kind === 'ref') {
        throw new CodecError(
            `a factor of a product names ref('${node.slot.name}'), which no scope binds yet — a product merges the declared names at its declaration, so take the product where the scope binds the name`,
        )
    }
    if (node?.kind === 'union') {
        // a dissection is a union of objects in the term, so its members distribute in declared
        // order like the options of any union
        return node.options.map((option) => {
            const one = objectNamed(option)
            if (!one) {
                throw new CodecError(
                    'an option of a union factor is not an object codec — a product merges declared names, and only an object declares any',
                )
            }
            return one
        })
    }
    const one = node && objectNamed(node)
    if (one) return [one]
    throw new CodecError(
        'a factor of a product is an object codec or a `union` of object codecs, and this is neither — a product merges declared names, and only an object declares any',
    )
}

/** The binary product, over the options each factor offers. */
const productOfTwo = (first: unknown, second: unknown): unknown => {
    const lefts = optionsOfFactor(first as AnyCodec)
    const rights = optionsOfFactor(second as AnyCodec)
    for (const option of [...lefts, ...rights]) {
        if (option.rest !== undefined) {
            throw new CodecError(
                'a factor holds undeclared names through a `rest` codec, and a product declares no meet of two of them. Close every factor: give it no open key entry',
            )
        }
    }
    const merges = lefts.flatMap((left) =>
        rights.map((right) => {
            for (const name in right.spec) {
                if (Object.hasOwn(left.spec, name)) {
                    throw new CodecError(
                        `both factors declare '${name}', and a product needs disjoint names — rename it, or drop it from one factor`,
                    )
                }
            }
            return objectFromMap({ ...left.spec, ...right.spec }, undefined)
        }),
    )
    // one merge is an object and needs no union around it; several are one flat union, built
    // through `union` itself so `agrees` runs over the products
    return merges.length === 1
        ? merges[0]
        : union(merges as unknown as readonly AnyCodec[])
}

/**
 * **The product of two objects, or of unions of objects: the object of their merged spec.**
 *
 * The founding operation of the Cartesian product over codecs.
 *
 * **A union factor distributes.** The result is one flat `union` of the `n·m` merges, outer over
 * the first factor's options and inner over the second: the `flatMap` order. It is built through {@link union}, so `agrees` runs
 * over the products and a pair of merges it cannot show compatible is refused there rather than here.
 *
 * **More than two factors fold left.** `product(a, b, c)` is `product(product(a, b), c)`. The other
 * nesting gives the same term: the model's merge of records is associative (`Term.product_assoc`).
 *
 * @example
 * ```ts
 * product(object({ petId: string }), object({ price: decimal }))
 * product(union([object({ a: string }), object({ b: string })]), object({ n: boolean }))
 * ```
 */
export const product = <const Fs extends readonly unknown[]>(
    ...factors: Fs & ValidateProduct<Fs>
): FoldProduct<Fs> => {
    const [head, ...rest] = factors as readonly unknown[]
    if (head === undefined || rest.length === 0) {
        throw new CodecError(
            'a product is taken of two or more factors, and fewer were given',
        )
    }
    return rest.reduce(
        (carried, next) => productOfTwo(carried, next),
        head,
    ) as FoldProduct<Fs>
}

/**
 * A builder for document paths into `T`.
 *
 * The one implementation behind both `item(...).path()` and `tableEntry(...).path()`. They must
 * agree about what a path means — `at` resolves a codec by walking the same segments this records —
 * and the surest way for two implementations to agree is for there to be one.
 */
export const pathBuilder = <T, F = unknown>(): PathOf<T, F> => rootPath()

/**
 * The recorder at the root, read as the path type `P` of its caller: {@link PathOf}, or the
 * selector of `at` that reads the term. One cast, at the one place where the recorder, which takes
 * any segment, meets a type that offers only the segments of a codec.
 */
const rootPath = <P>(): P => recordPath([]) as P

/** A segment addressing a list position, as opposed to an attribute named in digits. */
const asIndex = /^\d+$/

/**
 * **A step of a path**: a segment, or a clause. A clause adds no segment, and narrows the frontier
 * that the walk of `at` carries.
 */
type Step = string | number | Clause

/**
 * **The clause of `narrow`**, the model's `clauseTerm`: an object term whose keys are each required
 * at the term of a codec, and whose open block is `opaque`.
 */
type Clause = Extract<Term, { readonly kind: 'object' }>

/** The term of a clause, built one time when the path records the clause. */
const clauseTerm = (spec: Readonly<Record<string, AnyCodec>>): Clause => {
    const fields: Record<string, Field> = {}
    for (const name in spec) {
        const one = spec[name]
        if (one) fields[name] = { mark: 'req', t: one.def }
    }
    return { kind: 'object', body: { fields, rest: { kind: 'opaq' } } }
}

/** The segments of a path, without its clauses. */
const segmentsIn = (steps: readonly Step[]): readonly (string | number)[] =>
    steps.flatMap((step) => (typeof step === 'object' ? [] : [step]))

/** What each recorder recorded — read back by {@link stepsOf}. */
const recorded = new WeakMap<object, readonly Step[]>()

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
const recordPath = (steps: readonly Step[]): unknown => {
    const recorder = new Proxy(nothing, {
        get: (_target, prop) => {
            if (typeof prop !== 'string') return undefined
            if (prop === 'toString') return () => asPath(segmentsIn(steps))
            if (prop === 'at') {
                return (index: number) => recordPath([...steps, index])
            }
            // an open name, selected by a method, as `at` selects a position
            if (prop === 'entry') {
                return (key: string) => recordPath([...steps, key])
            }
            // a clause narrows the frontier of `at`; the document path is unchanged
            if (prop === 'narrow') {
                return (spec: Readonly<Record<string, AnyCodec>>) =>
                    recordPath([...steps, clauseTerm(spec)])
            }
            // digits all the way through, or it is an attribute name: `parseInt` accepted a
            // leading number and dropped the rest, so `'1abc'` recorded `[NaN]`
            return recordPath([
                ...steps,
                asIndex.test(prop) ? Number(prop) : prop,
            ])
        },
    })
    recorded.set(recorder, steps)
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
const stepsOf = (path: unknown): readonly Step[] => {
    // no `typeof` guard: `WeakMap.prototype.get` answers `undefined` for a key that cannot be held
    // weakly, so a selector that returned a string or a number falls into the same branch
    const steps = recorded.get(path as object)
    if (!steps) {
        throw new CodecError(
            'a path selector must return a path — an attribute, `at(...)` or `narrow(...)`',
        )
    }
    return steps
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
 * The runtime asks `term.ts`'s `member`; this is the same question of the type, so a spec can pin `SS`
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
    : // the same for a field: the attribute is the one the codec it marks writes
      C extends { readonly codec: AttributeCodec<infer _Marked, infer Marks> }
      ? Marks
      : C extends AttributeCodec<infer _Held, infer Written>
        ? Written
        : never

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

/**
 * What an item writes: the attributes the spec declares, plus whatever a rest policy adds.
 *
 * {@link Encoded} alone is a *lower bound* rather than the answer. With no rest nothing else
 * is written and the two agree; a rest codec emits attributes the spec never named, so
 * claiming `Encoded<Spec>` exactly would be a promise the compiler then enforces against the
 * caller — refusing to read an attribute the codec really did write.
 *
 * The closed state is matched rather than the codec: an {@link AttributeCodec} is
 * invariant in its value, so `Rest extends AttributeCodec<unknown, infer A>` fails for every codec
 * of a narrower value and quietly takes the wrong branch. {@link AttributeOf} infers both
 * parameters, so the open block's attribute is exact. The index also admits each declared
 * attribute, because an index signature intersects with every declared key. The index takes no
 * `undefined` from an optional key: an absent field writes no entry, so no entry holds `undefined`,
 * and the map stays an attribute that nests in another codec.
 */
type EncodedBy<Spec, Rest> = [Rest] extends [undefined]
    ? Encoded<Spec>
    : Encoded<Spec> & {
          readonly [name: string]:
              | AttributeOf<Rest>
              | Written<Encoded<Spec>, keyof Encoded<Spec>>
      }

/**
 * The item a spec writes, as a shape you could have written by hand.
 *
 * The fixed point. `Encoded<typeof Pet>` is what the codec puts in the table; a `PetItem` written
 * out by hand is what the table is believed to hold; pinning one against the other is what makes a
 * migration checkable rather than hoped for. Optional attributes are optional keys, because an
 * attribute a codec may omit is one the item may not have.
 */
export type Encoded<Spec> = show<
    {
        [K in keyof Spec as Spec[K] extends {
            readonly [optionalMarker]: true
        }
            ? never
            : K]: AttributeOf<Spec[K]>
    } & {
        // an optional name at `never` writes no attribute, so the item has no such key
        [K in keyof Spec as Spec[K] extends {
            readonly [optionalMarker]: true
        }
            ? [AttributeOf<Spec[K]>] extends [never]
                ? never
                : K
            : never]?: AttributeOf<Spec[K]>
    }
>

export type ObjectOf<Spec> = {
    // required key, and the attribute is always there
    [K in keyof Spec as Spec[K] extends { readonly [undefinableMarker]: true }
        ? never
        : Spec[K] extends { readonly [optionalMarker]: true }
          ? never
          : K]: Decoded<Spec[K]>
} & {
    // required key, and the attribute may not be there — so `undefined` joins the value
    [K in keyof Spec as Spec[K] extends { readonly [undefinableMarker]: true }
        ? K
        : never]: Decoded<Spec[K]> | undefined
} & {
    // the key itself may not be there
    [K in keyof Spec as Spec[K] extends { readonly [undefinableMarker]: true }
        ? never
        : Spec[K] extends { readonly [optionalMarker]: true }
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
    /** A use needs a closed codec, so a signature that asks for one admits no free name. */
    readonly [freeMarker]?: [never]
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
    readonly encode: (this: Closed, item: T) => Result<AttributeMap>
    readonly unsafeEncode: (this: Closed, item: T) => AttributeMap
    /**
     * The attributes a patch names, or why one could not be written.
     *
     * The discriminator is required in a patch, because it is what chooses the codec. This is a type
     * error, not a runtime one: `Partial<T> & Pick<T, D>`.
     */
    readonly encodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    readonly discriminator: D
    readonly spec: Spec
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
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
const dissect = <T extends Record<string, unknown>>(
    ks: readonly string[],
    options: readonly AnyObjectCodec[],
): DiscriminatedCodec<T, string, Record<string, unknown>> => {
    // **the empty key set, refused where the type cannot refuse it.** Over no discriminator every
    // value carries the empty assignment, so the first member answers for all of them and the
    // union is a union of one. The model carries no key set at all, so it never asks this; here
    // the key set is a `readonly string[]`, which cannot say it, and this is the gate
    if (ks.length === 0) {
        throw new CodecError(
            `a discriminated union needs at least one discriminator, and this one has none — every value carries the empty assignment, so the first variant would answer for all of them`,
        )
    }
    // **An empty option list is a mistake, not the bottom.** `never` is the bottom and says so as
    // a term; a `dunion` over no variants is what a typo or a `map` over an empty array produces,
    // and it admits nothing while no rule reads it as admitting nothing. The type refuses this
    // too — what reaches here is a cast, plain JavaScript, or an erased path
    if (options.length === 0) {
        throw new CodecError(
            `a discriminated union needs at least one option, and this one has none — no tag reaches a variant, so nothing can be written or read. If a codec that admits no value is what you meant, that is \`never\``,
        )
    }
    // **Each option names an object node, read through its `ref`s.** An option that names a `ref`
    // that no scope binds yet waits for the scope, where the index reads the node
    for (const option of options) {
        const node = resolvedTerm(termOf(option as unknown as AnyCodec))
        if (node?.kind !== 'ref' && !(node && objectNamed(node))) {
            throw new CodecError(
                `every option must be an object codec, and one of them is not — a bare spec has no variant to select, so pass \`object(...)\` around it`,
            )
        }
    }
    /**
     * **The term is a `union`, and the tag table is this builder's index over it.**
     *
     * A dissection is a certified union: its members are objects that differ at a required literal
     * key with disjoint alternatives, which is exactly what structural admission resolves and what
     * `Calculus.Closed.viewsDisjoint` certifies. So there is one sum in the term language, and the key set below
     * is a lookup this builder keeps for `encodePartial` and the item path — a host
     * index, carried by no term.
     */
    const memberTerms = options.map((option) =>
        termOf(option as unknown as AnyCodec),
    )
    const unionDef = { kind: 'union', options: memberTerms } as const

    // **every member's assignment, read off the member's own body, and no two alike.** Both rules
    // are the index's, not the union's: the one-key refusals `discriminatedUnion` used to spell
    // inline are these two at one key. The union's own gate does not replace them, because a
    // duplicated index key is a different fact from two members that are not disjoint, and the index is
    // what needs it.
    //
    // **A tag that a member reads through an unbound `ref` waits for the scope**, because the
    // index reads the literal of each tag through the `ref`. The scope builds the index with every
    // name bound, and each use builds it where no scope has
    const index = () => {
        const members = membersOf(
            ks,
            memberTerms.map((term, at) => {
                const node = resolvedTerm(term)
                const item = node && objectNamed(node)
                if (node?.kind !== 'object' || !item) {
                    throw new CodecError(
                        `every option must be an object codec, and option ${at} is a \`${node?.kind}\` — a bare spec has no variant to select, so pass \`object(...)\` around it`,
                    )
                }
                return [
                    node.body,
                    item as unknown as ItemCodec<T, unknown>,
                ] as const
            }),
        )
        if (failed(members)) throw members
        const { pick, tagOf } = byTagSem(ks, members) as unknown as {
            pick: (
                assignment: Readonly<Record<string, string>>,
            ) => Result<ItemCodec<T, unknown>>
            tagOf: (
                item: Partial<T>,
            ) => Result<Readonly<Record<string, string>>>
        }
        return { members, pick, tagOf }
    }
    let indexed: ReturnType<typeof index> | undefined
    const resolution = (): ReturnType<typeof index> => {
        indexed ??= index()
        return indexed
    }
    whenBound(memberTerms, resolution)
    const pick = (assignment: Readonly<Record<string, string>>) =>
        resolution().pick(assignment)
    const tagOf = (item: Partial<T>) => resolution().tagOf(item)

    // **the published one-key surface carries `discriminator`, and this is that name.** Where the
    // key set has one element, that element *is* the discriminator: it is the whole set, not the
    // head of a list. Where it has several there is no such name, and the codec carries `keys`
    // instead — so the field is absent rather than holding one of several
    const [only, ...rest] = ks
    const oneKey = rest.length === 0 ? (only as string) : undefined

    // a term that reads a name that no scope binds refuses each use
    const self = {
        encode: (item: T) =>
            openRefusal(unionDef) ??
            andThen(andThen(tagOf(item), pick), (variant) =>
                variant.encode(item as never),
            ),
        encodePartial: (patch: Partial<T>) =>
            openRefusal(unionDef) ??
            andThen(andThen(tagOf(patch), pick), (variant) =>
                variant.encodePartial(patch as never),
            ),
        decode: (item: StoredItem) =>
            openRefusal(unionDef) ??
            (andThen(andThen(readTags(item, ks), pick), (variant) =>
                variant.decode(item),
            ) as Result<T>),
        unsafeEncode: (item: T) => orThrow(self.encode(item)),
        unsafeEncodePartial: (patch: Partial<T>) =>
            orThrow(self.encodePartial(patch)),
        unsafeDecode: (item: StoredItem) => orThrow(self.decode(item)),
        keys: ks,
        ...(oneKey === undefined ? {} : { discriminator: oneKey }),
        // at one key the spec is keyed by the tag, which is what a caller walking the variants
        // reads today; at several there is no one string to key it by, so it is the members' specs
        // in the order the caller declared them
        get spec() {
            const { members } = resolution()
            return oneKey === undefined
                ? members.map(([, variant]) => variant.spec)
                : Object.fromEntries(
                      members.map(([assignment, variant]) => [
                          assignment[oneKey],
                          variant.spec,
                      ]),
                  )
        },
        def: unionDef,
    }

    const nested = codecOfTerm<T, Attribute<'M'>>(unionDef)
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        item: self as unknown as Tagged<T, string, Record<string, unknown>>,
        // **The slice keeps every key**, at one member as at several. A key the clause pins to one
        // tag is a constant key on the result, and no normalisation drops a constant key: the
        // codec writes the tag out of the member's own field, so every item carries it whatever
        // the key set says. So a one-member result is a one-member dissection that still reads its
        // key, and `dissect` is handed the same `ks` it was built with.
        extract: (pattern: unknown) => {
            const open = openRefusal(unionDef)
            if (open) throw open
            return slicedDissection(ks, options, pattern, true)
        },
        exclude: (pattern: unknown) => {
            const open = openRefusal(unionDef)
            if (open) throw open
            return slicedDissection(ks, options, pattern, false)
        },
    } as DiscriminatedCodec<T, string, Record<string, unknown>>
}

/**
 * A dissection's slice: the same keys, the members the clause keeps, and `never` where it keeps
 * none.
 *
 * `never` and not an empty dissection, which `dissect` refuses: an empty option list is what a typo
 * produces, so a rule reading it as the bottom reads that accident as intent. An extraction that
 * keeps nothing is the bottom on purpose, and there is one name for the bottom.
 */
const slicedDissection = (
    ks: readonly string[],
    options: readonly AnyObjectCodec[],
    pattern: unknown,
    keep: boolean,
): unknown => {
    const kept = picked(options, pattern, keep, false)
    return kept.length === 0 ? never : dissect(ks, kept)
}

// ── unions with no discriminator ────────────────────────────────────

type RequiredKeysOf<Spec> = {
    [K in keyof Spec]-?: Spec[K] extends { readonly [optionalMarker]: true }
        ? never
        : K
}[keyof Spec]

/**
 * **A codec that pins a literal**: a literal constructor built it, and it decodes to a literal type
 * rather than a base.
 *
 * The type level's reading of "this name is pinned to a literal". The runtime reads the term, and
 * a term pins a literal only where a literal constructor built it, so this reads
 * {@link literalMarker} first. A caller's adapter that decodes to a literal type carries no mark,
 * and pins nothing here as it pins nothing at the term.
 */
type PinsALiteral<C> = C extends LiteralMark
    ? PinsALiteralValue<Decoded<C>>
    : false

/**
 * Whether a decoded type is a literal type rather than a base. `'a'` and `'a' | 'b'` answer `true`;
 * `string`, `number` and `boolean` answer `false`, each excluded by its own row, because a base is
 * assignable *from* its literals and `extends` alone cannot tell the two apart.
 *
 * A {@link LiteralCarrier} answers `true`: the mark says that a literal constructor built the
 * codec, and the carrier can hold a value that no literal type names.
 */
type PinsALiteralValue<V> = [V] extends [never]
    ? false
    : string extends V
      ? false
      : number extends V
        ? false
        : boolean extends V
          ? false
          : [V] extends [string | number | boolean | LiteralCarrier]
            ? true
            : false

/**
 * **The carriers of a literal that is no primitive**: `dynamoNumber(n)` decodes a
 * {@link DynamoNumber} and `binary(bytes)` a `Uint8Array`.
 */
type LiteralCarrier = DynamoNumber | Uint8Array

/**
 * **Whether the type cannot name the alternatives of a carrier**: `true` for a `Uint8Array`, which
 * has no literal type, and for a {@link DynamoNumber} whose text is `string`. A clause at such a
 * value keeps a member only on the values, which the type cannot decide. `boolean` for a union
 * that holds both kinds of value.
 */
type UnnamedValues<V> = V extends Uint8Array
    ? true
    : V extends DynamoNumber
      ? string extends V['digits']
          ? true
          : false
      : false

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
        readonly spec: Record<string, ObjectSlot>
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
        ? Head extends AnyObjectCodec | AnyTaggedCodec
            ? AllObjects<Rest>
            : false
        : true

/**
 * A tagged codec with its variants forgotten — {@link AnyObjectCodec} for a `discriminatedUnion`.
 *
 * A tagged option reads a whole item as readily as an object one: its `Tagged` carries the same
 * `encode` and `decode` over an item, and the union's item path delegates to it unchanged. What it
 * does not carry is a record of attributes at `spec` — that position holds the tag map — so
 * `AnyObjectCodec` does not match it and a union holding one was told it had no whole-item
 * reading. `discriminator` is the member that says which of the two this is.
 */
type AnyTaggedCodec = {
    readonly item: {
        readonly encode: (item: never) => unknown
        readonly decode: (item: StoredItem) => unknown
        readonly discriminator: string
    }
}

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
    readonly encode: (this: Closed, item: T) => Result<AttributeMap>
    readonly unsafeEncode: (this: Closed, item: T) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    readonly spec: Specs
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Specs>
}

/**
 * One option of a union, reduced to what matching it actually asks.
 *
 * **Every option is admitted by attempt**, an object option included, as in the model, where a
 * union acts exactly where one of its options acts (`select_isSome_attempt`). The kind of the value is a cheap filter in front of the attempt, and the
 * names present select nothing. The declaration guard makes the attempt decide: two options that
 * both admit one value are refused where the union is declared, so at most one attempt succeeds.
 */
export type Option = {
    readonly codec: AnyCodec
    /** The member it writes, where the kind alone decides — a cheap filter on decode. */
    readonly member: AttributeName | undefined
    /** The kinds of value it takes, where the kind alone decides — the same filter on encode. */
    readonly carries: readonly Shape[]
    /** The whole-item reading, for object options only. */
    readonly item: ItemCodec<Record<string, unknown>, unknown> | undefined
    /** The names it declares, for object options only. */
    readonly declares: ReadonlySet<string> | undefined
    /** How it is named in a message — written the way it was declared. */
    readonly describe: string
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
    const base = optionOfTerm(termOf(codec))
    // a tagged builder carries a whole-item reading of its own — its `Tagged` — over a term that
    // is now an ordinary union, so the test is the presence of that reading and not the kind
    const asObject =
        codec.def?.kind === 'object' ||
        (codec.def?.kind === 'union' &&
            !!(codec as unknown as Partial<AnyObjectCodec>).item)
            ? (codec as unknown as Partial<AnyObjectCodec>).item
            : undefined
    return asObject
        ? {
              ...base,
              item: asObject as unknown as ItemCodec<
                  Record<string, unknown>,
                  unknown
              >,
          }
        : base
}

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
 * Indexed by position like {@link SharedAssignments}, and one option at a time rather than a
 * pair: this is
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

/**
 * A key that **some** option names with no tag: that option cannot be found at it.
 *
 * Asked of each option in turn, and not of `Specs[number]`. Asking the union of the specs answers a
 * question about the collection — "does anybody name this key" — and an option that names none of
 * them passes, because its neighbours answered for it. Every other rule here is already distributed
 * over the options one at a time ({@link MultiTagged}) or over their pairs
 * ({@link SharedAssignments}); this is the same shape, and it was the one
 * clause that was not.
 */
type UntaggedKey<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | {
                [K in Ks[number]]: [TagsOf<Head, K>] extends [never] ? K : never
            }[Ks[number]]
          | UntaggedKey<Rest, Ks>
    : never

/** An option whose literal at some key admits more than one value, at any key. */
type MultiTaggedAnywhere<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = { [K in Ks[number]]: MultiTagged<Specs, K> }[Ks[number]]

/**
 * Whether two options differ at some key.
 *
 * **At some key, not at the first.** Two members of a dissection are distinct when their
 * assignments differ anywhere, and asking that of every key at once is what makes the answer
 * independent of how the keys were written.
 */
type DiffersSomewhere<A, B, Ks extends readonly PropertyKey[]> = true extends {
    [K in Ks[number]]: [TagsOf<A, K> & TagsOf<B, K>] extends [never]
        ? true
        : false
}[Ks[number]]
    ? true
    : false

type SharedAssignmentsFrom<
    Head,
    Rest extends readonly unknown[],
    Ks extends readonly PropertyKey[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (DiffersSomewhere<Head, Next, Ks> extends true
                ? never
                : `options ${At} and ${Cursor['length']}`)
          | SharedAssignmentsFrom<Head, Tail, Ks, At, [...Cursor, unknown]>
    : never

/**
 * Which pairs of options carry one assignment, as `options i and j`.
 *
 * A discriminated union is a *lookup*, so two options claiming one assignment is not an ambiguity
 * to be resolved when a value turns up — it is a table with one key written twice, and the second
 * write wins in silence. Decidable from the declaration, so it is refused there.
 */
type SharedAssignments<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | SharedAssignmentsFrom<
                Head,
                Rest,
                Ks,
                Cursor['length'],
                [...Cursor, unknown]
            >
          | SharedAssignments<Rest, Ks, [...Cursor, unknown]>
    : never

/**
 * Nothing, or the fact that the options cannot be looked up — at a key set.
 *
 * The same three failures in the same order, asked of every key instead of one. An option that
 * does not name a key with a `literal` cannot be found at all; an option whose literal admits
 * several values is arity one's refusal; two options carrying one assignment can each be found and
 * only one ever is.
 *
 * The arity check comes before the sharing check because it is a defect in one option rather than
 * in a pair, and because an option with two tags has to lose one before the sharing question is
 * even well posed.
 */
type MembersTagged<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = Specs extends readonly []
    ? ErrorMessage<'[discriminatedUnion] a discriminated union needs at least one option, and this one has none — no tag reaches a variant, so nothing can be written or read. If a codec that admits no value is what you meant, that is `never`'>
    : [UntaggedKey<Specs, Ks>] extends [never]
      ? [MultiTaggedAnywhere<Specs, Ks>] extends [never]
          ? [SharedAssignments<Specs, Ks>] extends [never]
              ? unknown
              : ErrorMessage<`[discriminatedUnion] ${SharedAssignments<Specs, Ks>} answer to the same discriminator value, and a lookup reaches only one of them — give them distinct values`>
          : ErrorMessage<`[discriminatedUnion] ${MultiTaggedAnywhere<Specs, Ks>} names the discriminator with a literal admitting several values, and a variant answers to exactly one tag — split it into one option per value`>
      : ErrorMessage<'[discriminatedUnion] every option must name the discriminator with a literal at `string`, `number` or `decimal`, or a lookup cannot find it'>

/**
 * The one-key gate, as the instance of {@link MembersTagged} at a one-element key set.
 *
 * One rule and not two: the messages are the same strings at one key, so the surface a caller
 * reads did not move, and a change to the rule cannot reach one arity and miss the other.
 */
type EveryOptionTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
> = MembersTagged<Specs, readonly [D]>

/* ── the slice of a union ─────────────────────────────────────────────────────────────── */

/**
 * **A pattern**: a codec that says which options to keep.
 *
 * `extract(pattern)` keeps the options that fit the pattern, and `exclude(pattern)` keeps the rest.
 * An option fits where every value that it holds lies inside what the pattern holds. The host
 * decides that on a fragment: a literal inside a literal of the same base and adapter, a base
 * inside itself, an option inside a union that holds a member of it, and an object inside an object
 * pattern. An object pattern names the keys that it needs. The other keys of the option are free,
 * as in a type that extends another type, so the pattern is read as the keys that it declares and
 * not as a closed object. Each other pair fits only where the two terms are one term.
 *
 * **An object with a union at a field is the union of the objects**, one for each member of the
 * field (`Calculus.Term.product_join` states the product form). The slice goes into the field and
 * keeps the members that fit, in place, so an option stays one option. A union pattern is no
 * product of its keys, and there the option splits and each part fits or not.
 *
 * The slice of a union and the slice of a field are one operation, and a pattern nests as a
 * codec nests: `pet: pet.extract(object({ status: string('AVAILABLE') }))`.
 */
type PatternSpecs<P> = FieldSpecList<P>[number]

/** The member specs of the codec at a field: each option of a union of objects, or the object itself. */
type FieldSpecList<F> = F extends { readonly item: { readonly spec: infer Sp } }
    ? Sp extends readonly unknown[]
        ? Sp
        : [Sp]
    : never

type FieldSpecsAt<S, K> = S extends unknown
    ? K extends keyof S
        ? FieldSpecList<Marks<S[K]>>[number]
        : never
    : never

type KeysOfUnion<U> = U extends unknown ? keyof U : never

/**
 * The keys of a union as a tuple. The order is the order that the checker gives, which no reader
 * relies on: each key splits one object field, and the decoded type is a union.
 */
type KeyTuple<U, Last = LastOf<U>> = [U] extends [never]
    ? []
    : [...KeyTuple<Exclude<U, Last>>, Last]
type LastOf<U> = UnionToIntersection<
    U extends unknown ? () => U : never
> extends () => infer R
    ? R
    : never

type ObjectOfSpec<S> = S extends Record<string, ObjectSlot>
    ? ObjectCodec<show<S>>
    : never

/** A spec, split at the keys of the pattern specs `PU` where the spec holds objects. */
type SplitSpec<Spec, PU> = SplitKeys<[Spec], KeyTuple<KeysOfUnion<PU>>, PU>
type SplitKeys<
    States extends readonly unknown[],
    Keys extends readonly unknown[],
    PU,
> = Keys extends readonly [infer Key, ...infer Rest extends readonly unknown[]]
    ? SplitKeys<SplitAt<States, Key, PU>, Rest, PU>
    : States
type SplitAt<
    States extends readonly unknown[],
    Key,
    PU,
> = States extends readonly [
    infer State,
    ...infer Rest extends readonly unknown[],
]
    ? [...SplitState<State, Key, PU>, ...SplitAt<Rest, Key, PU>]
    : []
type SplitState<State, Key, PU> = Key extends keyof State
    ? SplitsAtPresence<State[Key], PatternCodecsAt<PU, Key>> extends true
        ? ReplaceField<
              [
                  ...(SplitSlot<
                      Marks<State[Key]>,
                      PatternCodecsAt<PU, Key>
                  > extends infer Parts extends readonly unknown[]
                      ? Parts
                      : [Marks<State[Key]>]),
                  MarkLike<State[Key], typeof never>,
              ],
              State,
              Key
          >
        : SplitSlot<
                State[Key],
                PatternCodecsAt<PU, Key>
            > extends infer Parts extends readonly unknown[]
          ? ReplaceField<Parts, State, Key>
          : [State]
    : [State]
/** The codec at a key in each spec of a union of specs. */
type PatternCodecsAt<PU, Key> = PU extends unknown
    ? Key extends keyof PU
        ? PU[Key]
        : never
    : never
/**
 * One slot, a field or a position of a fixed list, split against the pattern codecs there: the
 * codecs of its parts, or `false` where it splits nowhere. A slot that holds objects splits as the
 * objects do. A fixed list is a product of its positions, so it splits at each position, and a
 * position is a slot again.
 */
type SplitSlot<C, PC> = [FixedElements<C>] extends [never]
    ? [FieldSpecList<C>] extends [never]
        ? false
        : MapObjects<InnerSpecs<FieldSpecList<C>, FieldSpecList<PC>[number]>>
    : SplitPositions<
            [C],
            PC,
            FixedElements<C>['length']
        > extends infer Ls extends readonly unknown[]
      ? [Ls] extends [[C]]
          ? [[C]] extends [Ls]
              ? false
              : Ls
          : Ls
      : false
/** The lists split at each position, against the positions that the pattern lists of its arity hold. */
type SplitPositions<
    Ls extends readonly unknown[],
    PC,
    N extends number,
    I extends readonly unknown[] = [],
> = I['length'] extends N
    ? Ls
    : SplitPositions<SplitAtPosition<Ls, PC, N, I['length']>, PC, N, [...I, 0]>
type SplitAtPosition<
    Ls extends readonly unknown[],
    PC,
    N extends number,
    I extends number,
> = Ls extends readonly [infer L, ...infer Rest extends readonly unknown[]]
    ? [...SplitPositionState<L, PC, N, I>, ...SplitAtPosition<Rest, PC, N, I>]
    : []
type SplitPositionState<
    L,
    PC,
    N extends number,
    I extends number,
> = FixedElements<L> extends infer Es extends readonly unknown[]
    ? [PositionCodecsAt<PC, `${I}`, N>] extends [never]
        ? [L]
        : SplitSlot<
                Es[I],
                PositionCodecsAt<PC, `${I}`, N>
            > extends infer Parts extends readonly unknown[]
          ? WithPosition<Parts, Es, I>
          : [L]
    : [L]
/** The codec at a position in each pattern list of the arity `N`. */
type PositionCodecsAt<PC, I, N> = PC extends unknown
    ? FixedElements<PC>['length'] extends N
        ? I extends keyof FixedElements<PC>
            ? FixedElements<PC>[I]
            : never
        : never
    : never
type WithPosition<
    Parts extends readonly unknown[],
    Es extends readonly unknown[],
    I extends number,
> = Parts extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ListCodec<{
              [J in keyof Es]: J extends `${I}` ? Head : Es[J]
          }>,
          ...WithPosition<Rest, Es, I>,
      ]
    : []
type InnerSpecs<
    Members extends readonly unknown[],
    PU,
> = Members extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [...SplitSpec<Head, PU>, ...InnerSpecs<Rest, PU>]
    : []
type ReplaceField<
    Parts extends readonly unknown[],
    State,
    Key,
> = Parts extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          {
              [P in keyof State]: P extends Key ? Head : State[P]
          },
          ...ReplaceField<Rest, State, Key>,
      ]
    : []

/** The options split at the keys of a pattern. An option that is no object stays whole. */
type SplitOptions<
    Options extends readonly unknown[],
    P,
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...(Head extends { readonly item: { readonly spec: infer Sp } }
              ? Sp extends readonly unknown[]
                  ? [Head]
                  : FitsCodec<Head, P> extends 't'
                    ? [Head]
                    : MapObjects<SplitSpec<Sp, PatternSpecs<P>>>
              : [Head]),
          ...SplitOptions<Rest, P>,
      ]
    : []
type MapObjects<Specs extends readonly unknown[]> = {
    [I in keyof Specs]: ObjectOfSpec<Specs[I]>
}

/**
 * **Whether a codec fits a pattern**, as the run time decides it, read on the types that the codecs
 * carry. `'t'` fits, `'f'` does not, and `'u'` is where the type cannot decide: the extraction and
 * the exclusion each keep such an option, so each result type admits every option that the run time
 * keeps.
 *
 * A pattern that pins a literal is met by a codec that pins one, at the same stored type and a
 * decoded type inside the pattern's. The mark is what tells a literal from a caller's adapter that
 * decodes to a literal type. The stored type is what tells `string('1')` from `decimal('1')`, which
 * decode to one text. A pattern that holds objects is met by a codec that holds objects, each of
 * them inside some object of the pattern ({@link SpecFits}). Any other pattern is met by a codec
 * whose decoded and stored types lie inside the pattern's. A literal whose alternatives the type
 * cannot name ({@link UnnamedValues}) is `'u'`.
 */
type Fit = 't' | 'f' | 'u'
type FitsCodec<A, P> = PinsALiteral<MarkedCodec<P>> extends true
    ? PinsALiteral<MarkedCodec<A>> extends true
        ? [AttributeOf<A>] extends [AttributeOf<P>]
            ? [Decoded<A>] extends [Decoded<P>]
                ? true extends UnnamedValues<Decoded<P>>
                    ? 'u'
                    : 't'
                : 'f'
            : 'f'
        : 'f'
    : ListFit<A, P> extends infer LF extends Fit
      ? LF
      : [FieldSpecList<P>] extends [never]
        ? [Decoded<A>] extends [Decoded<P>]
            ? [AttributeOf<A>] extends [AttributeOf<P>]
                ? 't'
                : 'f'
            : 'f'
        : [FieldSpecList<A>] extends [never]
          ? 'f'
          : EveryFits<FieldSpecList<A>[number], FieldSpecList<P>[number]>
/** The fit of two lists with fixed positions, or `'none'` where either has none. */
type ListFit<A, P> = [FixedElements<P>] extends [never]
    ? 'none'
    : [FixedElements<A>] extends [never]
      ? 'none'
      : FitsPositions<FixedElements<A>, FixedElements<P>>
/** A list fits a list pattern of its arity where each position fits, as the run time reads a product. */
type FitsPositions<
    AE extends readonly unknown[],
    PE extends readonly unknown[],
> = AE['length'] extends PE['length']
    ? AllOf<
          {
              [I in keyof AE]: I extends keyof PE
                  ? FitsCodec<AE[I], PE[I]>
                  : 'f'
          }[number]
      >
    : 'f'
/** Whether a member spec fits a pattern codec: the pattern must hold objects. */
type FitsSpec<A, P> = [FieldSpecList<P>] extends [never]
    ? 'f'
    : EveryFits<A, PatternSpecs<P>>
/** Each member spec of the codec fits some member spec of the pattern. */
type EveryFits<A, P> = AllOf<A extends unknown ? SomeFit<A, P> : never>
type SomeFit<A, P> = 't' extends SpecFits<A, P>
    ? 't'
    : 'u' extends SpecFits<A, P>
      ? 'u'
      : 'f'
type SpecFits<A, P> = P extends unknown
    ? AllOf<
          {
              [K in keyof P]-?: K extends keyof A
                  ? [P[K]] extends [{ readonly [optionalMarker]: true }]
                      ? FitsCodec<A[K], P[K]>
                      : [A[K]] extends [{ readonly [optionalMarker]: true }]
                        ? 'f'
                        : FitsCodec<A[K], P[K]>
                  : [P[K]] extends [{ readonly [optionalMarker]: true }]
                    ? 't'
                    : 'f'
          }[keyof P]
      >
    : never
type AllOf<U extends Fit> = 'f' extends U ? 'f' : 'u' extends U ? 'u' : 't'
/** Whether the extraction (`Keep` true) or the exclusion keeps a codec with this fit. */
type KeepsFit<Keep extends boolean, F extends Fit> = Keep extends true
    ? F extends 'f'
        ? false
        : true
    : F extends 't'
      ? false
      : true

/**
 * **The option codecs that a union pattern keeps**, in the order they were declared, after the
 * split. A union pattern is no product of its keys, so an option splits at each field that the
 * pattern names, and the parts that fit stay. `Keep` is `true` for the extraction and `false` for
 * the exclusion, so the two are one walk and the complement cannot drift from the selection.
 */
type KeptSplit<
    Options extends readonly unknown[],
    P,
    Keep extends boolean = true,
> = KeptBy<SplitOptions<Options, P>, P, Keep>
type KeptBy<
    Options extends readonly unknown[],
    P,
    Keep extends boolean,
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...(KeepsFit<Keep, FitsCodec<Head, P>> extends true ? [Head] : []),
          ...KeptBy<Rest, P, Keep>,
      ]
    : []

type SameList<A extends readonly unknown[], B extends readonly unknown[]> = [
    A,
] extends [B]
    ? [B] extends [A]
        ? true
        : false
    : false

/** A split key of an option: the summand specs that the pattern keeps and rejects, and the summands as declared. */
type NestedKey<
    K,
    Keep extends readonly unknown[],
    Rest extends readonly unknown[],
    Orig extends readonly unknown[],
    Opt = never,
> = { key: K; keep: Keep; rest: Rest; orig: Orig; opt: Opt }

/** The one summand of a field that holds no object: the field as declared. */
type WholeField = { readonly whole: true }

/** Whether a field may be absent where the pattern requires the key: the field splits at presence. */
type SplitsAtPresence<A, P> = [A] extends [{ readonly [optionalMarker]: true }]
    ? [P] extends [{ readonly [optionalMarker]: true }]
        ? false
        : true
    : false

/**
 * A field that may be absent, against a pattern that requires the key: the present part follows
 * the fit of the declared codec, and the absent part is rejected.
 */
type SlicePresence<
    S,
    K extends keyof S,
    R extends readonly unknown[],
    PS,
    PK,
    Leaf extends Fit,
    Nested extends readonly unknown[],
> = SlotSlice<Marks<S[K]>, PK> extends infer Out
    ? Out extends { fit: 't' }
        ? SliceKeys<
              S,
              R,
              PS,
              Leaf,
              [...Nested, NestedKey<K, [WholeField], [], [WholeField], S[K]>]
          >
        : Out extends { fit: infer F extends Fit }
          ? SliceKeys<S, R, PS, Leaf | F, Nested>
          : Out extends {
                  keep: infer Kp extends readonly unknown[]
                  rest: infer Rs extends readonly unknown[]
              }
            ? SliceKeys<
                  S,
                  R,
                  PS,
                  Leaf,
                  [
                      ...Nested,
                      NestedKey<K, Kp, Rs, FieldSpecList<Marks<S[K]>>, S[K]>,
                  ]
              >
            : never
    : never

/**
 * The summands of a field, each kept whole, rejected whole, or sliced against the one object that
 * the pattern holds there. A summand that fits whole stays whole.
 */
type SliceSummands<
    Summands extends readonly unknown[],
    PK extends readonly unknown[],
    Keep extends readonly unknown[] = [],
    Rest extends readonly unknown[] = [],
> = Summands extends readonly [
    infer Head,
    ...infer Tail extends readonly unknown[],
]
    ? EveryFits<Head, PK[number]> extends 't'
        ? SliceSummands<Tail, PK, [...Keep, Head], Rest>
        : true extends IsUnion<PK[number]>
          ? EveryFits<Head, PK[number]> extends 'u'
              ? SliceSummands<Tail, PK, [...Keep, Head], [...Rest, Head]>
              : SliceSummands<Tail, PK, Keep, [...Rest, Head]>
          : SliceSpecOf<Head, PK[number]> extends {
                  keep: infer K extends readonly unknown[]
                  rest: infer R extends readonly unknown[]
              }
            ? SliceSummands<Tail, PK, [...Keep, ...K], [...Rest, ...R]>
            : never
    : { keep: Keep; rest: Rest }

/** A spec against one object pattern: the fit of the keys that do not split, and the keys that split. */
type SliceKeys<
    S,
    Keys extends readonly unknown[],
    PS,
    Leaf extends Fit,
    Nested extends readonly unknown[],
> = Keys extends readonly [infer K, ...infer R extends readonly unknown[]]
    ? K extends keyof PS
        ? K extends keyof S
            ? SplitsAtPresence<S[K], PS[K]> extends true
                ? SlicePresence<S, K, R, PS, PS[K], Leaf, Nested>
                : FitsCodec<S[K], PS[K]> extends 't'
                  ? SliceKeys<S, R, PS, Leaf, Nested>
                  : ListFit<S[K], PS[K]> extends 'u' | 'f'
                    ? FixedElements<S[K]>['length'] extends FixedElements<
                          PS[K]
                      >['length']
                        ? SlicePositions<
                              S,
                              R,
                              PS,
                              K,
                              FixedElements<S[K]>,
                              FixedElements<PS[K]>,
                              Leaf,
                              Nested
                          >
                        : SliceKeys<S, R, PS, Leaf | 'f', Nested>
                    : [FieldSpecList<S[K]>] extends [never]
                      ? SliceKeys<
                            S,
                            R,
                            PS,
                            Leaf | FitsCodec<S[K], PS[K]>,
                            Nested
                        >
                      : [FieldSpecList<PS[K]>] extends [never]
                        ? SliceKeys<
                              S,
                              R,
                              PS,
                              Leaf | FitsCodec<S[K], PS[K]>,
                              Nested
                          >
                        : SliceSummands<
                                FieldSpecList<S[K]>,
                                FieldSpecList<PS[K]>
                            > extends {
                                keep: infer Kp extends readonly unknown[]
                                rest: infer Rs extends readonly unknown[]
                            }
                          ? SliceKeys<
                                S,
                                R,
                                PS,
                                Leaf,
                                [
                                    ...Nested,
                                    NestedKey<K, Kp, Rs, FieldSpecList<S[K]>>,
                                ]
                            >
                          : never
            : [PS[K]] extends [{ readonly [optionalMarker]: true }]
              ? SliceKeys<S, R, PS, Leaf, Nested>
              : SliceKeys<S, R, PS, Leaf | 'f', Nested>
        : SliceKeys<S, R, PS, Leaf, Nested>
    : { leaf: AllOf<Leaf>; nested: Nested }

/**
 * The positions of a fixed list at the key `K`, each read as a slot of the object: a position that
 * the pattern does not hold whole is one more split slot, keyed `[K, index]`.
 */
type SlicePositions<
    S,
    R extends readonly unknown[],
    PS,
    K,
    AE extends readonly unknown[],
    PE extends readonly unknown[],
    Leaf extends Fit,
    Nested extends readonly unknown[],
    I extends readonly unknown[] = [],
> = I['length'] extends AE['length']
    ? SliceKeys<S, R, PS, Leaf, Nested>
    : SlotSlice<AE[I['length']], PE[I['length']]> extends infer Out
      ? Out extends {
            keep: infer Kp extends readonly unknown[]
            rest: infer Rs extends readonly unknown[]
        }
          ? SlicePositions<
                S,
                R,
                PS,
                K,
                AE,
                PE,
                Leaf,
                [
                    ...Nested,
                    NestedKey<
                        [K, I['length']],
                        Kp,
                        Rs,
                        FieldSpecList<AE[I['length']]>
                    >,
                ],
                [...I, 0]
            >
          : Out extends { fit: infer F extends Fit }
            ? SlicePositions<S, R, PS, K, AE, PE, Leaf | F, Nested, [...I, 0]>
            : never
      : never
/** One slot against the pattern there: its fit where it does not split, else its summands kept and rejected. */
type SlotSlice<A, P> = FitsCodec<A, P> extends 't'
    ? { fit: 't' }
    : [FieldSpecList<A>] extends [never]
      ? { fit: FitsCodec<A, P> }
      : [FieldSpecList<P>] extends [never]
        ? { fit: FitsCodec<A, P> }
        : SliceSummands<FieldSpecList<A>, FieldSpecList<P>>

/** The list at a key with one position replaced by the kept or the rejected summands. */
type ReplacePosition<
    Slot,
    I,
    Head extends Replacement,
> = FixedElements<Slot> extends infer Es extends readonly unknown[]
    ? ListCodec<{
          [J in keyof Es]: J extends `${I & number}`
              ? FieldOf<Head['list'], Head['orig'], Es[J]>
              : Es[J]
      }>
    : Slot

type Replacement = {
    key: unknown
    list: readonly unknown[]
    orig: readonly unknown[]
    opt: unknown
    of: 'keep' | 'rest'
}

/**
 * The field that holds the kept or the rejected part of a field that may be absent. The kept part
 * is present, so the key is required. The rejected part keeps the mark, and holds `never` where
 * the pattern rejects no present value.
 */
type PresenceField<Head extends Replacement> = (
    Head['list'] extends readonly []
        ? typeof never
        : FieldOf<Head['list'], Head['orig'], Marks<Head['opt']>>
) extends infer C extends AnyCodec
    ? Head['of'] extends 'keep'
        ? C
        : MarkLike<Head['opt'], C>
    : never
/** The codec `C` under the presence mark of the declared field `Opt`. */
type MarkLike<Opt, C extends AnyCodec> = Opt extends {
    readonly [undefinableMarker]: true
}
    ? UndefinableCodec<Decoded<C>, AttributeOf<C>, C> &
          TermMark<['optional', TermOf<C>]>
    : OptionalCodec<Decoded<C>, AttributeOf<C>, C> &
          TermMark<['optional', TermOf<C>]>

/** The slot that holds the kept summands: the declared slot where they are all of them, else their union. */
type FieldOf<
    L extends readonly unknown[],
    Orig extends readonly unknown[],
    Slot,
> = true extends SameList<L, Orig>
    ? Slot
    : L extends readonly [infer One]
      ? ObjectOfSpec<One>
      : UnionCodec<DerivedUnion<MapObjects<L>>, MapObjects<L>>
type ReplaceAll<S, Rs extends readonly unknown[]> = Rs extends readonly [
    infer Head extends Replacement,
    ...infer Tail extends readonly unknown[],
]
    ? ReplaceAll<
          Head['key'] extends readonly [infer K, infer I]
              ? {
                    [P in keyof S]: P extends K
                        ? ReplacePosition<S[P], I, Head>
                        : S[P]
                }
              : {
                    [P in keyof S]: P extends Head['key']
                        ? [Head['opt']] extends [never]
                            ? FieldOf<Head['list'], Head['orig'], S[P]>
                            : PresenceField<Head>
                        : S[P]
                },
          Tail
      >
    : S
type Lists<Nested extends readonly unknown[], Of extends 'keep' | 'rest'> = {
    [I in keyof Nested]: Nested[I] extends {
        key: infer K
        keep: infer Kp
        rest: infer Rs
        orig: infer O
        opt: infer Opt
    }
        ? {
              key: K
              list: Of extends 'keep' ? Kp : Rs
              orig: O
              opt: Opt
              of: Of
          }
        : never
}
type NonEmptyAll<Ls extends readonly unknown[]> = Ls extends readonly [
    infer H extends { list: readonly unknown[] },
    ...infer T extends readonly unknown[],
]
    ? H['list'] extends readonly []
        ? false
        : NonEmptyAll<T>
    : true

type SliceInfo = { leaf: Fit; nested: readonly unknown[] }

/** The kept spec: one spec with a union at each split field, or nothing. */
type KeptSpecs<S, Info extends SliceInfo> = Info['leaf'] extends 'f'
    ? []
    : Info['nested'] extends readonly []
      ? [S]
      : NonEmptyAll<Lists<Info['nested'], 'keep'>> extends true
        ? [ReplaceAll<S, Lists<Info['nested'], 'keep'>>]
        : []

/**
 * The rejected specs: one for each split key whose rejected summands remain, with the keys before it
 * kept and the keys after it as declared. The complement of a product is no product, and this is
 * its cover.
 */
type RestSpecs<S, Info extends SliceInfo> = Info['leaf'] extends 'f' | 'u'
    ? [S]
    : RestAt<S, Info['nested'], []>
type RestAt<
    S,
    Nested extends readonly unknown[],
    Before extends readonly unknown[],
> = Nested extends readonly [
    infer N extends {
        key: unknown
        keep: readonly unknown[]
        rest: readonly unknown[]
        orig: readonly unknown[]
        opt: unknown
    },
    ...infer Tail extends readonly unknown[],
]
    ? [
          // the absent part of a field that may be absent is rejected whatever the present part holds
          ...(N['rest'] extends readonly []
              ? [N['opt']] extends [never]
                  ? []
                  : RestOf<S, Before, N>
              : RestOf<S, Before, N>),
          ...RestAt<S, Tail, [...Before, N]>,
      ]
    : []
type RestOf<
    S,
    Before extends readonly unknown[],
    N extends {
        key: unknown
        rest: readonly unknown[]
        orig: readonly unknown[]
        opt: unknown
    },
> = NonEmptyAll<Lists<Before, 'keep'>> extends true
    ? [
          ReplaceAll<
              S,
              [
                  ...Lists<Before, 'keep'>,
                  {
                      key: N['key']
                      list: N['rest']
                      orig: N['orig']
                      opt: N['opt']
                      of: 'rest'
                  },
              ]
          >,
      ]
    : []

type SliceSpecOf<S, PS> = SliceKeys<
    S,
    KeyTuple<keyof PS>,
    PS,
    't',
    []
> extends infer Info extends SliceInfo
    ? { keep: KeptSpecs<S, Info>; rest: RestSpecs<S, Info> }
    : never

/**
 * Whether a summand of a field fits a member of a union pattern in part: some of its values fit,
 * and not all. The run time splits the option then, and keeps the parts that fit.
 */
type PartialMember<Hd, M> = M extends unknown
    ? SliceSpecOf<Hd, M>['keep'] extends readonly []
        ? false
        : true
    : never
type PartialSummand<Hd, PK extends readonly unknown[]> = EveryFits<
    Hd,
    PK[number]
> extends 't'
    ? false
    : true extends IsUnion<PK[number]>
      ? PartialMember<Hd, PK[number]>
      : HasPartialFit<Hd, PK[number]>
type PartialSummands<
    Summands extends readonly unknown[],
    PK extends readonly unknown[],
> = {
    [I in keyof Summands]: PartialSummand<Summands[I], PK>
}[number]
/**
 * Whether some field of a spec holds a summand that fits a union-pattern member in part. The
 * compact slice cannot state that case, because it would drop the whole summand and the run time
 * keeps the parts. The type splits the option as the run time does ({@link KeptSplit}).
 */
type HasPartialFit<S, PS> = true extends {
    [K in keyof PS]: K extends keyof S
        ? [FieldSpecList<S[K]>] extends [never]
            ? false
            : [FieldSpecList<PS[K]>] extends [never]
              ? false
              : FitsCodec<S[K], PS[K]> extends 't'
                ? false
                : PartialSummands<FieldSpecList<S[K]>, FieldSpecList<PS[K]>>
        : false
}[keyof PS]
    ? true
    : false

/**
 * **The option codecs that a pattern keeps**, in the order they were declared. `Keep` is `true` for
 * the extraction and `false` for the exclusion.
 *
 * **The slice goes into the field and the result stays compact.** An option `{ k, pet: U }` against
 * the pattern `{ pet: P }` is `{ k, pet: Extract<U, P> }`, one option with a narrower union, as
 * TypeScript's `Extract` reads it. So the extraction has one option for each option that it keeps,
 * and no more, which is what the model's slice of a union states. The exclusion has one option for
 * each split key, because the complement of a product is no product. A union pattern is no product of
 * its keys, and keeps the split ({@link KeptSplit}), and so does a pattern that holds no object.
 */
export type KeptOptions<
    Options extends readonly unknown[],
    P,
    Keep extends boolean = true,
> = [FieldSpecList<P>] extends [never]
    ? KeptSplit<Options, P, Keep>
    : true extends IsUnion<PatternSpecs<P>>
      ? KeptSplit<Options, P, Keep>
      : KeptCompact<Options, P, Keep>
type KeptCompact<
    Options extends readonly unknown[],
    P,
    Keep extends boolean,
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...(Head extends { readonly item: { readonly spec: infer Sp } }
              ? Sp extends readonly unknown[]
                  ? KeepsFit<Keep, FitsCodec<Head, P>> extends true
                      ? [Head]
                      : []
                  : FitsCodec<Head, P> extends 't'
                    ? Keep extends true
                        ? [Head]
                        : []
                    : HasPartialFit<Sp, PatternSpecs<P>> extends true
                      ? KeptSplit<[Head], P, Keep>
                      : SliceSpecOf<
                              Sp,
                              PatternSpecs<P>
                          > extends infer Sl extends {
                              keep: readonly unknown[]
                              rest: readonly unknown[]
                          }
                        ? SameSpecOrObject<
                              Keep extends true ? Sl['keep'] : Sl['rest'],
                              Sp,
                              Head
                          >
                        : []
              : KeepsFit<Keep, FitsCodec<Head, P>> extends true
                ? [Head]
                : []),
          ...KeptCompact<Rest, P, Keep>,
      ]
    : []
/** The option itself where its spec is unchanged, else the object of the new spec. */
type SameSpecOrObject<Specs extends readonly unknown[], Sp, Head> = {
    [I in keyof Specs]: [Specs[I]] extends [Sp]
        ? [Sp] extends [Specs[I]]
            ? Head
            : ObjectOfSpec<Specs[I]>
        : ObjectOfSpec<Specs[I]>
}

/** The member specs of a dissection that a pattern keeps. A dissection splits no member. */
export type Extracted<
    Specs extends readonly unknown[],
    P,
    Keep extends boolean = true,
> = Specs extends readonly [
    infer Head,
    ...infer Tail extends readonly unknown[],
]
    ? [
          ...(KeepsFit<Keep, FitsSpec<Head, P>> extends true ? [Head] : []),
          ...Extracted<Tail, P, Keep>,
      ]
    : []

/** …and the ones it rejects, the same walk at the complement. */
export type Excluded<Specs extends readonly unknown[], P> = Extracted<
    Specs,
    P,
    false
>

/** The members of a tag table a pattern keeps, keyed as they were. */
export type KeptByTag<Spec, P, Keep extends boolean = true> = {
    [K in keyof Spec as KeepsFit<Keep, FitsSpec<Spec[K], P>> extends true
        ? K
        : never]: Spec[K]
}

/** The codec a spec declares at one name, or nothing where it declares none. */
type FieldAt<Spec, K> = K extends keyof Spec ? Spec[K] : never

/** The entity a tag table describes, which is what its members describe. */
export type VariantsOf<Spec> = {
    [K in keyof Spec]: show<ObjectOf<Spec[K]>>
}[keyof Spec]

/**
 * The tags the members carry at one key, at one attribute — and only where the member pins a
 * literal there.
 *
 * The last clause is what stops a clause selecting on a plain field: `toy: string` writes an `S`
 * and admits every string, so a clause naming `'t'` would fit it and select nothing meaningful.
 */
type TagsAtSpecs<S, K, A> = S extends unknown
    ? K extends RequiredKeysOf<S>
        ? [AttributeOf<FieldAt<S, K>>] extends [A]
            ? PinsALiteral<MarkedCodec<FieldAt<S, K>>> extends true
                ? Decoded<FieldAt<S, K>>
                : never
            : never
        : never
    : never

/**
 * A key of a pattern that describes no member, whatever the values turn out to be: the model's
 * clause that is not keyed (`Calculus.AltClause.keyedC`), read at a pattern. A key is bad where no
 * member declares it, and where it pins a literal that no member pins at that base. A key that
 * holds objects is read one level down. A literal whose alternatives meet no member's is keyed, and
 * keeps nothing: that is a fact about the values, and the run time answers it.
 */
type BadPatternKey<S, PSpec> = {
    [K in keyof PSpec]: PinsALiteral<PSpec[K]> extends true
        ? [TagsAtSpecs<S, K, AttributeOf<PSpec[K]>>] extends [never]
            ? K
            : [CarrierOf<Decoded<PSpec[K]>>] extends [
                    CarrierOf<TagsAtSpecs<S, K, AttributeOf<PSpec[K]>>>,
                ]
              ? never
              : K
        : [FixedElements<PSpec[K]>] extends [never]
          ? BadObjectKey<S, PSpec, K>
          : [K] extends [KeysOfUnion<S>]
            ? BadPosition<S, K, FixedElements<PSpec[K]>>
            : K
}[keyof PSpec]
/**
 * A position of a fixed list answers to the refusals of a key, and a position that holds a fixed
 * list is a slot again. A position that no member declares is a refusal at the key: an `array`
 * declares no position, because its length is a run-time fact, so `FixedElements` of an array is
 * `never` and a fixed pattern reaches nothing in it.
 */
type BadPosition<
    S,
    K,
    PE extends readonly unknown[],
> = true extends BadPositions<PatternCodecsAt<S, K>, PE> ? K : never
type BadPositions<MC, PE extends readonly unknown[]> = {
    [I in keyof PE]: BadAtPosition<PositionCodecsAt<MC, I, number>, PE[I]>
}[number]
/** Whether the pattern codec `PC` at a slot describes nothing that the member codecs `MC` hold there. */
type BadAtPosition<MC, PC> = [FixedElements<PC>] extends [never]
    ? [FieldSpecList<PC>] extends [never]
        ? never
        : [FieldSpecList<MC>] extends [never]
          ? true
          : [
                  BadPatternKey<
                      FieldSpecList<MC>[number],
                      FieldSpecList<PC>[number]
                  >,
              ] extends [never]
            ? never
            : true
    : BadPositions<MC, FixedElements<PC>>
type BadObjectKey<S, PSpec, K extends keyof PSpec> = [
    FieldSpecList<PSpec[K]>,
] extends [never]
    ? [K] extends [KeysOfUnion<S>]
        ? never
        : K
    : [FieldSpecsAt<S, K>] extends [never]
      ? K
      : [
              BadPatternKey<
                  FieldSpecsAt<S, K>,
                  FieldSpecList<PSpec[K]>[number]
              >,
          ] extends [never]
        ? never
        : K

/**
 * Rejects a pattern that no member could answer, at the call rather than on the result. Each
 * failure is decidable from the declaration, which is the line that the run time refuses on too.
 */
export type ValidatePattern<S, P> = [FieldSpecList<P>] extends [never]
    ? unknown
    : [BadPatternKey<S, PatternSpecs<P>>] extends [never]
      ? unknown
      : ErrorMessage<`[extract] the pattern at '${BadPatternKey<S, PatternSpecs<P>> & string}' describes no member — no member declares the key, or none pins it to that literal at that base, or it holds no objects where the pattern nests`>

/**
 * **The carrier of a decoded literal**: the base type that the literal widens to. At one attribute
 * the carrier names the adapter word of the model's form (`Calculus.pinForm`): `number`, `decimal`
 * and `dynamoNumber` each write `N`, and decode a `number`, a `string` and a {@link DynamoNumber}.
 */
type CarrierOf<V> = V extends string
    ? string
    : V extends number
      ? number
      : V extends boolean
        ? boolean
        : V extends DynamoNumber
          ? DynamoNumber
          : V

/**
 * **Two literals of one form**: the same base, and the same adapter, or none on either. This is the
 * form of the model's pin (`Calculus.pinForm`), the adapter word and the base.
 */
const sameForm = (a: NameForm, b: NameForm): boolean =>
    a.form === b.form &&
    (a.adapter === undefined || b.adapter === undefined
        ? a.adapter === b.adapter
        : sameAdapter(a.adapter, b.adapter))

/**
 * Whether every value that the term `a` holds lies inside what the term `p` holds, on the fragment
 * that the host decides. A literal is read through a refinement on the side of the option, because
 * a refinement narrows a literal and the literal stays an upper bound. A pair that no rule here
 * covers fits only where the two terms are one term, so the answer errs towards no fit.
 *
 * The literal rule is `Calculus.altsSub`, and the object rule asks each key of the pattern: a
 * required key of the pattern is a required key of the option, and an absent key of the option fits
 * an optional key of the pattern only where the option has no open key entry.
 */
const fits = (a: Term, p: Term): boolean => {
    const A = resolvedTerm(a)
    const P = resolvedTerm(p)
    if (A === undefined || P === undefined) return false
    if (A === P) return true
    if (A.kind === 'union') return A.options.every((one) => fits(one, P))
    if (P.kind === 'union') return P.options.some((one) => fits(A, one))
    const pinned = clauseForm(P)
    if (pinned) {
        const mine = pinnedForm(A)
        return (
            mine !== undefined &&
            mine.form === pinned.form &&
            sameForm(
                { required: true, ...mine },
                { required: true, ...pinned },
            ) &&
            (mine.alts.ls as readonly LiteralValue[]).every((one) =>
                (pinned.alts.ls as readonly LiteralValue[]).some((tag) =>
                    sameLiteral(one, tag),
                ),
            )
        )
    }
    if (P.kind === 'object') {
        if (A.kind !== 'object') return false
        for (const [name, wanted] of Object.entries(P.body.fields)) {
            const mine = A.body.fields[name]
            if (mine === undefined) {
                if (alwaysWritten(wanted) || A.body.rest !== undefined) {
                    return false
                }
                continue
            }
            if (alwaysWritten(wanted) && !alwaysWritten(mine)) return false
            if (!fits(mine.t, wanted.t)) return false
        }
        return true
    }
    // a list is a product of its positions: the same layout, and each position inside the pattern's
    if (P.kind === 'list') {
        if (A.kind !== 'list') return false
        const { spread } = P
        return (
            A.pre.length === P.pre.length &&
            A.suf.length === P.suf.length &&
            (A.spread === undefined) === (spread === undefined) &&
            A.pre.every((one, at) => {
                const there = P.pre[at]
                return there !== undefined && fits(one, there)
            }) &&
            A.suf.every((one, at) => {
                const there = P.suf[at]
                return there !== undefined && fits(one, there)
            }) &&
            (A.spread === undefined ||
                (spread !== undefined && fits(A.spread, spread)))
        )
    }
    if (A.kind === 'held' && P.kind === 'held') {
        return sameAdapter(A, P) && fits(A.inner, P.inner)
    }
    // a literal fits the base that it is a literal of
    const literal = pinnedForm(A)
    if (
        literal &&
        literal.adapter === undefined &&
        literal.alts.base === P.kind
    ) {
        return true
    }
    if (A.kind !== P.kind) return false
    return (
        A.kind === 'string' ||
        A.kind === 'number' ||
        A.kind === 'boolean' ||
        A.kind === 'binary' ||
        A.kind === 'null'
    )
}

/** The object nodes that a term names: the object itself, or each object option of a union. */
const objectMembersOf = (
    t: Term,
): readonly Extract<Term, { kind: 'object' }>[] => {
    const node = resolvedTerm(t)
    if (node === undefined) return []
    if (node.kind === 'object') return [node]
    return node.kind === 'union' ? node.options.flatMap(objectMembersOf) : []
}

/** Whether a term is an object, or a union of objects only. */
const holdsObjects = (node: Term | undefined): boolean =>
    node?.kind === 'union'
        ? node.options.every((option) => objectNamed(option) !== undefined)
        : node !== undefined && objectNamed(node) !== undefined

/**
 * The codecs that a pattern splits one slot into, where a slot is a field or a position of a fixed
 * list. The slot comes back as the one element where it splits nowhere. A slot that holds objects
 * splits as the objects do. A fixed list is a product of its positions, as an object is a product of
 * its keys, so it splits at each position, and a position is a slot again.
 *
 * An object that is split and has an open key entry is refused, because the type of a part holds
 * the declared names only, and a part that reads more would decode a value that its type does not
 * name. The type cannot state the refusal, so the run time does.
 */
const splitSlot = (
    name: string,
    slot: AnyCodec,
    pattern: Term,
): readonly AnyCodec[] => {
    const node = resolvedTerm(termOf(slot))
    if (node?.kind === 'list') return splitList(name, slot, node, pattern)
    if (!holdsObjects(node)) return [slot]
    const parts = optionsOfFactor(slot).flatMap((one) =>
        splitBy(one.spec as Record<string, ObjectSlot>, pattern).map(
            (inner) => ({ one, inner }),
        ),
    )
    const [only] = parts
    if (parts.length === 1 && only?.inner === only?.one.spec) return [slot]
    return parts.map(({ one, inner }) => {
        if (one.rest !== undefined) {
            throw new CodecError(
                `'${name}' holds an object with an open key entry, and a pattern splits declared names only`,
            )
        }
        return objectFromMap(inner, undefined) as unknown as AnyCodec
    })
}

/** The list term that a term is, where it has no spread and no suffix: its length is fixed. */
const fixedList = (t: Term | undefined) =>
    t?.kind === 'list' && t.spread === undefined && t.suf.length === 0
        ? t
        : undefined

/**
 * A fixed list split at each position, against the positions that the pattern lists of the same
 * arity hold there. A pattern list of another arity names no position of this list. The parts of the
 * earlier positions split again at the later ones.
 */
const splitList = (
    name: string,
    slot: AnyCodec,
    node: Term,
    pattern: Term,
): readonly AnyCodec[] => {
    const arity = fixedList(node)?.pre.length
    if (arity === undefined) return [slot]
    const wanted = (
        pattern.kind === 'union' ? pattern.options : [pattern]
    ).flatMap((one) => {
        const list = fixedList(resolvedTerm(one))
        return list?.pre.length === arity ? [list] : []
    })
    let codecs = [slot]
    for (let at = 0; at < arity; at++) {
        const sub: Term = {
            kind: 'union',
            options: wanted.flatMap((list) => list.pre.slice(at, at + 1)),
        }
        codecs = codecs.flatMap((one) => {
            const list = fixedList(resolvedTerm(termOf(one)))
            const there = list?.pre[at]
            if (list === undefined || there === undefined) return [one]
            if (sub.options.length === 0) return [one]
            const position = codecOfTerm(there)
            const parts = splitSlot(name, position, sub)
            if (parts.length === 1 && parts[0] === position) return [one]
            return parts.map(
                (part) =>
                    codecOfTerm({
                        kind: 'list',
                        pre: list.pre.map((held, i) =>
                            i === at ? termOf(part) : held,
                        ),
                        suf: [],
                    }) as unknown as AnyCodec,
            )
        })
    }
    return codecs
}

/**
 * A spec, split at each field that the pattern names and that holds objects or a fixed list. The
 * spec comes back as it was, and as the one element, where no field splits.
 */
const splitBy = (
    spec: Record<string, ObjectSlot>,
    pattern: Term,
    presence = true,
): Record<string, ObjectSlot>[] => {
    const members = objectMembersOf(pattern)
    let states: Record<string, ObjectSlot>[] = [spec]
    const names = new Set(members.flatMap((m) => Object.keys(m.body.fields)))
    for (const name of names) {
        const sub: Term = {
            kind: 'union',
            options: members.flatMap((m) => {
                const field = m.body.fields[name]
                return field ? [field.t] : []
            }),
        }
        const required = members.some((m) => {
            const field = m.body.fields[name]
            return field !== undefined && alwaysWritten(field)
        })
        states = states.flatMap((state) => {
            const slot = state[name]
            if (slot === undefined) return [state]
            // a field that may be absent is the union of a present part and an absent part
            const declared = fieldOf(slot)
            if (presence && required && !alwaysWritten(declared)) {
                const absent =
                    declared.mark === 'undefinable'
                        ? undefinable(never)
                        : optional(never)
                return [...splitSlot(name, entryCodec(slot), sub), absent].map(
                    (part) => ({
                        ...state,
                        [name]: part as unknown as ObjectSlot,
                    }),
                )
            }
            if ('codec' in slot) return [state]
            const field = entryCodec(slot)
            const parts = splitSlot(name, field, sub)
            if (parts.length === 1 && parts[0] === field) return [state]
            return parts.map((part) => ({
                ...state,
                [name]: part as unknown as ObjectSlot,
            }))
        })
    }
    return states
}

/**
 * Why a pattern describes no member, or nothing. A key that no member declares, a literal that no
 * member pins at that key, and a literal at a base that no member pins there are facts of the
 * declaration, decidable before any item exists, so a pattern that names one is a typo and not an
 * answer. An empty result stays a legitimate answer where the bases agree and the alternatives
 * simply do not meet, because that is a fact about values.
 *
 * The model states the same refusal (`AltClause.keyedC`): some option pins each key at the form of
 * the clause, or the clause describes no option (`AltClause.extractC_eq_nil_of_keyedC_false`).
 */
const patternRefusal = (
    members: readonly Term[],
    pattern: Term,
): string | undefined => {
    const candidates = members.flatMap(objectMembersOf)
    for (const wanted of objectMembersOf(pattern)) {
        for (const [name, field] of Object.entries(wanted.body.fields)) {
            const here = candidates.flatMap((m) => {
                const mine = m.body.fields[name]
                return mine ? [mine] : []
            })
            if (here.length === 0) {
                const known = [
                    ...new Set(
                        candidates.flatMap((m) => Object.keys(m.body.fields)),
                    ),
                ]
                return `'${name}' is not a key any member declares; the keys available are ${known.map((one) => `'${one}'`).join(', ') || '(none)'}`
            }
            const form = clauseForm(field.t)
            if (form) {
                const pins = here.flatMap((mine) => {
                    const one = pinnedForm(mine.t)
                    return one ? [one] : []
                })
                if (pins.length === 0) {
                    return `'${name}' is declared without a literal by every member, so a pattern cannot select on it`
                }
                const sameBase = pins.some(
                    (one) =>
                        one.form === form.form &&
                        sameForm(
                            { required: true, ...one },
                            { required: true, ...form },
                        ),
                )
                if (!sameBase) {
                    return `the pattern at '${name}' is a \`${form.form}\` literal${form.adapter ? ' under an adapter' : ''} and no member pins '${name}' at that base and adapter, so it describes no member whatever its alternatives; the bases pinned at '${name}' are ${[...new Set(pins.map((one) => one.form))].map((one) => `\`${one}\``).join(', ')}`
                }
            } else if (resolvedTerm(field.t)?.kind === 'refine') {
                return `the pattern at '${name}' holds a refinement, and the host cannot decide whether a member lies inside a predicate. Pin the key to a literal, or slice the field first`
            } else {
                const inner = slotRefusal(
                    name,
                    here.map((mine) => mine.t),
                    field.t,
                )
                if (inner) return inner
            }
        }
    }
    return undefined
}

/**
 * Why a pattern at one slot, a field or a position of a list, describes no member. A fixed list is a
 * product of its positions, so each position is a slot again, and a pattern there answers to the
 * same refusals as a key. An array declares no position, because its length is a run-time fact, so a
 * fixed pattern that holds objects reaches nothing in it, and the refusal names the position.
 */
const slotRefusal = (
    name: string,
    mine: readonly Term[],
    there: Term,
): string | undefined => {
    const list = resolvedTerm(there)
    if (list?.kind !== 'list') return patternRefusal(mine, there)
    for (const [at, position] of list.pre.entries()) {
        const held = mine.flatMap((one) => {
            const node = resolvedTerm(one)
            return node?.kind === 'list' ? node.pre.slice(at, at + 1) : []
        })
        if (held.length === 0 && objectMembersOf(position).length > 0) {
            return `the pattern at '${name}' reaches position ${at}, and no member holds a list with that position. An array declares no position, because its length is a run-time fact`
        }
        const inner = slotRefusal(name, held, position)
        if (inner) return inner
    }
    return undefined
}

/** An object spec, with the open key entry of the object that holds it. */
type Piece = {
    readonly spec: Record<string, ObjectSlot>
    readonly rest: AnyCodec | undefined
}
type SpecSlice = {
    readonly keep: readonly Piece[]
    readonly rest: readonly Piece[]
}

/** The object nodes that a term names: the object itself, or each object option of a union. */
const objectNodesOf = (t: Term): readonly Term[] => {
    const node = resolvedTerm(t)
    if (node === undefined) return []
    return node.kind === 'union' ? node.options.flatMap(objectNodesOf) : [node]
}

/**
 * The part of an object that a pattern keeps, and the part that it rejects, each as a list of
 * objects that hold a union at the fields that the pattern splits.
 *
 * The slice goes into the field and the result stays compact: an object `{ k, pet: U }` against
 * the pattern `{ pet: P }` keeps `{ k, pet: Extract<U, P> }`. A key of an object pattern fits
 * apart from the other keys, so the kept set is a product over the keys, and the product is one
 * object. The complement of a product is no product, and the rejected part is its cover: one
 * object for each split key, with the keys before it kept and the keys after it as declared.
 *
 * Nothing where the pattern is a union of objects, because a union pattern is no product of its
 * keys. The caller splits then. An object with an open key entry is refused where a field changes,
 * because the type of a part holds the declared names only, and the type cannot state the refusal.
 *
 * `presence` is `true` where the caller can replace an option by parts. A field that may be absent,
 * against a pattern that requires the key, then splits into a present part and an absent part. It is
 * `false` for a dissection. The tag table of a dissection maps each literal to one member whole, and
 * a part is a member that changed, which the table cannot key. The dissection then keeps its old
 * answer: a member that does not fit whole stays out of the extraction, and the exclusion keeps the
 * member whole.
 */
const sliceSpec = (
    piece: Piece,
    node: Extract<Term, { kind: 'object' }>,
    pattern: Term,
    presence = true,
): SpecSlice | undefined => {
    const wantedObject = resolvedTerm(pattern)
    if (wantedObject?.kind !== 'object') return undefined
    let leafFits = true
    type Entry = {
        name: string
        at: number | undefined
        keep: Piece[]
        rest: Piece[]
        original: Piece[]
        /**
         * The declared field where the field may be absent and the pattern requires the key. The
         * field is the union of a present part and an absent part. The kept part holds the present
         * part, and the rejected part holds the absent part beside the present part that the
         * pattern rejects.
         */
        presence?: { readonly inner: AnyCodec; readonly mark: Field['mark'] }
    }
    const nested: Entry[] = []
    /** The one summand of a field that holds no object: the field as declared. */
    const whole: Piece = { spec: {}, rest: undefined }
    /**
     * The summands of one slot against the pattern there: a field, or a position of a fixed list.
     * `'leaf'` where the slot holds no union of objects, `'split'` where the caller splits.
     */
    const sliceSlot = (
        mine: Term,
        wanted: Term,
    ): Omit<Entry, 'name' | 'at'> | 'leaf' | 'split' => {
        const summands = objectNodesOf(mine)
        const members = objectNodesOf(wanted)
        if (
            summands.length === 0 ||
            members.length === 0 ||
            summands.some((one) => objectNamed(one) === undefined)
        ) {
            return 'leaf'
        }
        const wantedNode = resolvedTerm(wanted)
        const keep: Piece[] = []
        const rest: Piece[] = []
        const original: Piece[] = []
        for (const summand of summands) {
            const one = objectNamed(summand) as ObjectItem
            const here: Piece = {
                spec: one.spec as Record<string, ObjectSlot>,
                rest: one.rest,
            }
            original.push(here)
            if (fits(summand, wanted)) keep.push(here)
            else if (
                wantedNode?.kind === 'object' &&
                summand.kind === 'object'
            ) {
                const inner = sliceSpec(here, summand, wanted, presence)
                if (inner === undefined) return 'split'
                keep.push(...inner.keep)
                rest.push(...inner.rest)
            } else if (
                summand.kind === 'object' &&
                members.some(
                    (member) =>
                        member.kind === 'object' &&
                        (sliceSpec(here, summand, member, presence)?.keep
                            .length ?? 0) > 0,
                )
            ) {
                // a summand that fits a member of a union pattern in part: the caller splits
                return 'split'
            } else rest.push(here)
        }
        return { keep, rest, original }
    }
    for (const [name, wanted] of Object.entries(wantedObject.body.fields)) {
        const mine = node.body.fields[name]
        if (mine === undefined) {
            if (alwaysWritten(wanted) || node.body.rest !== undefined) {
                leafFits = false
            }
            continue
        }
        if (alwaysWritten(wanted) && !alwaysWritten(mine)) {
            const declared = piece.spec[name]
            if (!presence || declared === undefined || !('codec' in declared)) {
                leafFits = false
                continue
            }
            if (fits(mine.t, wanted.t)) {
                nested.push({
                    name,
                    at: undefined,
                    keep: [whole],
                    rest: [],
                    original: [whole],
                    presence: { inner: entryCodec(declared), mark: mine.mark },
                })
                continue
            }
            const one = sliceSlot(mine.t, wanted.t)
            if (one === 'split') return undefined
            if (one === 'leaf') {
                leafFits = false
                continue
            }
            nested.push({
                name,
                at: undefined,
                ...one,
                presence: { inner: entryCodec(declared), mark: mine.mark },
            })
            continue
        }
        if (fits(mine.t, wanted.t)) continue
        const slot = piece.spec[name]
        if (slot === undefined || 'codec' in slot) {
            leafFits = false
            continue
        }
        /**
         * A fixed list is a product of its positions, as an object is a product of its keys. So each
         * position that the pattern does not hold whole is one more split slot of this object, and
         * the kept part and the cover below read it as they read a key. A list with a spread has no
         * fixed positions: its length is free, so no finite product of slots states it.
         */
        const mineList = resolvedTerm(mine.t)
        const wantedList = resolvedTerm(wanted.t)
        if (mineList?.kind === 'list' && wantedList?.kind === 'list') {
            if (
                mineList.spread !== undefined ||
                wantedList.spread !== undefined ||
                mineList.suf.length > 0 ||
                wantedList.suf.length > 0 ||
                mineList.pre.length !== wantedList.pre.length
            ) {
                leafFits = false
                continue
            }
            for (const [at, position] of mineList.pre.entries()) {
                const there = wantedList.pre[at]
                if (there === undefined || fits(position, there)) continue
                const one = sliceSlot(position, there)
                if (one === 'split') return undefined
                if (one === 'leaf') {
                    leafFits = false
                    continue
                }
                nested.push({ name, at, ...one })
            }
            continue
        }
        const one = sliceSlot(mine.t, wanted.t)
        if (one === 'split') return undefined
        if (one === 'leaf') {
            leafFits = false
            continue
        }
        nested.push({ name, at: undefined, ...one })
    }
    if (!leafFits) return { keep: [], rest: [piece] }
    if (nested.length === 0) return { keep: [piece], rest: [] }
    const rebuild = (replaced: ReadonlyMap<Entry, readonly Piece[]>): Piece => {
        const spec: Record<string, ObjectSlot> = { ...piece.spec }
        const positions = new Map<string, Map<number, Term>>()
        for (const [entry, list] of replaced) {
            const same =
                list.length === entry.original.length &&
                list.every((one, at) => one === entry.original[at])
            const { name, presence } = entry
            if (same && presence === undefined) continue
            if (presence !== undefined && (same || list.length === 0)) {
                const held = same ? presence.inner : (never as AnyCodec)
                spec[name] = (list === entry.keep
                    ? held
                    : presence.mark === 'undefinable'
                      ? undefinable(held)
                      : optional(held)) as unknown as ObjectSlot
                continue
            }
            if (list.some((one) => one.rest !== undefined)) {
                throw new CodecError(
                    `'${name}' holds an object with an open key entry, and a pattern splits declared names only`,
                )
            }
            const codecs = list.map(
                (one) =>
                    objectFromMap(one.spec, undefined) as unknown as AnyCodec,
            )
            const codec = (
                codecs.length === 1 ? codecs[0] : union(codecs as never)
            ) as AnyCodec
            if (entry.at === undefined) {
                spec[name] = (presence === undefined || list === entry.keep
                    ? codec
                    : presence.mark === 'undefinable'
                      ? undefinable(codec)
                      : optional(codec)) as unknown as ObjectSlot
                continue
            }
            const at = positions.get(name) ?? new Map<number, Term>()
            at.set(entry.at, termOf(codec))
            positions.set(name, at)
        }
        for (const [name, at] of positions) {
            const declared = resolvedTerm(
                termOf(piece.spec[name] as unknown as AnyCodec),
            )
            if (declared?.kind !== 'list') {
                throw new Error(
                    `'${name}' was split by position and holds no list`,
                )
            }
            spec[name] = codecOfTerm({
                kind: 'list',
                pre: declared.pre.map((one, i) => at.get(i) ?? one),
                suf: [],
            }) as unknown as ObjectSlot
        }
        return { spec, rest: piece.rest }
    }
    const keepAll = new Map(nested.map((one) => [one, one.keep] as const))
    const keep = nested.every((one) => one.keep.length > 0)
        ? [rebuild(keepAll)]
        : []
    const rest: Piece[] = []
    for (const [at, one] of nested.entries()) {
        // the absent part of a field that may be absent is rejected whatever the present part holds
        if (one.rest.length === 0 && one.presence === undefined) continue
        const before = nested.slice(0, at)
        if (before.some((other) => other.keep.length === 0)) break
        const replaced = new Map<Entry, readonly Piece[]>()
        for (const other of before) replaced.set(other, other.keep)
        replaced.set(one, one.rest)
        rest.push(rebuild(replaced))
    }
    return { keep, rest }
}

/** The parts of an option that fit a pattern, where each field that the pattern names is split. */
const splitParts = <O>(
    option: O,
    wanted: Term,
    keep: boolean,
    splits: boolean,
): readonly O[] => {
    const item = objectNamed(termOf(option as unknown as AnyCodec))
    const parts: readonly O[] = item
        ? ((specs) => {
              const [only] = specs
              if (specs.length === 1 && only === item.spec) return [option]
              if (!splits) {
                  throw new CodecError(
                      'a dissection keeps its members whole, and this pattern splits a member at a field that holds a union of objects. Slice the field first, or take the pattern from a union',
                  )
              }
              if (item.rest !== undefined) {
                  throw new CodecError(
                      'a member has an open key entry, and a pattern splits declared names only',
                  )
              }
              return specs.map(
                  (spec) => objectFromMap(spec, undefined) as unknown as O,
              )
          })(splitBy(item.spec as Record<string, ObjectSlot>, wanted, splits))
        : [option]
    return parts.filter(
        (part) => fits(termOf(part as unknown as AnyCodec), wanted) === keep,
    )
}

/**
 * The options that fit a pattern. An option that fits whole stays whole. An option that an object
 * pattern slices keeps its place and holds a narrower union at the fields that the pattern names:
 * the extraction has no option that the original lacks. A union pattern splits the option, and the
 * parts that fit stay.
 *
 * `splits` is `false` for a dissection, whose table is keyed by the literals of its members: a
 * member that changes has no key there, so a pattern that changes a member is refused and the
 * caller slices the field first.
 */
const picked = <O>(
    options: readonly O[],
    pattern: unknown,
    keep: boolean,
    splits: boolean,
): readonly O[] => {
    const wanted = termOf(pattern as AnyCodec)
    const why = patternRefusal(
        options.map((option) => termOf(option as unknown as AnyCodec)),
        wanted,
    )
    if (why) throw new CodecError(why)
    return options.flatMap((option) => {
        const term = termOf(option as unknown as AnyCodec)
        // an option that fits whole has parts that all fit, so it stays whole and no part remains
        if (fits(term, wanted)) return keep ? [option] : []
        const item = objectNamed(term)
        const node = resolvedTerm(term)
        const sliced =
            item && node?.kind === 'object'
                ? sliceSpec(
                      {
                          spec: item.spec as Record<string, ObjectSlot>,
                          rest: item.rest,
                      },
                      node,
                      wanted,
                      splits,
                  )
                : undefined
        if (sliced === undefined)
            return splitParts(option, wanted, keep, splits)
        return (keep ? sliced.keep : sliced.rest).map((one) => {
            if (one.spec === item?.spec) return option
            if (!splits) {
                throw new CodecError(
                    'a dissection keeps its members whole, and this pattern changes a member at a field that holds a union of objects. Slice the field first, or take the pattern from a union',
                )
            }
            if (item?.rest !== undefined) {
                throw new CodecError(
                    'a member has an open key entry, and a pattern splits declared names only',
                )
            }
            return objectFromMap(one.spec, undefined) as unknown as O
        })
    })
}

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
export const mdunion = <
    const Ks extends readonly [string, ...string[]],
    const Options extends readonly AnyObjectCodec[],
>(
    ks: Ks,
    options: Options & MembersTagged<SpecsOf<Options>, Ks>,
): Dissection<Ks, Options> &
    TermMark<['union', TermsOf<Options>]> &
    OptionsMark<Options> =>
    // one cast, at the one place where a runtime table meets a type computed from the specs: the
    // builder is written once over `readonly string[]`, and {@link Dissection} is what that builder
    // produces read at the arity the caller wrote
    dissect(ks, options as readonly AnyObjectCodec[]) as never

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
 * **{@link mdunion} at one discriminator**, and nothing else: the two spellings build the same term,
 * the same table and the same codec, so a caller can replace one with the other and change no other
 * line. This name is the one-key case because one discriminator is what almost every entity needs.
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
    ByTag<SpecsOf<Options>, D>,
    FreeOf<Options[number]>
> &
    TermMark<['union', TermsOf<Options>]> &
    OptionsMark<Options> =>
    // **the type arguments are given, not inferred, and that is what makes the alias cast-free.**
    // Inferring them from `options` would take `Options` to be the *intersection* the parameter
    // declares — `Options & MembersTagged<…>` — and the return type computed from that intersection
    // is not the one this signature promises. Pinned, `Dissection<readonly [D], Options>` reduces to
    // exactly the `DiscriminatedCodec` below, and `EveryOptionTagged<SpecsOf<Options>, D>` is
    // `MembersTagged<SpecsOf<Options>, readonly [D]>` by definition, so the argument needs nothing.
    mdunion<readonly [D], Options>([discriminator], options)

/**
 * **The term that admits no value**, and the unit the product and the slice need.
 *
 * `Term.never` on both sides. The model types it — `TOp.rule` gives it the held set `HNever`,
 * which is `False` — and denotes it as `Codec.empty`, whose laws hold vacuously because both
 * domains are empty.
 *
 * **A constructor rather than a `discriminatedUnion` over no options.** The derived form works and
 * costs a structural test: an empty option list is a term a caller can build by accident, so every
 * rule reading it as the bottom reads that accident as intent, and the term carries a discriminator
 * no value will ever name. `discriminatedUnion` stays refused on an empty list — that list is a
 * typo or a `map` over an empty array — and this is the one name that reaches the bottom.
 *
 * It is the zero of `union`: an empty option is compatible with every option
 * (`Closed.pairwiseCompat_never_left`, `Closed.pairwiseCompat_never_right`), so `union([X, never])` is `X`.
 */
export const never: AttributeCodec<never, never> & {
    readonly def: { readonly kind: 'never' }
} & TermMark<['never']> = codecOfTerm({ kind: 'never' }) as AttributeCodec<
    never,
    never
> & {
    readonly def: { readonly kind: 'never' }
}

/**
 * A union told apart by what each option holds, with no tag to switch on — `zod`'s `union`.
 *
 * **The union is the join of its options.** Options are codecs of any kind. The first option that
 * admits a value writes the value, and the first option that reads an attribute reads it. An
 * object option is no exception: the names present select nothing.
 *
 * **The declaration refuses a pair that it cannot show compatible**, and nothing else. Two
 * compatible options that both admit a value write it to one attribute, and two that both read an
 * attribute read it to one value, so no value and no attribute can observe the option order.
 * Options that overlap, nest, or repeat are therefore well formed: `union([string('A'), string])`
 * is `string`. A pair that the declaration cannot show compatible is refused, because there the
 * order would choose an owner of the overlap that nobody named.
 *
 * @example
 * ```ts
 * union([object({ petId: string, price: decimal }), object({ petIds: array(string) })])
 * union([string, number])                    // an attribute that is either
 * union([object({ at: string }), string])     // a map or a bare string
 * union([string('A', 'B'), string('B', 'C')]) // two restrictions of one base
 * ```
 */
export const union = <const Options extends readonly AnyCodec[]>(
    options: Options,
): UnionCodec<DerivedUnion<Options>, Options> &
    LiteralMarkOf<Options[number]> => {
    // **The judgment decides the union's obligation**: each two options compatible, at the
    // declaration, or at the first scope that binds a name of an option. The resolution reads each
    // option through its `ref`s, so it runs at the first use, where every name is bound
    const settle = () => {
        const all: readonly Option[] = (options as readonly AnyCodec[]).map(
            optionOf,
        )
        return { all, ...altSem(all) }
    }
    let settled: ReturnType<typeof settle> | undefined
    const resolution = (): ReturnType<typeof settle> => {
        settled ??= settle()
        return settled
    }
    const optionTerms = options.map(termOf)
    const declared: Term = { kind: 'union', options: optionTerms }
    judged(declared)
    // **A use needs every name bound.** Each use refuses while a `ref` of an option is unbound
    const closed = (): void => {
        const open = openRefusal(declared)
        if (open) throw open
    }

    type T = DerivedUnion<Options>

    /**
     * The item reading's own matcher: the value is always a record, so the shape filter has nothing
     * to do, and each option is attempted. The names present select nothing, as the model's
     * `Closed.AdmA` reads no name.
     */
    const readItem = (item: StoredItem): Result<T> => {
        const open = openRefusal(declared)
        if (open) return open
        const deep = membersTooDeeply(item, 0)
        if (deep) return deep
        const names = namesOf(item)
        const { only, naming, named } = resolution()
        // The item reading asks the same lookup as the attribute reading, so the outer union of a table
        // dispatches. The cast drops the `undefined` that `StoredItem` admits: a lookup reads it as missing.
        const hit = named({ M: item } as AttributeValue)
        if (hit?.item) {
            const direct = (
                hit.item as ItemCodec<Record<string, unknown>, unknown>
            ).decode(item) as Result<T>
            if (!failed(direct)) return direct
        }
        return only(
            () => true,
            naming('this item', names),
            (option) =>
                (
                    option.item as ItemCodec<Record<string, unknown>, unknown>
                ).decode(item) as Result<T>,
        )
    }

    const writeItem = (item: T): Result<AttributeMap> => {
        const open = openRefusal(declared)
        if (open) return open
        const names = namesOf(item as Record<string, unknown>)
        const { onlyAdmitting, naming } = resolution()
        return onlyAdmitting(
            () => true,
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
        spec: (options as readonly AnyCodec[]).map(
            (option) =>
                (option as unknown as Partial<AnyObjectCodec>).item?.spec,
        ) as never,
        def: {
            kind: 'union',
            options: optionTerms,
        },
    }

    // the option chosen writes what it writes; `WrittenBy` is the union of those, which no single
    // call can be narrowed to from inside
    // the resolution is erased — a sum's rule is about options, not about the type they carry —
    // so the two halves get their types back here, once, the way `codecOfTerm` does for a term
    const encode = ((value: T) =>
        openRefusal(declared) ??
        resolution().pair.encode(value as never, 0)) as (
        value: T,
    ) => Result<WrittenBy<Options>>
    const decode = ((attribute: AttributeValue) =>
        openRefusal(declared) ?? resolution().pair.decode(attribute)) as (
        attribute: AttributeValue,
    ) => Result<T>
    const codec: UnionCodec<DerivedUnion<Options>, Options> = {
        encode,
        decode,
        unsafeEncode: (value) => orThrow(encode(value)),
        unsafeDecode: (attribute) => orThrow(decode(attribute)),
        def: {
            kind: 'union',
            options: optionTerms,
        },
        item: self as never,
        // built either way rather than branched, exactly as `item` is: an option that writes no map
        // declares no name, so it survives no clause, and the type is what says the capability does
        // not apply to such a union
        extract: ((pattern: unknown) => {
            closed()
            return slicedUnion(options as readonly AnyCodec[], pattern, true)
        }) as never,
        exclude: ((pattern: unknown) => {
            closed()
            return slicedUnion(options as readonly AnyCodec[], pattern, false)
        }) as never,
    }
    // the mark is phantom, so no value carries it and no check can produce it. A union of literal
    // codecs pins their literals at run time (`literalAlternatives`), so the type states the mark
    // where each option carries the mark
    return codec as typeof codec & LiteralMarkOf<Options[number]>
}

/**
 * A union's slice: the options the clause keeps, and `never` where it keeps none.
 *
 * Rebuilt through {@link union} and not assembled here, so the declaration guard runs over the
 * result. It has to: a sub-selection of a certified union is certified, and a sub-selection of one
 * that was never certified is not. The model needs no such step: a slice keeps pairwise
 * compatibility (`Calculus.AltClause.pairs_extractC`).
 */
const slicedUnion = (
    options: readonly AnyCodec[],
    pattern: unknown,
    keep: boolean,
): unknown => {
    const kept = picked(options, pattern, keep, true)
    return kept.length === 0 ? never : union(kept as never)
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
