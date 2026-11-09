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
import type {
    AnyCodec,
    AttributeCodec,
    Closed,
    freeMarker,
    ObjectSlot,
} from './build'

import type { ItemTerm, OpaqueNumbers, Option } from './denote'
import {
    altSem,
    byTagSem,
    codecAtLevel,
    codecOfTerm,
    defOf,
    equipCodecs,
    guard,
    itemSem,
    judged,
    literalCodec,
    literalTermOf,
    membersOf,
    membersTooDeeply,
    opaqueTerms,
    optionOfTerm,
    termOf,
} from './denote'
import type {
    ApartG,
    Block,
    DecodeTerm,
    HoldsFree,
    HoldsNoValue,
    KindOfFrames,
    NarrowFrames,
    NodeOf,
    Norm,
    OffersAt,
    OpenT,
    OwnsNull,
    Same,
    ScopeWallCycle,
    SlotAt,
    StepFrames,
} from './pathModel'
import {
    andThen,
    asPath,
    CodecError,
    failed,
    orThrow,
    type Result,
    setOwn,
} from './result'
import {
    alignedRows,
    callerApart,
    childAt,
    flatOf,
    guardAt,
    sideOf,
    storedApart,
} from './scoped'
import type {
    Body,
    Field,
    LiteralBase,
    LiteralValue,
    NameForm,
    Order,
    RefSlot,
    Rng,
    Term,
} from './term'
import {
    absentBelow,
    clauseForm,
    closedCopy,
    holdsNoValue,
    isCallerPin,
    member as memberOf,
    openRefusal,
    ownsNullOf,
    pinnedValue,
    resolvedTerm,
    sameAdapter,
    storedPin,
    targetOf,
    unanimous,
    unboundRefs,
    usedTargetOf,
} from './term'

/**
 * The types that the entries publish and that a lower file owns now. A lower file owns a type
 * where its readers need the type, and this file names the type again for the entries.
 */
export type { AnyCodec, AttributeCodec, ObjectSlot } from './build'
/**
 * Forwarded for the consumers that still name them here.
 *
 * They are `denote.ts`'s now — each answers about a term's *pair* — and this keeps the move to one
 * pass. Six of the eight go in the pass that deletes the readers; `codecOfTerm` and `termOf` stay,
 * and their callers move to the module that owns them there.
 */
export { codecOfTerm, termOf, valueKinds } from './denote'
export type { Precondition } from './scoped'
export type {
    LiteralBase,
    LiteralValue,
    Refinement,
    Rng,
} from './term'
export type { SetSlot, Shape } from './value'

import type { ErrorMessage, show } from '../utils'
import type { MissingCodec, RefineOptions } from './adapters'
import { fillRefusal } from './adapters'
import type {
    AnySpread,
    AttributeOf,
    Decoded,
    EncodedBy,
    EncodedPatch,
    Free,
    FreeOf,
    Marks,
    Nestable,
    ObjectOf,
    WritesPin,
    WritesVariantsPin,
} from './build'
import type { Clause, ClausePattern } from './clause'
import { clauseOf, opened } from './clause'
import type {
    AnyObjectCodec,
    AnyObjectEntry,
    Declares,
    DecodedTags,
    DerivedItem,
    DerivedUnion,
    DerivedVariants,
    EntrySpecs,
    InexactAll,
    InexactValue,
    IsUnion,
    ItemOf,
    KnownKeys,
    OptionInexact,
    RestsOf,
    SpecsOf,
    TagIntersection,
    UnionToIntersection,
    VariantOf,
} from './derivedItem'
import { entryCodec, fieldOf, keySets, slotsOf } from './derivedItem'
import type {
    ClauseTerms,
    Cycles,
    DecodeFrames,
    ElementOf,
    ItemFrontier,
    LastPart,
    Member,
    Narrowed,
    ParsePath,
    PathTerminal,
    PlainName,
    Reached,
    Refused,
    Segment,
    SegmentsOf,
    Spoken,
    Step,
    StoredText,
    TermPathEncoded,
    TermPathValue,
    UnionKeys,
    ValueAt,
    Wide,
    WrittenMembers,
} from './frontier'
import {
    admitsNothing,
    asIndex,
    including,
    nothing,
    refusedAt,
    segmentsIn,
} from './frontier'
import type {
    ArrayOver,
    FixedElements,
    LeadingElements,
    ListCodec,
    NoNeverField,
    NoSpreadMember,
    SetCapable,
    SpreadOver,
} from './products'
import { setOf } from './products'
import type { Precondition } from './scoped'
import type {
    BaseT,
    DefOf,
    ElementMark,
    ElementsMark,
    elementMarker,
    FloatText,
    FloatTexts,
    FreeTerm,
    fillMarker,
    HeldT,
    Itemable,
    itemMarker,
    itemOfMarker,
    itemTermMarker,
    LitT,
    locatedFrom,
    NumText,
    NumTexts,
    ObjectTermOf,
    OfParts,
    OptionsMark,
    optionalMarker,
    optionsMarker,
    ReadingOf,
    restsMarker,
    ScopeTerms,
    SlotOf,
    TermMark,
    TermOf,
    TermsOf,
    termMarker,
    undefinableMarker,
    writesMarker,
} from './term'
import { locatedSlot } from './term'
import {
    describeShape,
    itemRefusal,
    namedLiteral,
    namesOf,
    own,
    readTags,
    sameLiteral,
} from './value'

export type { Reader } from './adapters'
export { held, legacy } from './adapters'
export type {
    AnySpread,
    AttributeOf,
    Attributes,
    Decoded,
    Encoded,
    EncodedPatch,
    EncodedVariants,
    Marks,
    Nestable,
    ObjectOf,
    SetOf,
    Writes,
} from './build'
export type {
    AnyObjectCodec,
    DerivedUnion,
    DerivedVariants,
    IsUnion,
    ObjectEntry,
    SpecsOf,
    VariantOf,
} from './derivedItem'
export type { PathTerminal, Segment } from './frontier'
export type {
    ListOf,
    ListWrites,
    SetCapable,
    SpreadCodec,
    SpreadOnce,
} from './products'
export { array, list, spread } from './products'

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

/** The free names of an object: the names of its spec and its rest. An entry of a scope has none. */
type ObjectFree<Spec, Rest, Tm> = [Tm] extends [OfParts]
    ? FreeOf<Spec[keyof Spec]> | FreeOf<Rest>
    : never
type LitsT<
    K extends string,
    L extends readonly unknown[],
> = L extends readonly [infer One]
    ? LitT<K, One>
    : ['union', { -readonly [I in keyof L]: LitT<K, L[I]> }]
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

/* ── the readers ──────────────────────────────────────────────────────────────────────── */

/*
 * A reader here answers from the **term** and nothing else, which is what makes the term determine
 * the codec rather than describe it. `constantOf` is the one left in this file; `member`, `occV`
 * and `agrees` are `term.ts`'s, and
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
 * What one declared attribute decides, read where the field is held.
 *
 * The two presence marks answer differently and neither is the codec's answer. A name that may be absent
 * decides nothing about a key, because a key built from it would have no value to build from in the
 * rows that omit it. A fill value is written always, so what it fills still decides.
 *
 * A reader of the term alone does not answer this. A term is what a codec has, a field is not a
 * codec, and the body is what holds a field — so this reads the mark first and the term second.
 */
export const constantOf = (declared: ObjectSlot): unknown => {
    const def = defOf(declared)
    if (
        'mark' in def &&
        (def.mark === 'optional' || def.mark === 'undefinable')
    )
        return undefined
    const t = 'mark' in def ? def.t : def
    // **A single-valued literal decides; two admissible values narrow without deciding.** The term
    // answers the row, deliberately *not* through the wrappers `member` descends: a constant is a claim about
    // the value, and `refine` can reject it, `legacy` can decode an older encoding into something
    // else, and `optional` admits absence, which is not the value. `fill` is the one that keeps
    // it, always writing the attribute at a value typed to the same alternative.
    //
    // **An adapter is the second that keeps it**, and it has to be: `number` and `decimal` are
    // adapters over the one numeric base, so a numeric discriminator is a literal under a
    // `held` and reading only the bare row would lose every one of them. The value is the
    // caller's rather than the carrier's, so it is the inner literal's put back through the
    // adapter — well defined because `held` owes that the pair cancels.
    //
    // The walk is `storedPin`, the one reader of a term through its wrappers, and a `ref` is read as
    // its target. A throw of the adapter of a caller is not caught here: the caller of this
    // function names the attribute in the refusal.
    const at = resolvedTerm(t)
    if (at === undefined || at.kind === 'refine') return undefined
    return pinnedValue(storedPin(at))
}

/* ── the seam: a definition, as the term it denotes ───────────────────────────────────── */

/**
 * Every codec a segment can reach, which is more than one exactly where a union's variants
 * disagree about it.
 *
 * A union is the only definition that branches, and what it branches into is a *set of codecs* —
 * not a codec. The disagreement belongs to the walk, so it is the walk that carries it.
 *
 * **A segment has four answers.** The model's `childG` has the same four, and its `none` is the
 * refusal. The codecs at the segment. No
 * codec, where the term stores a member that is not the container of the segment: the store
 * refuses the segment on every attribute of the term, so the term leaves the frontier.
 * {@link absent}, where the container admits no value at the segment: a closed object that lacks
 * the name, or a list with no spread past its prefix. A write there leaves an item that the codec
 * does not read, so `absent` stays on the frontier and the frontier refuses on use. A returned
 * `CodecError`, where the path cannot continue: a position past the prefix of a list with a suffix,
 * and a path into a `held`, a `refine` or a `legacy`. `at` turns it into a codec that refuses on use.
 * No segment throws, so the option order of a union never decides the channel of the answer.
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
            const field = own(fields, String(segment))
            return [
                field
                    ? codecOfTerm(field.t)
                    : rest
                      ? codecOfTerm(rest)
                      : absent,
            ]
        }
        // a position enters the prefix or the spread of a list, and a name enters no list
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
            return new CodecError(
                `a path cannot go into \`refine\` at '${segment}': the predicate reads the whole value, and a write at the path writes one part of the value without the predicate. Address the refined attribute itself`,
            )
        case 'legacy':
            if (apart) return []
            return new CodecError(
                `a path cannot go into \`legacy\` at '${segment}': an older encoding of the attribute has another shape, and a path addresses the current shape only. Address the attribute itself`,
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
        // a primitive, a literal and a set each store a member that no segment enters. A set is
        // unordered, so no document path addresses a member of one. A walk whose frontier admits no
        // codec, as an empty frontier does, throws 'no attribute is declared' with kind `vacant`
        default:
            return []
    }
}

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
        'vacant',
    )
}

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
        // a clause has no scoped form only where its flat scope is refused, and `scope` refuses an
        // unguarded cycle of refs (RecursionRefused) before any path records the clause
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
                ? `'${path}' is declared by some variants only, so a write at this path would leave an item of another variant that no variant reads. Call \`narrow(object({...}))\` to keep the variants that declare it.`
                : `'${path}' is declared differently in different variants, so this path cannot say which codec to encode with. Call \`narrow(object({...}))\` to keep the variants that agree, for example \`narrow(object({ type: string('A') }))\` where \`type\` is the discriminator.`,
            partial ? 'someVariants' : 'ambiguous',
        ),
    )

// ── scalars ─────────────────────────────────────────────────────────

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
 * **The constant that the term of a codec decides**, the type of {@link constantOf}, row for row: a
 * literal of one value, and a `held` over a literal of one value, a caller's adapter included. The
 * answer is the pair of the text that the literal names and the value that the codec decodes to, or
 * `never` where the term decides none. The text tells two variants apart where their decoded types
 * are one type, because the value of a caller's adapter is caller code and the type cannot read it.
 * A literal whose value type is a union, a union of literals and any other term decide none.
 */
export type ConstantOf<C> = TermOf<C> extends [
    'prim',
    ['literal', string, infer V],
]
    ? ConstantPair<V, Decoded<C>>
    : TermOf<C> extends [
            'held',
            false,
            ['prim', ['literal', string, infer V]],
            unknown,
            [unknown, false],
            unknown,
        ]
      ? ConstantPair<V, Decoded<C>>
      : never
type ConstantPair<V, D> = IsUnion<V> extends true ? never : [V, D]

const literalCapability =
    (base: LiteralBase) =>
    (...allowed: readonly LiteralValue[]) =>
        literalCodec(base, someAlternatives(base, allowed))

/**
 * **The capabilities that a term decides**, added to the codec that `codecOfTerm` denotes for it.
 *
 * - The literal call: the four bases at the term of the base (`string('A')`), the two numeric
 *   adapters at the term of the adapter (`decimal('1.5')`, `number(5)`).
 * - `.set()`: the bases that have a set (`boolean` has none), the two numeric adapters, and a
 *   refinement of any term. `set` refuses an element that names no member of `S`, `N` or `B`.
 * - `.spec` and `.rest`: the slots of an object term.
 *
 * The constants are the codecs that this gives for their own term, so a codec that a slice or a meet
 * builds from a term is the codec that the caller wrote. `opaque` is not here: its call chooses
 * among three codecs by a policy, and the canonical term holds no policy, so the policy would be a
 * fact outside the term.
 */
const equip = (codec: AnyCodec, term: Term): unknown => {
    if (term.kind === 'object') {
        // read at the first use: a scope binds its names after the terms that name them are built
        let slots: ReturnType<typeof slotsOf> | undefined
        const read = () => {
            slots ??= slotsOf(term.body)
            return slots
        }
        return Object.defineProperties(
            { ...codec },
            {
                spec: { enumerable: true, get: () => read().spec },
                rest: { enumerable: true, get: () => read().rest },
            },
        )
    }
    if (term.kind === 'refine') {
        const capable: AnyCodec = {
            ...codec,
            set: setOf(() => capable),
        } as AnyCodec
        return capable
    }
    const call = literalCallOf(term)
    if (call === undefined) return codec
    const carrier = Object.assign(call, codec) as unknown as AnyCodec
    return term.kind === 'boolean'
        ? carrier
        : Object.assign(carrier, { set: setOf(() => carrier, call) })
}

/**
 * The literal call that a term has, or nothing. Each call is a function of its own: the carrier
 * takes the properties of the codec, so one function shared by two terms would carry the `def` of
 * the last.
 */
const literalCallOf = (
    term: Term,
): ((...allowed: never[]) => AnyCodec) | undefined => {
    switch (term.kind) {
        case 'string':
        case 'number':
        case 'boolean':
        case 'binary':
            return literalCapability(term.kind) as (
                ...allowed: never[]
            ) => AnyCodec
        case 'held':
            if (term.inner.kind !== 'number') return undefined
            if (term.via === 'decimalText' && term.outer.kind === 'string')
                return (...allowed) => decimalCall(...(allowed as string[]))
            return term.via === 'float'
                ? (...allowed) => numberCall(...(allowed as number[]))
                : undefined
        default:
            return undefined
    }
}

equipCodecs(equip)

/**
 * **The codec where a container admits no value at a segment**: one `never`, so a frontier that
 * holds it agrees with no writer, and the walk refuses on use. One term, so the frontier keeps one
 * copy.
 */
const absent: AnyCodec = codecOfTerm({ kind: 'never' })

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
        ): AttributeCodec<T, Attribute<'S'>> & TermMark<LitT<'string', T>>
        <const L extends readonly string[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'S'>> &
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

/** @see {@link StringCodec} */
export const string: StringCodec = codecOfTerm({
    kind: 'string',
}) as unknown as StringCodec

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
        ): AttributeCodec<T, Attribute<'N'>> &
            TermMark<LitT<'number', NumText<T>>>
        // a tuple, because inference unions no two object candidates: `readonly T[]` reads `T` off
        // the first numeral, and refuses a second numeral with another text
        <const T extends readonly DynamoNumber[]>(
            ...allowed: T
        ): AttributeCodec<T[number], Attribute<'N'>> &
            TermMark<LitsT<'number', NumTexts<T>>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<DynamoNumber>, NS> &
                TermMark<['set', BaseT<'number'>]>
            <const T extends readonly DynamoNumber[]>(
                ...allowed: T
            ): AttributeCodec<ReadonlySet<T[number]>, NS> &
                TermMark<['set', LitsT<'number', NumTexts<T>>]>
        }
    } = codecOfTerm({ kind: 'number' }) as never

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
    via?: 'decimalText' | 'float',
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

/** The literal call of {@link decimal}: the digits are refused unless they are the stored spelling. */
const decimalCall = (...allowed: readonly string[]) => {
    const stored = allowed.map((one) => orThrow(storedOnly(one)))
    return numericAdapter<string>(
        termOf(literalCapability('number')(...stored) as AnyCodec),
        // the held side is the texts the adapter hands the caller, so the view is exact
        literalTermOf(
            'string',
            stored.map((held) => held.toString()),
        ),
        storedOnly,
        (held) => held.toString(),
        'decimalText',
    )
}

/**
 * The refusal in the type of a decimal literal that is not the stored spelling: the run time of
 * {@link decimal} refuses the text that {@link DynamoNumber.from} gives another print. A text that
 * is no literal reads as the stored spelling, so a spread of `string[]` stays legal.
 */
type StoredSpelling<T extends string> = string extends T
    ? unknown
    : [
            NumText<
                Extract<ReturnType<typeof DynamoNumber.from<T>>, DynamoNumber>
            >,
        ] extends [T]
      ? unknown
      : ErrorMessage<`[decimal] '${T}' is not the spelling DynamoDB stores, which returns the normalised form: no leading or trailing zeros, no exponent, no '+'`>

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
            only: T & StoredSpelling<T>,
        ): AttributeCodec<T, Attribute<'N'>> &
            TermMark<HeldT<LitT<'number', T>, LitT<'string', T>, 'decimalText'>>
        <const L extends readonly string[]>(
            ...allowed: L & { [I in keyof L]: StoredSpelling<L[I]> }
        ): AttributeCodec<L[number], Attribute<'N'>> &
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
    } = numericAdapter<string>(
    { kind: 'number' },
    { kind: 'string' },
    storedOnly,
    (held) => held.toString(),
    'decimalText',
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
                `\`number(...)\` admits number values, and ${namedLiteral(one)} is not one`,
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

/** The literal call of {@link number}: each alternative is refused at the caller's level first. */
const numberCall = (...allowed: readonly number[]) =>
    numericAdapter<number>(
        termOf(
            literalCapability('number')(
                ...numericAlternatives(allowed),
            ) as AnyCodec,
        ),
        { kind: 'number' },
        asFloat,
        asJsNumber,
        'float',
    )

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
        ): AttributeCodec<T, Attribute<'N'>> &
            TermMark<FloatT<LitT<'number', FloatText<T>>>>
        <const L extends readonly number[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'N'>> &
            TermMark<FloatT<LitsT<'number', FloatTexts<L>>>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<number>, NS> &
                TermMark<['set', FloatT<BaseT<'number'>>]>
            <const L extends readonly number[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, NS> &
                TermMark<['set', FloatT<LitsT<'number', FloatTexts<L>>>]>
        }
    } = numericAdapter<number>(
    { kind: 'number' },
    { kind: 'number' },
    asFloat,
    asJsNumber,
    'float',
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
        ): AttributeCodec<T, Attribute<'BOOL'>> & TermMark<LitT<'boolean', T>>
        <const L extends readonly boolean[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'BOOL'>> &
            TermMark<LitsT<'boolean', L>>
    }

/** @see {@link BooleanCodec} */
export const boolean: BooleanCodec = codecOfTerm({
    kind: 'boolean',
}) as unknown as BooleanCodec

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
        ): AttributeCodec<Uint8Array, Attribute<'B'>> &
            TermMark<LitT<'binary', string>>
        (
            ...allowed: readonly Uint8Array[]
        ): AttributeCodec<Uint8Array, Attribute<'B'>> &
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

/** @see {@link BinaryCodec} */
export const binary: BinaryCodec = codecOfTerm({
    kind: 'binary',
}) as unknown as BinaryCodec

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
 * A codec narrowed by a predicate. The term `['refine', Tm, () => Narrow]` keeps the term under
 * the predicate, so the members of a slice and the walk of `at` read a literal through a
 * refinement. It keeps the narrowed type too, so a path and a scope decode the brand that the
 * predicate proves. The type sits behind a function, where a walk of the term stops: a recursive
 * type names its own term.
 */
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
): Refined<Narrow, A, ['refine', Tm, () => Narrow]> &
    TermMark<['refine', Tm, () => Narrow]> &
    Free<F>
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
    // `equip` carries `.set()` across the refinement, and it is the whole of why the brand
    // survives: `amount.set()` decodes as `ReadonlySet<Price>` because the set is built from
    // `amount`, where the predicate that produces a `Price` already lives.
    return codecOfTerm<Narrow, A>({
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
    }) as unknown as Refined<Narrow, A, unknown>
}

/**
 * Reads a missing attribute as a value, and writes the attribute always.
 *
 * Not {@link optional}: the entity always has it, the *data* may not — a row written before the
 * attribute existed. Replaces `item.channel ?? 'IN_STORE'` at every read site.
 *
 * **The fill value must be writable by the codec it fills**, and that is checked here, at the
 * declaration. The model carries it as the premise `hfill` of `carrier_objectCodec`: the fill value of a
 * `.fill` slot is in the write domain of its codec. The premise exists because the proof failed
 * without it: a row missing the attribute reads back as the fill value, and if the inner codec cannot write that value the item cannot be written back —
 * **(C)** broken at the read, with the refusal surfacing on some later write rather than at the
 * declaration responsible for it. `fill(string('A'), 'B')` is the whole of it.
 *
 * The fill value is a **value and not a thunk**, which is what makes the check possible here rather
 * than on whichever read happens to need it first. A fill value that the codec writes through a
 * {@link ref} that no scope binds is checked by the {@link scope} that binds the name. It does not become shared state for that: the
 * declaration holds one value and each read that needs one gets a copy of it, so a mutable fill value
 * still cannot leak between entities. The copy keeps the class of each value, because a decode must
 * be writable: a `DynamoNumber` is shared, being immutable. Primitives are handed over as they are,
 * being unable to leak anything.
 */
export const fill = <const C extends AnyCodec>(
    // the *argument's own* type, not a re-declared `AttributeCodec<T, A>`: the guard has to see the
    // marker the caller passed, and a parameter written in terms of inferred `T` and `A` reconstructs
    // a plain codec that never carries one
    inner: C,
    // `NoInfer` so the codec is the only thing that says what it holds. Inferring from both sites
    // unified them, and a fill value written `'A'` widens to `string`, which then refused the very
    // codec it fills — invisible while the entity was declared first and pinned it itself
    value: NoInfer<Decoded<C>>,
): MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> &
    TermMark<['fill', TermOf<C>]> &
    Free<FreeOf<C>> => {
    // The rule `(fill)`: the fill value must be *writable*, or a row missing the name decodes to a
    // value the item cannot be written back as — (C) broken at the read, with the refusal arriving
    // on the next write instead of at the declaration that caused it. Decidable from the
    // declaration alone, which is why the fill value is a value and not a thunk
    const filledCodec = inner as unknown as AnyCodec
    // **A fill value that the codec writes through an unbound `ref` is checked by the scope**, on the
    // closed copy, because the write reads through the ref
    if (unboundRefs([termOf(filledCodec)]).size === 0)
        checkFill(filledCodec, value)
    const attribute = inner as unknown as AttributeCodec<Decoded<C>>
    return {
        codec: attribute,
        def: { mark: 'fill', t: termOf(inner), v: value },
    } as unknown as MissingCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue,
        C
    > &
        TermMark<['fill', TermOf<C>]> &
        Free<FreeOf<C>>
}

/** Throws the refusal of a fill value that the codec it fills cannot write. */
const checkFill = (filledCodec: AnyCodec, value: unknown): void => {
    const refusal = fillRefusal(filledCodec, value)
    if (refusal) {
        throw new CodecError(
            `The fill value of \`fill\` must be a value the codec it fills can write, and this \`${filledCodec.def.kind}\` refuses the fill value: ${refusal.message}. A row missing the attribute would read back as the fill value and then refuse on the way out`,
        )
    }
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
type ScopeTerm<Defs, K> = ['scope', ScopeTerms<Defs>, K]
type ScopeOf<Defs> = {
    readonly [K in keyof Defs]: EntryOf<
        DefOf<Defs, Defs[K]>,
        ScopeTerm<Defs, K>,
        Defs
    >
}
/**
 * **A `ref` read in a scope**: the codec of the `ref` with the term of the entry that the name
 * binds. The decoded type reads the term, and the attribute reads the definition. The codec holds
 * no structure of the entry, so a cycle of entries is no cycle of types, and a reader of the term
 * resolves the name where the run time resolves it.
 */
type ClosedRef<Defs, N extends keyof Defs> = AttributeCodec<
    DecodeTerm<ScopeTerm<Defs, N>>,
    AttributeOf<DefOf<Defs, Defs[N]>> & AttributeValue
> &
    TermMark<ScopeTerm<Defs, N>> &
    SpecOfEntry<Defs, DefOf<Defs, Defs[N]>>
/** The spec of the object that an entry names, so a fit reads the object through the `ref`. */
type SpecOfEntry<Defs, C> = C extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    AnyCodec | undefined
>
    ? { readonly spec: SpecInScope<Spec, Defs> }
    : C extends UnionCodec<infer _T, infer Os extends readonly unknown[]>
      ? { readonly spec: OptionSpecs<Defs, Os> }
      : unknown
/**
 * The specs of the options of a union entry, one for each object, or `false` where an option is no
 * object. An option that names a union entry reads as the options of that entry.
 */
type OptionSpecs<Defs, Os extends readonly unknown[]> = Os extends readonly [
    infer H,
    ...infer R extends readonly unknown[],
]
    ? OptionSpec<Defs, DefOf<Defs, H>> extends infer S extends
          readonly unknown[]
        ? OptionSpecs<Defs, R> extends infer T extends readonly unknown[]
            ? [...S, ...T]
            : false
        : false
    : []
type OptionSpec<Defs, D> = D extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    AnyCodec | undefined,
    infer _T,
    infer _Tm
>
    ? [SpecInScope<Spec, Defs>]
    : D extends UnionCodec<infer _T, infer Os extends readonly unknown[]>
      ? OptionSpecs<Defs, Os>
      : false
/**
 * A slot of an object, with each `ref` closed in the scope `Defs` that the slot reads: a bare `ref`,
 * the codec that an `optional` or an `undefinable` marks, each option of a union, and each slot of
 * an object, at any depth of those nodes. A fill closes only a bare `ref`. Any other slot is the slot.
 */
type SlotInScope<S, Defs> = [FreeOf<S>] extends [never]
    ? S
    : S extends { readonly codec: infer C }
      ? TermOf<C> extends ['ref', infer N extends keyof Defs]
          ? S extends { readonly [fillMarker]: infer T }
              ? MissingCodec<
                    T,
                    AttributeOf<ClosedRef<Defs, N>> & AttributeValue,
                    ClosedRef<Defs, N>
                > &
                    TermMark<['fill', ScopeTerm<Defs, N>]>
              : MarkLike<S, ClosedRef<Defs, N>>
          : S extends { readonly [fillMarker]: unknown }
            ? S
            : Deep<C, Defs> extends infer D extends AnyCodec
              ? MarkLike<S, D>
              : S
      : Deep<S, Defs>
/** A codec with each `ref` of its union options and object slots closed in the scope `Defs`. */
type Deep<C, Defs> = TermOf<C> extends ['ref', infer N extends keyof Defs]
    ? ClosedRef<Defs, N>
    : C extends UnionCodec<infer _T, infer Os extends readonly unknown[]>
      ? UnionInScope<{ [I in keyof Os]: SlotInScope<Os[I], Defs> }>
      : C extends ObjectCodec<
              infer Spec extends Record<string, ObjectSlot>,
              infer Rest extends AnyCodec | undefined
          >
        ? ObjectCodec<SpecInScope<Spec, Defs>, Rest>
        : C extends ElementsMark<infer Cs extends readonly unknown[]>
          ? [readonly unknown[]] extends [Cs]
              ? C
              : ListCodec<{
                    [I in keyof Cs]: Cs[I] extends AnySpread
                        ? SpreadInScope<Cs[I], Defs>
                        : SlotInScope<Cs[I], Defs>
                }>
          : C extends ElementMark<infer E>
            ? Deep<E, Defs> extends infer D extends AnyCodec
                ? ArrayOver<D>
                : C
            : C
/** A spread with each `ref` of its element closed in the scope `Defs`. */
type SpreadInScope<S, Defs> = S extends ElementMark<infer E>
    ? Deep<E, Defs> extends infer D extends AnyCodec
        ? SpreadOver<D>
        : S
    : S
type UnionInScope<Os extends readonly unknown[]> = UnionCodec<
    DecodeTerm<['union', TermsOf<Os>]>,
    Os
>
/** The spec of an object, with each bare `ref` of a slot closed in the scope `Defs`. */
type SpecInScope<Spec extends Record<string, ObjectSlot>, Defs> = {
    [K in keyof Spec]: SlotInScope<Spec[K], Defs>
} extends infer S extends Record<string, ObjectSlot>
    ? S
    : never
/** An option of an entry: an object reads its slots in the scope `Defs`, and any other option is the option. */
type OptionInScope<O, Defs> = O extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    infer Rest extends AnyCodec | undefined
>
    ? ObjectCodec<SpecInScope<Spec, Defs>, Rest>
    : O
/**
 * An entry: the codec of the definition that the entry names, read at the term `Tm` of the entry.
 * An object keeps its item, and a union keeps its item and its slices, each typed from the term.
 * Each option of a union is the definition that the option names, so a slice reads a `ref` option
 * as the definition. Each slot of an object, and of an option that is an object, reads a bare `ref`
 * as the entry that the `ref` names ({@link ClosedRef}). Any other entry keeps the `.set()` of an
 * element that writes `S`, `N` or `B`, and a dissection keeps its options in declared order, each
 * the definition that the option names.
 */
type EntryOf<C, Tm, Defs> = C extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    infer Rest extends AnyCodec | undefined,
    infer _T,
    infer _Tm
>
    ? ObjectCodec<SpecInScope<Spec, Defs>, Rest, DecodeTerm<Tm>, Tm>
    : C extends UnionCodec<infer _T, infer Options extends readonly unknown[]>
      ? UnionCodec<
            DecodeTerm<Tm>,
            {
                [I in keyof Options]: OptionInScope<
                    DefOf<Defs, Options[I]>,
                    Defs
                >
            },
            Tm
        >
      : AttributeCodec<DecodeTerm<Tm>, AttributeOf<C> & AttributeValue> &
            TermMark<Tm> &
            SetCapable<DecodeTerm<Tm>, AttributeOf<C> & AttributeValue, Tm> &
            (C extends OptionsMark<infer Os extends readonly unknown[]>
                ? OptionsMark<{
                      [I in keyof Os]: OptionInScope<DefOf<Defs, Os[I]>, Defs>
                  }>
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
    return codecOfTerm({ kind: 'ref', slot: { name } })
}

/**
 * **Codecs that name each other**, each one an entry. A {@link ref} in a definition names an entry,
 * and the decoded type of each entry follows from the definitions, with no annotation. A single
 * cycle is a scope of one entry.
 *
 * Each former ran before the names were bound, so the guard runs here: a recursion with no
 * container on its path, or with an adapter on its path, is refused. A `ref` to a name that `defs`
 * does not declare is refused. Then each check that reads through a `ref` runs on the closed copy:
 * the check of a `union` with a `ref` option, which a `nullable` over a `ref` builds, the index of
 * a dissection whose tag reads a `ref`, and the fill value of a `fill` that writes through
 * a `ref`.
 *
 * **A scope closes a copy, by lexical scope.** Each entry is the codec of its closed term. A `ref`
 * binds in the record of its own scope, and a cycle is a recursive binding of that record
 * (`letrec`), not a slot written in place. Each entry has no free name, in the type and at run
 * time, so each entry is a codec to use. A fragment stays an open term, so the fragment refuses
 * each use, and the result of a scope depends on its own arguments only.
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
    for (const slot of unboundRefs(Object.values(terms)))
        if (!Object.hasOwn(defs, slot.name))
            throw new CodecError(
                `[scope] a ref names '${slot.name}', which this scope does not declare`,
            )
    // **A scope closes a copy.** Each `ref` of the copy is bound in `record`, and no slot that a
    // caller holds changes. So a scope reads its own arguments only, and a fragment stays open.
    // The key set of a dissection is the one fact that the term does not carry, so the copy of a
    // dissection takes the key set of the node that it replaces
    const record: Record<string, Term> = {}
    const [close, copies] = closedCopy(record)
    for (const [name, t] of Object.entries(terms))
        setOwn(record, name, close(t))
    for (const [was, copy] of copies) {
        const ks = keySets.get(was)
        if (ks !== undefined) keySets.set(copy, ks)
    }
    // The refusal of the guard carries the term of the entry, so a checker states the model's
    // guard on that term. Then each copy is judged one time, with each name bound
    for (const [name, t] of Object.entries(record)) {
        const refused = guard(t, name)
        if (refused) throw refused
    }
    for (const copy of copies.values()) {
        judged(copy, false)
        if (copy.kind === 'object')
            for (const f of Object.values(copy.body.fields))
                if (f.mark === 'fill') checkFill(codecOfTerm(f.t), f.v)
        const ks = keySets.get(copy)
        if (ks !== undefined && copy.kind === 'union')
            dissectionOf(copy, ks).resolution()
    }
    // **An entry is the codec of its closed term.** An entry that reaches no free name is the
    // codec that the caller declared. An object entry reads its spec and its open block from the
    // term. An entry carries the `.set()` of the node that its chain of `ref`s names, as its type
    // does. A `ref` and a literal carry no `.set()` of their own, so such an entry builds the set
    // of itself, and the judgment of the set refuses an element that writes no `S`, `N` or `B`. An
    // object and a union write `M` or no single member, so their entries carry no `.set()`
    return Object.fromEntries(
        Object.entries(defs).map(([name, def]) => {
            const t = record[name]
            if (t === undefined || t === terms[name])
                return [name, entryOf(def, t?.kind)]
            const codec: AnyCodec = codecOfTerm(t)
            if (t.kind !== 'object') return [name, entryOf(codec, t.kind)]
            const { spec, rest } = objectItem(t)
            return [name, { ...codec, spec, rest }]
        }),
    )
}

/** The entry of a scope over its codec: a codec with no `.set()` builds the set of itself. */
const entryOf = (codec: AnyCodec, kind: Term['kind'] | undefined): object =>
    'set' in codec || kind === 'object' || kind === 'union'
        ? codec
        : { ...codec, set: setOf(() => codec) }

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
 * marked declaration is refused the same way: `fill(c, v)` is the attribute that may be absent
 * and has a fill value, and it is what both nestings meant.
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
 * takes on no premise of its own — unlike {@link fill}, which must check its fill value is
 * writable because it writes one.
 */
export const undefinable = <const C extends AnyCodec>(
    inner: C,
): UndefinableCodec<Decoded<C>, AttributeOf<C>, C> &
    TermMark<['undefinable', TermOf<C>]> =>
    ({
        codec: inner,
        def: { mark: 'undefinable', t: termOf(inner) },
    }) as unknown as UndefinableCodec<Decoded<C>, AttributeOf<C>, C>

/**
 * The refusal in the type of {@link nullable} over a term whose null point no term decides. The run
 * time refuses at construction, unless a free name leaves the question open for the scope.
 */
type NullPointOver<Tm, F extends string> = [F] extends [never]
    ? [OwnsNull<Tm>] extends ['unknown']
        ? ErrorMessage<'[nullable] this term decides the null point by running a function, so whether the union would be certified is unknown. Write the wrapper inside instead, as in held(nullable(inner), outer, adapter)'>
        : unknown
    : unknown

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
    inner: AttributeCodec<T, A> & TermMark<Tm> & Free<F> & NullPointOver<Tm, F>,
): AttributeCodec<T | null, A | Attribute<'NULL'>> &
    TermMark<['union', [Tm, BaseT<'null'>]]> &
    Free<F> => {
    const t = termOf(inner as unknown as AnyCodec)
    const owns = ownsNullOf(t)
    // **An unbound `ref` leaves the answer open**: the codec is the union with `NULL`, an open
    // fragment, and the scope that binds the names checks the union on its closed copy. A `ref`
    // whose entry owns the null point fails that check, as a second option that writes `NULL`
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
 * clean. An attribute named `at`, `entry`, `narrow` or `toString` is a hop where the path reads it,
 * and the method where the path calls it.
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

/** The members of a codec: each option of a union, each variant of a tagged union, or the object. */
type MembersOf<C> = C extends UnionCodec<infer _T, infer Options>
    ? MembersOf<Options[number]>
    : C extends DiscriminatedCodec<infer T, infer D, infer Table>
      ? {
            [V in keyof Table]: {
                readonly spec: Table[V]
                readonly rest: undefined
                readonly t: VariantOf<T, D & keyof T, DecodedTags<Table[V], D>>
            }
        }[keyof Table]
      : C extends {
              readonly spec: infer Spec
              readonly rest: infer Rest
          }
        ? { readonly spec: Spec; readonly rest: Rest; readonly t: Decoded<C> }
        : unknown

/** The codec that a member holds at a key: the declared field, then the open entry. */
export type CodecAt<M, K> = M extends Spoken
    ? K extends keyof M['spec']
        ? Marks<M['spec'][K]>
        : M['rest'] extends AnyCodec
          ? M['rest']
          : never
    : unknown

/** The frontier one key down. A key that no known member holds gives an unknown frontier. */
export type ChildAt<F, K> = unknown extends F
    ? unknown
    : MembersOf<CodecAt<F, K>> extends infer Next
      ? [Next] extends [never]
          ? unknown
          : Next
      : unknown

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
 * p.priceIn.narrow(object({ tenderType: string('CASH') })).cardId   // → 'priceIn.cardId'
 * ```
 */
type PathNarrowing<T, F> = IsUnion<T> extends true
    ? {
          /**
           * **Narrows the path at run time and in the type, to the members that the clause does not
           * separate.** The pattern is an object
           * codec, read as {@link extract} reads an object pattern: each object of the pattern is open.
           *
           * A member stays where the clause cannot tell it apart. A pin `'A' | 'B'` stays under the
           * clause `'A'`, and a member with no pin at the key stays too. The walk of `at` separates
           * on the stored views, so `number(1)` and `decimal('1')` meet, and `decimal` and
           * `string` are apart. Where the path knows the codecs, this type separates on the stored
           * attributes too ({@link Kept}). Below a list, an adapter or a `ref`, and in the path of a
           * `tableEntry`, the type knows only the decoded types and is coarser ({@link Narrowed}).
           */
          narrow<const P extends ClausePattern>(
              pattern: P & ClauseOn<T, F, P['spec']>,
          ): unknown extends F
              ? PathOf<Narrowed<T, P['spec']>>
              : PathOf<Kept<F, P['spec']>['t'], Kept<F, P['spec']>>
      }
    : unknown

/**
 * **The members of a known frontier that a clause does not separate**, as the walk of `at` decides
 * it: on the stored side. A member goes where, at one key of the clause, the member holds no codec,
 * or the codec of the member and the codec of the clause are apart ({@link StoredApart}).
 */
type Kept<F, C> = F extends Member
    ? ClauseApart<F, C> extends true
        ? never
        : F
    : never

/**
 * **Whether a clause separates an object**, with each object of the clause open: the object is
 * apart where, at one key of the clause, it holds no codec, or its codec and the codec of the
 * clause are apart ({@link StoredApart}).
 */
type ClauseApart<X, C> = true extends {
    [K in keyof C]: [CodecAt<X, K>] extends [never]
        ? true
        : StoredApart<CodecAt<X, K>, C[K]>
}[keyof C]
    ? true
    : false

/**
 * **Two codecs whose stored attributes cannot meet**: the members of DynamoDB that the two write
 * share none, or each pins literals and the two pins share no stored value. The stored attribute
 * of an adapter is the attribute of its inner codec, so `number` and `decimal` each write `N`, and
 * `number(1)` and `decimal('1')` each store the text `1`. The pins are read on the term, under each
 * refinement and each adapter of the library.
 *
 * Two objects are apart where the clause separates the first, each object of the clause open. Coarser
 * than the walk of `at` in two places: two lists are never apart here, and a caller's adapter over a
 * literal pins nothing here, where the walk reads the literal under it.
 */
type StoredApart<X, Y> = [
    WrittenMembers<AttributeOf<X>> & WrittenMembers<AttributeOf<Y>>,
] extends [never]
    ? true
    : [X, Y] extends [Spoken, { readonly spec: infer Spec }]
      ? ClauseApart<X, Spec>
      : [StoredPin<X>] extends [never]
        ? false
        : [StoredPin<Y>] extends [never]
          ? false
          : [StoredPin<X> & StoredPin<Y>] extends [never]
            ? true
            : false

/** The stored texts that the term of a codec pins, or `never` where the term pins no literal. */
type StoredPin<C> = StoredPinAt<TermOf<C>, []>
type StoredPinAt<T, Env> = Norm<T, Env> extends [infer N, infer E]
    ? StoredPinOf<N, E>
    : never
type StoredPinOf<N, E> = N extends ['prim', ['literal', unknown, infer V]]
    ? StoredText<V>
    : N extends ['union', infer Os extends unknown[]]
      ? true extends {
            [I in keyof Os]: [StoredPinAt<Os[I], E>] extends [never]
                ? true
                : false
        }[number]
          ? never
          : { [I in keyof Os]: StoredPinAt<Os[I], E> }[number]
      : N extends ['refine', infer I, ...unknown[]]
        ? StoredPinAt<I, E>
        : [LibraryInner<N>] extends [never]
          ? never
          : StoredPinAt<LibraryInner<N>, E>
/**
 * The inner term of an adapter of the library, as `decimal('1')` and `number(1)` build, or `never`.
 * A caller's adapter (`['caller']`) pins nothing at the type: its decoded type is the caller's.
 */
type LibraryInner<N> = N extends [
    'held',
    unknown,
    infer I,
    unknown,
    [infer G, unknown],
    ...unknown[],
]
    ? [G] extends [['caller']]
        ? never
        : I
    : never

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
 * **The marker of a whole-item reading.** Each reading that {@link item} returns carries the
 * marker, and no other codec carries it: an object codec has a `spec` too, so `spec` does not tell
 * a reading from a codec. Test a root with `itemMark in root`. The reading types state the same
 * fact as `readonly [itemMark]: true`, and the type of a root reads it from there.
 */
export const itemMark = Symbol('item reading')
/** Nothing, or why the clause keeps no option: `K` holds the frames that the clause keeps. */
type ClauseOnFrames<K> = K extends []
    ? ErrorMessage<'[narrow] the clause separates every member of this union'>
    : unknown

/** The place one segment down, or {@link Refused}. */
type StepAt<H, S> = H extends ['term', infer Fs, infer T, infer F, unknown]
    ? StepTerm<Fs, NonNullable<T>, F, OffersAt<Fs>, S>
    : H extends ['path', infer T, infer F]
      ? StepPath<NonNullable<T>, F, S>
      : Refused
type StepTerm<Fs, T, F, O, S> = S extends string
    ? string extends S
        ? [Extract<O, ['open']>] extends [never]
            ? Refused
            : ['path', ValueAt<T, string>, unknown]
        : [S] extends [Extract<O, ['name', unknown]>[1]]
          ? [
                'term',
                StepFrames<['name', S], Fs>,
                ValueAt<T, S>,
                ChildAt<F, S>,
                false,
            ]
          : [Extract<O, ['open']>] extends [never]
            ? Refused
            : [
                  'term',
                  StepFrames<['name', S], Fs>,
                  ValueAt<T, S>,
                  ChildAt<F, S>,
                  false,
              ]
    : S extends number
      ? [Extract<O, ['pos']>] extends [never]
          ? Refused
          : number extends S
            ? ['path', ElementOf<T>, unknown]
            : ['term', StepFrames<['pos', S], Fs>, ElementOf<T>, unknown, false]
      : Refused
type StepPath<T, F, S> = [T] extends [readonly unknown[]]
    ? [T[number]] extends [never]
        ? Refused
        : S extends number
          ? ['path', T[number], unknown]
          : Refused
    : [T] extends [object]
      ? S extends string
          ? [S] extends [UnionKeys<T>]
              ? ['path', ValueAt<T, S>, ChildAt<F, S>]
              : Refused
          : Refused
      : Refused

/** The segments that a place offers one step down: the names, any name where open, a position. */
type OfferedAt<H> = H extends ['term', infer Fs, unknown, unknown, unknown]
    ? OffersAt<Fs> extends infer O
        ?
              | Extract<O, ['name', unknown]>[1]
              | ([Extract<O, ['open']>] extends [never] ? never : string)
              | ([Extract<O, ['pos']>] extends [never] ? never : number)
        : never
    : H extends ['path', infer T, unknown]
      ? [NonNullable<T>] extends [readonly unknown[]]
          ? number
          : [NonNullable<T>] extends [object]
            ? UnionKeys<NonNullable<T>> & string
            : never
      : never

/** The place at the end of a path, or {@link Refused}. A path that is no tuple has no place. */
type WalkAt<H, S> = H extends Wide
    ? Wide
    : S extends readonly [infer Head, ...infer Tail]
      ? WalkAt<StepAt<H, Head>, Tail>
      : S extends readonly []
        ? H
        : Wide

/** Why the place at the end of a path holds no one codec, or nothing where the place holds one. */
type ResolvesAt<H> = H extends ['term', infer Fs, unknown, unknown, unknown]
    ? [KindOfFrames<Fs>] extends ['resolved']
        ? unknown
        : ErrorMessage<`[at] the path is ${KindOfFrames<Fs> & string}: no one codec stands at the path`>
    : H extends ['path', unknown, unknown]
      ? unknown
      : ErrorMessage<'[at] no codec stands at the path'>

/** The refusal of a segment, with the segments that the place offers. */
type NoSegment<O> = ErrorMessage<'[at] the place offers no such segment'> & {
    readonly '[at] the place offers': O
}

/**
 * **The check of a tuple path**, as an intersection with the parameter. A segment that the place
 * does not offer meets a refusal that names the segments that the place offers, so the refusal lands
 * on that segment. A path to a place that holds no one codec is a refusal of the path.
 */
type CheckPath<H, S, Done extends readonly unknown[] = []> = H extends
    | Wide
    | Refused
    ? unknown
    : S extends readonly [infer Head, ...infer Tail]
      ? StepAt<H, Head> extends infer N
          ? N extends Refused
              ? readonly [...Done, Head & NoSegment<OfferedAt<H>>, ...Tail]
              : CheckPath<N, Tail, [...Done, Head]>
          : never
      : S extends readonly []
        ? ResolvesAt<H>
        : unknown

/** The check of a path in DynamoDB syntax: the refusal names the path. */
type CheckString<H, S extends string> = string extends S
    ? unknown
    : WalkAt<H, ParsePath<S>> extends infer N
      ? N extends Refused
          ? ErrorMessage<`[at] '${S}' is no path of this codec`>
          : ResolvesAt<N>
      : never

/**
 * **The segments that an editor completes**, as a second member of the parameter, which accepts
 * no path that the check refuses. The editor blocks the inference from the element that it
 * completes, so that element infers as `unknown`, and no path that the user writes holds `unknown`.
 * At that element the member offers the segments that the place offers after the elements before
 * it. A string path gets the text up to the last `.`, followed by each name that the place there
 * offers. The member excludes each string of the path, so the member never accepts the path that
 * the user wrote, and the check alone decides.
 */
type CompleteAt<H, S> = [S] extends [string]
    ? CompleteString<H, S, LastPart<S>>
    : S extends readonly unknown[]
      ? unknown extends S[number]
          ? CompletePath<H, S>
          : never
      : never
type CompletePath<H, S, Done extends readonly unknown[] = []> = H extends
    | Wide
    | Refused
    ? never
    : S extends readonly [infer Head, ...infer Tail]
      ? unknown extends Head
          ? 0 extends 1 & Head
              ? never
              : readonly [...Done, OfferedAt<H>, ...Tail]
          : CompletePath<StepAt<H, Head>, Tail, [...Done, Head]>
      : never
type CompleteString<H, S extends string, L> = L extends [
    infer P extends string,
    unknown,
]
    ? WalkAt<H, ParsePath<P extends `${infer Q}.` ? Q : P>> extends infer N
        ? N extends Wide | Refused
            ? never
            : Exclude<`${P}${PlainName<OfferedAt<N>>}`, S>
        : never
    : never

type CheckAt<H, S> = S extends string ? CheckString<H, S> : CheckPath<H, S>

/**
 * **The place at the start of a walk.** A located codec continues its own place. An item starts at
 * its root, which writes a row. Any other codec starts at its own term, an attribute at level 0.
 */
type StartOf<C> = C extends { readonly [locatedFrom]?: [infer H, RootKind] }
    ? unknown extends H
        ? StartOfCodec<C>
        : H
    : StartOfCodec<C>
type StartOfCodec<C> = C extends { readonly [itemOfMarker]?: [infer U] }
    ? unknown extends U
        ? StartOfItem<C>
        : ['term', [[TermOf<U>, []]], Decoded<U>, MembersOf<U>, true]
    : StartOfItem<C>
type StartOfItem<C> = C extends {
    readonly encodePartial: unknown
    readonly spec: infer Spec
    readonly rest: infer Rest
    readonly unsafeDecode: (this: Closed, item: StoredItem) => infer T
}
    ? [
          'term',
          [
              [
                  C extends { readonly [itemTermMarker]?: [infer Tm] }
                      ? [Tm] extends [OfParts]
                          ? ObjectTermOf<Spec, Rest>
                          : Tm
                      : ObjectTermOf<Spec, Rest>,
                  [],
              ],
          ],
          T,
          ItemFrontier<T, Spec, Rest>,
          true,
      ]
    : ['term', [[TermOf<C>, []]], Decoded<C>, MembersOf<C>, false]

/**
 * **The located codec at a place.** The decoded type is a function of the first frame, and the
 * attribute is the member that the model reads there. The root of an item is an item reading: it
 * writes a row and reads a row. A place where the type knows no frame keeps the decoded type and the
 * wide `AttributeValue`. A place that holds no one codec is a codec that refuses each value on use,
 * so a `narrow` that keeps several options continues, and `at(l, [])` refuses where it ends.
 */
type FocusAt<H, R extends RootKind> = H extends Wide
    ? AnyCodec & { readonly [locatedFrom]?: [Wide, R] }
    : H extends ['term', infer Fs, unknown, unknown, infer Root]
      ? Root extends true
          ? LocatedRow<
                [KindOfFrames<Fs>] extends ['resolved']
                    ? Exclude<TermPathValue<Fs>, undefined>
                    : unknown,
                H,
                R
            >
          : TermPathEncoded<Fs> extends infer A extends AttributeValue
            ? [KindOfFrames<Fs>] extends ['resolved']
                ? LocatedCodec<Exclude<TermPathValue<Fs>, undefined>, A, H, R>
                : LocatedCodec<unknown, AttributeValue, H, R>
            : never
      : H extends ['path', infer T, unknown]
        ? LocatedCodec<Exclude<T, undefined>, AttributeValue, H, R>
        : // a refused place follows a refusal of the type, and keeps the codec usable after it
          LocatedCodec<unknown, AttributeValue, Refused, R>

/**
 * **The place after `narrow`**, or {@link Refused}: the options that the clause does not separate.
 * Where the place holds frames, the frames decide the clause. Where it holds none, the decoded type
 * and the frontier decide it, on a union only.
 */
type NarrowAt<H, C> = H extends Wide
    ? Wide
    : H extends ['term', infer Fs, infer T, infer F, infer Root]
      ? HoldsFree<Fs> extends true
          ? NarrowPath<NonNullable<T>, F, C>
          : NarrowFrames<Fs, ClauseTerms<C>> extends infer K
            ? K extends []
                ? Refused
                : ['term', K, DecodeFrames<K>, unknown, Root]
            : never
      : H extends ['path', infer T, infer F]
        ? NarrowPath<NonNullable<T>, F, C>
        : Refused
type NarrowPath<T, F, C> = [T] extends [readonly unknown[]]
    ? Refused
    : [T] extends [object]
      ? IsUnion<T> extends true
          ? unknown extends F
              ? ['path', Narrowed<T, C>, unknown]
              : ['path', Kept<F, C>['t'], Kept<F, C>]
          : Refused
      : Refused

/** Nothing, or why `narrow` refuses the clause at the place. */
type CheckNarrow<H, C> = H extends Wide
    ? unknown
    : H extends ['term', infer Fs, infer T, infer F, unknown]
      ? HoldsFree<Fs> extends true
          ? CheckNarrowPath<NonNullable<T>, F, C>
          : ClauseOnFrames<NarrowFrames<Fs, ClauseTerms<C>>>
      : H extends ['path', infer T, infer F]
        ? CheckNarrowPath<NonNullable<T>, F, C>
        : ErrorMessage<'[narrow] no codec stands at the path'>
type CheckNarrowPath<T, F, C> = NarrowPath<T, F, C> extends Refused
    ? ErrorMessage<'[narrow] the codec at the path is no union'>
    : ClauseOn<T, F, C>

/**
 * The codecs an item needs: one per attribute, optional exactly where the entity is.
 *
 * Each attribute that the entity states has a field, and the spec names no other attribute. A field
 * is an {@link OptionalCodec} where the entity admits `undefined` at the attribute. Elsewhere the
 * field is a {@link Nestable} codec of the type of the attribute. A plain codec at an optional
 * attribute is a type error of this type, and `tableEntry` accepts that record.
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
    /** What this object declares. {@link item} reads the same declaration as a whole item. */
    readonly spec: Spec
    /** The codec of an attribute the spec does not declare, or `undefined` for a closed object. */
    readonly rest: Rest
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
    /** The reading of this union as a whole item, which {@link item} returns. Type-level only. */
    readonly [itemMarker]: [Tagged<T, D, Spec> & Free<F>]
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
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
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
    Rests extends readonly unknown[] = [],
> = {
    readonly encode: (this: Closed, value: T) => Result<Attribute<'M'>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => Attribute<'M'>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    /** The reading of this dissection as a whole item, which {@link item} returns. Type-level only. */
    readonly [itemMarker]: [Dissected<T, Ks, Specs> & Free<F>]
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [F]
    /** The rest of each member, which a slice keeps with the member. Type-level only. */
    readonly [restsMarker]?: [Rests]
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
          DerivedVariants<SpecsOf<Options>, RestsOf<Options>>,
          D,
          ByTag<SpecsOf<Options>, D>,
          FreeOf<Options[number]>
      >
    : DissectedCodec<
          DerivedVariants<SpecsOf<Options>, RestsOf<Options>>,
          Ks,
          SpecsOf<Options>,
          FreeOf<Options[number]>,
          RestsOf<Options>
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
    readonly [itemMarker]: [
        AllObjects<Options> extends true
            ? Untagged<T, SpecsOf<Options>> & Free<UnionFree<Options, Tm>>
            : ErrorMessage<'[union] this union can hold an attribute that is not a map, so it has no whole-item reading — an item is always a map'>,
    ]
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

/**
 * **What a pattern keeps of a codec**: the slice of a sum, and the slice of a union of one option
 * for any other codec. A sum keeps its form: a tagged union slices to a tagged union over the same
 * keys, and a dissection to a dissection.
 *
 * The tag table of a tagged union does not shrink with the entity type. A member that the clause
 * dropped is still keyed in the table, and asking for it gives an `ItemCodec<never>`: the entity
 * type is what the slice narrows, and the runtime is what refuses the assignment.
 */
type Slice<C, P, Keep extends boolean> = C extends DiscriminatedCodec<
    infer T,
    infer D,
    infer Spec,
    infer _F
>
    ? DiscriminatedCodec<
          KeptVariants<T, D, KeptByTag<Spec, P, Keep>>,
          D,
          KeptByTag<Spec, P, Keep>
      >
    : C extends DissectedCodec<
            infer _T,
            infer Ks,
            infer Specs,
            infer _F,
            infer Rests
        >
      ? DissectedCodec<
            DerivedVariants<
                Extracted<Specs, P, Keep>,
                ExtractedRests<Specs, Rests, P, Keep>
            >,
            Ks,
            Extracted<Specs, P, Keep>,
            never,
            ExtractedRests<Specs, Rests, P, Keep>
        >
      : C extends UnionCodec<
              infer _T,
              infer Options extends readonly unknown[],
              infer Tm
          >
        ? UnionSlice<Tm, KeptOptions<Options, P, Keep>>
        : UnionSlice<OfParts, KeptOptions<LiteralOptions<C>, P, Keep>>

/**
 * **The options of a codec that no union former built**: one option for each literal where the term
 * is a union of literals, as `string('A', 'B')` builds, because the run time slices that term by its
 * options. Any other codec is one option.
 */
type LiteralOptions<C> = TermOf<C> extends [
    'union',
    infer Ts extends readonly ['prim', ['literal', string, unknown]][],
]
    ? {
          -readonly [I in keyof Ts]: AttributeCodec<
              DecodeTerm<Ts[I]>,
              AttributeOf<C> & AttributeValue
          > &
              TermMark<Ts[I]>
      }
    : [C]

export type ItemCodec<T, Spec = unknown, Rest = undefined, Tm = OfParts> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
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
    readonly spec: Spec
    /** The codec of an attribute the spec does not declare, or `undefined` for a closed object. */
    readonly rest: Rest
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
    /** The term that {@link at} walks. Type-level only. */
    readonly [itemTermMarker]?: [Tm]
}

/** An {@link AttributeCodec} that also knows where it lives, and keeps the attribute it writes. */
export type LocatedCodec<
    T,
    A extends AttributeValue = AttributeValue,
    P = unknown,
    R extends RootKind = RootKind,
> = AttributeCodec<T, A> & {
    /**
     * The place where this codec sits, which {@link at} and {@link narrow} continue, and the kind
     * of the root that the walk started from, which {@link path} reads. Type-level only.
     */
    readonly [locatedFrom]?: [P, R]
}

/** The codec at the root of an item reading: it writes a row and reads a row, and keeps its place. */
type LocatedRow<T, P, R extends RootKind> = {
    readonly encode: (this: Closed, value: T) => Result<AttributeMap>
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => AttributeMap
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    readonly def: Term
    readonly [locatedFrom]?: [P, R]
}

/**
 * **The kind of the root of a walk**: an item, or any other codec. Only an item writes the
 * top-level attributes of a row, so only a path from an item is a document path of the row.
 */
export type RootKind = 'item' | 'relative'

/**
 * The kind of the root that a walk from `C` starts at: a located codec keeps its own. Only an item
 * reading carries {@link itemMark}, so the mark is the one test of an item. An object codec holds a
 * `spec` as well, so `spec` is no test.
 */
type RootOf<C> = C extends {
    readonly [locatedFrom]?: [unknown, infer R extends RootKind]
}
    ? RootKind extends R
        ? KindOfRoot<C>
        : R
    : KindOfRoot<C>
type KindOfRoot<C> = C extends Marked ? 'item' : 'relative'

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
 * const delivered = at(Adoption.item, ['shipment', 'legs', i, 'deliveredAt'])
 * path(delivered)             // 'shipment.legs[1].deliveredAt'
 * delivered.encode(stamp)     // through the codec declared for it
 * ```
 *
 * The codec keeps the attribute it writes: `A` is the member that the model reads at the
 * resolved frame, as the one attribute of that member, so `encode` gives `{ S: string }` at a
 * string. A frame where the model reads no one member gives the union of the attributes of
 * its options, and the wide `AttributeValue` where an option has no member the type computes
 * (`opaque`). The root of the item writes a row, and keeps the wide `AttributeValue`.
 *
 * A free function and not a member: a member is typed on each codec type that carries the member,
 * and a function is typed only at a call. The parameter is {@link Closed}, so a codec that reads an
 * unbound name is refused at the call.
 */
export function at<C, const S extends readonly Segment[] | string>(
    codec: Closed & C & { readonly def: Term },
    path: (S & CheckAt<StartOf<C>, S>) | NoInfer<CompleteAt<StartOf<C>, S>>,
): FocusAt<WalkAt<StartOf<C>, SegmentsOf<S>>, RootOf<C>>
export function at(
    codec: { readonly def: Term },
    path: readonly Segment[] | string,
): unknown {
    // a located codec continues its own path from its own root, so `at(at(c, p), q)` walks
    // `p ++ q` from the root of `c`: the segments join, and the preconditions conjoin
    // the slot is a symbol property and not a registry entry, so a spread copy of a located codec
    // keeps its location. The read casts, because no type names the slot
    const prior = (codec as { readonly [locatedSlot]?: Located })[locatedSlot]
    // the walk reads the item codec as one codec among those it carries, which it is at run time
    const root = prior?.root ?? (codec as unknown as AnyCodec)
    return locate(
        root,
        [
            ...(prior?.steps ?? []),
            ...(typeof path === 'string' ? parsePath(path) : path),
        ],
        prior,
    )
}

/**
 * **Narrows a located codec to the options that a pattern does not separate.** The pattern is an
 * object codec, read as {@link extract} reads an object pattern: each object of the pattern is open.
 * The path keeps its segments, and the clause adds its preconditions at the path.
 *
 * The test reads the stored views, so `number(1)` and `decimal('1')` meet, and `decimal` and
 * `string` are apart. A kept option stays as the codec declares it: the narrowing refines no option.
 */
export function narrow<L, const P extends ClausePattern>(
    located: Closed & L & { readonly def: Term },
    pattern: P & CheckNarrow<StartOf<L>, P['spec']>,
): FocusAt<NarrowAt<StartOf<L>, P['spec']>, RootOf<L>>
export function narrow(
    located: { readonly def: Term },
    pattern: ClausePattern,
): unknown {
    // read through a cast, for the reason at {@link at}: a spread copy must keep its location
    const prior = (located as { readonly [locatedSlot]?: Located })[locatedSlot]
    const root = prior?.root ?? (located as unknown as AnyCodec)
    return locate(root, [...(prior?.steps ?? []), clauseOf(pattern)], prior)
}

/**
 * **The segments of a document path in DynamoDB syntax**: a name, or a position in brackets, each
 * name after the first behind a `.`. A name holds no `.`, `[` or `]`: the tuple form carries such a
 * name. A malformed path is a defect of the caller, and the type of {@link at} refuses it first.
 */
const parsePath = (path: string): readonly Segment[] => {
    if (path === '') return []
    const segments: Segment[] = []
    for (const part of path.split('.')) {
        const parsed = /^([^[\]]*)((?:\[\d+\])*)$/.exec(part)
        if (parsed === null) {
            throw new CodecError(
                `'${path}' is no document path: a name holds no '[' or ']', and a position is digits in brackets`,
            )
        }
        const [, name = '', positions = ''] = parsed
        if (name !== '' || positions === '') segments.push(name)
        for (const [, digits] of positions.matchAll(/\[(\d+)\]/g)) {
            segments.push(Number(digits))
        }
    }
    return segments
}

/** Whether a codec is a whole-item reading: an object's, a union's or a tagged union's `item`. */
const isItemReading = (codec: object): boolean => itemMark in codec

/** The codec at the steps of a path from a root, with its place. */
const locate = (
    root: AnyCodec,
    steps: readonly Step[],
    prior: Located | undefined,
): unknown => {
    const itemDef = termOf(root)
    // a whole-item reading writes no map, and only such a reading carries the item mark. An object
    // codec holds a `spec` as well, so `spec` is no test
    const whole = isItemReading(root)
    const segments = segmentsIn(steps)
    const located = asPath(segments)

    /**
     * The walk carries a *set* of codecs, not one.
     *
     * A path may pass through a segment the variants declare differently and still arrive
     * where they agree — `legs` is a one-tuple in `SINGLE_LEG` and a two-tuple in
     * `MULTI_LEG`, but indexing either reaches the same leg codec. So the disagreement is
     * carried along and reported only if it survives to the end, where using it would mean
     * encoding with a codec nobody declared.
     */
    let reached: Reached | undefined
    const walk = (): AnyCodec => {
        // a prior place that the walk reached continues from its frontier, so a composition
        // walks each step one time
        const from: Reached | undefined = prior?.reached
        let frontier: readonly AnyCodec[] = from?.frontier ?? [root]
        let cycles = from?.cycles
        if (cycles === undefined) {
            const open = openRefusal(itemDef)
            if (open) return refusedAt(open)
            const flat = flatOf(itemDef)
            // `openRefusal` refused an open item above, and `scope` refuses an unguarded cycle of refs
            // (RecursionRefused), so a closed item has a flat scope
            if (flat.kind === 'refused')
                return refusedAt(new CodecError(flat.reason))
            cycles = flat.cycles
        }
        for (const step of from ? steps.slice(prior?.steps.length) : steps) {
            const next =
                typeof step === 'object'
                    ? narrowAcross(frontier, step)
                    : acrossVariants(frontier, step, cycles)
            if (next instanceof CodecError) return refusedAt(next)
            // a frontier where no codec admits a value is a name that no codec declares
            if (next.every(admitsNothing)) {
                throw new CodecError(
                    `no attribute is declared at '${located}'`,
                    'vacant',
                )
            }
            frontier = next
        }
        reached = { frontier, cycles }
        // the root keeps its form. A clause at the root keeps the options that it does not separate,
        // and the codec of the kept options refuses a value of a dropped option. The root of an item
        // is an item reading, which the kept options read as a row
        if (segments.length === 0) {
            const [only, ...others] = frontier as [AnyCodec, ...AnyCodec[]]
            if (frontier.length === 1 && only === root) return root
            const kept = others.length === 0 ? only : union(frontier as never)
            // the walk carries each codec as an `AnyCodec`, and the codec of the kept options is
            // one, which it is at run time as the root is
            return (whole ? item(kept as never) : kept) as unknown as AnyCodec
        }
        const [first, ...ambiguous] = frontier as [AnyCodec, ...AnyCodec[]]
        // the item root is no level, and each segment past the first crosses one L or M. Any
        // other root is an attribute at level 0, and each segment crosses one L or M. Only an
        // item writes the top-level attributes of a row, and the 32-level limit counts from the
        // row, so from any other root the bound counts one level early and stays conservative
        const level = segments.length - (whole ? 1 : 0)
        return ambiguous.length === 0
            ? level === 0
                ? first
                : codecAtLevel(first.def, level)
            : unresolvedAt(String(located), frontier.some(admitsNothing))
    }
    const here = walk()

    const made: Located = { root, steps, path: located, reached }
    return { ...here, [locatedSlot]: made }
}
type Located = {
    readonly root: AnyCodec
    readonly steps: readonly Step[]
    readonly path: string
    /** The frontier at the end of the steps, where the walk reached the end. */
    readonly reached: Reached | undefined
}

/**
 * **The document path of a located codec**, in DynamoDB expression syntax: the external form of
 * the segments, so `path(at(c, 'a.b[1]'))` is `'a.b[1]'`. A codec that no `at` located stands at
 * its own root, and its path is empty.
 *
 * From a root that is not an item, the path is relative to that root, and `path` gives the segments
 * and no string. Only an item writes the top-level attributes of a row, so no other root knows the
 * prefix of the row, and a relative string in an `UpdateExpression` writes at the wrong place.
 */
export function path(codec: {
    readonly def: Term
    readonly [locatedFrom]?: [unknown, 'item']
}): string
export function path(codec: {
    readonly def: Term
    readonly [locatedFrom]?: [unknown, 'relative']
}): readonly Segment[]
export function path(codec: { readonly def: Term }): string | readonly Segment[]
export function path(codec: {
    readonly def: Term
}): string | readonly Segment[] {
    // read through a cast, for the reason at {@link at}: a spread copy must keep its location
    const located = (codec as { readonly [locatedSlot]?: Located })[locatedSlot]
    if (located === undefined) return ''
    // only an item writes the top-level attributes of a row, so only a path from an item is a
    // document path; any other root gives its segments, which no expression takes for a path
    return isItemReading(located.root)
        ? located.path
        : segmentsIn(located.steps)
}

/**
 * **The condition under which a write at the path of a located codec is safe**, as a conjunction
 * of {@link Precondition}s: one group for each `narrow` on the path, empty where the path has no
 * `narrow`. The narrowing drops options, and an item of a dropped option may still be stored. Put
 * the preconditions in the `ConditionExpression` of the write, so the write refuses such an item.
 *
 * A refusal where a clause key stores a term that no exact precondition states.
 */
export const preconditions = (located: {
    readonly def: Term
}): Result<readonly Precondition[]> =>
    // read through a cast, for the reason at {@link at}: a spread copy must keep its location
    preconditionsOf(
        (located as { readonly [locatedSlot]?: Located })[locatedSlot]?.steps ??
            [],
    )

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
    // not: whether a fill value has to be copied per read, a fact about this runtime and not about
    // the declaration.
    const fields: Record<string, Field> = {}
    const declaredSpec = spec as unknown as Record<string, ObjectSlot>
    for (const name in declaredSpec) {
        setOwn(fields, name, fieldOf(declaredSpec[name] as ObjectSlot))
    }

    const declaredBody: Body =
        rest === undefined ? { fields } : { fields, rest: termOf(rest) }
    const itemDef = { kind: 'object', body: declaredBody } as const
    // the judgment of the node runs before the item pair is built
    const nested = codecOfTerm(itemDef) as unknown as AttributeCodec<
        DerivedItem<Spec, Rest>,
        M<EncodedBy<Spec, Rest>>
    >
    // the `M` is what this codec writes; `item` is the same two directions with the wrapper taken
    // off. Named member by member rather than spread so the cast keeps the *shape* the map carries —
    // `Attribute<'M'>` would flatten it to "some map" — and so that a call to `object` stays a plain
    // object literal, which is what lets a bundler drop an unused one
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        spec,
        rest,
    }
}

/**
 * **The whole-item reading of an object node, a function of the node.** The spec holds the codec
 * of each field term, and `rest` holds the codec of the open term. The memo is a cache only.
 */
const objectReadings = new WeakMap<ItemTerm, ObjectItem>()

const objectItem = (itemDef: ItemTerm): ObjectItem => {
    const built = objectReadings.get(itemDef)
    if (built) return built
    /**
     * **The view, and this is where it starts.**
     *
     * The owner's ruling: the top-level map belongs to the view, not to the codec. An `object`
     * codec writes an `M` like any other term, and {@link item} is the one reading that writes no map —
     * the same pair, one level in.
     *
     * So the pair is not built here. `denote.ts` builds one item pair per term and this hands out
     * that one, which is what makes `item.encode === codec.encode`'s body the same function. They
     * were two objects before `579ed89`, and nothing said which of them a caller was running.
     */
    const body = itemSem(itemDef)
    const { spec, rest } = slotsOf(itemDef.body)
    // a term that reads a name that no scope binds refuses each use
    const self: ObjectItem = {
        [itemMark]: true,
        encode: (item) =>
            openRefusal(itemDef) ??
            itemRefusal(item) ??
            (body.encode(item) as never),

        encodePartial: (patch) =>
            openRefusal(itemDef) ??
            itemRefusal(patch) ??
            (body.encode(patch as Record<string, unknown>, 0, true) as never),

        decode: (item) =>
            openRefusal(itemDef) ??
            itemRefusal(item) ??
            membersTooDeeply(item, 0) ??
            (body.decode(
                item as Readonly<Record<string, AttributeValue>>,
            ) as never),

        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        unsafeEncodePartial: (patch) => orThrow(self.encodePartial(patch)),

        spec,
        rest,
        def: itemDef,
    }
    objectReadings.set(itemDef, self)
    return self
}

type Marked = { readonly [itemMark]: true }

/** A whole-item reading, as the run time holds it. */
type Reading = Marked & { readonly spec: unknown }

/** The whole-item reading of the node that a term names: an object, a dissection, or a union. */
const readingOf = (t: Term): Reading | undefined => {
    const node = resolvedTerm(t)
    if (node?.kind === 'object') return objectItem(node)
    if (node?.kind !== 'union') return undefined
    const ks = keySets.get(node)
    return ks ? dissectionOf(node, ks).self : unionOf(node)
}

/** The whole-item reading of an object node: the declared spec, the open block, and the pair. */
type ObjectItem = ItemCodec<
    Record<string, unknown>,
    Record<string, ObjectSlot>,
    AnyCodec | undefined
>

/**
 * The same declaration, read as a whole item: the same two directions without the top-level map,
 * and the things only a top-level codec can offer: `encodePartial`, `field`, `at`, `path`.
 *
 * A DynamoDB item is a map that is never written as one; `PutItem` takes the attributes bare.
 * That is the *only* thing that separated an item codec from a nested one, and it is a fact about
 * where a codec is used rather than about what it declares, so it is a reading of one codec
 * rather than a second constructor. The marshaller draws the same line, under
 * `convertTopLevelContainer`.
 *
 * A free function and not a member: a member is typed on each codec type that carries the member,
 * and a function is typed only at a call. The reading is a function of the term, built once per
 * term. An object codec carries no type for the reading. A union carries the type of the reading
 * in one tuple.
 *
 * The union overload reads a union by the reading that its type carries: the reading of a union
 * of objects, of a tagged union, or of a dissection. A union that can hold an attribute that is not
 * a map has no reading, and the type is a message that says so.
 */
export function item<
    Spec extends Record<string, ObjectSlot>,
    Rest extends AnyCodec | undefined,
    T,
    Tm,
>(
    codec: ObjectCodec<Spec, Rest, T, Tm>,
): ItemCodec<ItemOf<T, Spec, Rest>, Spec, Rest, Tm> &
    Free<ObjectFree<Spec, Rest, Tm>>
export function item<C extends Itemable<unknown>>(codec: C): ReadingOf<C>
export function item(codec: object): unknown {
    const reading = readingOf(termOf(codec as AnyCodec))
    if (reading === undefined) {
        throw new CodecError(
            'this codec has no whole-item reading: `item` takes an object or a union',
        )
    }
    return reading
}

/** The whole-item reading of the node that a term names, or nothing where the node is no object. */
const objectNamed = (t: Term): ObjectItem | undefined => {
    const node = resolvedTerm(t)
    return node?.kind === 'object' ? objectItem(node) : undefined
}

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

type WildcardEntry<Entries extends readonly AnyObjectEntry[]> =
    Entries[number] extends infer Entry
        ? Entry extends readonly [
              AttributeCodec<infer Key, Attribute<'S'>>,
              infer Value extends ObjectSlot,
          ]
            ? string extends Key
                ? Marks<Value>
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
 * names fix the body at the declaration, so a key that names a `ref` that no scope binds is
 * refused at the declaration.
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
        if (names.length === term.options.length) {
            // a union with no option names no key, and an empty list of names is the wildcard
            if (names.length > 0) return names
            throw new CodecError(
                'an object entry key is a union with no option, which names no key',
            )
        }
    }
    if (term?.kind === 'string') return []
    throw new CodecError(
        'an object entry key must be `string` or a string literal key set',
    )
}

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
            if (Object.hasOwn(fields, name)) {
                throw new CodecError(`'${name}' is declared more than once`)
            }
            setOwn(fields, name, slot)
        }
    }
    return objectFromMap(fields, rest) as ObjectCodec<
        Record<string, ObjectSlot>,
        AnyCodec | undefined
    >
}

/** The options a factor offers, at the type level: a union's, or the factor itself. */
// the term is matched too: an entry of a scope is a union at the term of the entry, and a match at
// the default term reads such an entry as one option
type FactorOptions<F> = F extends UnionCodec<infer _T, infer Os, infer _Tm>
    ? Os
    : F extends {
            readonly [optionsMarker]?: infer Os extends readonly unknown[]
        }
      ? Os
      : readonly [F]

/** Whether any option of a factor is left open by a rest codec. */
type AnyOpen<F> = FactorOptions<F>[number] extends infer O
    ? O extends ObjectCodec<infer _S, infer R, infer _T, infer _Tm>
        ? [R] extends [undefined]
            ? never
            : true
        : never
    : never

/**
 * The members that the attribute of a codec carries: the required keys of `Attribute`, because an
 * `Attribute` types each other member as an optional `never`.
 */
type StoredMembers<C> = AttributeOf<C> extends infer W
    ? W extends unknown
        ? {
              [K in keyof W]-?: object extends Pick<W, K> ? never : K
          }[keyof W]
        : never
    : never

/**
 * **The meet of two slots at one name, at the type level**: the meet of the two codecs, under the
 * presence mark that the run time gives ({@link meetSlots}). The presence marks lie in the order of
 * {@link absentBelow} at the `relation` order, and the meet takes the mark of the side that lies
 * below the other, and `req` where neither side does: `undefinable` lies below `optional`, a
 * required slot lies below each slot, and a fill lies below no other mark. Two fills keep the fill
 * where the two slots are one type. The type reads no fill value, so the run time decides where two
 * fills of one type hold two fill values, and it gives `req` there.
 */
type MeetSlot<A, B> = MeetCodecs<Marks<A>, Marks<B>> extends infer M
    ? MeetMark<SlotMark<A>, SlotMark<B>> extends infer K
        ? [K] extends ['req']
            ? M
            : [K] extends ['fill']
              ? Same<A, B> extends true
                  ? MarkedMeet<'fill', M>
                  : M
              : MarkedMeet<K, M>
        : never
    : never

/**
 * The codec of a meet under a presence mark. A meet at `never` is the codec `never` there, because
 * a slot that may be absent still holds the absent row: `optional(never)` decodes to `{}`.
 */
type MarkedMeet<
    K,
    M,
    C = [M] extends [never] ? typeof never : M,
> = K extends 'fill'
    ? MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> &
          TermMark<['fill', TermOf<C>]>
    : K extends 'undefinable'
      ? UndefinableCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> &
            TermMark<['undefinable', TermOf<C>]>
      : OptionalCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> &
            TermMark<['optional', TermOf<C>]>

type SlotMark<S> = S extends { readonly [fillMarker]: unknown }
    ? 'fill'
    : S extends { readonly [undefinableMarker]: true }
      ? 'undefinable'
      : S extends { readonly [optionalMarker]: true }
        ? 'optional'
        : 'req'

/** The greatest lower bound of two presence marks, in the order of {@link absentBelow}. */
type MeetMark<A, B> = 'req' extends A | B
    ? 'req'
    : 'fill' extends A | B
      ? [A, B] extends ['fill', 'fill']
          ? 'fill'
          : 'req'
      : 'undefinable' extends A | B
        ? 'undefinable'
        : 'optional'

/**
 * The meet of two codecs at one name, at the type level. Two object slots meet on the union of
 * their names, as the run time reads both open. Of two other slots, the slot that fits the other is
 * the meet. Two slots that fit neither way and share no decoded value meet at
 * `never`. Two slots whose stored attributes share no member meet at `never` too, whatever adapter sits
 * over them. Two literal sets of one base that share a literal meet at the common literals, as the
 * run time reads them ({@link MeetLiterals}). Any other two slots that overlap without one fitting
 * the other keep the intersection of the two codecs, and decode to the values that both decode to:
 * the pair of a meet is one row and one value that both sides relate.
 */
type MeetCodecs<A, B> = [StoredMembers<A> & StoredMembers<B>] extends [never]
    ? never
    : [A, B] extends [AnyObjectCodec, AnyObjectCodec]
      ? MeetObjects<A, B>
      : [FitsCodec<A, B>] extends ['t']
        ? A
        : [FitsCodec<B, A>] extends ['t']
          ? B
          : [ArrayElement<A>] extends [never]
            ? MeetByDecoded<A, B>
            : [ArrayElement<B>] extends [never]
              ? MeetByDecoded<A, B>
              : MeetArrays<ArrayElement<A>, ArrayElement<B>>

/** The element of an `array` codec, or `never` for any other codec. */
type ArrayElement<C> = C extends { readonly [elementMarker]?: infer E }
    ? unknown extends E
        ? never
        : E
    : never

/**
 * **The meet of two arrays, at the type level**: the array of the meet of the two elements, as the
 * run time builds it ({@link meetLists}, the model's `alignedRows`). Where the elements meet at
 * `never`, the spread is `never` and the row of length zero stays, so the codec holds the empty
 * list and is no `never`.
 */
type MeetArrays<EA, EB> = MeetOfTwo<EA, EB> extends infer M
    ? ArrayOver<([M] extends [never] ? typeof never : M) & AnyCodec>
    : never

/** The meet of two codecs that share a member and fit neither way, by what they decode to. */
type MeetByDecoded<A, B> = [Decoded<A> & Decoded<B>] extends [never]
    ? never
    : MeetLiterals<A, B>

/**
 * **The meet of two literal sets, at the type level**: the codec of the common literals, as the run
 * time builds it. Each side is a literal or a union of literals at `string`, `number` or `boolean`,
 * with no adapter: the type reads no bytes of a `binary` literal. A side of another form is {@link Overlap}.
 */
type MeetLiterals<A, B> = [PlainLits<TermOf<A>>] extends [never]
    ? [PlainLits<TermOf<B>>] extends [never]
        ? Overlap<A, B>
        : MeetInexact<A, B>
    : [PlainLits<TermOf<B>>] extends [never]
      ? MeetInexact<B, A>
      : CommonCodec<CommonLits<PlainLits<TermOf<A>>, PlainLits<TermOf<B>>>, A>
/**
 * The meet of an inexact literal `W` with a literal `E` that is exact: the literals of `E` that
 * the decoded type of `W` holds, as the same codec in both orders.
 */
type MeetInexact<W, E> = Inexact<TermOf<W>> extends true
    ? CommonCodec<WithinLits<PlainLits<TermOf<E>>, Decoded<W>>, E>
    : Overlap<W, E>
type WithinLits<Ls extends unknown[], D> = Ls extends [
    infer Head,
    ...infer Rest extends unknown[],
]
    ? [DecodeTerm<Head>] extends [D]
        ? [Head, ...WithinLits<Rest, D>]
        : WithinLits<Rest, D>
    : []
/**
 * The intersection of two codecs that overlap, with the decoded type of the values that both
 * decode to. The last member decides the decoded type of an intersection of codecs, so a member
 * that states the intersection of the two decoded types comes last.
 */
type Overlap<A, B> = A &
    B &
    AttributeCodec<
        Decoded<A> & Decoded<B>,
        AttributeOf<A> & AttributeOf<B> & AttributeValue
    >
/**
 * The literal terms of a literal or of a union of literals with no adapter, or `never`. An inexact
 * literal ({@link Inexact}) names no value that two terms can share, so it is `never`.
 */
type PlainLits<T> = Inexact<T> extends true
    ? never
    : T extends ['prim', ['literal', PlainBase, unknown]]
      ? [T]
      : T extends ['union', infer Os extends unknown[]]
        ? [Os[number]] extends [['prim', ['literal', PlainBase, unknown]]]
            ? Os
            : never
        : never
type PlainBase = 'string' | 'number' | 'boolean'
/** The literals of `As` that `Bs` holds too: the same base and the same stored value. */
type CommonLits<As extends unknown[], Bs extends unknown[]> = As extends [
    infer Head,
    ...infer Rest extends unknown[],
]
    ? InLits<Head, Bs> extends true
        ? [Head, ...CommonLits<Rest, Bs>]
        : CommonLits<Rest, Bs>
    : []
type InLits<L, Bs extends unknown[]> = Bs extends [
    infer Head,
    ...infer Rest extends unknown[],
]
    ? Same<L, Head> extends true
        ? true
        : InLits<L, Rest>
    : false
/** The codec of the literals `Ls`, at the attribute of `A`: `never` where no literal is common. */
type CommonCodec<Ls extends unknown[], A> = Ls extends []
    ? never
    : Ls extends [infer One]
      ? AttributeCodec<DecodeTerm<One>, AttributeOf<A> & AttributeValue> &
            TermMark<One>
      : AttributeCodec<
            DecodeTerm<['union', Ls]>,
            AttributeOf<A> & AttributeValue
        > &
            TermMark<['union', Ls]>

/**
 * The slot of a name that the other object leaves undeclared. The other object holds the name at
 * its open block, an optional slot, and a fill lies below no optional slot, so the slot is required
 * at the codec that the fill fills.
 */
type Unfilled<S> = S extends {
    readonly [fillMarker]: unknown
    readonly codec: infer C
}
    ? C
    : S

/** One meet of two objects at the type level: the union of the names. */
type MeetSpecs<A, B> = {
    readonly [K in keyof Omit<A, keyof B>]: Unfilled<A[K & keyof A]>
} & {
    readonly [K in keyof Omit<B, keyof A>]: Unfilled<B[K & keyof B]>
} & {
    readonly [K in keyof A & keyof B]: MeetSlot<A[K], B[K]>
}

/** `never` where a name that the object requires meets at `never`, and the object holds no value. */
type HoldsNone<S> = true extends {
    [K in keyof S]: [S[K]] extends [never] ? true : false
}[keyof S]
    ? true
    : false

type MeetObjects<X, Y> = X extends ObjectCodec<
    infer A,
    infer _RA,
    infer _TA,
    infer _TmA
>
    ? Y extends ObjectCodec<infer B, infer _RB, infer _TB, infer _TmB>
        ? HoldsNone<MeetSpecs<A, B>> extends true
            ? never
            : ObjectCodec<show<MeetSpecs<A, B>>>
        : MeetSlot<X, Y>
    : MeetSlot<X, Y>

type DistributeOne<X, Ys extends readonly unknown[]> = {
    [I in keyof Ys]: MeetObjects<X, Ys[I]>
}

/** The `flatMap` order: outer first, inner second. */
type Distribute<
    Xs extends readonly unknown[],
    Ys extends readonly unknown[],
> = Xs extends readonly [infer H, ...infer T extends readonly unknown[]]
    ? [...DistributeOne<H, Ys>, ...Distribute<T, Ys>]
    : []

/** The meets without those at `never`, as `meetFactors` drops each option that meets at the bottom. */
type DropNever<Ms extends readonly unknown[]> = Ms extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? [H] extends [never]
        ? DropNever<T>
        : [TermOf<H>] extends [never]
          ? // an overlap of two codecs of two forms has no one term, and that is no meet at `never`
            [H, ...DropNever<T>]
          : [TermOf<H>] extends [['never']]
            ? DropNever<T>
            : [H, ...DropNever<T>]
    : []

/** The flat union of the meets, or the one meet, or the bottom where each meet is at `never`. */
type MeetOptions<X, Y> = DropNever<
    Distribute<FactorOptions<X>, FactorOptions<Y>>
> extends infer Ms extends readonly unknown[]
    ? Ms extends readonly []
        ? never
        : Ms extends readonly [infer One]
          ? One
          : UnionCodec<DerivedUnion<Ms>, Ms>
    : never

/**
 * One meet needs no union around it; several are one flat union. A factor that lies below the
 * other is the meet, and the run time tests the order of the whole factors before it distributes a
 * union. So the type tests the order first where a factor is a union, as `meetFactors` does. The
 * order is {@link BelowT} at the `value` order, and the run time reads the `relation` order, which
 * differs at a `fill` slot only.
 */
type MeetOfTwo<X, Y> = [TermOf<X>] extends [['never']]
    ? X
    : [TermOf<Y>] extends [['never']]
      ? Y
      : [FactorOptions<X>, FactorOptions<Y>] extends [
              readonly [unknown],
              readonly [unknown],
          ]
        ? MeetOptions<X, Y>
        : [MeetBelow<X, Y>] extends ['t']
          ? X
          : [MeetBelow<Y, X>] extends ['t']
            ? Y
            : MeetOptions<X, Y>

/** The order of the meet: each factor reads open, as {@link meetFactors} reads it. */
type MeetBelow<A, B> = BelowT<
    OpenT<TermOf<Marks<A>>>,
    OpenT<TermOf<Marks<B>>>,
    [],
    [],
    []
>

/** More than two factors fold left. */
type FoldMeet<Fs extends readonly unknown[]> = Fs extends readonly [
    infer A,
    infer B,
    ...infer R extends readonly unknown[],
]
    ? FoldMeet<[MeetOfTwo<A, B>, ...R]>
    : Fs extends readonly [infer A]
      ? A
      : never

/**
 * Nothing, or why the type of a meet refuses these factors. An open factor holds an undeclared name
 * through a codec of its own. The run time meets the open block, and the type of a meet reads no
 * open block, so the type refuses the factor at the call.
 */
export type ValidateMeet<Fs extends readonly unknown[]> = [
    AnyOpen<Fs[number]>,
] extends [never]
    ? HeldRefusal<Fs> extends true
        ? ErrorMessage<'[meet] a factor holds a `held` or an older part that fits neither side, and the two parts are apart in neither view. An opaque function decides which common rows relate one value, and the host cannot read the function. Meet only a part that one side fits'>
        : unknown
    : ErrorMessage<'[meet] a factor holds undeclared names through a `rest` codec, and the type of a meet reads no open block. Close every factor: give it no open key entry'>

/**
 * **Whether the fold of a meet reaches a `held` or an older part that the run time refuses**, read
 * at the top node of each factor, step by step as {@link FoldMeet} folds. The rule is the last
 * refusal of `meetParts`: one top node is a `held` or an older part, no top node is a refinement,
 * the order holds in neither direction, and the two parts are apart in neither view. The order is
 * `'f'` in both directions ({@link FitsCodec}), and `'u'` in one direction is no refusal, because
 * the type cannot decide. The stored views are apart where {@link ApartG} says so, and the caller
 * views are apart where {@link ApartG} says so over the outer term of each part ({@link CallerView}),
 * as `callerApart` reads the terms. Two caller
 * adapters meet at `'u'`: a caller's adapter against a caller's adapter is one adapter or two, and
 * the type cannot see which, so the run time builds the first and refuses the second. A `held` part
 * below a field of an object is no refusal here either, and the run time refuses it.
 */
type HeldRefusal<Fs extends readonly unknown[]> = Fs extends readonly [
    infer A,
    infer B,
    ...infer R extends readonly unknown[],
]
    ? HeldPairRefused<A, B> extends true
        ? true
        : HeldRefusal<[MeetOfTwo<A, B>, ...R]>
    : false
type HeldPairRefused<A, B> = [
    NodeOf<TermOf<Marks<A>>>,
    NodeOf<TermOf<Marks<B>>>,
] extends [infer NA, infer NB]
    ? true extends IsPart<NA> | IsPart<NB>
        ? true extends IsRefine<NA> | IsRefine<NB> | OneAdapter<NA, NB>
            ? false
            : [FitsCodec<A, B>, FitsCodec<B, A>] extends ['f', 'f']
              ? ApartG<
                    TermOf<Marks<A>>,
                    [],
                    TermOf<Marks<B>>,
                    [],
                    []
                > extends true
                  ? false
                  : ApartG<
                          CallerView<NA, TermOf<Marks<A>>>,
                          [],
                          CallerView<NB, TermOf<Marks<B>>>,
                          [],
                          []
                      > extends true
                    ? false
                    : true
              : false
        : false
    : false
/**
 * The caller view of a node, as `callerApart` reads the terms: a `held` reads its outer term, an
 * older reading reads its current form, and any other node is its own caller view. That view is the
 * term `T` of the factor, and not the node, because the term holds the scope that binds its names.
 * The outer term of a foreign schema is `opaque`, which overlaps each view.
 */
type CallerView<N, T> = N extends [
    'held',
    unknown,
    unknown,
    infer O,
    ...unknown[],
]
    ? O
    : N extends ['legacy', infer Current]
      ? Current
      : T
/** Whether a node is a part that no meet reads: a `held` or an older reading. */
type IsPart<N> = N extends ['held', ...unknown[]] | ['legacy', unknown]
    ? true
    : false
type IsRefine<N> = N extends ['refine', ...unknown[]] ? true : false
/**
 * Whether two `held` nodes carry one adapter tag. The run time meets two literal sets under one
 * adapter at the common literals ({@link commonHeldLiterals}), before it reads the refusal. The
 * type reads no literal set here, so the pair of one tag is no refusal.
 */
type OneAdapter<NA, NB> = [HeldTag<NA>] extends [never]
    ? false
    : [HeldTag<NB>] extends [never]
      ? false
      : Same<HeldTag<NA>, HeldTag<NB>>
/**
 * The tag of the adapter of a `held` node, as `[tag]`, or `never` where the node is no `held`. The
 * tag of a library adapter is its name. The tag of a caller's adapter is `['caller']`, and the
 * type cannot tell two of them apart, because the run time tells them apart by object identity.
 */
type HeldTag<N> = N extends [
    'held',
    unknown,
    unknown,
    unknown,
    [infer G, unknown],
    ...unknown[],
]
    ? [G]
    : never

/** The options of a factor: each option of the union node it names, or the factor itself. */
const meetOptions = (factor: AnyCodec): readonly AnyCodec[] => {
    const node = resolvedTerm(termOf(factor))
    if (node?.kind === 'ref') {
        throw new CodecError(
            `a factor of a meet names ref('${node.slot.name}'), which no scope binds yet — a meet reads the declared names at its declaration, so take the meet where the scope binds the name`,
        )
    }
    if (node?.kind !== 'union') return [factor]
    return node.options.map((option) =>
        codecOfTerm<never, AttributeValue>(option),
    )
}

/**
 * **The common literals of two literal sets under one adapter.** The model's `Codec.meet` is the
 * intersection of the two graphs, and one adapter relates one inner literal to one outer literal.
 * So the common pairs are the pairs of the common inner literals, and the held part stays. Two
 * adapters, or one adapter on one side only, give nothing: an opaque function decides which common
 * rows relate one value, so the caller refuses.
 */
const commonHeldLiterals = (a: Term, b: Term): readonly Term[] | undefined => {
    const A = resolvedTerm(a)
    const B = resolvedTerm(b)
    if (A?.kind !== 'held' || B?.kind !== 'held' || !sameAdapter(A, B)) {
        return undefined
    }
    const inner = commonLiterals(A.inner, B.inner)
    if (inner === undefined) return undefined
    const outer =
        clauseForm(A.outer) && clauseForm(B.outer)
            ? commonLiterals(A.outer, B.outer)
            : [A.outer]
    if (outer === undefined || inner.length === 0 || outer.length === 0) {
        return []
    }
    const [innerTerm, outerTerm] = [inner, outer].map((terms) =>
        termOf(codecOfTerms(terms)),
    )
    return innerTerm && outerTerm
        ? [{ ...A, inner: innerTerm, outer: outerTerm }]
        : undefined
}

/** The common literals of two pinned terms of one form, or nothing where the form differs. */
const commonLiterals = (a: Term, b: Term): readonly Term[] | undefined => {
    const left = clauseForm(a)
    const right = clauseForm(b)
    if (left === undefined || right === undefined) return undefined
    if (left.adapter !== undefined || right.adapter !== undefined) {
        return commonHeldLiterals(a, b)
    }
    if (left.alts.base !== right.alts.base) return []
    const node = resolvedTerm(a)
    const options = node?.kind === 'union' ? node.options : node ? [node] : []
    return options.filter((one) => {
        const value = clauseForm(one)?.alts.ls[0]
        return (
            value !== undefined &&
            right.alts.ls.some((tag: unknown) => sameLiteral(value, tag))
        )
    })
}

/** The codec of a list of terms of one base: `never`, the one term, or their union. */
const codecOfTerms = (terms: readonly Term[]): AnyCodec => {
    const [only] = terms
    if (only === undefined) return never
    return codecOfTerm(
        terms.length === 1 ? only : { kind: 'union', options: terms },
    )
}

/**
 * **The meet of two codecs that are neither a union nor `never`**, at the reading of each side: the
 * intersection of the two relations between stored rows and decoded values. Two sides that hold
 * one set of values at their readings meet at the left side. Two objects meet on their alignment,
 * and no order decides them, so {@link fits} is a consequence of the meet and no premise of it. Any
 * other pair meets by the order of the walk first: where one side lies below the other, the meet
 * is that side. Two lists then meet on their aligned rows, and two sets by element.
 *
 * **Two parts apart in one view meet at the bottom**, whatever adapter sits over them. The stored
 * views of the two parts share no attribute, or the caller views share no value: each view is a
 * projection of the relation, so the two relations share no pair.
 *
 * **A refinement reads through**, as the model's `rowSpecC` reads `refine`: the meet refines the
 * meet of its inner term with the other side by the same predicate. A pair of the meet is one row
 * and one value that both sides relate, so the predicate reads that value on either side, whatever
 * adapter the other side holds. A `held` or an older reading meets only a part that it lies below,
 * because an opaque function decides which common rows relate one value.
 */
const meetParts = (a: AnyCodec, b: AnyCodec, walk: MeetWalk): AnyCodec => {
    const A = resolvedTerm(termOf(a))
    const B = resolvedTerm(termOf(b))
    // a term resolves to nothing only for a cycle of refs alone, and `scope` refuses that cycle
    // (RecursionRefused) before a meet reads the term
    if (A === undefined || B === undefined) {
        throw new CodecError(
            'a factor of a meet names a cycle of refs with no node',
        )
    }
    const readA = readAs(A, walk.readings[0])
    const readB = readAs(B, walk.readings[1])
    const aBelow = below(readA, readB, walk.order)
    const bBelow = below(readB, readA, walk.order)
    // two sides that hold one set of values at their readings meet at either side, so the meet of
    // one term with itself ends, and the walk of a recursive term ends where the two sides agree
    if (aBelow && bBelow) return a
    if (A.kind === 'object' && B.kind === 'object') {
        return meetObjects(A, B, walk)
    }
    const common = commonLiterals(A, B)
    if (common !== undefined) return codecOfTerms(common)
    if (aBelow) return a
    if (bBelow) return b
    if (A.kind === 'list' && B.kind === 'list') return meetLists(A, B, walk)
    if (A.kind === 'set' && B.kind === 'set') {
        const elem = meetOfTwo(codecOfTerm(A.elem), codecOfTerm(B.elem), walk)
        const node = resolvedTerm(termOf(elem))
        return node?.kind === 'never'
            ? never
            : codecOfTerm({ kind: 'set', elem: termOf(elem) })
    }
    // two parts apart in the stored view or in the caller view share no pair, whatever adapter sits
    // over them: the meet is the bottom. Only a pair apart in neither view can need a function to
    // decide. The caller view reads each side at its reading, because an open side holds more values
    if (storedApart(A, B) || callerApart(readA, readB)) return never
    if (A.kind === 'refine') {
        return refined(A, () => meetOfTwo(codecOfTerm(A.inner), b, walk))
    }
    if (B.kind === 'refine') {
        return refined(B, () => meetOfTwo(a, codecOfTerm(B.inner), walk))
    }
    for (const one of [A, B]) {
        if (one.kind === 'held' || one.kind === 'legacy') {
            throw new CodecError(
                `[meet] a factor holds a \`${one.kind}\` part that fits neither side, and the two parts are apart in neither view. An opaque function decides which common rows relate one value: ${one.kind === 'held' ? 'the adapter of the part, a caller adapter or a library adapter such as `decimalText`' : 'the older reader of the part'}. The host cannot read the function. Meet only a part that one side fits`,
            )
        }
    }
    const left = memberOf(A)
    const right = memberOf(B)
    if (left !== undefined && right !== undefined && left !== right) {
        return never
    }
    if (A.kind !== B.kind) return never
    throw new CodecError(
        `[meet] no rule of the meet covers a \`${A.kind}\` against a \`${B.kind}\``,
    )
}

/**
 * The refinement `r` over the meet `inner` of its inner term with the other side, by the predicate
 * of `r`. `never` where the inner meet holds no value.
 */
const refined = (
    r: Extract<Term, { kind: 'refine' }>,
    inner: () => AnyCodec,
): AnyCodec => {
    const met = inner()
    return holdsNoValue(termOf(met))
        ? never
        : codecOfTerm({ kind: 'refine', inner: termOf(met), q: r.q })
}

/** A term at a reading: as declared, or its opening. */
const readAs = (t: Term, reading: MeetReading): Term =>
    reading === 'open' ? opened(t) : t

/**
 * **Two lists meet on their aligned rows**, the model's `alignedRows`. A side with no spread fixes
 * one length, and the meet is the row of each side at that length, met position by position. Two
 * spreading sides share each length from the longer declared part up. Below `hi`, the sum of the
 * longer prefix and the longer suffix, each common length is one fixed row. From `hi` up, each row
 * holds the meets of the row at `hi` at its ends and the meet of the two spreads between them: one
 * list term, the tail. A row with a position at `never` holds no value and drops. The meet is the
 * union of the rows that stay, and `never` where none stays.
 */
const meetLists = (
    A: Extract<Term, { kind: 'list' }>,
    B: Extract<Term, { kind: 'list' }>,
    walk: MeetWalk,
): AnyCodec => {
    const meetAt = (x: Term, y: Term): Term =>
        termOf(meetOfTwo(codecOfTerm(x), codecOfTerm(y), walk))
    const positions = (
        ls: readonly Term[],
        rs: readonly Term[],
    ): readonly Term[] | undefined => {
        const met = ls.flatMap((one, at) => {
            const there = rs[at]
            return there === undefined ? [] : [meetAt(one, there)]
        })
        return met.some((one) => holdsNoValue(one)) ? undefined : met
    }
    const rows = alignedRows(A.pre, A.spread, A.suf, B.pre, B.spread, B.suf)
    const hi =
        A.spread === undefined || B.spread === undefined
            ? Number.POSITIVE_INFINITY
            : Math.max(A.pre.length, B.pre.length) +
              Math.max(A.suf.length, B.suf.length)
    const terms: Term[] = rows.flatMap(([ls, rs]): Term[] => {
        if (ls.length >= hi) return []
        const pre = positions(ls, rs)
        return pre === undefined ? [] : [{ kind: 'list', pre, suf: [] }]
    })
    if (A.spread !== undefined && B.spread !== undefined) {
        const at = rows.find(([ls]) => ls.length === hi)
        const ends = at && positions(at[0], at[1])
        const split = Math.max(A.pre.length, B.pre.length)
        if (ends !== undefined) {
            terms.push({
                kind: 'list',
                pre: ends.slice(0, split),
                spread: meetAt(A.spread, B.spread),
                suf: ends.slice(split),
            })
        }
    }
    const [only] = terms
    if (only === undefined) return never
    return terms.length === 1
        ? codecOfTerm(only)
        : union(terms.map((one) => codecOfTerm(one)))
}

/**
 * **How a meet reads one side.** `written` reads the side as declared, so a closed object holds no
 * undeclared name. `open` reads the opening of the side: a closed object holds each undeclared name
 * at `opaque`, and a declared open block stays. The composition reads both sides open, as TypeScript
 * reads `A & B`. The order {@link fits} reads the option as written and the pattern open.
 */
type MeetReading = 'written' | 'open'

/** The reading of each side of a meet, the left side first. */
type MeetReadings = readonly [MeetReading, MeetReading]

/** Both sides as declared: the reading of {@link below}, whose pattern side is an opened term. */
const asWritten: MeetReadings = ['written', 'written']

/** The reading of the composition: both sides open, at the `relation` order. */
const asComposed: MeetReadings = ['open', 'open']

/** The reading of the order and of the overlap: the option as written, the pattern open. */
const asOrdered: MeetReadings = ['written', 'open']

/**
 * **The state of one meet**: the reading of each side, and the pairs of nodes on the path of the
 * walk, each with the slot of the `ref` that names the meet of the pair.
 */
type MeetWalk = {
    readonly readings: MeetReadings
    readonly order: Order
    readonly entered: Map<Term, Map<Term, RefSlot>>
}

const walkAt = (readings: MeetReadings, order: Order): MeetWalk => ({
    readings,
    order,
    entered: new Map(),
})

/** The term that admits every value: the open block of a closed object read open. */
const opaqueTerm: Term = { kind: 'opaq' }

/**
 * The open block of an object as a term, at a reading. A declared block stays. A closed object
 * holds the bottom as written and `opaque` read open.
 */
const blockOf = (body: Body, reading: MeetReading): Term =>
    body.rest ?? (reading === 'open' ? opaqueTerm : never.def)

/**
 * **The alignment of two objects**, as the model's `objK` aligns them: each name that either side
 * declares, with the slot of each side there. A side that does not declare the name holds it as an
 * optional slot at its open block, read at the reading of that side (`slotAtG` reads the written
 * side). The two blocks are the last pair, which the reader takes from {@link blockOf}.
 */
const aligned = (
    a: Body,
    b: Body,
    [left, right]: MeetReadings,
): readonly (readonly [string, Field, Field])[] => {
    const at = (body: Body, name: string, reading: MeetReading): Field =>
        own(body.fields, name) ?? {
            mark: 'optional',
            t: blockOf(body, reading),
        }
    return [
        ...new Set([...Object.keys(a.fields), ...Object.keys(b.fields)]),
    ].map((name): readonly [string, Field, Field] => [
        name,
        at(a, name, left),
        at(b, name, right),
    ])
}

/**
 * **Two slots at one name meet** at the meet of their codecs, and at the meet of their presence. The
 * presence of a slot is one element of the order of {@link absentBelow}, at the order of the walk,
 * so the meet is the greatest lower bound in that order: the mark of the side that lies below the
 * other, and `req` where neither side does. A slot that one side leaves undeclared is the open key
 * entry of that side, an optional slot at the block, as {@link aligned} gives it. An `opaque`
 * block meets at the codec of the other side, and the presence of the slot meets as any other.
 *
 * At the `relation` order two fills meet at a fill only where the fill values are one value
 * ({@link fillEquals}), as the model's `absentAgreeG` admits two fills only there. Two fills
 * with different fill values, and a fill beside an `optional` slot, share no pair at the absent row,
 * so the slot is required over the meet of the two codecs. At the `value` order a fill reads as a
 * required slot, so it lies below `optional` and the fill stays.
 *
 * A fill stays only where the meet of the two codecs writes the fill value. At the `value` order a
 * required slot of the pattern lies above the fill, and the meet can refuse the fill value, so the
 * slot is then required.
 *
 * `undefined` where a required slot meets at `never`, and the object holds no value.
 */
const meetSlots = (
    left: ObjectSlot | AnyCodec,
    right: ObjectSlot | AnyCodec,
    [mine, theirs]: readonly [Field, Field],
    walk: MeetWalk,
): ObjectSlot | undefined => {
    if (left === right) return left
    const held = meetOfTwo(entryCodec(left), entryCodec(right), walk)
    const lower = absentBelow(mine, theirs, walk.order)
        ? mine
        : absentBelow(theirs, mine, walk.order)
          ? theirs
          : undefined
    // a fill stays where the meet writes the fill value. Where the meet refuses the fill value, the
    // absent row has no pair in the meet, so the slot is required, as `fill` itself would refuse
    const below =
        lower?.mark === 'fill' &&
        unboundRefs([termOf(held)]).size === 0 &&
        fillRefusal(held, lower.v) !== undefined
            ? undefined
            : lower
    switch (below?.mark) {
        case 'fill':
            return fill(held, below.v as Decoded<typeof held>)
        case 'undefinable':
            return undefinable(held)
        case 'optional':
            return optional(held)
        default:
            return holdsNoValue(termOf(held)) ? undefined : held
    }
}

/**
 * **Two objects meet on their alignment**, each side at its reading. Each aligned pair meets, and
 * the two open blocks meet. The result is closed where both objects are closed, and where the two
 * blocks meet at `never`. A closed result holds no undeclared name, so a name that one side leaves
 * undeclared and that meets at `never` is no name of the result.
 */
const meetObjects = (
    A: Extract<Term, { kind: 'object' }>,
    B: Extract<Term, { kind: 'object' }>,
    walk: MeetWalk,
): AnyCodec => {
    const left = objectItem(A)
    const right = objectItem(B)
    const block =
        A.body.rest === undefined && B.body.rest === undefined
            ? undefined
            : meetOfTwo(
                  codecOfTerm(blockOf(A.body, walk.readings[0])),
                  codecOfTerm(blockOf(B.body, walk.readings[1])),
                  walk,
              )
    const rest =
        block === undefined || holdsNoValue(termOf(block)) ? undefined : block
    const spec: Record<string, ObjectSlot> = {}
    for (const [name, mine, theirs] of aligned(A.body, B.body, walk.readings)) {
        const declared = [
            Object.hasOwn(left.spec, name),
            Object.hasOwn(right.spec, name),
        ] as const
        const slot = meetSlots(
            own(left.spec, name) ?? codecOfTerm(mine.t),
            own(right.spec, name) ?? codecOfTerm(theirs.t),
            [mine, theirs],
            walk,
        )
        if (slot === undefined) return never
        // a closed result holds no name that no side declares and that holds no value. The rule reads
        // the slot and not its term: `undefinable` over `never` holds the absent row with the key set
        // to `undefined`, so the name stays, and only an `optional` slot over `never` drops
        if (
            rest === undefined &&
            !(declared[0] && declared[1]) &&
            holdsNoValue(fieldOf(slot).t) &&
            fieldOf(slot).mark === 'optional'
        )
            continue
        setOwn(spec, name, slot)
    }
    return objectFromMap(spec, rest)
}

/**
 * The binary meet at the reading of each side: `never` absorbs, `opaque` is the unit, a union
 * distributes, and the parts meet otherwise. Each rule reads the node behind each `ref`, as the
 * model reads the term, so a thunk changes no meet.
 */
const meetOfTwo = (
    first: AnyCodec,
    second: AnyCodec,
    walk: MeetWalk,
): AnyCodec => {
    if (holdsNoValue(termOf(first)) || holdsNoValue(termOf(second))) {
        return never
    }
    const A = resolvedTerm(termOf(first))
    const B = resolvedTerm(termOf(second))
    if (B?.kind === 'opaq') return first
    if (A?.kind === 'opaq') return second
    if (A === undefined || B === undefined) {
        return meetFactors(first, second, walk)
    }
    // **A pair on the path of the walk is a `ref` to its own meet.** The meet of two recursive terms
    // is recursive, so the walk meets the pair again. The `ref` binds the meet of the pair when the
    // walk of the pair returns, and closes the cycle there
    const entered = walk.entered.get(A) ?? new Map<Term, RefSlot>()
    const known = entered.get(B)
    if (known !== undefined) return codecOfTerm({ kind: 'ref', slot: known })
    const slot: RefSlot = { name: 'meet' }
    walk.entered.set(A, entered.set(B, slot))
    try {
        const met = meetFactors(first, second, walk)
        slot.bound = { [slot.name]: termOf(met) }
        return met
    } finally {
        entered.delete(B)
    }
}

/**
 * A union distributes, outer over the options of the first factor, and two parts meet. **A factor
 * that lies below the other is the meet**, at the readings of the walk, so the walk distributes a
 * union only where neither factor lies below the other. Two options of the distribution can
 * otherwise meet the other factor at two codecs that overlap, which no union holds.
 */
const meetFactors = (
    first: AnyCodec,
    second: AnyCodec,
    walk: MeetWalk,
): AnyCodec => {
    const lefts = meetOptions(first)
    const rights = meetOptions(second)
    if (lefts.length === 1 && rights.length === 1) {
        const [left] = lefts
        const [right] = rights
        if (left !== undefined && right !== undefined) {
            return meetParts(left, right, walk)
        }
    }
    const readFirst = readAs(termOf(first), walk.readings[0])
    const readSecond = readAs(termOf(second), walk.readings[1])
    if (below(readFirst, readSecond, walk.order)) return first
    if (below(readSecond, readFirst, walk.order)) return second
    const meets = lefts.flatMap((left) =>
        rights.flatMap((right) => {
            const one = meetOfTwo(left, right, walk)
            return resolvedTerm(termOf(one))?.kind === 'never' ? [] : [one]
        }),
    )
    // one meet needs no union around it; several are one flat union, built through `union`
    // itself so `agrees` runs over the meets
    const [only] = meets
    if (only === undefined) return never
    return meets.length === 1 ? only : union(meets)
}

/**
 * **The meet that reads the option as written and the pattern open.** The option `o` lies below the
 * pattern `p` ({@link fits}) exactly where this meet is `o`, up to a refinement and an older
 * reading, whose functions the host cannot read, and `o` overlaps `p` exactly where this meet holds
 * a value. A pattern has no decode of its own, so the walk reads the `value` order.
 */
export const meetOrdered = (option: AnyCodec, pattern: AnyCodec): AnyCodec =>
    meetOfTwo(option, pattern, walkAt(asOrdered, 'value'))

/**
 * **The meet of codecs: the values that every factor holds**, as TypeScript reads `A & B`.
 *
 * Each factor reads open: a closed object holds each undeclared name at `opaque`. So two objects
 * meet at the union of their names, a name that one factor declares keeps the slot of that factor,
 * and a shared name holds the meet of its two fields. The result closes again where both factors
 * are closed. The meet of two recursive factors is recursive, and a `ref` closes it.
 *
 * Two literal sets meet at their common literals, a base meets its own literal at the literal, and
 * two bases of different members meet at `never`. A list and a set meet by element, and a fixed list
 * meets position by position. A union distributes, outer over the first factor's options and inner
 * over the second: the `flatMap` order. `never` absorbs.
 *
 * **More than two factors fold left.** `meet(a, b, c)` is `meet(meet(a, b), c)`.
 *
 * @example
 * ```ts
 * meet(object({ petId: string }), object({ price: decimal }))
 * meet(union([object({ a: string }), object({ b: string })]), object({ n: boolean }))
 * ```
 */
export const meet = <const Fs extends readonly AnyCodec[]>(
    ...factors: Fs & ValidateMeet<Fs>
): FoldMeet<Fs> => {
    const [head, ...rest] = factors
    if (head === undefined || rest.length === 0) {
        throw new CodecError(
            'a meet is taken of two or more factors, and fewer were given',
        )
    }
    // one cast, where the run-time fold meets a type computed from the tuple of factors: the fold
    // returns `AnyCodec`, and `FoldMeet` is the same fold on the types, which the host cannot prove
    // equal. `tsc` refuses the line without the cast: `AnyCodec` is not assignable to `FoldMeet<Fs>`
    return rest.reduce(
        (met, factor) => meetOfTwo(met, factor, walkAt(asComposed, 'relation')),
        head,
    ) as FoldMeet<Fs>
}

/**
 * A builder for document paths into `T`.
 *
 * The builder behind `tableEntry(...).path()`. A table entry holds no codec to walk, so a path of
 * the entry is recorded from a selector and `at` takes no selector. {@link recordPath} stays for
 * this builder alone. The one cast reads the recorder, which takes any segment, as a type that
 * offers only the attributes of an entity.
 */
export const pathBuilder = <T, F = unknown>(): PathOf<T, F> =>
    recordPath([]) as PathOf<T, F>

/**
 * Records what a path expression walks through.
 *
 * Every hop returns a *new* recorder carrying its own segments, rather than pushing into a shared
 * array. Accumulating in place would be shorter and wrong: a selector that names an intermediate
 * node and reads more than one attribute off it — `const step = p.route.at(0); step.id; return
 * step.status` — would record both reads as one path. It also makes a recorder reusable, which is
 * what `path()` has always been.
 */
const recordPath = (steps: readonly Step[]): unknown =>
    new Proxy(nothing, { get: (_target, prop) => hop(steps, prop) })

/**
 * **A method of a path is also an attribute name.** DynamoDB admits an attribute named `at`, and
 * the path type offers it as a hop. So the hop to a method name is a recorder that is callable: read
 * as a property, it is the hop to the attribute; called, it is the method at the node before the
 * hop. Only these hops are callable, and their `then` is a plain hop, so no path is a thenable.
 */
const hop = (steps: readonly Step[], prop: string | symbol): unknown => {
    if (typeof prop !== 'string') return undefined
    // digits all the way through, or it is an attribute name: `parseInt` accepted a
    // leading number and dropped the rest, so `'1abc'` recorded `[NaN]`
    const next = [...steps, asIndex.test(prop) ? Number(prop) : prop]
    const method = methodAt(steps, prop)
    if (method === undefined) return recordPath(next)
    return new Proxy(method, {
        get: (_target, inner) => hop(next, inner),
    })
}

/** The method of a path that `name` names, at the node that `steps` reaches. */
const methodAt = (
    steps: readonly Step[],
    name: string,
): ((arg: never) => unknown) | undefined => {
    switch (name) {
        case 'toString':
            return () => asPath(segmentsIn(steps))
        case 'at':
            return (index: number | string) => recordPath([...steps, index])
        // an open name, selected by a method, as `at` selects a position
        case 'entry':
            return (key: string) => recordPath([...steps, key])
        // a clause narrows the frontier of `at`; the document path is unchanged
        case 'narrow':
            return (pattern: ClausePattern) =>
                recordPath([...steps, clauseOf(pattern)])
        default:
            return undefined
    }
}

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

export type Tagged<T, D extends string = keyof T & string, Spec = unknown> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
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
 */
const dissect = <T extends Record<string, unknown>>(
    ks: readonly string[],
    options: readonly (AnyObjectCodec | AnyCodec)[],
): DiscriminatedCodec<T, string, Record<string, unknown>> => {
    // **the empty key set, refused where the type cannot refuse it.** Over no discriminator every
    // value carries the empty assignment, so the first member answers for all of them and the
    // union is a union of one. The model carries no key set at all, so it never asks this; here
    // the key set is a `readonly string[]`, which cannot say it, and this is the gate
    if (ks.length === 0) {
        throw new CodecError(
            'a discriminated union needs at least one discriminator, and this one has none — every value carries the empty assignment, so the first variant would answer for all of them',
        )
    }
    // **An empty option list is a mistake, not the bottom.** `never` is the bottom and says so as
    // a term; a `dunion` over no variants is what a typo or a `map` over an empty array produces,
    // and it admits nothing while no rule reads it as admitting nothing. The type refuses this
    // too — what reaches here is a cast, plain JavaScript, or an erased path
    if (options.length === 0) {
        throw new CodecError(
            'a discriminated union needs at least one option, and this one has none — no tag reaches a variant, so nothing can be written or read. If a codec that admits no value is what you meant, that is \`never\`',
        )
    }
    // **Each option names an object node, read through its `ref`s.** An option that names a `ref`
    // that no scope binds is read by the scope, where the index reads the node of the closed copy
    for (const option of options) {
        const node = resolvedTerm(termOf(option as unknown as AnyCodec))
        if (node?.kind !== 'ref' && !(node && objectNamed(node))) {
            throw new CodecError(
                'every option must be an object codec, and one of them is not',
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

    keySets.set(unionDef, ks)
    // **A tag that a member reads through an unbound `ref` is indexed by the scope**, on the closed
    // copy, because the index reads the literal of each tag through the `ref`
    if (unboundRefs(memberTerms).size === 0)
        dissectionOf(unionDef, ks).resolution()
    const nested = codecOfTerm<T, Attribute<'M'>>(unionDef)
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
    } as unknown as DiscriminatedCodec<T, string, Record<string, unknown>>
}

/** The whole-item reading of a dissection, a function of the term and the key set. */
type Dissecting = { readonly self: Reading; readonly resolution: () => unknown }
const dissections = new WeakMap<Term, Dissecting>()

const dissectionOf = (
    unionDef: Extract<Term, { kind: 'union' }>,
    ks: readonly string[],
): Dissecting => {
    const built = dissections.get(unionDef)
    if (built) return built
    type T = Record<string, unknown>
    const memberTerms = unionDef.options
    // **every member's assignment, read off the member's own body, and no two alike.** Both rules
    // are the index's, not the union's: the one-key refusals `discriminatedUnion` used to spell
    // inline are these two at one key. The union's own gate does not replace them, because a
    // duplicated index key is a different fact from two members that are not disjoint, and the index is
    // what needs it.
    //
    // **A tag that a member reads through an unbound `ref` is indexed by the scope**, on the closed
    // copy, because the index reads the literal of each tag through the `ref`
    const index = () => {
        // a tag is written through its field only where a caller's adapter holds one: a plain
        // literal is its own stored text
        const callerMembers = new Map<unknown, Set<string>>()
        const written = (
            variant: ItemCodec<T, unknown>,
            patch: Readonly<Record<string, unknown>>,
            scope: 'member' | 'adapter',
        ) => {
            // the write of a tag reads `adapter`: it runs for a name that holds a caller's adapter in
            // this member, and for no other name, because a plain key of the member is its own
            // literal and no adapter refused it. The check of a member against its own value reads
            // `member`, the whole write of a member that holds an adapter at some key.
            const names = callerMembers.get(variant)
            return names &&
                (scope === 'member' ||
                    Object.keys(patch).every((name) => names.has(name)))
                ? variant.encodePartial(patch as never)
                : undefined
        }
        const members = membersOf(
            ks,
            memberTerms.map((term, at) => {
                const node = resolvedTerm(term)
                const item = node && objectNamed(node)
                if (node?.kind !== 'object' || !item) {
                    throw new CodecError(
                        `every option must be an object codec, and option ${at} is a \`${node?.kind}\``,
                    )
                }
                for (const name of ks) {
                    const field = own(node.body.fields, name)
                    if (field && isCallerPin(storedPin(field.t))) {
                        const names = callerMembers.get(item) ?? new Set()
                        callerMembers.set(item, names.add(name))
                    }
                }
                return [
                    node.body,
                    item as unknown as ItemCodec<T, unknown>,
                ] as const
            }),
            callerMembers.size > 0 ? written : undefined,
        )
        if (failed(members)) throw members
        const { pick, tagOf } = byTagSem(
            ks,
            members,
            callerMembers.size > 0 ? written : undefined,
        ) as unknown as {
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
        [itemMark]: true as const,
        encode: (item: T) =>
            openRefusal(unionDef) ??
            itemRefusal(item) ??
            andThen(andThen(tagOf(item), pick), (variant) =>
                variant.encode(item as never),
            ),
        encodePartial: (patch: Partial<T>) =>
            openRefusal(unionDef) ??
            itemRefusal(patch) ??
            andThen(andThen(tagOf(patch), pick), (variant) =>
                variant.encodePartial(patch as never),
            ),
        decode: (item: StoredItem) =>
            openRefusal(unionDef) ??
            itemRefusal(item) ??
            (andThen(andThen(readTags(item, ks), pick), (variant) =>
                variant.decode(item),
            ) as Result<T>),
        // the variant that the tags of an item select, read as `encode` reads them. The key layer
        // reads each variant through this one reader, so a tag under an adapter of a caller selects
        // the variant by the stored literal
        variantOf: (item: Partial<T>) =>
            openRefusal(unionDef) ?? andThen(tagOf(item), pick),
        // each variant, in the order of the options, for a key that no item names the variant of
        variants: () => resolution().members.map(([, variant]) => variant),
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
    const made = { self, resolution }
    dissections.set(unionDef, made)
    return made
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
    options: readonly AnyCodec[],
    pattern: unknown,
    keep: boolean,
): unknown => {
    const kept = picked(options, pattern, keep, false)
    return kept.length === 0 ? never : dissect(ks, kept)
}

// ── unions with no discriminator ────────────────────────────────────

/**
 * **Whether a term holds a literal that the type does not name exactly**: the value type is a
 * union, a template literal, a whole base, or a list that is no tuple, as `string(u)` gives for
 * `u: 'a' | 'b'`. A `binary` and a `dynamoNumber` with free text are the same case, because the
 * type of their value is the whole base. The constructor keeps such an argument. The value at run
 * time is one value, or the values of the list, and the type names a set that holds it. So the type
 * cannot say which alternative the term pins ({@link FitsCodec}). A union with an option that is no
 * literal is no literal term.
 */
type Inexact<T, Env = []> = Norm<T, Env> extends [infer N, infer E]
    ? N extends ['prim', ['literal', unknown, infer V]]
        ? InexactValue<V>
        : N extends ['union', infer Os extends unknown[]]
          ? InexactAll<{ [I in keyof Os]: OptionInexact<Os[I], E> }[number]>
          : N extends ['refine', infer I, ...unknown[]]
            ? Inexact<I, E>
            : [LibraryInner<N>] extends [never]
              ? false
              : Inexact<LibraryInner<N>, E>
    : false

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
type AnyTaggedCodec = Itemable<{
    readonly encode: (item: never) => unknown
    readonly decode: (item: StoredItem) => unknown
    readonly discriminator: string
}>

/** What a union writes: whatever the option it chose writes. */
export type WrittenBy<Options extends readonly unknown[]> = Extract<
    { [I in keyof Options]: AttributeOf<Options[I]> }[number],
    AttributeValue
>

/** The variants of an untagged union. There is no tag, so there is nothing to key them by. */
export type UntaggedSpec<T> = readonly ItemSpec<T>[]

export type Untagged<T, Specs extends readonly unknown[] = UntaggedSpec<T>> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
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

const optionOf = (
    t: Term,
): Option<ItemCodec<Record<string, unknown>, unknown>> => {
    /**
     * Read from the definition, not from the presence of a reading.
     *
     * A nested union has a reading too, and its `spec` is the *list* of its options rather than a
     * record of attributes — so testing for the reading classified a union as an object and then walked
     * that list as though `0` and `1` were attribute names. `attributes` is the definition of an
     * object codec and of nothing else.
     */
    const base = optionOfTerm(t)
    const asObject = readingOf(t)
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

/** The stored literals that a term names: a literal, or the options of a union of literals. */
type StoredLiterals<T> = T extends ['prim', ['literal', string, infer V]]
    ? V extends string
        ? V
        : never
    : T extends ['union', infer Os extends readonly unknown[]]
      ? StoredLiterals<Os[number]>
      : never

/**
 * The stored literals of a field under the adapter of a caller, which the inner term names, or
 * `never`. A library adapter is lawful by its own term: `number` reads its text as its value.
 */
type HeldStored<Field> = Field extends { readonly [termMarker]?: infer M }
    ? Unrefined<M> extends [
          'held',
          false,
          infer Inner,
          unknown,
          [['caller'], false],
          ...unknown[],
      ]
        ? StoredLiterals<Inner>
        : never
    : never

/** The term under each `refine` and each presence mark, as `pinOfG` reads it. */
type Unrefined<M> = M extends ['refine', infer I, ...unknown[]]
    ? Unrefined<I>
    : M extends ['optional' | 'undefinable' | 'fill', infer J]
      ? Unrefined<J>
      : M

/** Whether a field is under the adapter of a caller, through each `refine` and each presence mark. */
type CallerHeld<Field> = Field extends { readonly [termMarker]?: infer M }
    ? Unrefined<M> extends [
          'held',
          false,
          unknown,
          unknown,
          [['caller'], false],
          ...unknown[],
      ]
        ? true
        : false
    : false

/**
 * The text that a field of an entity prints in a key, where the entity holds `Value`. A field under
 * the adapter of a caller prints the stored text, which the caller's value does not give: the
 * literal of the inner term where the inner term pins one, and `string` where it pins none. Any
 * other field prints its value.
 *
 * An absent value stays absent: where `Value` holds `undefined` or `null`, so does the text.
 *
 * A key of one attribute reads this type too. That key holds the stored payload of an attribute
 * under the adapter of a caller, as the row does, because an entry that holds a value such as a
 * `Date` cannot be stored. A field with no adapter of a caller holds its value.
 */
export type KeyText<Value, Field> = [Field] extends [never]
    ? Value
    : true extends CallerHeld<Field>
      ?
            | ([HeldStored<Field>] extends [never] ? string : HeldStored<Field>)
            | Extract<Value, null | undefined>
      : Value

/**
 * The tag values a variant answers to — its discriminator's whole admissible set, not one value.
 * A tag is the stored literal on both sides, so a field under `held` answers to the literal of its
 * inner term, and the caller's value is written through the field to reach it.
 *
 * A variant may span several tags, and this codebase relies on it: a carrier declared
 * `carrierId: string('ACME', 'GLOBEX')` is *one* variant covering two stored values, which is why
 * {@link VariantOf} asks whether a tag is *among* a member's tags rather than equal to it.
 */
type TagsOf<Spec, D extends PropertyKey> = Spec extends unknown
    ? // distributed over the *variants*: the conditional below is on `Spec[D]`, so a union of specs
      // handed in whole would ask about a union of codecs and answer nothing
      D extends keyof Spec
        ? [HeldStored<Spec[D]>] extends [never]
            ? true extends CallerHeld<Spec[D]>
                ? // an adapter of a caller whose inner term pins no literal names no tag, and the run
                  // time refuses the codec at construction
                  never
                : Spec[D] extends AttributeCodec<infer Tag, AttributeValue>
                  ? // a tag is stored as `S` or as `N`, so a numeric enum indexes variants as readily as
                    // a string one — `readTag` reads either member and keys on the text it carries
                    Tag extends string | number
                      ? Tag
                      : never
                  : never
            : HeldStored<Spec[D]>
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
 *
 * **A tag is its text**, as the lookup keys it: `string('1')`, `number(1)` and `decimal('1')` each
 * answer to '1'. The type spells a number as a template does, so a number with an exponent form
 * differs from its stored text here.
 */
type DiffersSomewhere<A, B, Ks extends readonly PropertyKey[]> = true extends {
    [K in Ks[number]]: [`${TagsOf<A, K>}` & `${TagsOf<B, K>}`] extends [never]
        ? true
        : false
}[Ks[number]]
    ? true
    : false

/**
 * Whether two options decode one value at a key where they store two texts. The run time refuses
 * such a pair, because the write of the value reaches only one of the two stored texts. **The
 * narrowing:** the type states the overlap of the decoded tags, and it compares the values by
 * their types, so `1` and `'1'` are two values. The type does not state the lookup law of the
 * run time: that the write of each decoded value gives the text of its own option. A caller
 * adapter that does not write its own literal stays a refusal at construction. The narrowing has a
 * second direction: the type refuses a pair that the run time admits. The overlap reads the
 * decoded type of the adapter, so an adapter whose decoded type is wider than the values that its
 * schema admits overlaps every tag of that type, and the pair is refused.
 */
type DecodesTogether<A, B, Ks extends readonly PropertyKey[]> = true extends {
    [K in Ks[number]]: [DecodedTags<A, K> & DecodedTags<B, K>] extends [never]
        ? false
        : [`${TagsOf<A, K>}` & `${TagsOf<B, K>}`] extends [never]
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
                ? DecodesTogether<Head, Next, Ks> extends true
                    ? `options ${At} and ${Cursor['length']}`
                    : never
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
 * `extract(codec, pattern)` keeps the options that fit the pattern, and `exclude` keeps the rest.
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
 * codec nests: `pet: extract(pet, object({ status: string('AVAILABLE') }))`.
 */
type PatternSpecs<P> = P extends unknown
    ? [OptionsOfCodec<P>] extends [never]
        ? FieldSpecList<P>[number]
        : PatternSpecs<OptionsOfCodec<P>[number]>
    : never
type OptionsOfCodec<P> = P extends UnionCodec<
    infer _T,
    infer Os extends readonly unknown[],
    infer _Tm
>
    ? Os
    : never

/** The member specs of the codec at a field: each option of a union of objects, or the object itself. */
type FieldSpecList<F> = F extends Declares<infer Sp>
    ? Sp extends readonly unknown[]
        ? Sp
        : [Sp]
    : never

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
type SplitSpec<Spec, PU> = SplitKeys<[Spec], KeyTuple<UnionKeys<PU>>, PU>
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

/**
 * The most parts that the fit reads from one term, as a tuple of that length ({@link JoinParts}).
 * The run time bounds the parts at 1024 ({@link PARTS_LIMIT}), and the type bounds them at 64. A
 * term whose parts reach the bound has the fit `'u'`, so the slice keeps the option.
 */
type PartsCap = Repeat<64>
type Repeat<
    N extends number,
    T extends readonly unknown[] = [],
> = T['length'] extends N ? T : Repeat<N, [...T, unknown]>

/** The options split at the keys of a pattern. An option that is no object stays whole. */
type SplitOptions<
    Options extends readonly unknown[],
    P,
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...(Head extends Declares<infer Sp>
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
 * **Whether a codec fits a pattern**, as the run time decides it, read on the terms that the codecs
 * carry. `'t'` fits, `'f'` does not, and `'u'` is where the type cannot decide: the extraction and
 * the exclusion each keep such an option, so each result type admits every option that the run time
 * keeps.
 *
 * The fit is {@link BelowT}, rule for rule the order `below` of the run time at the `value` order,
 * with the pattern open at every object ({@link opened}). A rule that reads a fact that the type
 * lacks answers `'u'`: a `ref` that no scope binds, a caller's adapter against a caller's adapter,
 * a literal whose value type is not one value ({@link Inexact}), a term that two readings of one
 * term decide differently, and a term whose parts pass the bound ({@link PartsCap}).
 */
type Fit = 't' | 'f' | 'u'
type FitsCodec<A, P> = BelowT<
    TermOf<Marks<A>>,
    OpenT<TermOf<Marks<P>>>,
    [],
    [],
    []
>
/** The most pairs that the walk of {@link BelowT} enters on one path, as a tuple of that length. */
type BelowDepth = Repeat<16>
/**
 * **The order `below` of the run time on terms**, three-valued. `A` is the term of the option and
 * `P` the term of the pattern, each under its own scope (`EA`, `EP`). `Seen` holds the pairs that the
 * walk entered at a name step on the path, and such a pair is below, as the order is the greatest
 * fixed point of its rules. The caller opens the pattern with {@link OpenT}, as the run time opens it.
 */
type BelowT<A, P, EA, EP, Seen extends readonly unknown[]> = [
    Norm<A, EA>,
    Norm<P, EP>,
] extends [[infer NA, infer EA2], [infer NP, infer EP2]]
    ? [IsRef<A>, IsRef<P>] extends [false, false]
        ? BelowStep<NA, NP, EA2, EP2, Seen>
        : SeenPair<Seen, RefKey<A, NA, EA2>, RefKey<P, NP, EP2>> extends true
          ? 't'
          : Seen extends BelowDepth
            ? 'u'
            : BelowStep<
                  NA,
                  NP,
                  EA2,
                  EP2,
                  [[RefKey<A, NA, EA2>, RefKey<P, NP, EP2>], ...Seen]
              >
    : 'u'
/** Whether a term is a name that `Norm` resolves: a `ref`, or an entry of a scope. */
type IsRef<T> = T extends ['ref', unknown] | ['scope', unknown, unknown]
    ? true
    : false
/**
 * The key of a node in `Seen`: the name as written with the scope that it resolved under, or the
 * node where the term is no name. A cycle passes through a name, so the walk records a pair at a
 * name step only, and two names compare by their text and scope, not by the terms that they resolve
 * to.
 */
type RefKey<T, N, E> = IsRef<T> extends true ? [T, E] : N
/**
 * The rules at two nodes, and `'u'` for the pair of one term where the rules give `'f'`. The run
 * time answers `true` for one object, so two codecs built apart read by the rules, and the same
 * codec reads `true`. The type cannot tell the two cases apart.
 */
type BelowStep<NA, NP, EA, EP, Seen extends readonly unknown[]> = BelowN<
    NA,
    NP,
    EA,
    EP,
    Seen
> extends 'f'
    ? Same<NA, NP> extends true
        ? 'u'
        : 'f'
    : BelowN<NA, NP, EA, EP, Seen>
/** Whether the pair is on the path. */
type SeenPair<Seen extends readonly unknown[], A, P> = Seen extends readonly [
    [infer SA, infer SP],
    ...infer Rest extends readonly unknown[],
]
    ? Same<SA, A> extends true
        ? Same<SP, P> extends true
            ? true
            : SeenPair<Rest, A, P>
        : SeenPair<Rest, A, P>
    : false
/** The rules of {@link BelowT} at two nodes. */
type BelowN<A, P, EA, EP, Seen extends readonly unknown[]> = HoldsNoValue<
    A,
    EA
> extends true
    ? 't'
    : P extends ['opaq']
      ? 't'
      : A extends ['ref', unknown]
        ? 'u'
        : P extends ['ref', unknown]
          ? 'u'
          : A extends ['union', infer Os extends unknown[]]
            ? AllOf<
                  {
                      [I in keyof Os]: BelowT<Os[I], P, EA, EP, Seen>
                  }[number]
              >
            : P extends ['union', infer Ps extends unknown[]]
              ? JoinParts<A, PatternNodes<Ps, EP>, EP> extends infer Parts
                  ? Parts extends readonly unknown[]
                      ? AllOf<
                            {
                                [I in keyof Parts]: SomeOf<
                                    {
                                        [J in keyof Ps]: BelowT<
                                            Parts[I],
                                            Ps[J],
                                            EA,
                                            EP,
                                            Seen
                                        >
                                    }[number]
                                >
                            }[number]
                        >
                      : 'u'
                  : 'u'
              : A extends ['refine', infer I, ...unknown[]]
                ? BelowT<I, P, EA, EP, Seen>
                : P extends ['legacy', infer I]
                  ? A extends ['legacy', infer AI]
                      ? SomeOf<
                            | ([BelowT<AI, I, EA, EP, Seen>] extends ['f']
                                  ? 'f'
                                  : 'u')
                            | BelowT<A, I, EA, EP, Seen>
                        >
                      : BelowT<A, I, EA, EP, Seen>
                  : [ClauseOf<P>] extends [never]
                    ? BelowShape<A, P, EA, EP, Seen>
                    : BelowClause<A, P>
type SomeOf<U extends Fit> = 't' extends U ? 't' : 'u' extends U ? 'u' : 'f'
type AllOf<U extends Fit> = 'f' extends U ? 'f' : 'u' extends U ? 'u' : 't'
/**
 * **The form that a literal names**, as {@link clauseForm} reads it: the adapters that it sits
 * under and the base and value of the literal, or `never`. An adapter whose held side is `opaque`
 * names no form.
 */
type ClauseOf<N, Tags extends readonly unknown[] = []> = N extends [
    'prim',
    ['literal', infer K, infer V],
]
    ? ['form', Tags, K, V]
    : N extends [
            'held',
            unknown,
            infer I,
            infer O,
            [infer G, unknown],
            ...unknown[],
        ]
      ? [NodeOf<O>] extends [['opaq']]
          ? never
          : ClauseOf<NodeOf<I>, [...Tags, G]>
      : never
/**
 * A literal against the literal of the pattern: the two forms are one form, and each value is a
 * value of the pattern. A literal whose value type is not one value is `'u'`, or `'f'` where the
 * two value types are disjoint ({@link Inexact}).
 */
type BelowClause<A, P> = ClauseOf<A> extends [
    'form',
    infer AT,
    infer AK,
    infer AV,
]
    ? ClauseOf<P> extends ['form', infer PT, infer PK, infer PV]
        ? SameTags<AT, PT> extends 'f'
            ? 'f'
            : Same<AK, PK> extends true
              ? SameTags<AT, PT> extends 'u'
                  ? 'u'
                  : true extends InexactValue<AV> | InexactValue<PV>
                    ? [AV & PV] extends [never]
                        ? 'f'
                        : 'u'
                    : [AV] extends [PV]
                      ? 't'
                      : 'f'
              : 'f'
        : 'f'
    : 'f'
/** `'f'` where two chains of adapter tags differ, `'u'` where a caller's adapter meets one, else `'t'`. */
type SameTags<A, B> = Same<A, B> extends true
    ? [A] extends [readonly []]
        ? 't'
        : true extends (
                A extends readonly (infer G)[]
                    ? [G] extends [['caller']]
                        ? true
                        : false
                    : false
            )
          ? 'u'
          : 't'
    : 'f'
/** The rules at a pattern that is no literal. */
type BelowShape<A, P, EA, EP, Seen extends readonly unknown[]> = P extends [
    'object',
    ['mk', infer PF, infer PW],
]
    ? A extends ['object', ['mk', infer AF, infer AW]]
        ? AllOf<
              | {
                    [K in keyof AF | keyof PF]: BelowSlot<
                        SlotAt<AF, AW, K>,
                        SlotAt<PF, PW, K>,
                        EA,
                        EP,
                        Seen
                    >
                }[keyof AF | keyof PF]
              | BelowT<Block<AW>, Block<PW>, EA, EP, Seen>
          >
        : 'f'
    : P extends [
            'list',
            infer PP extends unknown[],
            infer PS,
            infer PU extends unknown[],
        ]
      ? A extends [
            'list',
            infer AP extends unknown[],
            infer AS,
            infer AU extends unknown[],
        ]
          ? BelowList<AP, AS, AU, PP, PS, PU, EA, EP, Seen>
          : 'f'
      : P extends [
              'held',
              unknown,
              infer PI,
              unknown,
              [infer PG, unknown],
              ...unknown[],
          ]
        ? A extends [
              'held',
              unknown,
              infer AI,
              unknown,
              [infer AG, unknown],
              ...unknown[],
          ]
            ? Same<AG, PG> extends true
                ? [AG] extends [['caller']]
                    ? 'u'
                    : BelowT<AI, PI, EA, EP, Seen>
                : 'f'
            : 'f'
        : P extends ['set', infer PE]
          ? A extends ['set', infer AE]
              ? BelowT<AE, PE, EA, EP, Seen>
              : 'f'
          : A extends ['prim', ['literal', infer K, unknown]]
            ? P extends ['prim', ['base', K]]
                ? 't'
                : 'f'
            : A extends ['prim', ['base', infer K]]
              ? P extends ['prim', ['base', K]]
                  ? 't'
                  : 'f'
              : 'f'
/**
 * The slot of the option against the slot of the pattern: the absent row, then the term. At the
 * `value` order a fill value counts no absent row, so a `fill` slot reads as a required one.
 * `undefinable` pairs the absent row with `{ k: undefined }`, which `optional` reads as `{}`.
 */
type BelowSlot<M, W, EA, EP, Seen extends readonly unknown[]> = [M, W] extends [
    [infer MM extends string, infer MT],
    [infer WM extends string, infer WT],
]
    ? AllOf<
          | AbsentBelow<
                MM extends 'fill' ? 'req' : MM,
                WM extends 'fill' ? 'req' : WM
            >
          | BelowT<MT, WT, EA, EP, Seen>
      >
    : 'u'
/** The presence mark of a field, where a fill value counts as required at the `value` order. */
type SlotMarkOf<F> = SlotOf<F> extends [infer M extends string, unknown]
    ? M extends 'fill'
        ? 'req'
        : M
    : never
type AbsentBelow<M extends string, W extends string> = W extends 'req'
    ? M extends 'req'
        ? 't'
        : 'f'
    : W extends 'undefinable'
      ? M extends 'req' | 'undefinable'
          ? 't'
          : 'f'
      : 't'
/**
 * A list against a list pattern: a pattern of one element holds every list whose positions each fit
 * the element. Any other pattern is a product of positions: the same layout, and each position
 * inside the pattern's.
 */
type BelowList<
    AP extends unknown[],
    AS,
    AU extends unknown[],
    PP extends unknown[],
    PS,
    PU extends unknown[],
    EA,
    EP,
    Seen extends readonly unknown[],
> = [PS, PP, PU] extends [['some', infer E], [], []]
    ? AllOf<
          | { [I in keyof AP]: BelowT<AP[I], E, EA, EP, Seen> }[number]
          | (AS extends ['some', infer S] ? BelowT<S, E, EA, EP, Seen> : never)
          | { [I in keyof AU]: BelowT<AU[I], E, EA, EP, Seen> }[number]
      >
    : AP['length'] extends PP['length']
      ? AU['length'] extends PU['length']
          ? [AS extends ['some', unknown] ? true : false] extends [
                PS extends ['some', unknown] ? true : false,
            ]
              ? AllOf<
                    | {
                          [I in keyof AP]: I extends keyof PP
                              ? BelowT<AP[I], PP[I], EA, EP, Seen>
                              : 'f'
                      }[number]
                    | {
                          [I in keyof AU]: I extends keyof PU
                              ? BelowT<AU[I], PU[I], EA, EP, Seen>
                              : 'f'
                      }[number]
                    | (AS extends ['some', infer S]
                          ? PS extends ['some', infer E2]
                              ? BelowT<S, E2, EA, EP, Seen>
                              : 'f'
                          : never)
                >
              : 'f'
          : 'f'
      : 'f'
/** The nodes that the options of a pattern union name, each union read through. */
type PatternNodes<Ps extends readonly unknown[], EP> = {
    [I in keyof Ps]: Norm<Ps[I], EP> extends [infer N, infer E]
        ? N extends ['union', infer Os extends readonly unknown[]]
            ? PatternNodes<Os, E>
            : N
        : never
}[number]
/**
 * **The parts of the normal form of a term in the value order**, as {@link joinParts} builds them,
 * split at the names that the pattern options declare: `boolean` is `true` and `false`, a union
 * flattens, an object is the product of the parts of its fields, and a list is the product of the
 * parts of its positions. A field that may be absent splits as {@link presenceParts} splits it
 * ({@link PresenceSlots}). A split at a name that no option declares changes no fit, because the
 * pattern is open there. `'over'` where the parts pass {@link PartsCap}.
 */
type JoinParts<A, Ps, EP> = A extends [
    'union',
    infer Os extends readonly unknown[],
]
    ? FlatParts<Os, Ps, EP>
    : A extends ['prim', ['base', 'boolean']]
      ? [
            ['prim', ['literal', 'boolean', true]],
            ['prim', ['literal', 'boolean', false]],
        ]
      : A extends ['object', ['mk', infer F, infer W]]
        ? ObjectParts<
              F,
              W,
              KeyTuple<
                  Ps extends ['object', ['mk', infer PF, unknown]]
                      ? keyof PF
                      : never
              >,
              Ps,
              EP,
              [Record<never, never>]
          >
        : A extends [
                'list',
                infer Pre extends readonly unknown[],
                infer Sp,
                infer Suf extends readonly unknown[],
            ]
          ? ListParts<Pre, Sp, Suf, PatternElems<Ps, EP>, EP>
          : [A]
type FlatParts<Os extends readonly unknown[], Ps, EP> = Os extends readonly [
    infer H,
    ...infer R extends readonly unknown[],
]
    ? JoinParts<H, Ps, EP> extends infer HP extends readonly unknown[]
        ? FlatParts<R, Ps, EP> extends infer RP extends readonly unknown[]
            ? Capped<[...HP, ...RP]>
            : 'over'
        : 'over'
    : []
type Capped<T extends readonly unknown[]> = T extends readonly [
    ...PartsCap,
    ...unknown[],
]
    ? 'over'
    : T
type ObjectParts<
    F,
    W,
    Keys extends readonly unknown[],
    Ps,
    EP,
    Rows extends readonly unknown[],
> = Keys extends readonly [infer K, ...infer Rest extends readonly unknown[]]
    ? K extends keyof F
        ? F[K] extends [infer M, infer T]
            ? JoinParts<
                  T,
                  PatternSlotNodes<Ps, K, EP>,
                  EP
              > extends infer Parts extends readonly unknown[]
                ? Capped<
                      CrossFields<Rows, K, PresenceSlots<M, Parts>>
                  > extends infer Next extends readonly unknown[]
                    ? ObjectParts<F, W, Rest, Ps, EP, Next>
                    : 'over'
                : 'over'
            : ObjectParts<F, W, Rest, Ps, EP, Rows>
        : ObjectParts<F, W, Rest, Ps, EP, Rows>
    : {
          [I in keyof Rows]: [
              'object',
              ['mk', Omit<F, keyof Rows[I]> & Rows[I], W],
          ]
      }
type CrossFields<
    Rows extends readonly unknown[],
    K,
    Slots extends readonly unknown[],
> = Rows extends readonly [infer Row, ...infer Rest extends readonly unknown[]]
    ? [
          ...{ [I in keyof Slots]: Row & { [P in K & string]: Slots[I] } },
          ...CrossFields<Rest, K, Slots>,
      ]
    : []

/**
 * The slots of a field that {@link presenceParts} gives, at the type level: `optional` and
 * `undefinable` give the absent row, a slot of the same mark over `never`, then the present parts
 * as required slots. Any other mark keeps its mark over each part.
 */
type PresenceSlots<M, Parts extends readonly unknown[]> = M extends
    | 'optional'
    | 'undefinable'
    ? [[M, ['never']], ...{ [I in keyof Parts]: ['req', Parts[I]] }]
    : { [I in keyof Parts]: [M, Parts[I]] }
/** The nodes at the name `K` in the slots of the object options. */
type PatternSlotNodes<Ps, K, EP> = Ps extends [
    'object',
    ['mk', infer F, unknown],
]
    ? K extends keyof F
        ? F[K] extends [unknown, infer T]
            ? PatternNodes<[T], EP>
            : never
        : never
    : never
/** The nodes of each position of the list options of the pattern, and of their spreads. */
type PatternElems<Ps, EP> = Ps extends [
    'list',
    infer Pre extends readonly unknown[],
    infer Sp,
    infer Suf extends readonly unknown[],
]
    ? PatternNodes<
          [...Pre, ...(Sp extends ['some', infer E] ? [E] : []), ...Suf],
          EP
      >
    : never
type ListParts<
    Pre extends readonly unknown[],
    Sp,
    Suf extends readonly unknown[],
    Ps,
    EP,
> = PositionRows<Pre, Ps, EP, [[]]> extends infer PreRows extends
    readonly unknown[]
    ? PositionRows<Suf, Ps, EP, [[]]> extends infer SufRows extends
          readonly unknown[]
        ? Capped<CrossLists<PreRows, SufRows, Sp>>
        : 'over'
    : 'over'
type PositionRows<
    Items extends readonly unknown[],
    Ps,
    EP,
    Rows extends readonly unknown[],
> = Items extends readonly [infer H, ...infer R extends readonly unknown[]]
    ? JoinParts<H, Ps, EP> extends infer Parts extends readonly unknown[]
        ? Capped<CrossRows<Rows, Parts>> extends infer Next extends
              readonly unknown[]
            ? PositionRows<R, Ps, EP, Next>
            : 'over'
        : 'over'
    : Rows
type CrossRows<
    Rows extends readonly unknown[],
    Parts extends readonly unknown[],
> = Rows extends readonly [
    infer Row extends readonly unknown[],
    ...infer Rest extends readonly unknown[],
]
    ? [...{ [I in keyof Parts]: [...Row, Parts[I]] }, ...CrossRows<Rest, Parts>]
    : []
type CrossLists<
    PreRows extends readonly unknown[],
    SufRows extends readonly unknown[],
    Sp,
> = PreRows extends readonly [
    infer Pre,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...{ [I in keyof SufRows]: ['list', Pre, Sp, SufRows[I]] },
          ...CrossLists<Rest, SufRows, Sp>,
      ]
    : []

type SpecTerm<S> = ObjectTermOf<S, undefined>
/** The term of the member specs of a pattern: one object, or the union of the objects. */
type SpecsTerm<P> = true extends IsUnion<P>
    ? ['union', SpecTerms<KeyTuple<P>>]
    : SpecTerm<P>
type SpecTerms<Ps extends readonly unknown[]> = {
    [I in keyof Ps]: SpecTerm<Ps[I]>
}
/** Whether a member spec fits the member specs of a pattern: the fit of the closed object at the opened pattern. */
type EveryFits<A, P> = BelowT<SpecTerm<A>, OpenT<SpecsTerm<P>>, [], [], []>
/** Whether a member spec fits a pattern codec: the pattern must hold objects. */
type FitsSpec<A, P> = BelowT<SpecTerm<A>, OpenT<TermOf<Marks<P>>>, [], [], []>
/** Whether two codecs hold lists with fixed positions. */
type HasFixed<A, P> = [FixedElements<A>] extends [never]
    ? false
    : [FixedElements<P>] extends [never]
      ? false
      : true

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
 * pattern names, and the parts that fit stay. An option whose parts all fit stays whole, because
 * the fit reads the parts of the normal form ({@link BelowT}). `Keep` is `true` for the
 * extraction and `false` for the exclusion, so the two are one walk and the complement cannot
 * drift from the selection.
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

/**
 * Whether a field splits at presence: the pattern refuses the absent row of the field, which
 * {@link AbsentBelow} decides on the marks. A required field, and a fill value at the `value` order,
 * hold no absent row.
 */
type SplitsAtPresence<A, P> = AbsentBelow<
    SlotMarkOf<A>,
    SlotMarkOf<P>
> extends 'f'
    ? true
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
        : EveryFits<Head, PK[number]> extends 'u'
          ? SliceSummands<Tail, PK, [...Keep, Head], [...Rest, Head]>
          : CoverSummand<Head, PK> extends {
                  keep: infer K extends readonly unknown[]
                  rest: infer R extends readonly unknown[]
              }
            ? SliceSummands<Tail, PK, [...Keep, ...K], [...Rest, ...R]>
            : never
    : { keep: Keep; rest: Rest }

/**
 * One summand against the member specs of the pattern at its field. Each member covers what the
 * earlier members left, as {@link coverOf} does at run time, so one member is the case of one object.
 */
type CoverSummand<
    Head,
    Members extends readonly unknown[],
    Keep extends readonly unknown[] = [],
    Rest extends readonly unknown[] = [Head],
> = Members extends readonly [infer M, ...infer Tail extends readonly unknown[]]
    ? CoverPieces<Rest, M> extends {
          keep: infer K extends readonly unknown[]
          rest: infer R extends readonly unknown[]
      }
        ? CoverSummand<Head, Tail, [...Keep, ...K], R>
        : never
    : { keep: Keep; rest: Rest }
type CoverPieces<
    Pieces extends readonly unknown[],
    M,
    Keep extends readonly unknown[] = [],
    Rest extends readonly unknown[] = [],
> = Pieces extends readonly [
    infer Piece,
    ...infer Tail extends readonly unknown[],
]
    ? SliceSpecOf<Piece, M> extends {
          keep: infer K extends readonly unknown[]
          rest: infer R extends readonly unknown[]
      }
        ? CoverPieces<Tail, M, [...Keep, ...K], [...Rest, ...R]>
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
                  : HasFixed<S[K], PS[K]> extends true
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
            : AbsentBelow<'optional', SlotMarkOf<PS[K]>> extends 't'
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
          TermMark<['undefinable', TermOf<C>]>
    : OptionalCodec<Decoded<C>, AttributeOf<C>, C> &
          TermMark<['optional', TermOf<C>]>

/** The slot that holds the kept summands: the declared slot where they are all of them, else their union. */
type FieldOf<
    L extends readonly unknown[],
    Orig extends readonly unknown[],
    Slot,
> = true extends Same<L, Orig>
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
 * **The option codecs that a pattern keeps**, in the order they were declared. `Keep` is `true` for
 * the extraction and `false` for the exclusion.
 *
 * **The slice goes into the field and the result stays compact.** An option `{ k, pet: U }` against
 * the pattern `{ pet: P }` is `{ k, pet: Extract<U, P> }`, one option with a narrower union, as
 * TypeScript's `Extract` reads it. So the extraction has one option for each option that it keeps,
 * and no more, which is what the model's slice of a union states. The exclusion has one option for
 * each split key, because the complement of a product is no product. A union pattern of objects
 * reads member by member ({@link KeptWhole}), as the run time does. A union pattern with a member
 * that is no object keeps the split ({@link KeptSplit}), and so does a pattern that holds no object.
 */
export type KeptOptions<
    Options extends readonly unknown[],
    P,
    Keep extends boolean = true,
> = [OptionsOfCodec<P>] extends [never]
    ? [FieldSpecList<P>] extends [never]
        ? KeptSplit<Options, P, Keep>
        : KeptCompact<Options, P, Keep>
    : ObjectMembers<OptionsOfCodec<P>> extends infer Os extends
            readonly unknown[]
      ? Os extends readonly []
          ? KeptSplit<Options, P, Keep>
          : KeptWhole<Options, P, Os, Keep>
      : never
/**
 * The object members of a union pattern, read through nested unions. A member that is no object
 * holds no part of an object option, so the cover reads the object members only.
 */
type ObjectMembers<Ms extends readonly unknown[]> = Ms extends readonly [
    infer M,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...([OptionsOfCodec<M>] extends [never]
              ? M extends Declares<infer Sp>
                  ? Sp extends readonly unknown[]
                      ? []
                      : [M]
                  : []
              : ObjectMembers<OptionsOfCodec<M>>),
          ...ObjectMembers<Rest>,
      ]
    : []
/**
 * An option against a union pattern of objects. An option that the whole pattern holds stays whole
 * or goes whole. Past the bound of {@link FitsCodec} the fit is unknown, and the option splits as
 * {@link KeptSplit} splits it. Otherwise each member of the pattern covers what the earlier members
 * left, as {@link coverOf} does at run time.
 */
type KeptWhole<
    Options extends readonly unknown[],
    P,
    Members extends readonly unknown[],
    Keep extends boolean,
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...(FitsCodec<Head, P> extends 't'
              ? Keep extends true
                  ? [Head]
                  : []
              : OverCap<Head, P> extends true
                ? KeptSplit<[Head], P, Keep>
                : KeptFold<[Head], Members, Keep>),
          ...KeptWhole<Rest, P, Members, Keep>,
      ]
    : []
/** Whether the parts of the option, split at the members of the union pattern, pass {@link PartsCap}. */
type OverCap<A, P> = [
    Norm<TermOf<Marks<A>>, []>,
    Norm<OpenT<TermOf<Marks<P>>>, []>,
] extends [
    [infer NA, unknown],
    [['union', infer Ps extends unknown[]], infer EP],
]
    ? JoinParts<NA, PatternNodes<Ps, EP>, EP> extends 'over'
        ? true
        : false
    : false
type KeptFold<
    Options extends readonly unknown[],
    Members extends readonly unknown[],
    Keep extends boolean,
> = Members extends readonly [infer M, ...infer Rest extends readonly unknown[]]
    ? Keep extends true
        ? [
              ...KeptCompact<Options, M, true>,
              ...KeptFold<KeptCompact<Options, M, false>, Rest, true>,
          ]
        : KeptFold<KeptCompact<Options, M, false>, Rest, false>
    : Keep extends true
      ? []
      : Options
type KeptCompact<
    Options extends readonly unknown[],
    P,
    Keep extends boolean,
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [
          ...(Head extends Declares<infer Sp>
              ? Sp extends readonly unknown[]
                  ? KeepsFit<Keep, FitsCodec<Head, P>> extends true
                      ? [Head]
                      : []
                  : FitsCodec<Head, P> extends 't'
                    ? Keep extends true
                        ? [Head]
                        : []
                    : SliceSpecOf<Sp, PatternSpecs<P>> extends infer Sl extends
                            {
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

/** The rests of the members that {@link Extracted} keeps, in step with the specs. */
export type ExtractedRests<
    Specs extends readonly unknown[],
    Rests extends readonly unknown[],
    P,
    Keep extends boolean = true,
> = Specs extends readonly [
    infer Head,
    ...infer Tail extends readonly unknown[],
]
    ? Rests extends readonly [
          infer RestHead,
          ...infer RestTail extends readonly unknown[],
      ]
        ? [
              ...(KeepsFit<Keep, FitsSpec<Head, P>> extends true
                  ? [RestHead]
                  : []),
              ...ExtractedRests<Tail, RestTail, P, Keep>,
          ]
        : []
    : []

/**
 * The entity of the members that a tag table keeps, read off the entity of the whole union, so a
 * member keeps the rest that it declares.
 */
type KeptVariants<T, D, Kept> = {
    [K in keyof Kept]: VariantOf<T, D & keyof T, DecodedTags<Kept[K], D>>
}[keyof Kept]

/** The members of a tag table a pattern keeps, keyed as they were. */
export type KeptByTag<Spec, P, Keep extends boolean = true> = {
    [K in keyof Spec as KeepsFit<Keep, FitsSpec<Spec[K], P>> extends true
        ? K
        : never]: Spec[K]
}

/** The entity a tag table describes, which is what its members describe. */
export type VariantsOf<Spec> = {
    [K in keyof Spec]: show<ObjectOf<Spec[K]>>
}[keyof Spec]

/**
 * A key of a pattern that holds a refinement, at any depth: no function decides whether a member
 * lies inside a predicate. A pattern that no member fits is an answer, and the result keeps nothing.
 */
type BadPatternKey<
    PSpec,
    Seen extends readonly unknown[] = [],
> = PSpec extends unknown
    ? {
          [K in keyof PSpec]: RefinedSlot<PSpec[K], Seen> extends true
              ? K
              : never
      }[keyof PSpec]
    : never
/**
 * Whether the pattern codec at a slot holds a refinement, at the slot or below it. `Seen` holds
 * the terms of the names that the walk entered, so a walk through a recursive `ref` ends.
 */
type RefinedSlot<PC, Seen extends readonly unknown[] = []> = NodeOf<
    TermOf<PC>
> extends ['refine', ...unknown[]]
    ? true
    : IsRef<TermOf<PC>> extends true
      ? [TermOf<PC>] extends [Seen[number]]
          ? false
          : RefinedBelow<PC, [TermOf<PC>, ...Seen]>
      : RefinedBelow<PC, Seen>
type RefinedBelow<PC, Seen extends readonly unknown[]> = [
    LeadingElements<PC>,
] extends [never]
    ? [PatternSpecs<PC>] extends [never]
        ? false
        : [BadPatternKey<PatternSpecs<PC>, Seen>] extends [never]
          ? false
          : true
    : true extends RefinedAmong<LeadingElements<PC>[number], Seen>
      ? true
      : false
/** Whether the pattern codec at any of the positions holds a refinement. */
type RefinedAmong<
    Slots,
    Seen extends readonly unknown[],
> = Slots extends unknown ? RefinedSlot<Slots, Seen> : never

/** Rejects a pattern that holds a part no meet reads, at the call rather than on the result. */
export type ValidatePattern<P> = [PatternSpecs<P>] extends [never]
    ? unknown
    : [BadPatternKey<PatternSpecs<P>>] extends [never]
      ? unknown
      : ErrorMessage<`[extract] the pattern at '${BadPatternKey<PatternSpecs<P>> & string}' holds a refinement, and the host cannot decide whether a member lies inside a predicate`>

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
 * **The order of the slice**: whether every value that the term `a` decodes, as written, is a
 * value of the opening of the pattern `p`. `fits(a, p)` holds exactly where the meet that reads `a`
 * as written and `p` open ({@link meetOrdered}) is `a`, up to a refinement, whose predicate the
 * host cannot read. The order itself is {@link below} at the `value` order, and the opening is
 * {@link opened}.
 */
export const fits = (a: Term, p: Term): boolean => below(a, opened(p), 'value')

/**
 * **The order of the meet**, on terms as they are written, on the fragment that the host decides.
 * At the `relation` order it compares pairs of a stored row and a decoded value, and at the `value`
 * order it compares decoded values ({@link Order}). The two orders differ only at the absent row of
 * a `fill` slot. `narrow`, `disjoint` and {@link storedApart} read stored rows through their own walk, and
 * not this one. `opaque` is the top, and a term that holds no value is the bottom. A set is below a
 * set where its element is below the element. A list is below a list of one element where each
 * position and the spread are below that element. A refinement on the side of the option reads
 * through, because a refinement holds a part of the pairs of its inner term, as the model's
 * `rowSpecC` reads it. An older reading on the side of the pattern reads through, because it holds
 * each pair of its current form. A pair that no rule here covers is below only where the two terms
 * are one term, so the answer errs towards no fit.
 *
 * The literal rule is `Calculus.altsSub`. Two objects compare on their {@link aligned} slots: each
 * slot of the option is below the slot of the pattern at the absent row ({@link absentBelow}) and at
 * its term, and the open block of the option is below the open block of the pattern. A closed
 * object holds no undeclared name, as its open block is the bottom.
 *
 * **A pair on the path of the walk is below.** The order on recursive terms is coinductive: the
 * order is the greatest fixed point of the rules, so a pair that the walk already entered is below,
 * and a walk through a recursive `ref` ends.
 */
const below = (
    a: Term,
    p: Term,
    order: Order,
    assumed: Map<Term, Set<Term>> = new Map(),
): boolean => {
    const A = resolvedTerm(a)
    const P = resolvedTerm(p)
    if (A === undefined || P === undefined) return false
    if (A === P) return true
    // **A pair on the path of the walk fits**, the greatest fixed point of the rules, so a walk
    // through a recursive `ref` ends. The pair leaves the set where its walk ends
    const pending = assumed.get(A) ?? new Set<Term>()
    if (pending.has(P)) return true
    assumed.set(A, pending.add(P))
    try {
        return fitsNode(A, P, order, (x, y) => below(x, y, order, assumed))
    } finally {
        pending.delete(P)
    }
}

/**
 * **A slot that may be absent is the join of its absent row and its present values.** `optional` and
 * `undefinable` give the absent row, a slot of the same mark that holds no value, and the present
 * values, a required slot. `req` and a fill give the slot whole. This is the one place that states
 * the split: {@link joinParts} reads it as terms, and {@link underMark} writes the absent row as a
 * codec.
 */
const presenceParts = (
    field: Field,
): { readonly absent?: Field; readonly present: Field } =>
    field.mark === 'optional' || field.mark === 'undefinable'
        ? {
              absent: { mark: field.mark, t: { kind: 'never' } },
              present: { mark: 'req', t: field.t },
          }
        : { present: field }

/** The codec `held` under the presence mark that {@link presenceParts} splits: `undefinable` keeps the key. */
const underMark = (mark: Field['mark'], held: AnyCodec) =>
    mark === 'undefinable' ? undefinable(held) : optional(held)

/**
 * The most parts that {@link joinParts} builds for one term. A term past the limit stays one part,
 * and `fits` errs towards no fit. The limit refuses, and the reason is the size: the parts of an
 * object are a product of the parts of its fields, so `n` boolean fields give `2^n` parts, and the
 * union rule walks each part against each option of the pattern.
 */
const PARTS_LIMIT = 1024

/**
 * **The parts of the normal form of a term in the value order**: a finite join of join-prime
 * terms. `boolean` is `true ∨ false`. An optional field is its absent row joined with its present
 * values, an absent row being an optional field that holds no value. An object distributes over a
 * union at a field, and a list
 * distributes over a union at a position of its prefix or suffix. A list of a union is one part,
 * because the list holds mixed lists. A refinement, an older reading, an adapter, a `ref` and a
 * set are one part: the host cannot read the first two, and the others hold no split of their own.
 * The split of one part is the split of its parts, so each union is flattened. The union rule of
 * {@link fitsNode} needs this, because `a ≤ ⋁ pᵢ` gives `a ≤ pᵢ` for some `i` only where `a` is
 * join-prime. A term whose parts pass {@link PARTS_LIMIT} stays one part, and `fits` errs towards
 * no fit.
 */
const joinParts = (t: Term): Term[] => {
    const product = <T>(slots: readonly T[][]): T[][] | undefined => {
        let count = 1
        for (const one of slots) {
            count *= one.length
            if (count > PARTS_LIMIT) return undefined
        }
        return slots.reduce<T[][]>(
            (rows, one) => rows.flatMap((row) => one.map((x) => [...row, x])),
            [[]],
        )
    }
    switch (t.kind) {
        case 'union':
            return t.options.flatMap(joinParts)
        case 'boolean':
            return [true, false].map((v) => ({
                kind: 'literal',
                base: 'boolean',
                v,
            }))
        case 'object': {
            const rows = product(
                Object.entries(t.body.fields).map(([name, field]) => {
                    const { absent, present } = presenceParts(field)
                    return [
                        ...(absent === undefined
                            ? []
                            : [[name, absent] as [string, Field]]),
                        ...joinParts(present.t).map((part): [string, Field] => [
                            name,
                            { ...present, t: part },
                        ]),
                    ]
                }),
            )
            return rows === undefined
                ? [t]
                : rows.map((row) => ({
                      kind: 'object',
                      body: { ...t.body, fields: Object.fromEntries(row) },
                  }))
        }
        case 'list': {
            const rows = product([...t.pre, ...t.suf].map(joinParts))
            return rows === undefined
                ? [t]
                : rows.map((row) => ({
                      ...t,
                      pre: row.slice(0, t.pre.length),
                      suf: row.slice(t.pre.length),
                  }))
        }
        default:
            return [t]
    }
}

/** The rules of {@link below} at two nodes that are not `ref`s, with `fits` as the order of each child pair. */
const fitsNode = (
    A: Term,
    P: Term,
    order: Order,
    fits: (a: Term, p: Term) => boolean,
): boolean => {
    if (holdsNoValue(A) || P.kind === 'opaq') return true
    if (A.kind === 'union') return A.options.every((one) => fits(one, P))
    if (P.kind === 'union') {
        const { options } = P
        return joinParts(A).every((part) =>
            options.some((one) => fits(part, one)),
        )
    }
    // a refinement holds a part of the pairs of its inner term, and an older reading holds each
    // pair of its current form. Two older readings of one reader hold the same older pairs, so
    // they compare at their current forms
    if (A.kind === 'refine') return fits(A.inner, P)
    if (P.kind === 'legacy')
        return (
            (A.kind === 'legacy' && A.r === P.r && fits(A.inner, P.inner)) ||
            fits(A, P.inner)
        )
    const pinned = clauseForm(P)
    if (pinned) {
        const mine = clauseForm(A)
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
        return (
            aligned(A.body, P.body, asWritten).every(
                ([, mine, wanted]) =>
                    absentBelow(mine, wanted, order) && fits(mine.t, wanted.t),
            ) && fits(blockOf(A.body, 'written'), blockOf(P.body, 'written'))
        )
    }
    // a list is a product of its positions: the same layout, and each position inside the pattern's
    if (P.kind === 'list') {
        if (A.kind !== 'list') return false
        const { spread } = P
        // a list of one element holds every list whose positions each fit the element
        if (spread !== undefined && P.pre.length === 0 && P.suf.length === 0) {
            return [
                ...A.pre,
                ...(A.spread === undefined ? [] : [A.spread]),
                ...A.suf,
            ].every((one) => fits(one, spread))
        }
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
    if (A.kind === 'set' && P.kind === 'set') return fits(A.elem, P.elem)
    // a literal fits the base that it is a literal of
    const literal = clauseForm(A)
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

/** The object nodes that a term names: each summand of the term that is an object. */
const objectMembersOf = (
    t: Term,
): readonly Extract<Term, { kind: 'object' }>[] =>
    summandsOf(t).filter(
        (node): node is Extract<Term, { kind: 'object' }> =>
            node.kind === 'object',
    )

/**
 * Why a pattern holds a part that no meet reads, or nothing. A refinement at a key of the pattern
 * is refused, because no function decides whether a member lies inside a predicate. A pattern that
 * no member fits is an answer: the extraction keeps nothing, and the exclusion keeps all.
 */
const patternRefusal = (
    pattern: Term,
    seen: Set<Term> = new Set(),
): string | undefined => {
    // **A node that the walk entered has no refusal that the walk did not return**, so a walk
    // through a recursive `ref` ends where it meets the node again
    const node = resolvedTerm(pattern)
    if (node !== undefined) {
        if (seen.has(node)) return undefined
        seen.add(node)
    }
    for (const wanted of objectMembersOf(pattern)) {
        for (const [name, field] of Object.entries(wanted.body.fields)) {
            const why = slotRefusal(name, field.t, seen)
            if (why) return why
        }
    }
    return undefined
}

/** Why the pattern at one slot, a field or a position of a list, holds a refinement, or nothing. */
const slotRefusal = (
    name: string,
    there: Term,
    seen: Set<Term>,
): string | undefined => {
    const node = resolvedTerm(there)
    if (node?.kind === 'refine') {
        return `the pattern at '${name}' holds a refinement, and the host cannot decide whether a member lies inside a predicate. Pin the key to a literal, or slice the field first`
    }
    if (node?.kind !== 'list') return patternRefusal(there, seen)
    for (const position of node.pre) {
        const why = slotRefusal(name, position, seen)
        if (why) return why
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
type ObjectNode = Extract<Term, { kind: 'object' }>

/** The object node that a piece is: the declared fields and the open key entry. */
const nodeOfPiece = (piece: Piece): ObjectNode => {
    const fields: Record<string, Field> = {}
    for (const [name, slot] of Object.entries(piece.spec)) {
        setOwn(fields, name, fieldOf(slot))
    }
    return {
        kind: 'object',
        body:
            piece.rest === undefined
                ? { fields }
                : { fields, rest: termOf(piece.rest) },
    }
}

/**
 * **The cover of an object against the object members of a pattern.** Each member splits the parts
 * that the earlier members left, so the kept parts do not overlap and the rejected parts are what
 * no member fits. A pattern of one object is the case of one member, and a member that is no object
 * fits no object. A part that no member splits is the piece itself.
 */
const coverOf = (
    here: Piece,
    node: ObjectNode,
    members: readonly Term[],
    presence: boolean,
): SpecSlice => {
    const keep: Piece[] = []
    let rest: readonly Piece[] = [here]
    for (const member of members) {
        if (member.kind !== 'object') continue
        rest = rest.flatMap((piece) => {
            const inner = sliceSpec(
                piece,
                piece === here ? node : nodeOfPiece(piece),
                member,
                presence,
            )
            keep.push(...inner.keep)
            return inner.rest
        })
    }
    return { keep, rest }
}

/**
 * **The summands of a term**: the nodes that its nested unions hold, each read through its `ref`s.
 * A chain of `ref`s that names no node gives none.
 */
const summandsOf = (t: Term): readonly Term[] => {
    const node = resolvedTerm(t)
    if (node === undefined) return []
    return node.kind === 'union' ? node.options.flatMap(summandsOf) : [node]
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
 * A union pattern is no product of its keys, so {@link coverOf} reads it member by member. An object
 * with an open key entry is refused where a field changes, because the type of a part holds the
 * declared names only, and the type cannot state the refusal.
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
    node: ObjectNode,
    wantedObject: ObjectNode,
    presence = true,
): SpecSlice => {
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
     * `'leaf'` where the slot holds no union of objects.
     */
    const sliceSlot = (
        mine: Term,
        wanted: Term,
    ): Omit<Entry, 'name' | 'at'> | 'leaf' => {
        const summands = summandsOf(mine)
        const members = summandsOf(wanted)
        if (
            summands.length === 0 ||
            members.length === 0 ||
            summands.some((one) => objectNamed(one) === undefined)
        ) {
            return 'leaf'
        }
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
            if (below(summand, wanted, 'value')) keep.push(here)
            else if (summand.kind === 'object') {
                const inner = coverOf(here, summand, members, presence)
                keep.push(...inner.keep)
                rest.push(...inner.rest)
            } else rest.push(here)
        }
        return { keep, rest, original }
    }
    if (
        !below(
            blockOf(node.body, 'written'),
            blockOf(wantedObject.body, 'written'),
            'value',
        )
    )
        leafFits = false
    for (const [name, mine, wanted] of aligned(
        node.body,
        wantedObject.body,
        asWritten,
    )) {
        // a name that one side holds at its open block splits nowhere: it fits whole or not
        if (
            !(
                Object.hasOwn(node.body.fields, name) &&
                Object.hasOwn(wantedObject.body.fields, name)
            )
        ) {
            if (
                !absentBelow(mine, wanted, 'value') ||
                !below(mine.t, wanted.t, 'value')
            ) {
                leafFits = false
            }
            continue
        }
        // a slot whose absent row the pattern refuses splits into a present part and an absent
        // part, where the absent part has a codec: `optional` or `undefinable` at `never`. At the
        // `value` order a `fill` slot is required, so the pattern refuses no absent row
        if (!absentBelow(mine, wanted, 'value')) {
            const declared = own(piece.spec, name)
            if (!presence || declared === undefined || !('codec' in declared)) {
                leafFits = false
                continue
            }
            if (below(mine.t, wanted.t, 'value')) {
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
        if (below(mine.t, wanted.t, 'value')) continue
        const slot = own(piece.spec, name)
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
                if (there === undefined || below(position, there, 'value'))
                    continue
                const one = sliceSlot(position, there)
                if (one === 'leaf') {
                    leafFits = false
                    continue
                }
                nested.push({ name, at, ...one })
            }
            continue
        }
        const one = sliceSlot(mine.t, wanted.t)
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
        let changed = false
        for (const [entry, list] of replaced) {
            const same =
                list.length === entry.original.length &&
                list.every((one, at) => one === entry.original[at])
            const { name, presence } = entry
            if (same && presence === undefined) continue
            changed = true
            if (presence !== undefined && (same || list.length === 0)) {
                const held = same ? presence.inner : (never as AnyCodec)
                setOwn(
                    spec,
                    name,
                    (list === entry.keep
                        ? held
                        : underMark(
                              presence.mark,
                              held,
                          )) as unknown as ObjectSlot,
                )
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
                setOwn(
                    spec,
                    name,
                    (presence === undefined || list === entry.keep
                        ? codec
                        : underMark(
                              presence.mark,
                              codec,
                          )) as unknown as ObjectSlot,
                )
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
            setOwn(
                spec,
                name,
                codecOfTerm({
                    kind: 'list',
                    pre: declared.pre.map((one, i) => at.get(i) ?? one),
                    suf: [],
                }) as unknown as ObjectSlot,
            )
        }
        return changed ? { spec, rest: piece.rest } : piece
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

/**
 * The options that fit a pattern. An option that fits whole stays whole. An option that an object
 * pattern slices keeps its place and holds a narrower union at the fields that the pattern names:
 * the extraction has no option that the original lacks. A union pattern is read member by member
 * ({@link coverOf}), so a union of one pattern gives the options that the pattern gives.
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
    const written = termOf(pattern as AnyCodec)
    const why = patternRefusal(written)
    if (why) throw new CodecError(why)
    const wanted = opened(written)
    return options.flatMap((option) => {
        const term = termOf(option as unknown as AnyCodec)
        // an option that fits whole has parts that all fit, so it stays whole and no part remains
        if (below(term, wanted, 'value')) return keep ? [option] : []
        const item = objectNamed(term)
        const node = resolvedTerm(term)
        // an option that is no object holds no part that an object member fits
        if (!item || node?.kind !== 'object') return keep ? [] : [option]
        const sliced = coverOf(
            {
                spec: item.spec as Record<string, ObjectSlot>,
                rest: item.rest,
            },
            node,
            summandsOf(wanted),
            splits,
        )
        return (keep ? sliced.keep : sliced.rest).map((one) => {
            if (one.spec === item.spec) return option
            if (!splits) {
                throw new CodecError(
                    'a dissection keeps its members whole, and this pattern changes a member at a field that holds a union of objects. Slice the field first, or take the pattern from a union',
                )
            }
            if (item.rest !== undefined) {
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
    DerivedVariants<SpecsOf<Options>, RestsOf<Options>>,
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
 * **The term that admits no value**, the bottom that the meet and the slice return.
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
export const never: AttributeCodec<never, never> & TermMark<['never']> =
    codecOfTerm<never, never>({ kind: 'never' })

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
): UnionCodec<DerivedUnion<Options>, Options> => {
    const declared = { kind: 'union', options: options.map(termOf) } as const
    // the judgment of the node runs here, and the item reading is a function of the term
    return codecOfTerm(declared) as unknown as UnionCodec<
        DerivedUnion<Options>,
        Options
    >
}

/** The whole-item reading of a union, a function of the term. The memo is a cache only. */
const unions = new WeakMap<Term, Reading>()

const unionOf = (declared: Extract<Term, { kind: 'union' }>): Reading => {
    const built = unions.get(declared)
    if (built) return built
    // **The judgment decides the union's obligation**: each two options compatible, at the
    // declaration, or at the first scope that binds a name of an option. The resolution reads each
    // option through its `ref`s, so it runs at the first use, where every name is bound
    const settle = () => {
        const all: readonly Option<
            ItemCodec<Record<string, unknown>, unknown>
        >[] = declared.options.map(optionOf)
        return { all, ...altSem(all) }
    }
    let settled: ReturnType<typeof settle> | undefined
    const resolution = (): ReturnType<typeof settle> => {
        settled ??= settle()
        return settled
    }
    type T = Record<string, unknown>

    /**
     * The item reading's own matcher: the value is always a record, so the shape filter has nothing
     * to do, and each option is attempted. The names present select nothing, as the model's
     * `Closed.AdmA` reads no name.
     */
    const readItem = (item: StoredItem): Result<T> => {
        const open = openRefusal(declared)
        if (open) return open
        const refused = itemRefusal(item)
        if (refused) return refused
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
     * not be reached here also cannot be selected here: `item` is what an all-object union reads,
     * and only an object option has it.
     */
    const self = {
        [itemMark]: true as const,
        encode: writeItem,
        decode: readItem,
        unsafeEncode: (item: T) => orThrow(self.encode(item)),
        unsafeDecode: (item: StoredItem) => orThrow(self.decode(item)),
        // an object option declares its spec, and a tagged option declares its tag map
        spec: declared.options.map((option) => readingOf(option)?.spec),
        def: declared,
    }

    unions.set(declared, self)
    return self
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
 * The slice of a sum, or of the union of one option that any other codec is.
 *
 * The result is `unknown`: only {@link extract} and {@link exclude} know the codec type that a
 * call gives. Each of the two casts the result once, to the `Slice` of the call. A dissection keeps
 * every key in its slice, because each member still writes its tag.
 */
const sliced = (codec: AnyCodec, pattern: unknown, keep: boolean): unknown => {
    const t = termOf(codec)
    // a slice of `never` keeps nothing, and leaves nothing to exclude
    if (t.kind === 'never') return codec
    if (t.kind !== 'union') return sliced(union([codec]), pattern, keep)
    const open = openRefusal(t)
    if (open) throw open
    const options = t.options.map((option) => codecOfTerm(option))
    const ks = keySets.get(t)
    return ks
        ? slicedDissection(ks, options, pattern, keep)
        : slicedUnion(options, pattern, keep)
}

/**
 * **The part of a codec that a pattern keeps**: TypeScript's `Extract`, on codecs. The pattern is a
 * codec, and an option is kept where every value that it holds lies inside what the pattern holds.
 *
 * Every codec is a union of one option, so every codec takes a pattern. A union, a tagged union and
 * a dissection keep the options that fit, and each keeps its form. Any other codec slices as
 * `union([codec])`: one option stays whole or goes, and a pattern that splits the option gives
 * several. The result is rebuilt through {@link union}, so a slice of a certified union is
 * certified. An extraction that keeps nothing is `never`.
 *
 * An object pattern names the keys that it needs, and an option may declare more. The slice goes
 * into a field that holds a union of objects, and the result stays compact, as the `Extract` of
 * TypeScript reads it: `{ k, pet: U }` against `{ pet: P }` keeps `{ k, pet: Extract<U, P> }`. So
 * the extraction has no option that the original lacks.
 *
 * @example
 * ```ts
 * extract(pet, object({ status: string('AVAILABLE') }))
 * ```
 */
export const extract = <const C extends AnyCodec, const P extends AnyCodec>(
    codec: C & Closed,
    pattern: P & ValidatePattern<P>,
): Slice<C, P, true> => sliced(codec, pattern, true) as Slice<C, P, true>

/** …and the part that it rejects, the complement of the same pattern: TypeScript's `Exclude`. */
export const exclude = <const C extends AnyCodec, const P extends AnyCodec>(
    codec: C & Closed,
    pattern: P & ValidatePattern<P>,
): Slice<C, P, false> => sliced(codec, pattern, false) as Slice<C, P, false>

/**
 * How a union of objects is declared: with a tag, or by the attributes each variant has.
 *
 * One parameter and one signature. Overloads would read the same at the call and cost the
 * diagnostic — `No overload matches this call` at the call site instead of a message on the
 * argument, which is what two signatures on `tableEntry` were measured to do. A union in one
 * inference slot would cost worse: a string and an array sharing a slot is how `tableEntry` came to
 * infer a codec from a separator.
 */
