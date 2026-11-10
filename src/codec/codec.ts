import type {
    Attribute,
    AttributeMap,
    AttributeName,
    AttributeValue,
    M,
    StoredItem,
} from './attribute'
import type { AnyCodec, AttributeCodec, Closed, ObjectSlot } from './build'

import { codecAtLevel, codecOfTerm, defOf, termOf } from './denote'
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
    Same,
    SlotAt,
    StepFrames,
} from './pathModel'
import { asPath, CodecError, type Result, setOwn } from './result'
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
    LiteralValue,
    NameForm,
    Order,
    RefSlot,
    Term,
} from './term'
import {
    absentBelow,
    clauseForm,
    holdsNoValue,
    member as memberOf,
    openRefusal,
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
import type { MissingCodec } from './adapters'
import { fillRefusal } from './adapters'
import type { AttributeOf, Decoded, EncodedBy, Marks, ObjectOf } from './build'
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
    OptionInexact,
    UnionToIntersection,
    VariantOf,
} from './derivedItem'
import { entryCodec, fieldOf, keySets } from './derivedItem'
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
import type { LibraryInner } from './prisms'
import { fill, never } from './prisms'
import type {
    ArrayOver,
    FixedElements,
    LeadingElements,
    ListCodec,
    NoNeverField,
    NoSpreadMember,
} from './products'
import type {
    Marked,
    MarkLike,
    ObjectCodec,
    ObjectItem,
    OptionalCodec,
    UndefinableCodec,
    UnionCodec,
} from './scope'
import { itemMark, objectItem, objectNamed } from './scope'
import type { Precondition } from './scoped'
import type { DiscriminatedCodec, DissectedCodec, LiteralOptions } from './sums'
import { dissect, item, union } from './sums'
import type {
    elementMarker,
    fillMarker,
    itemOfMarker,
    itemTermMarker,
    locatedFrom,
    ObjectTermOf,
    OfParts,
    optionalMarker,
    optionsMarker,
    SlotOf,
    TermMark,
    TermOf,
    TermsOf,
    undefinableMarker,
} from './term'
import { locatedSlot } from './term'
import { own, sameLiteral } from './value'

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
export { opaque } from './opaque'
export type {
    BinaryCodec,
    BooleanCodec,
    ConstantOf,
    Refined,
    SetBase,
    StringCodec,
} from './prisms'
export {
    binary,
    boolean,
    decimal,
    fill,
    never,
    nullValue,
    number,
    refine,
    string,
} from './prisms'
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
export type {
    AllObjects,
    ItemCodec,
    ItemSpec,
    ObjectCodec,
    OptionalCodec,
    UndefinableCodec,
    UnionCodec,
    Untagged,
    UntaggedSpec,
    WrittenBy,
} from './scope'
export { ref, scope } from './scope'
export type {
    DiscriminatedCodec,
    Dissected,
    DissectedCodec,
    Dissection,
    Tagged,
    TaggedCodec,
} from './sums'
export { discriminatedUnion, item, mdunion, nullable, union } from './sums'

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

/**
 * **The codec where a container admits no value at a segment**: one `never`, so a frontier that
 * holds it agrees with no writer, and the walk refuses on use. One term, so the frontier keeps one
 * copy.
 */
const absent: AnyCodec = codecOfTerm({ kind: 'never' })

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
