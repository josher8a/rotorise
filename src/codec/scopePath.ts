import type { ErrorMessage } from '../utils'
import type {
    AttributeMap,
    AttributeName,
    AttributeValue,
    StoredItem,
} from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    AttributeOf,
    Closed,
    Decoded,
    Marks,
} from './build'
import { codecOfTerm } from './capabilities'
import type { Clause, ClausePattern } from './clause'
import { clauseOf } from './clause'
import { codecAtLevel, termOf } from './denote'
import type { DecodedTags, IsUnion, VariantOf } from './derivedItem'
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
    HoldsFree,
    KindOfFrames,
    NarrowFrames,
    Norm,
    OffersAt,
    StepFrames,
} from './pathModel'
import type { LibraryInner } from './prisms'
import type { Result } from './result'
import { asPath, CodecError } from './result'
import type { Marked, UnionCodec } from './scope'
import { itemMark } from './scope'
import type { Precondition } from './scoped'
import { childAt, flatOf, guardAt, sideOf, storedApart } from './scoped'
import type { DiscriminatedCodec } from './sums'
import { item, union } from './sums'
import type {
    itemOfMarker,
    itemTermMarker,
    locatedFrom,
    ObjectTermOf,
    OfParts,
    Term,
    TermOf,
} from './term'
import {
    locatedSlot,
    member as memberOf,
    openRefusal,
    targetOf,
    unanimous,
    usedTargetOf,
} from './term'
import { own } from './value'

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
export const childrenOf = (
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
export const printedMember = (
    t: Term,
    cycles: Cycles,
): AttributeName | undefined => {
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
export const acrossVariants = (
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
 * **The frontier after a clause**, the model's `narrowC`. A union gives each option whose stored
 * view {@link storedApart} does not separate from the stored view of the clause. Any other member
 * stays where the clause does not separate the member. A clause that separates every member is a
 * refusal that names the keys of the clause. A `ref` resolves as {@link childrenOf} resolves it.
 *
 * **The test reads the stored views**, because a path addresses a stored attribute. An adapter is
 * apart only from the bottom, so a test on the terms separates nothing at a `number` tag. The
 * stored view of an adapter is its inner term, which the test reads.
 */
export const narrowAcross = (
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
export const preconditionsOf = (
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
        // a clause has no scoped form only where its flat scope is refused, and `scope` refuses that
        // scope, for an unguarded cycle of refs or for a wall (RecursionRefused), before any path
        // records the clause
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
export const unresolvedAt = (path: string, partial: boolean): AnyCodec =>
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
export const absent: AnyCodec = codecOfTerm({ kind: 'never' })

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
 * clean. A map offers `at(key)` and no bracket hop, because a hop in digits is a position, and only
 * a list holds positions. An attribute named `at`, `narrow` or `toString` is a hop where the path
 * reads it, and the method where the path calls it.
 */
export type PathOf<T, F = unknown> = PathTerminal<T> &
    PathBody<NonNullable<T>, F>

export type PathBody<T, F> = [T] extends [readonly unknown[]]
    ? // a list that holds no value offers no position, as the walk answers a position of it as vacant
      [T[number]] extends [never]
        ? Record<never, never>
        : PathList<T[number]>
    : [T] extends [object]
      ? {
            readonly [K in HopNames<T>]: PathOf<ValueAt<T, K>, ChildAt<F, K>>
        } & PathRecord<T> &
            PathNarrowing<T, F>
      : Record<never, never>

/** The members of a codec: each option of a union, each variant of a tagged union, or the object. */
export type MembersOf<C> = C extends UnionCodec<infer _T, infer Options>
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
export type PathNarrowing<T, F> = IsUnion<T> extends true
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
export type Kept<F, C> = F extends Member
    ? ClauseApart<F, C> extends true
        ? never
        : F
    : never

/**
 * **Whether a clause separates an object**, with each object of the clause open: the object is
 * apart where, at one key of the clause, it holds no codec, or its codec and the codec of the
 * clause are apart ({@link StoredApart}).
 */
export type ClauseApart<X, C> = true extends {
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
export type StoredApart<X, Y> = [
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
export type StoredPin<C> = StoredPinAt<TermOf<C>, []>
export type StoredPinAt<T, Env> = Norm<T, Env> extends [infer N, infer E]
    ? StoredPinOf<N, E>
    : never
export type StoredPinOf<N, E> = N extends [
    'prim',
    ['literal', unknown, infer V],
]
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
export type ClauseOn<T, F, C> = [Exclude<keyof C, UnionKeys<T>>] extends [never]
    ? [unknown extends F ? Narrowed<T, C> : Kept<F, C>] extends [never]
        ? ErrorMessage<'[narrow] the clause separates every member of this union'>
        : unknown
    : ErrorMessage<`[narrow] no member of this union declares '${Exclude<
          keyof C,
          UnionKeys<T>
      > &
          string}'`>

/**
 * The names that a path offers as a hop on an object: the names that the type declares. The path
 * reads a hop in digits as a list position, and an expression prints a position as `[n]`. So an
 * index signature gives no hop, whatever the pattern of the key, and neither does a name that reads
 * as a number. Such a name is a key of a map, and `at(key)` carries a key ({@link PathRecord}).
 */
export type HopNames<T> = T extends unknown
    ? keyof { [K in keyof T as HopName<K>]: unknown }
    : never
/**
 * A declared name is a required property of `Record<K, unknown>`, so `Record<never, never>` is no
 * subtype of that record. An index signature of each key form, wide or a pattern, is a subtype.
 */
export type HopName<K> = K extends number
    ? never
    : K extends string
      ? Record<never, never> extends Record<K, unknown>
          ? never
          : K extends `${number}`
            ? never
            : K
      : K

/** The keys of a map: each index signature whose key is a string, wide or a pattern. */
export type MapKeys<T> = T extends unknown
    ? keyof { [K in keyof T as MapKey<K>]: unknown }
    : never
export type MapKey<K> = K extends string
    ? Record<never, never> extends Record<K, unknown>
        ? K
        : never
    : never

/**
 * A map whose keys are not known ahead of time, indexed by `at`.
 *
 * `requirements[someId]` would be an index signature access. A hop in digits is a list position,
 * and a key of a map is a name, so the type offers no bracket hop on a map. Only present when the
 * type has an index signature whose key is a string, so an object with known keys is untouched
 * and `.foo` stays the way to reach `foo`. The key of `at` is the pattern of the index signature.
 */
export type PathRecord<T> = [MapKeys<T>] extends [never]
    ? unknown
    : { at(key: MapKeys<T>): PathOf<ValueAt<T, MapKeys<T>>> }

/**
 * A list, indexed by `at`.
 *
 * Deliberately not a mapped tuple. Preserving the tuple would let a literal index work in brackets,
 * but it also inherits `Array.prototype.at`, whose signature returns `| undefined` and shadows this
 * one — reintroducing at every index the assertion this type exists to remove.
 */
export type PathList<Element> = {
    readonly [index: number]: PathOf<Element>
    at(index: number): PathOf<Element>
}
/** Nothing, or why the clause keeps no option: `K` holds the frames that the clause keeps. */
export type ClauseOnFrames<K> = K extends []
    ? ErrorMessage<'[narrow] the clause separates every member of this union'>
    : unknown

/** The place one segment down, or {@link Refused}. */
export type StepAt<H, S> = H extends [
    'term',
    infer Fs,
    infer T,
    infer F,
    unknown,
]
    ? StepTerm<Fs, NonNullable<T>, F, OffersAt<Fs>, S>
    : H extends ['path', infer T, infer F]
      ? StepPath<NonNullable<T>, F, S>
      : Refused
export type StepTerm<Fs, T, F, O, S> = S extends string
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
export type StepPath<T, F, S> = [T] extends [readonly unknown[]]
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
export type OfferedAt<H> = H extends [
    'term',
    infer Fs,
    unknown,
    unknown,
    unknown,
]
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
export type WalkAt<H, S> = H extends Wide
    ? Wide
    : S extends readonly [infer Head, ...infer Tail]
      ? WalkAt<StepAt<H, Head>, Tail>
      : S extends readonly []
        ? H
        : Wide

/** Why the place at the end of a path holds no one codec, or nothing where the place holds one. */
export type ResolvesAt<H> = H extends [
    'term',
    infer Fs,
    unknown,
    unknown,
    unknown,
]
    ? [KindOfFrames<Fs>] extends ['resolved']
        ? unknown
        : ErrorMessage<`[at] the path is ${KindOfFrames<Fs> & string}: no one codec stands at the path`>
    : H extends ['path', unknown, unknown]
      ? unknown
      : ErrorMessage<'[at] no codec stands at the path'>

/** The refusal of a segment, with the segments that the place offers. */
export type NoSegment<O> =
    ErrorMessage<'[at] the place offers no such segment'> & {
        readonly '[at] the place offers': O
    }

/**
 * **The check of a tuple path**, as an intersection with the parameter. A segment that the place
 * does not offer meets a refusal that names the segments that the place offers, so the refusal lands
 * on that segment. A path to a place that holds no one codec is a refusal of the path.
 */
export type CheckPath<H, S, Done extends readonly unknown[] = []> = H extends
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
export type CheckString<H, S extends string> = string extends S
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
export type CompleteAt<H, S> = [S] extends [string]
    ? CompleteString<H, S, LastPart<S>>
    : S extends readonly unknown[]
      ? unknown extends S[number]
          ? CompletePath<H, S>
          : never
      : never
export type CompletePath<H, S, Done extends readonly unknown[] = []> = H extends
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
export type CompleteString<H, S extends string, L> = L extends [
    infer P extends string,
    unknown,
]
    ? WalkAt<H, ParsePath<P extends `${infer Q}.` ? Q : P>> extends infer N
        ? N extends Wide | Refused
            ? never
            : Exclude<`${P}${PlainName<OfferedAt<N>>}`, S>
        : never
    : never

export type CheckAt<H, S> = S extends string
    ? CheckString<H, S>
    : CheckPath<H, S>

/**
 * **The place at the start of a walk.** A located codec continues its own place. An item starts at
 * its root, which writes a row. Any other codec starts at its own term, an attribute at level 0.
 */
export type StartOf<C> = C extends {
    readonly [locatedFrom]?: [infer H, RootKind]
}
    ? unknown extends H
        ? StartOfCodec<C>
        : H
    : StartOfCodec<C>
export type StartOfCodec<C> = C extends { readonly [itemOfMarker]?: [infer U] }
    ? unknown extends U
        ? StartOfItem<C>
        : ['term', [[TermOf<U>, []]], Decoded<U>, MembersOf<U>, true]
    : StartOfItem<C>
export type StartOfItem<C> = C extends {
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
export type FocusAt<H, R extends RootKind> = H extends Wide
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
export type NarrowAt<H, C> = H extends Wide
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
export type NarrowPath<T, F, C> = [T] extends [readonly unknown[]]
    ? Refused
    : [T] extends [object]
      ? IsUnion<T> extends true
          ? unknown extends F
              ? ['path', Narrowed<T, C>, unknown]
              : ['path', Kept<F, C>['t'], Kept<F, C>]
          : Refused
      : Refused

/** Nothing, or why `narrow` refuses the clause at the place. */
export type CheckNarrow<H, C> = H extends Wide
    ? unknown
    : H extends ['term', infer Fs, infer T, infer F, unknown]
      ? HoldsFree<Fs> extends true
          ? CheckNarrowPath<NonNullable<T>, F, C>
          : ClauseOnFrames<NarrowFrames<Fs, ClauseTerms<C>>>
      : H extends ['path', infer T, infer F]
        ? CheckNarrowPath<NonNullable<T>, F, C>
        : ErrorMessage<'[narrow] no codec stands at the path'>
export type CheckNarrowPath<T, F, C> = NarrowPath<T, F, C> extends Refused
    ? ErrorMessage<'[narrow] the codec at the path is no union'>
    : ClauseOn<T, F, C>

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
export type LocatedRow<T, P, R extends RootKind> = {
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
export type RootOf<C> = C extends {
    readonly [locatedFrom]?: [unknown, infer R extends RootKind]
}
    ? RootKind extends R
        ? KindOfRoot<C>
        : R
    : KindOfRoot<C>
export type KindOfRoot<C> = C extends Marked ? 'item' : 'relative'

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
 * const delivered = at(item(Adoption), ['shipment', 'legs', i, 'deliveredAt'])
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
 * name. The function reads more names than {@link expressionPath} prints: a name with a `-` is a
 * name here, and has no expression string. A malformed path is a defect of the caller, and the type
 * of {@link at} refuses it first.
 */
export const parsePath = (path: string): readonly Segment[] => {
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

/**
 * A name that an expression of DynamoDB reads as one name: a letter, then letters, digits and `_`.
 * An expression reads a `.` as a separator, `[n]` as a position and `,` as the end of a path, drops
 * a space at an end of a name, and refuses each other name.
 */
const expressionName = /^[A-Za-z][A-Za-z0-9_]*$/

/**
 * **The string of the segments of a document path, in DynamoDB expression syntax.** The string is a
 * projection of the segments, and `parsePath` is the inverse. The projection is partial: the string
 * exists where an expression reads each name as one name. An expression has no escape for a name:
 * any other name needs a placeholder of `ExpressionAttributeNames`, which a string cannot carry. So
 * the projection refuses such a name, and the tuple form of {@link at} still carries the name. The
 * message gives the position of the segment, and not the name, because a key is data.
 * A position is a non-negative integer.
 *
 * A reserved word of DynamoDB has a string, and DynamoDB refuses the expression with the word in the
 * message. The list of reserved words belongs to DynamoDB, so this package holds no copy.
 */
export const expressionPath = (segments: readonly Segment[]): string => {
    let out = ''
    segments.forEach((segment, at) => {
        if (typeof segment === 'number') {
            if (!Number.isSafeInteger(segment) || segment < 0) {
                throw new CodecError(
                    `the position at segment ${at} of the path is no non-negative integer, so the path has no expression string`,
                )
            }
            out += `[${segment}]`
            return
        }
        if (!expressionName.test(segment)) {
            throw new CodecError(
                `the name at segment ${at} of the path is not a letter, then letters, digits and '_': an expression does not read it as one name, so the name needs a placeholder of ExpressionAttributeNames and the path has no expression string`,
            )
        }
        out += out === '' ? segment : `.${segment}`
    })
    return out
}

/** Whether a codec is a whole-item reading: an object's, a union's or a tagged union's `item`. */
export const isItemReading = (codec: object): boolean => itemMark in codec

/** The codec at the steps of a path from a root, with its place. */
export const locate = (
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

    const made: Located = { root, steps, reached }
    return { ...here, [locatedSlot]: made }
}
export type Located = {
    readonly root: AnyCodec
    readonly steps: readonly Step[]
    /** The frontier at the end of the steps, where the walk reached the end. */
    readonly reached: Reached | undefined
}

/**
 * **The document path of a located codec**, in DynamoDB expression syntax: the external form of
 * the segments, so `path(at(c, 'a.b[1]'))` is `'a.b[1]'`. A codec that no `at` located stands at
 * its own root, and its path is empty. A name has a string where the name is a letter, then
 * letters, digits and `_`, because an expression reads no other name as one name: `path` throws a
 * {@link CodecError} for another name, and {@link at} still builds from the tuple form, which
 * carries the name.
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
        ? expressionPath(segmentsIn(located.steps))
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
export const recordPath = (steps: readonly Step[]): unknown =>
    new Proxy(nothing, { get: (_target, prop) => hop(steps, prop) })

/**
 * **A method of a path is also an attribute name.** DynamoDB admits an attribute named `at`, and
 * the path type offers it as a hop. So the hop to a method name is a recorder that is callable: read
 * as a property, it is the hop to the attribute; called, it is the method at the node before the
 * hop. Only these hops are callable, and their `then` is a plain hop, so no path is a thenable.
 */
export const hop = (steps: readonly Step[], prop: string | symbol): unknown => {
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
export const methodAt = (
    steps: readonly Step[],
    name: string,
): ((arg: never) => unknown) | undefined => {
    switch (name) {
        case 'toString':
            return () => expressionPath(segmentsIn(steps))
        case 'at':
            return (index: number | string) => recordPath([...steps, index])
        // a clause narrows the frontier of `at`; the document path is unchanged
        case 'narrow':
            return (pattern: ClausePattern) =>
                recordPath([...steps, clauseOf(pattern)])
        default:
            return undefined
    }
}
