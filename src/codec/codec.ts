import type { AttributeValue } from './attribute'
import type { AnyCodec, AttributeCodec, ObjectSlot } from './build'

import { codecOfTerm, termOf } from './denote'
import type { ApartG, DecodeTerm, NodeOf, OpenT, Same } from './pathModel'
import { CodecError, setOwn } from './result'
import { alignedRows, callerApart, storedApart } from './scoped'
import type { Field, RefSlot, Term } from './term'
import {
    absentBelow,
    clauseForm,
    holdsNoValue,
    member as memberOf,
    resolvedTerm,
    sameAdapter,
    unboundRefs,
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
import type { AttributeOf, Decoded, Marks } from './build'

import { opened } from './clause'
import type { AnyObjectCodec, DerivedUnion } from './derivedItem'
import { entryCodec, fieldOf } from './derivedItem'

import type { AnyOpen, FactorOptions, Inexact, StoredMembers } from './objects'
import { objectFromMap, optional, undefinable } from './objects'

import { fill, never } from './prisms'
import type { ArrayOver } from './products'
import type {
    ObjectCodec,
    OptionalCodec,
    UndefinableCodec,
    UnionCodec,
} from './scope'
import { objectItem } from './scope'
import type {
    BelowT,
    FitsCodec,
    IsRefine,
    MeetReading,
    MeetWalk,
} from './separation'
import {
    aligned,
    asComposed,
    asOrdered,
    below,
    blockOf,
    walkAt,
} from './separation'

import { union } from './sums'
import type {
    elementMarker,
    fillMarker,
    optionalMarker,
    TermMark,
    TermOf,
    undefinableMarker,
} from './term'
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
export { object, optional, undefinable } from './objects'
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
export type { LocatedCodec, PathOf } from './scopePath'
export { at, narrow, path, pathBuilder, preconditions } from './scopePath'
export { exclude, extract } from './scopeSlice'
export type {
    DiscriminatedCodec,
    Dissected,
    DissectedCodec,
    Dissection,
    Tagged,
    TaggedCodec,
} from './sums'
export { discriminatedUnion, item, mdunion, nullable, union } from './sums'

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
 * How a union of objects is declared: with a tag, or by the attributes each variant has.
 *
 * One parameter and one signature. Overloads would read the same at the call and cost the
 * diagnostic — `No overload matches this call` at the call site instead of a message on the
 * argument, which is what two signatures on `tableEntry` were measured to do. A union in one
 * inference slot would cost worse: a string and an array sharing a slot is how `tableEntry` came to
 * infer a codec from a separator.
 */
