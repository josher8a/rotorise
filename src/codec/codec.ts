import type { AttributeValue } from './attribute'
import type { AnyCodec, AttributeCodec, Closed, ObjectSlot } from './build'

import { codecOfTerm, termOf } from './denote'
import type { ApartG, DecodeTerm, NodeOf, Norm, OpenT, Same } from './pathModel'
import { CodecError, setOwn } from './result'
import { alignedRows, callerApart, storedApart } from './scoped'
import type { Field, RefSlot, Term } from './term'
import {
    absentBelow,
    clauseForm,
    holdsNoValue,
    member as memberOf,
    openRefusal,
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
import type { AttributeOf, Decoded, Marks, ObjectOf } from './build'

import { opened } from './clause'
import type {
    AnyObjectCodec,
    Declares,
    DecodedTags,
    DerivedUnion,
    DerivedVariants,
    VariantOf,
} from './derivedItem'
import { entryCodec, fieldOf, keySets } from './derivedItem'
import type { UnionKeys } from './frontier'

import type { AnyOpen, FactorOptions, Inexact, StoredMembers } from './objects'
import { objectFromMap, optional, undefinable } from './objects'

import { fill, never } from './prisms'
import type {
    ArrayOver,
    FixedElements,
    LeadingElements,
    ListCodec,
} from './products'
import type {
    MarkLike,
    ObjectCodec,
    ObjectItem,
    OptionalCodec,
    UndefinableCodec,
    UnionCodec,
} from './scope'
import { objectItem, objectNamed } from './scope'
import type {
    AbsentBelow,
    AllOf,
    BelowT,
    EveryFits,
    Fit,
    FitsCodec,
    FitsSpec,
    IsRef,
    IsRefine,
    JoinParts,
    KeepsFit,
    KeyTuple,
    MeetReading,
    MeetWalk,
    ObjectNode,
    PatternNodes,
    Piece,
    SlotMarkOf,
    SpecSlice,
} from './separation'
import {
    aligned,
    asComposed,
    asOrdered,
    asWritten,
    below,
    blockOf,
    nodeOfPiece,
    objectMembersOf,
    summandsOf,
    underMark,
    walkAt,
} from './separation'
import type { DiscriminatedCodec, DissectedCodec, LiteralOptions } from './sums'
import { dissect, union } from './sums'
import type {
    elementMarker,
    fillMarker,
    OfParts,
    optionalMarker,
    TermMark,
    TermOf,
    TermsOf,
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
/** Whether two codecs hold lists with fixed positions. */
type HasFixed<A, P> = [FixedElements<A>] extends [never]
    ? false
    : [FixedElements<P>] extends [never]
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
