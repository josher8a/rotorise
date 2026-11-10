import type { ErrorMessage, show } from '../utils'
import type { AnyCodec, Closed, Marks, ObjectOf, ObjectSlot } from './build'
import { codecOfTerm } from './capabilities'
import { opened } from './clause'
import { termOf } from './denote'
import type {
    Declares,
    DecodedTags,
    DerivedUnion,
    DerivedVariants,
    VariantOf,
} from './derivedItem'
import { entryCodec, keySets } from './derivedItem'
import type { UnionKeys } from './frontier'
import { objectFromMap } from './objects'
import type { DecodeTerm, NodeOf, Norm, OpenT, Same } from './pathModel'
import { never } from './prisms'
import type { FixedElements, LeadingElements, ListCodec } from './products'
import { CodecError, setOwn } from './result'
import type { MarkLike, ObjectCodec, ObjectItem, UnionCodec } from './scope'
import { objectNamed } from './scope'
import type {
    AbsentBelow,
    AllOf,
    EveryFits,
    Fit,
    FitsCodec,
    FitsSpec,
    IsRef,
    JoinParts,
    KeepsFit,
    KeyTuple,
    ObjectNode,
    PatternNodes,
    Piece,
    SlotMarkOf,
    SpecSlice,
} from './separation'
import {
    aligned,
    asWritten,
    below,
    blockOf,
    nodeOfPiece,
    objectMembersOf,
    summandsOf,
    underMark,
} from './separation'
import type { DiscriminatedCodec, DissectedCodec, LiteralOptions } from './sums'
import { dissect, union } from './sums'
import type { Field, OfParts, Term, TermOf, TermsOf } from './term'
import { absentBelow, openRefusal, resolvedTerm } from './term'
import { own } from './value'

/**
 * The options that a clause keeps. A slice of an entry of a `scope` holds the `ref`s of the entry,
 * so the slice is one more entry of that scope, at a key that no `ref` can name.
 */
export type UnionSlice<Tm, Kept extends readonly unknown[]> = [Tm] extends [
    ['scope', infer D, unknown],
]
    ? UnionCodec<DecodeTerm<SliceTerm<D, Kept>>, Kept, SliceTerm<D, Kept>>
    : UnionCodec<DerivedUnion<Kept>, Kept>
export declare const sliceKey: unique symbol
export type SliceTerm<D, Kept extends readonly unknown[]> = [
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
export type Slice<C, P, Keep extends boolean> = C extends DiscriminatedCodec<
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
 * A dissection's slice: the same keys, the members the clause keeps, and `never` where it keeps
 * none.
 *
 * `never` and not an empty dissection, which `dissect` refuses: an empty option list is what a typo
 * produces, so a rule reading it as the bottom reads that accident as intent. An extraction that
 * keeps nothing is the bottom on purpose, and there is one name for the bottom.
 */
export const slicedDissection = (
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
export type PatternSpecs<P> = P extends unknown
    ? [OptionsOfCodec<P>] extends [never]
        ? FieldSpecList<P>[number]
        : PatternSpecs<OptionsOfCodec<P>[number]>
    : never
export type OptionsOfCodec<P> = P extends UnionCodec<
    infer _T,
    infer Os extends readonly unknown[],
    infer _Tm
>
    ? Os
    : never

/** The member specs of the codec at a field: each option of a union of objects, or the object itself. */
export type FieldSpecList<F> = F extends Declares<infer Sp>
    ? Sp extends readonly unknown[]
        ? Sp
        : [Sp]
    : never

export type ObjectOfSpec<S> = S extends Record<string, ObjectSlot>
    ? ObjectCodec<show<S>>
    : never

/** A spec, split at the keys of the pattern specs `PU` where the spec holds objects. */
export type SplitSpec<Spec, PU> = SplitKeys<[Spec], KeyTuple<UnionKeys<PU>>, PU>
export type SplitKeys<
    States extends readonly unknown[],
    Keys extends readonly unknown[],
    PU,
> = Keys extends readonly [infer Key, ...infer Rest extends readonly unknown[]]
    ? SplitKeys<SplitAt<States, Key, PU>, Rest, PU>
    : States
export type SplitAt<
    States extends readonly unknown[],
    Key,
    PU,
> = States extends readonly [
    infer State,
    ...infer Rest extends readonly unknown[],
]
    ? [...SplitState<State, Key, PU>, ...SplitAt<Rest, Key, PU>]
    : []
export type SplitState<State, Key, PU> = Key extends keyof State
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
export type PatternCodecsAt<PU, Key> = PU extends unknown
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
export type SplitSlot<C, PC> = [FixedElements<C>] extends [never]
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
export type SplitPositions<
    Ls extends readonly unknown[],
    PC,
    N extends number,
    I extends readonly unknown[] = [],
> = I['length'] extends N
    ? Ls
    : SplitPositions<SplitAtPosition<Ls, PC, N, I['length']>, PC, N, [...I, 0]>
export type SplitAtPosition<
    Ls extends readonly unknown[],
    PC,
    N extends number,
    I extends number,
> = Ls extends readonly [infer L, ...infer Rest extends readonly unknown[]]
    ? [...SplitPositionState<L, PC, N, I>, ...SplitAtPosition<Rest, PC, N, I>]
    : []
export type SplitPositionState<
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
export type PositionCodecsAt<PC, I, N> = PC extends unknown
    ? FixedElements<PC>['length'] extends N
        ? I extends keyof FixedElements<PC>
            ? FixedElements<PC>[I]
            : never
        : never
    : never
export type WithPosition<
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
export type InnerSpecs<
    Members extends readonly unknown[],
    PU,
> = Members extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? [...SplitSpec<Head, PU>, ...InnerSpecs<Rest, PU>]
    : []
export type ReplaceField<
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
export type SplitOptions<
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
export type MapObjects<Specs extends readonly unknown[]> = {
    [I in keyof Specs]: ObjectOfSpec<Specs[I]>
}
/** Whether two codecs hold lists with fixed positions. */
export type HasFixed<A, P> = [FixedElements<A>] extends [never]
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
export type KeptSplit<
    Options extends readonly unknown[],
    P,
    Keep extends boolean = true,
> = KeptBy<SplitOptions<Options, P>, P, Keep>
export type KeptBy<
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
export type NestedKey<
    K,
    Keep extends readonly unknown[],
    Rest extends readonly unknown[],
    Orig extends readonly unknown[],
    Opt = never,
> = { key: K; keep: Keep; rest: Rest; orig: Orig; opt: Opt }

/** The one summand of a field that holds no object: the field as declared. */
export type WholeField = { readonly whole: true }

/**
 * Whether a field splits at presence: the pattern refuses the absent row of the field, which
 * {@link AbsentBelow} decides on the marks. A required field, and a fill value at the `value` order,
 * hold no absent row.
 */
export type SplitsAtPresence<A, P> = AbsentBelow<
    SlotMarkOf<A>,
    SlotMarkOf<P>
> extends 'f'
    ? true
    : false

/**
 * A field that may be absent, against a pattern that requires the key: the present part follows
 * the fit of the declared codec, and the absent part is rejected.
 */
export type SlicePresence<
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
export type SliceSummands<
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
export type CoverSummand<
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
export type CoverPieces<
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
export type SliceKeys<
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
export type SlicePositions<
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
export type SlotSlice<A, P> = FitsCodec<A, P> extends 't'
    ? { fit: 't' }
    : [FieldSpecList<A>] extends [never]
      ? { fit: FitsCodec<A, P> }
      : [FieldSpecList<P>] extends [never]
        ? { fit: FitsCodec<A, P> }
        : SliceSummands<FieldSpecList<A>, FieldSpecList<P>>

/** The list at a key with one position replaced by the kept or the rejected summands. */
export type ReplacePosition<
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

export type Replacement = {
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
export type PresenceField<Head extends Replacement> = (
    Head['list'] extends readonly []
        ? typeof never
        : FieldOf<Head['list'], Head['orig'], Marks<Head['opt']>>
) extends infer C extends AnyCodec
    ? Head['of'] extends 'keep'
        ? C
        : MarkLike<Head['opt'], C>
    : never

/** The slot that holds the kept summands: the declared slot where they are all of them, else their union. */
export type FieldOf<
    L extends readonly unknown[],
    Orig extends readonly unknown[],
    Slot,
> = true extends Same<L, Orig>
    ? Slot
    : L extends readonly [infer One]
      ? ObjectOfSpec<One>
      : UnionCodec<DerivedUnion<MapObjects<L>>, MapObjects<L>>
export type ReplaceAll<S, Rs extends readonly unknown[]> = Rs extends readonly [
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
export type Lists<
    Nested extends readonly unknown[],
    Of extends 'keep' | 'rest',
> = {
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
export type NonEmptyAll<Ls extends readonly unknown[]> = Ls extends readonly [
    infer H extends { list: readonly unknown[] },
    ...infer T extends readonly unknown[],
]
    ? H['list'] extends readonly []
        ? false
        : NonEmptyAll<T>
    : true

export type SliceInfo = { leaf: Fit; nested: readonly unknown[] }

/** The kept spec: one spec with a union at each split field, or nothing. */
export type KeptSpecs<S, Info extends SliceInfo> = Info['leaf'] extends 'f'
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
export type RestSpecs<S, Info extends SliceInfo> = Info['leaf'] extends
    | 'f'
    | 'u'
    ? [S]
    : RestAt<S, Info['nested'], []>
export type RestAt<
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
export type RestOf<
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

export type SliceSpecOf<S, PS> = SliceKeys<
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
export type ObjectMembers<Ms extends readonly unknown[]> = Ms extends readonly [
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
export type KeptWhole<
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
export type OverCap<A, P> = [
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
export type KeptFold<
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
export type KeptCompact<
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
export type SameSpecOrObject<Specs extends readonly unknown[], Sp, Head> = {
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
export type KeptVariants<T, D, Kept> = {
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
export type BadPatternKey<
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
export type RefinedSlot<PC, Seen extends readonly unknown[] = []> = NodeOf<
    TermOf<PC>
> extends ['refine', ...unknown[]]
    ? true
    : IsRef<TermOf<PC>> extends true
      ? [TermOf<PC>] extends [Seen[number]]
          ? false
          : RefinedBelow<PC, [TermOf<PC>, ...Seen]>
      : RefinedBelow<PC, Seen>
export type RefinedBelow<PC, Seen extends readonly unknown[]> = [
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
export type RefinedAmong<
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
export const patternRefusal = (
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
export const slotRefusal = (
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
export const coverOf = (
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
export const sliceSpec = (
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
export const picked = <O>(
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
export const slicedUnion = (
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
export const sliced = (
    codec: AnyCodec,
    pattern: unknown,
    keep: boolean,
): unknown => {
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
