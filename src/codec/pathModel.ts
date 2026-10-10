/*
 * **The selector of `at`, read from the term of a codec.** The closure of `Alg.Term.at`
 * (`formal/Calculus/Lang/Path.lean`) and of `pathKind` (`formal/Calculus/Bridge/Paths.lean`),
 * translated to types. The comparator is `frameSame` as an exact type equality, with no depth: the
 * term in a type carries no closure and no fill value, so equal data is equal types.
 *
 * A term is a tuple. `['scope', D, K]` is the entry `K` of the record `D` of the terms of a scope,
 * and `['var', N]` is a name of the scope that holds it. A frame is `[Term, Env]`, the binder
 * stack head first. A segment is `['name', K]` or `['pos', I]`.
 */
import type { DynamoNumber as DynamoNumberOf } from './attribute'

type Some<X> = ['some', X]
type None = ['none']

// ── μSyn (Lang/Typing.lean) at DynamoDB ──
type KindMember<K> = K extends 'string'
    ? 'S'
    : K extends 'number'
      ? 'N'
      : K extends 'boolean'
        ? 'BOOL'
        : K extends 'binary'
          ? 'B'
          : 'NULL'
type SetMember<M> = M extends 'S'
    ? 'SS'
    : M extends 'N'
      ? 'NS'
      : M extends 'B'
        ? 'BS'
        : 'none'
type MuSyn<T> = T extends ['prim', ['base', infer K]]
    ? KindMember<K>
    : T extends ['prim', ['literal', infer K, unknown]]
      ? KindMember<K>
      : T extends ['set', infer E]
        ? MuSyn<E> extends 'none'
            ? 'none'
            : SetMember<MuSyn<E>>
        : T extends ['list', unknown, unknown, unknown]
          ? 'L'
          : T extends ['held', unknown, infer I, unknown, unknown, unknown]
            ? MuSyn<I>
            : T extends ['refine', infer I]
              ? MuSyn<I>
              : T extends ['legacy', infer I]
                ? MuSyn<I>
                : T extends ['object', unknown]
                  ? 'M'
                  : T extends ['union', infer Os]
                    ? Unanimous<MuSynList<Os>>
                    : 'none'
type MuSynList<Os> = Os extends [infer H, ...infer R]
    ? [MuSyn<H>, ...MuSynList<R>]
    : []
/** `unanimous`: the first member when every member equals it (`none` included), else `none`. */
type Unanimous<L> = L extends [infer H, ...infer R]
    ? AllEq<R, H> extends true
        ? H
        : 'none'
    : 'none'
type AllEq<R, H> = R extends [infer X, ...infer Rs]
    ? [X] extends [H]
        ? [H] extends [X]
            ? AllEq<Rs, H>
            : false
        : false
    : true

// ── the segment, and the store's refusal (`Seg.member`, `apartAt`) ──
type SegMember<S> = S extends ['name', unknown] ? 'M' : 'L'
type ApartAt<S, T> = MuSyn<T> extends 'none'
    ? false
    : [MuSyn<T>] extends [SegMember<S>]
      ? false
      : true
type ApartOr<S, T> = ApartAt<S, T> extends true ? Some<[]> : None

// ── the body (`Body.block`, `Body.slotAt`, `ObjectSlot.term`) ──
type Block<W> = W extends ['some', infer T] ? T : ['never']
type SlotAt<F, W, N> = N extends keyof F ? F[N] : ['optional', Block<W>]
type SlotTerm<S> = S extends
    | ['req', infer T]
    | ['optional', infer T]
    | ['fill', infer T]
    ? T
    : never

// ── `listChild` ──
type At<L, I, C extends unknown[] = []> = L extends [infer H, ...infer R]
    ? C['length'] extends I
        ? Some<H>
        : At<R, I, [...C, 0]>
    : None
type ListChild<Pre, Sp, Suf, I> = At<Pre, I> extends ['some', infer T]
    ? Some<T>
    : Suf extends []
      ? Sp extends ['some', infer T]
          ? Some<T>
          : Some<['never']>
      : None

/**
 * The binder of the name `N` in the stack, and the stack under it (`env[i]?`, `env.drop (i + 1)`).
 * A scope `['scope', D]` binds each name of the record `D`. The name `N` reads the definition
 * `D[N]`, by one lookup in `D`, under the scope alone: a scope is closed.
 */
type Lookup<Env, N> = Env extends [infer H, ...infer R]
    ? H extends ['scope', infer D]
        ? // a record with an index signature is the erased scope, and binds no name
          string extends keyof D
            ? Lookup<R, N>
            : N extends keyof D
              ? ['some', D[N], [['scope', D]]]
              : Lookup<R, N>
        : Lookup<R, N>
    : None

/**
 * The fuel of a chain of names in a scope. A term enters a scope with this fuel, and a scope holds
 * no term of itself, so the reset ends.
 */
type ScopeFuel = [0, 0, 0, 0, 0, 0, 0, 0]
type FuelOf<Env extends unknown[]> = Env extends [['scope', unknown]]
    ? ScopeFuel
    : [...Env, 0]

/**
 * **One frame for one entry.** An entry of a scope, or a variable that a scope binds, is the frame
 * of the definition of the entry, under the scope alone. So two paths to one entry give one frame,
 * as two paths to one term object give one term.
 */
type Norm<T, Env, Fuel extends unknown[] = ScopeFuel> = Fuel extends [
    unknown,
    ...infer F2,
]
    ? T extends ['scope', infer D, infer K]
        ? Norm<D[K & keyof D], [['scope', D]], F2>
        : T extends ['var', infer N]
          ? Lookup<Env, N> extends ['some', infer M, [['scope', infer D]]]
              ? Norm<M, [['scope', D]], F2>
              : [T, Env]
          : [T, Env]
    : [T, Env]

// ── `childD`, `childDL`, `childN`, `Frame.child` ──
type ChildD<S, Env extends unknown[], T, Fuel extends unknown[]> = T extends [
    'never',
]
    ? Some<[]>
    : T extends ['opaq']
      ? Some<[[T, Env]]>
      : T extends ['scope', infer D, infer K]
        ? ChildD<S, [['scope', D]], D[K & keyof D], ScopeFuel>
        : T extends ['var', infer N]
          ? Lookup<Env, N> extends [
                'some',
                infer M,
                infer Rest extends unknown[],
            ]
              ? ChildN<Fuel, S, M, Rest>
              : Some<[]>
          : T extends ['union', infer Os]
            ? ChildDL<S, Env, Os, Fuel>
            : T extends ['object', ['mk', infer F, infer W]]
              ? S extends ['name', infer N]
                  ? Some<[Norm<SlotTerm<SlotAt<F, W, N>>, Env>]>
                  : ApartOr<S, T>
              : T extends ['list', infer Pre, infer Sp, infer Suf]
                ? S extends ['pos', infer I]
                    ? ListChild<Pre, Sp, Suf, I> extends ['some', infer C]
                        ? Some<[Norm<C, Env>]>
                        : None
                    : ApartOr<S, T>
                : ApartOr<S, T>
type ChildDL<
    S,
    Env extends unknown[],
    Os,
    Fuel extends unknown[],
> = Os extends [infer H, ...infer R]
    ? ChildD<S, Env, H, Fuel> extends ['some', infer A extends unknown[]]
        ? ChildDL<S, Env, R, Fuel> extends ['some', infer B extends unknown[]]
            ? Some<[...A, ...B]>
            : None
        : None
    : Some<[]>
type ChildN<
    Fuel extends unknown[],
    S,
    T,
    Env extends unknown[],
> = Fuel extends [unknown, ...infer F2] ? ChildD<S, Env, T, F2> : None
type FrameChild<S, F> = F extends [infer T, infer Env extends unknown[]]
    ? ChildN<FuelOf<Env>, S, T, Env>
    : None

// ── `Term.at`, one segment ──
type MapChild<S, Fs> = Fs extends [infer F, ...infer R]
    ? FrameChild<S, F> extends ['some', infer A extends unknown[]]
        ? MapChild<S, R> extends ['some', infer B extends unknown[]]
            ? Some<[...A, ...B]>
            : None
        : None
    : Some<[]>
// ── `pathHead`, `frameNever` ──
type PathHead<Fuel extends unknown[], F> = Fuel extends [unknown, ...infer F2]
    ? F extends [['scope', infer D, infer K], unknown]
        ? PathHead<F2, [D[K & keyof D], [['scope', D]]]>
        : F extends [['var', infer N], infer Env]
          ? Lookup<Env, N> extends ['some', infer M, infer Rest]
              ? PathHead<F2, [M, Rest]>
              : F
          : F
    : F
type Head<F> = F extends [unknown, infer Env extends unknown[]]
    ? PathHead<[...Env, 0, 0], F>
    : F
type FrameNever<F> = Head<F> extends [['never'], unknown] ? true : false

/** `frameSame`: one datum at each position, as an exact type equality. */
type FrameSame<F, G> = (<X>() => X extends F ? 1 : 2) extends <
    X,
>() => X extends G ? 1 : 2
    ? true
    : false

type AllNever<Fs> = Fs extends [infer F, ...infer R]
    ? FrameNever<F> extends true
        ? AllNever<R>
        : false
    : true
type AnyNever<Fs> = Fs extends [infer F, ...infer R]
    ? FrameNever<F> extends true
        ? true
        : AnyNever<R>
    : false
type AllSame<F, Fs> = Fs extends [infer G, ...infer R]
    ? FrameSame<F, G> extends true
        ? AllSame<F, R>
        : false
    : true

/*
 * A node of the selector holds the frames of `Term.at` at its path, or `'refused'` where the store
 * refuses the path. The node offers a name that some head declares, an open name where a head
 * holds a rest or an opaque term, and a position where a head is a list. The decision at the node
 * is `pathKind` of its frames.
 */

/** The frames one segment down, or `'refused'`. */
export type StepFrames<S, Fs> = Fs extends unknown[]
    ? MapChild<S, Fs> extends ['some', infer G]
        ? G
        : 'refused'
    : 'refused'

/** `pathKind` of the frames of a node. */
export type KindOfFrames<Fs> = Fs extends [infer F, ...infer R]
    ? AnyNever<Fs> extends true
        ? AllNever<Fs> extends true
            ? 'vacant'
            : 'someVariants'
        : AllSame<F, R> extends true
          ? 'resolved'
          : 'ambiguous'
    : Fs extends []
      ? 'vacant'
      : 'refused'

/**
 * What a frame offers one step down: `['name', K]` for the names that a head declares, `['open']`
 * where a head holds a rest or is opaque, and `['pos']` where a head is a list or is opaque.
 */
type OffersD<Env extends unknown[], T, Fuel extends unknown[]> = T extends [
    'opaq',
]
    ? ['open'] | ['pos']
    : T extends ['scope', infer D, infer K]
      ? OffersD<[['scope', D]], D[K & keyof D], ScopeFuel>
      : T extends ['var', infer N]
        ? Lookup<Env, N> extends ['some', infer M, infer Rest extends unknown[]]
            ? Fuel extends [unknown, ...infer F2]
                ? OffersD<Rest, M, F2>
                : never
            : never
        : T extends ['union', infer Os extends unknown[]]
          ? { [I in keyof Os]: OffersD<Env, Os[I], Fuel> }[number]
          : T extends ['object', ['mk', infer F, infer W]]
            ?
                  | ['name', keyof F & string]
                  | (W extends ['some', unknown] ? ['open'] : never)
            : T extends ['list', unknown, unknown, unknown]
              ? ['pos']
              : never
export type OffersAt<Fs> = Fs extends unknown[]
    ? {
          [I in keyof Fs]: Fs[I] extends [infer T, infer Env extends unknown[]]
              ? OffersD<Env, T, FuelOf<Env>>
              : never
      }[number]
    : never

/** The first frame of a node: the frame that a resolved path reads. */
export type FirstFrame<Fs> = Fs extends [infer F, ...unknown[]] ? F : never

type Opt<S> = S extends ['optional', unknown] ? true : false
type FloatOf<S> = S extends `${infer N extends number}` ? N : number
type DecodeLit<K, V> = K extends 'string'
    ? V
    : K extends 'number'
      ? V extends string
          ? DynamoNumberOf<V>
          : never
      : K extends 'boolean'
        ? V
        : K extends 'binary'
          ? Uint8Array
          : null
type DecodeBase<K> = K extends 'string'
    ? string
    : K extends 'number'
      ? DynamoNumberOf<string>
      : K extends 'boolean'
        ? boolean
        : K extends 'binary'
          ? Uint8Array
          : null
type FloatLits<T> = T extends ['prim', ['literal', 'number', infer S]]
    ? FloatOf<S>
    : T extends ['union', infer Os extends unknown[]]
      ? { [I in keyof Os]: FloatLits<Os[I]> }[number]
      : number

/**
 * The decoded type of the codec at a frame, as a function of the term. An adapter of a caller
 * decodes to the decoded type of its outer term. A refinement decodes to the decoded type of its
 * inner term, because the term carries no predicate type.
 */
export type DecodeFrame<F> = F extends [infer T, infer Env extends unknown[]]
    ? DecodeT<T, Env>
    : never
/** The decoded type of a closed term, as of an entry of a scope. */
export type DecodeTerm<T> = DecodeT<T, []>
/*
 * `Fuel` bounds a chain of names with no list and no object between them. A guarded recursion
 * resets the fuel at its container, where the decoded type is lazy. An unguarded scope, which the
 * run time refuses, decodes to `never` and does not recurse without end.
 */
type DecodeT<
    T,
    Env extends unknown[],
    Fuel extends unknown[] = ScopeFuel,
> = T extends ['prim', ['base', infer K]]
    ? DecodeBase<K>
    : T extends ['prim', ['literal', infer K, infer V]]
      ? DecodeLit<K, V>
      : T extends ['never']
        ? never
        : T extends ['opaq']
          ? unknown
          : T extends ['scope', infer D, infer K]
            ? DecodeT<D[K & keyof D], [['scope', D]], Fuel>
            : T extends ['var', infer N]
              ? Lookup<Env, N> extends [
                    'some',
                    infer M,
                    infer Rest extends unknown[],
                ]
                  ? Fuel extends [unknown, ...infer F2 extends unknown[]]
                      ? DecodeT<M, Rest, F2>
                      : never
                  : unknown
              : T extends ['set', infer E]
                ? ReadonlySet<DecodeT<E, Env, Fuel>>
                : T extends ['union', infer Os extends unknown[]]
                  ? { [I in keyof Os]: DecodeT<Os[I], Env, Fuel> }[number]
                  : T extends [
                          'held',
                          unknown,
                          infer I,
                          infer O,
                          [infer G, unknown],
                          unknown,
                      ]
                    ? G extends ['caller', 'asFloat']
                        ? FloatLits<I>
                        : G extends ['caller', 'opaqueLossy' | 'opaqueRefuse']
                          ? unknown
                          : DecodeT<O, Env, Fuel>
                    : T extends ['refine', infer I]
                      ? DecodeT<I, Env, Fuel>
                      : T extends ['legacy', infer I]
                        ? DecodeT<I, Env, Fuel>
                        : T extends [
                                'list',
                                infer Pre extends unknown[],
                                infer Sp,
                                infer Suf extends unknown[],
                            ]
                          ? DecodeList<Pre, Sp, Suf, Env>
                          : T extends ['object', ['mk', infer Fd, infer W]]
                            ? DecodeObject<Fd, W, Env>
                            : unknown
type DecodeList<
    Pre extends unknown[],
    Sp,
    Suf extends unknown[],
    Env extends unknown[],
> = Sp extends ['some', infer E]
    ? Pre extends []
        ? Suf extends []
            ? readonly DecodeT<E, Env>[]
            : readonly [
                  ...DecodeTuple<Pre, Env>,
                  ...DecodeT<E, Env>[],
                  ...DecodeTuple<Suf, Env>,
              ]
        : readonly [
              ...DecodeTuple<Pre, Env>,
              ...DecodeT<E, Env>[],
              ...DecodeTuple<Suf, Env>,
          ]
    : readonly [...DecodeTuple<Pre, Env>]
type DecodeTuple<L extends unknown[], Env extends unknown[]> = {
    [I in keyof L]: DecodeT<L[I], Env>
}
/*
 * An empty half is no `{}`. A `{}` in the intersection makes an object of optional names
 * no weak type, and a weak type is what keeps two members of a union apart.
 */
type ReqNames<Fd> = {
    [K in keyof Fd]: Opt<Fd[K]> extends true ? never : K
}[keyof Fd]
type OptNames<Fd> = {
    [K in keyof Fd]: Opt<Fd[K]> extends true ? K : never
}[keyof Fd]
type DecodeObject<Fd, W, Env extends unknown[]> = ([ReqNames<Fd>] extends [
    never,
]
    ? [OptNames<Fd>] extends [never]
        ? Record<never, never>
        : unknown
    : { readonly [K in ReqNames<Fd>]: DecodeT<SlotTerm<Fd[K]>, Env> }) &
    ([OptNames<Fd>] extends [never]
        ? unknown
        : { readonly [K in OptNames<Fd>]?: DecodeT<SlotTerm<Fd[K]>, Env> }) &
    (W extends ['some', infer R]
        ? { readonly [name: string]: DecodeT<R, Env> }
        : unknown)

/*
 * **The clause of `narrow`, read on the terms**, as the walk of `at` reads it. A frame gives the
 * options of its union, or itself, through names. The clause separates an option where the stored
 * views of the two are disjoint: the option stores no map, a required slot of the option stores
 * nothing, or at one key of the clause the slot and the codec of the clause store no common
 * attribute. A union is separated where each of its options is, and an adapter where its inner
 * term is. The frames of the narrowed node are the options that the clause keeps.
 *
 * `Seen` holds each entry that the walk resolved from the option down. An entry that the walk
 * reaches again is the variable of a recursion, which the model's disjointness separates from the
 * bottom alone, so the walk reads it as `['again']`: any stored attribute.
 */
type Resolved<
    T,
    Env extends unknown[],
    Seen,
    Fuel extends unknown[] = ScopeFuel,
> = Fuel extends [unknown, ...infer F2 extends unknown[]]
    ? T extends ['scope', infer D, infer K]
        ? [['entry', D, K]] extends [Seen]
            ? [['again'], Env, Seen]
            : Resolved<
                  D[K & keyof D],
                  [['scope', D]],
                  Seen | ['entry', D, K],
                  F2
              >
        : T extends ['var', infer N]
          ? Lookup<Env, N> extends ['some', infer M, [['scope', infer D]]]
              ? [['entry', D, N]] extends [Seen]
                  ? [['again'], Env, Seen]
                  : Resolved<M, [['scope', D]], Seen | ['entry', D, N], F2>
              : [T, Env, Seen]
          : [T, Env, Seen]
    : [T, Env, Seen]
type OptionsOf<F> = F extends [
    ['union', infer Os extends unknown[]],
    infer Env,
    infer Seen,
]
    ? { [I in keyof Os]: [Os[I], Env, Seen] }
    : [F]

/** Every member of DynamoDB: what an opaque term, a free term or an older reader can store. */
type AnyMember =
    | 'S'
    | 'N'
    | 'B'
    | 'BOOL'
    | 'NULL'
    | 'M'
    | 'L'
    | 'SS'
    | 'NS'
    | 'BS'

/** The members of DynamoDB that a term can store. An older reader reads any stored attribute. */
type WritesT<T, Env extends unknown[], Seen = never> = Resolved<
    T,
    Env,
    Seen
> extends [infer U, infer E extends unknown[], infer S]
    ? U extends ['prim', ['base' | 'literal', infer K, ...unknown[]]]
        ? KindMember<K>
        : U extends ['set', infer El]
          ? SetMember<MuSyn<El>>
          : U extends ['list', unknown, unknown, unknown]
            ? 'L'
            : U extends ['object', unknown]
              ? 'M'
              : U extends ['never']
                ? never
                : U extends
                        | ['held', unknown, infer I, ...unknown[]]
                        | ['refine', infer I]
                  ? WritesT<I, E, S>
                  : U extends ['union', infer Os extends unknown[]]
                    ? { [I in keyof Os]: WritesT<Os[I], E, S> }[number]
                    : AnyMember
    : AnyMember

/**
 * The stored texts that a term pins, as `['pin', texts]`, or `['unpinned']` where the term
 * stores a value that no literal pins.
 */
type PinsT<T, Env extends unknown[], Seen = never> = Resolved<
    T,
    Env,
    Seen
> extends [infer U, infer E extends unknown[], infer S]
    ? U extends ['prim', ['literal', infer K, infer V]]
        ? K extends 'binary'
            ? ['unpinned']
            : ['pin', `${V & (string | number | boolean)}`]
        : U extends
                | ['held', unknown, infer I, ...unknown[]]
                | ['refine', infer I]
          ? PinsT<I, E, S>
          : U extends ['union', infer Os extends unknown[]]
            ? PinsOfAll<{ [I in keyof Os]: PinsT<Os[I], E, S> }>
            : ['unpinned']
    : ['unpinned']
type PinsOfAll<Ps extends unknown[]> = ['unpinned'] extends Ps[number]
    ? ['unpinned']
    : ['pin', Extract<Ps[number], ['pin', unknown]>[1]]

/** Two terms that store no common attribute: no common member, or two pins with no common text. */
type ApartT<X, Env extends unknown[], Seen, Y> = [
    WritesT<X, Env, Seen> & WritesT<Y, []>,
] extends [never]
    ? true
    : PinsT<X, Env, Seen> extends ['pin', infer A]
      ? PinsT<Y, []> extends ['pin', infer B]
          ? [A & B] extends [never]
              ? true
              : false
          : false
      : false

/** Whether the clause separates an option. `CT` holds the term of the codec at each key. */
type Separates<H, CT> = H extends [
    infer T0,
    infer E0 extends unknown[],
    infer S0,
]
    ? Resolved<T0, E0, S0> extends [
          infer T,
          infer Env extends unknown[],
          infer Seen,
      ]
        ? T extends ['object', ['mk', infer F, infer W]]
            ? true extends
                  | {
                        [K in keyof CT]: ApartT<
                            SlotTerm<SlotAt<F, W, K>>,
                            Env,
                            Seen,
                            CT[K]
                        >
                    }[keyof CT]
                  | {
                        [K in keyof F]: F[K] extends ['req', infer S]
                            ? [WritesT<S, Env, Seen>] extends [never]
                                ? true
                                : false
                            : false
                    }[keyof F]
                ? true
                : false
            : T extends ['union', infer Os extends unknown[]]
              ? false extends {
                    [I in keyof Os]: Separates<[Os[I], Env, Seen], CT>
                }[number]
                  ? false
                  : true
              : T extends
                      | ['held', unknown, infer I, ...unknown[]]
                      | ['refine', infer I]
                ? Separates<[I, Env, Seen], CT>
                : 'M' extends WritesT<T, Env, Seen>
                  ? false
                  : true
        : false
    : false
type KeptOptions<Hs, CT> = Hs extends [infer H, ...infer R]
    ? Separates<H, CT> extends true
        ? KeptOptions<R, CT>
        : [Frame<H>, ...KeptOptions<R, CT>]
    : []
/** The frame of an option: its term and its binder stack. */
type Frame<H> = H extends [infer T, infer Env, unknown] ? [T, Env] : never

/**
 * The frames of a node after `narrow`, or `'refused'`: the options that the clause keeps, each one
 * a frame, as the walk of `at` carries each kept option as one codec.
 */
export type NarrowFrames<Fs, CT> = Fs extends unknown[]
    ? NarrowEach<Fs, CT>
    : 'refused'
type NarrowEach<Fs, CT> = Fs extends [
    [infer T, infer Env extends unknown[]],
    ...infer R,
]
    ? [
          ...KeptOptions<OptionsOf<Resolved<T, Env, never>>, CT>,
          ...NarrowEach<R, CT>,
      ]
    : []

/**
 * Whether an option of the frames is a free variable: a codec whose type carries no term, which a
 * clause cannot read.
 */
export type HoldsFree<Fs> = Fs extends unknown[]
    ? [
          Extract<
              {
                  [I in keyof Fs]: Fs[I] extends [
                      infer T,
                      infer Env extends unknown[],
                  ]
                      ? OptionsOf<Resolved<T, Env, never>>[number]
                      : never
              }[number],
              [['var', unknown], unknown, unknown]
          >,
      ] extends [never]
        ? false
        : true
    : true
