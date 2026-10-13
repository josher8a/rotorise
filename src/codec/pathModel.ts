/*
 * **The selector of `at`, read from the term of a codec.** The walk of a path at the type level:
 * each segment steps each frame to its children (`StepFrames`), and the frontier names a decision
 * (`KindOfFrames`). Two frames are one frame where their types are equal (`FrameSame`), with no
 * depth: the term in a type carries no closure and no fill value, so equal data is equal types.
 *
 * A term is a tuple. `['scope', D, K]` is the entry `K` of the record `D` of the terms of a scope,
 * and `['var', N]` is a name of the scope that holds it. A frame is `[Term, Env]`: the type keeps
 * its own stack of scopes, head first, and `Lookup` resolves a name against the stack. A segment
 * is `['name', K]` or `['pos', I]`.
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
/**
 * An entry of a scope is the model's \`mu\` where the entry reaches its own name, and its definition
 * elsewhere: the emitter prints an entry that closes no cycle as its body. So the member of an
 * entry is \`none\` on a cycle, and the member of the definition otherwise.
 */
type MuSyn<T, Env = []> = T extends ['scope', infer D, infer K]
    ? MuSynEntry<D, K>
    : T extends ['var', infer N]
      ? Lookup<Env, N> extends ['some', unknown, [['scope', infer D]]]
          ? MuSynEntry<D, N>
          : 'none'
      : T extends ['prim', ['base', infer K]]
        ? KindMember<K>
        : T extends ['prim', ['literal', infer K, unknown]]
          ? KindMember<K>
          : T extends ['set', infer E]
            ? MuSyn<E, Env> extends 'none'
                ? 'none'
                : SetMember<MuSyn<E, Env>>
            : T extends ['list', unknown, unknown, unknown]
              ? 'L'
              : T extends ['held', unknown, infer I, unknown, unknown, unknown]
                ? MuSyn<I, Env>
                : T extends ['refine', infer I]
                  ? MuSyn<I, Env>
                  : T extends ['legacy', infer I]
                    ? MuSyn<I, Env>
                    : T extends ['object', unknown]
                      ? 'M'
                      : T extends ['union', infer Os]
                        ? Unanimous<MuSynList<Os, Env>>
                        : 'none'
type MuSynList<Os, Env> = Os extends [infer H, ...infer R]
    ? [MuSyn<H, Env>, ...MuSynList<R, Env>]
    : []
type MuSynEntry<D, K> = K extends Reached<D, VarsOf<D[K & keyof D]>, never>
    ? 'none'
    : MuSyn<D[K & keyof D], [['scope', D]]>
/** The names that a term reads and that no scope inside the term binds. */
type VarsOf<T> = T extends ['var', infer N]
    ? N
    : T extends ['scope', unknown, unknown]
      ? never
      : T extends readonly unknown[]
        ? VarsOf<T[number]>
        : T extends object
          ? VarsOf<T[keyof T]>
          : never
/** The names of \`D\` that the names \`New\` reach, through the definitions of \`D\`. */
type Reached<D, New, Seen> = [Exclude<New, Seen>] extends [never]
    ? Seen
    : Reached<
          D,
          VarsOf<D[Exclude<New, Seen> & keyof D]>,
          Seen | (New & keyof D)
      >
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
type ApartAt<S, T, Env> = MuSyn<T, Env> extends 'none'
    ? false
    : [MuSyn<T, Env>] extends [SegMember<S>]
      ? false
      : true
type ApartOr<S, T, Env> = ApartAt<S, T, Env> extends true ? Some<[]> : None

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
                  : ApartOr<S, T, Env>
              : T extends ['list', infer Pre, infer Sp, infer Suf]
                ? S extends ['pos', infer I]
                    ? ListChild<Pre, Sp, Suf, I> extends ['some', infer C]
                        ? Some<[Norm<C, Env>]>
                        : None
                    : ApartOr<S, T, Env>
                : ApartOr<S, T, Env>
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
 * options of its union, or itself, through names. The frames of the narrowed node are the options
 * that the clause keeps ({@link Separates}).
 */
type Resolved<
    T,
    Env extends unknown[],
    Fuel extends unknown[] = ScopeFuel,
> = Fuel extends [unknown, ...infer F2 extends unknown[]]
    ? T extends ['scope', infer D, infer K]
        ? Resolved<D[K & keyof D], [['scope', D]], F2>
        : T extends ['var', infer N]
          ? Lookup<Env, N> extends ['some', infer M, [['scope', infer D]]]
              ? Resolved<M, [['scope', D]], F2>
              : [T, Env]
          : [T, Env]
    : [T, Env]
type OptionsOf<F> = F extends [['union', infer Os extends unknown[]], infer Env]
    ? { [I in keyof Os]: [Os[I], Env] }
    : [F]

/*
 * **The graph decision of `narrow`, read on the terms**: the model's `Scoped.disjoint` at the
 * stored views of the clause and of an option, as `narrowAcross` reads it. The left operand is the
 * clause, and the right operand is the option. A `held` reads its inner term, an older reader reads
 * any attribute, and a `fallback` slot is optional. Below a guard a pair of entries is assumed apart
 * while the walk compares the two bodies: `A` holds the assumed pairs. `false` states nothing.
 * Two list shapes and the predicates of a refinement are not ported, and read as not apart.
 */
type GraphFuel = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/** An entry of a scope, as `['entry', D, K]` with its body and binder stack, or `None`. */
type EntryOf<T, Env> = T extends ['scope', infer D, infer K]
    ? ['some', ['entry', D, K], D[K & keyof D], [['scope', D]]]
    : T extends ['var', infer N]
      ? Lookup<Env, N> extends ['some', infer M, [['scope', infer D]]]
          ? ['some', ['entry', D, N], M, [['scope', D]]]
          : None
      : None
type Assumed<P, A> = A extends [infer Q, ...infer R]
    ? FrameSame<P, Q> extends true
        ? true
        : Assumed<P, R>
    : false
type ApartG<L, LE, R, RE, A extends unknown[], Fuel> = Fuel extends [
    unknown,
    ...infer F,
]
    ? RowG<L, LE, R, RE, A, F>
    : false
type RowG<L, LE, R, RE, A extends unknown[], F> = EntryOf<L, LE> extends [
    'some',
    unknown,
    infer M,
    infer ME,
]
    ? ApartG<M, ME, R, RE, A, F>
    : L extends ['var', unknown]
      ? RightG<L, LE, R, RE, A, F, ['none']>
      : L extends ['never']
        ? true
        : L extends
                | ['held', unknown, infer I, ...unknown[]]
                | ['refine', infer I]
          ? RowG<I, LE, R, RE, A, F>
          : L extends ['legacy', unknown] | ['opaq']
            ? RightG<L, LE, R, RE, A, F, ['none']>
            : L extends ['union', infer Os extends unknown[]]
              ? false extends {
                    [I in keyof Os]: RowG<Os[I], LE, R, RE, A, F>
                }[number]
                  ? false
                  : true
              : L extends ['prim', infer G]
                ? RightG<L, LE, R, RE, A, F, ['prim', G]>
                : L extends ['set', infer E]
                  ? RightG<L, LE, R, RE, A, F, ['set', E, LE]>
                  : L extends ['list', unknown, unknown, unknown]
                    ? RightG<L, LE, R, RE, A, F, ['list']>
                    : L extends ['object', ['mk', infer CF, infer CW]]
                      ? RightG<L, LE, R, RE, A, F, ['obj', CF, CW, LE]>
                      : false
/** The rows of the right operand alone (`rightRows`), then the family `Fam` of the left row. */
type RightG<L, LE, R, RE, A extends unknown[], F, Fam> = EntryOf<
    R,
    RE
> extends ['some', unknown, infer M, infer ME]
    ? ApartG<L, LE, M, ME, A, F>
    : R extends ['var', unknown]
      ? false
      : R extends ['never']
        ? true
        : R extends
                | ['held', unknown, infer I, ...unknown[]]
                | ['refine', infer I]
          ? RightG<L, LE, I, RE, A, F, Fam>
          : R extends ['union', infer Os extends unknown[]]
            ? false extends {
                  [I in keyof Os]: RightG<L, LE, Os[I], RE, A, F, Fam>
              }[number]
                ? false
                : true
            : FamG<Fam, R, RE, A, F>
type FamG<Fam, R, RE, A extends unknown[], F> = Fam extends ['prim', infer G]
    ? R extends ['prim', infer G2]
        ? PrimsApartT<G, G2>
        : R extends
                | ['set', unknown]
                | ['list', unknown, unknown, unknown]
                | ['object', unknown]
          ? true
          : false
    : Fam extends ['set', infer E, infer LE]
      ? R extends ['set', infer E2]
          ? ApartG<E, LE, E2, RE, [], F>
          : R extends
                  | ['prim', unknown]
                  | ['list', unknown, unknown, unknown]
                  | ['object', unknown]
            ? true
            : false
      : Fam extends ['list']
        ? R extends ['prim', unknown] | ['set', unknown] | ['object', unknown]
            ? true
            : false
        : Fam extends ['obj', infer CF, infer CW, infer LE]
          ? R extends ['object', ['mk', infer F2, infer W2]]
              ? true extends
                    | {
                          [K in keyof CF]: IsReqT<CF[K]> extends true
                              ? PairG<
                                    SlotTerm<CF[K]>,
                                    LE,
                                    SlotTerm<SlotAt<F2, W2, K>>,
                                    RE,
                                    A,
                                    F
                                >
                              : IsReqT<SlotAt<F2, W2, K>> extends true
                                ? PairG<
                                      SlotTerm<CF[K]>,
                                      LE,
                                      SlotTerm<SlotAt<F2, W2, K>>,
                                      RE,
                                      A,
                                      F
                                  >
                                : false
                      }[keyof CF]
                    | {
                          [K in keyof F2]: K extends keyof CF
                              ? false
                              : IsReqT<F2[K]> extends true
                                ? CW extends ['some', infer B]
                                    ? PairG<B, LE, SlotTerm<F2[K]>, RE, A, F>
                                    : true
                                : false
                      }[keyof F2]
                  ? true
                  : false
              : R extends
                      | ['prim', unknown]
                      | ['set', unknown]
                      | ['list', unknown, unknown, unknown]
                ? true
                : false
          : false
/** Whether a slot holds its name in the stored view: `req` only, as a `fallback` may lack it. */
type IsReqT<S> = S extends ['req', unknown] ? true : false
/** `pairAt`: a pair of entries already assumed is apart, and a new pair is assumed. */
type PairG<X, XE, Y, YE, A extends unknown[], F> = EntryOf<X, XE> extends [
    'some',
    infer I,
    infer XM,
    infer XME,
]
    ? EntryOf<Y, YE> extends ['some', infer J, infer YM, infer YME]
        ? Assumed<[I, J], A> extends true
            ? true
            : ApartG<XM, XME, YM, YME, [[I, J], ...A], F>
        : ApartG<X, XE, Y, YE, A, F>
    : ApartG<X, XE, Y, YE, A, F>
/** `primsApart`: two kinds, or two literals of one kind with two texts. Bytes are not compared. */
type PrimsApartT<G, G2> = G extends ['base' | 'literal', infer K, ...unknown[]]
    ? G2 extends ['base' | 'literal', infer K2, ...unknown[]]
        ? [K] extends [K2]
            ? [K2] extends [K]
                ? G extends ['literal', unknown, infer V]
                    ? G2 extends ['literal', unknown, infer V2]
                        ? K extends 'binary'
                            ? false
                            : FrameSame<V, V2> extends true
                              ? false
                              : true
                        : false
                    : false
                : true
            : true
        : false
    : false
/** The clause as a term: each key required at the term of its codec, and an opaque block. */
type ClauseT<CT> = [
    'object',
    ['mk', { [K in keyof CT]: ['req', CT[K]] }, ['some', ['opaq']]],
]

/** Whether the clause separates an option. `CT` holds the term of the codec at each key. */
type Separates<H, CT> = H extends [infer T0, infer E0 extends unknown[]]
    ? ApartG<ClauseT<CT>, [], T0, E0, [], GraphFuel>
    : false
type KeptOptions<Hs, CT> = Hs extends [infer H, ...infer R]
    ? Separates<H, CT> extends true
        ? KeptOptions<R, CT>
        : [H, ...KeptOptions<R, CT>]
    : []

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
    ? [...KeptOptions<OptionsOf<Resolved<T, Env>>, CT>, ...NarrowEach<R, CT>]
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
                      ? Unbound<OptionsOf<Resolved<T, Env>>[number]>
                      : never
              }[number],
              [['var', unknown], unknown]
          >,
      ] extends [never]
        ? false
        : true
    : true

/** An option that is a variable that no binder of its stack binds. */
type Unbound<O> = O extends [['var', infer N], infer Env]
    ? Lookup<Env, N> extends ['some', unknown, unknown]
        ? never
        : O
    : never
