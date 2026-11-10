import type { AnyCodec, Marks, ObjectSlot } from './build'
import { opened } from './clause'
import { termOf } from './denote'
import type { InexactValue, IsUnion, UnionToIntersection } from './derivedItem'
import { fieldOf } from './derivedItem'
import { optional, undefinable } from './objects'
import type {
    Block,
    HoldsNoValue,
    NodeOf,
    Norm,
    OpenT,
    Same,
    SlotAt,
} from './pathModel'
import { never } from './prisms'
import { setOwn } from './result'
import type {
    Body,
    Field,
    LiteralValue,
    NameForm,
    ObjectTermOf,
    Order,
    RefSlot,
    SlotOf,
    Term,
    TermOf,
} from './term'
import {
    absentBelow,
    clauseForm,
    holdsNoValue,
    resolvedTerm,
    sameAdapter,
} from './term'
import { own, sameLiteral } from './value'

export type IsRefine<N> = N extends ['refine', ...unknown[]] ? true : false

/**
 * **How a meet reads one side.** `written` reads the side as declared, so a closed object holds no
 * undeclared name. `open` reads the opening of the side: a closed object holds each undeclared name
 * at `opaque`, and a declared open block stays. The composition reads both sides open, as TypeScript
 * reads `A & B`. The order {@link fits} reads the option as written and the pattern open.
 */
export type MeetReading = 'written' | 'open'

/** The reading of each side of a meet, the left side first. */
export type MeetReadings = readonly [MeetReading, MeetReading]

/** Both sides as declared: the reading of {@link below}, whose pattern side is an opened term. */
export const asWritten: MeetReadings = ['written', 'written']

/** The reading of the composition: both sides open, at the `relation` order. */
export const asComposed: MeetReadings = ['open', 'open']

/** The reading of the order and of the overlap: the option as written, the pattern open. */
export const asOrdered: MeetReadings = ['written', 'open']

/**
 * **The state of one meet**: the reading of each side, and the pairs of nodes on the path of the
 * walk, each with the slot of the `ref` that names the meet of the pair.
 */
export type MeetWalk = {
    readonly readings: MeetReadings
    readonly order: Order
    readonly entered: Map<Term, Map<Term, RefSlot>>
}

export const walkAt = (readings: MeetReadings, order: Order): MeetWalk => ({
    readings,
    order,
    entered: new Map(),
})

/** The term that admits every value: the open block of a closed object read open. */
export const opaqueTerm: Term = { kind: 'opaq' }

/**
 * The open block of an object as a term, at a reading. A declared block stays. A closed object
 * holds the bottom as written and `opaque` read open.
 */
export const blockOf = (body: Body, reading: MeetReading): Term =>
    body.rest ?? (reading === 'open' ? opaqueTerm : never.def)

/**
 * **The alignment of two objects**, as the model's `objK` aligns them: each name that either side
 * declares, with the slot of each side there. A side that does not declare the name holds it as an
 * optional slot at its open block, read at the reading of that side (`slotAtG` reads the written
 * side). The two blocks are the last pair, which the reader takes from {@link blockOf}.
 */
export const aligned = (
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
 * The keys of a union as a tuple. The order is the order that the checker gives, which no reader
 * relies on: each key splits one object field, and the decoded type is a union.
 */
export type KeyTuple<U, Last = LastOf<U>> = [U] extends [never]
    ? []
    : [...KeyTuple<Exclude<U, Last>>, Last]
export type LastOf<U> = UnionToIntersection<
    U extends unknown ? () => U : never
> extends () => infer R
    ? R
    : never

/**
 * The most parts that the fit reads from one term, as a tuple of that length ({@link JoinParts}).
 * The run time bounds the parts at 1024 ({@link PARTS_LIMIT}), and the type bounds them at 64. A
 * term whose parts reach the bound has the fit `'u'`, so the slice keeps the option.
 */
export type PartsCap = Repeat<64>
export type Repeat<
    N extends number,
    T extends readonly unknown[] = [],
> = T['length'] extends N ? T : Repeat<N, [...T, unknown]>

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
export type Fit = 't' | 'f' | 'u'
export type FitsCodec<A, P> = BelowT<
    TermOf<Marks<A>>,
    OpenT<TermOf<Marks<P>>>,
    [],
    [],
    []
>
/** The most pairs that the walk of {@link BelowT} enters on one path, as a tuple of that length. */
export type BelowDepth = Repeat<16>
/**
 * **The order `below` of the run time on terms**, three-valued. `A` is the term of the option and
 * `P` the term of the pattern, each under its own scope (`EA`, `EP`). `Seen` holds the pairs that the
 * walk entered at a name step on the path, and such a pair is below, as the order is the greatest
 * fixed point of its rules. The caller opens the pattern with {@link OpenT}, as the run time opens it.
 */
export type BelowT<A, P, EA, EP, Seen extends readonly unknown[]> = [
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
export type IsRef<T> = T extends ['ref', unknown] | ['scope', unknown, unknown]
    ? true
    : false
/**
 * The key of a node in `Seen`: the name as written with the scope that it resolved under, or the
 * node where the term is no name. A cycle passes through a name, so the walk records a pair at a
 * name step only, and two names compare by their text and scope, not by the terms that they resolve
 * to.
 */
export type RefKey<T, N, E> = IsRef<T> extends true ? [T, E] : N
/**
 * The rules at two nodes, and `'u'` for the pair of one term where the rules give `'f'`. The run
 * time answers `true` for one object, so two codecs built apart read by the rules, and the same
 * codec reads `true`. The type cannot tell the two cases apart.
 */
export type BelowStep<NA, NP, EA, EP, Seen extends readonly unknown[]> = BelowN<
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
export type SeenPair<
    Seen extends readonly unknown[],
    A,
    P,
> = Seen extends readonly [
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
export type BelowN<
    A,
    P,
    EA,
    EP,
    Seen extends readonly unknown[],
> = HoldsNoValue<A, EA> extends true
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
export type SomeOf<U extends Fit> = 't' extends U
    ? 't'
    : 'u' extends U
      ? 'u'
      : 'f'
export type AllOf<U extends Fit> = 'f' extends U
    ? 'f'
    : 'u' extends U
      ? 'u'
      : 't'
/**
 * **The form that a literal names**, as {@link clauseForm} reads it: the adapters that it sits
 * under and the base and value of the literal, or `never`. An adapter whose held side is `opaque`
 * names no form.
 */
export type ClauseOf<N, Tags extends readonly unknown[] = []> = N extends [
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
export type BelowClause<A, P> = ClauseOf<A> extends [
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
export type SameTags<A, B> = Same<A, B> extends true
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
export type BelowShape<
    A,
    P,
    EA,
    EP,
    Seen extends readonly unknown[],
> = P extends ['object', ['mk', infer PF, infer PW]]
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
export type BelowSlot<M, W, EA, EP, Seen extends readonly unknown[]> = [
    M,
    W,
] extends [
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
export type SlotMarkOf<F> = SlotOf<F> extends [infer M extends string, unknown]
    ? M extends 'fill'
        ? 'req'
        : M
    : never
export type AbsentBelow<M extends string, W extends string> = W extends 'req'
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
export type BelowList<
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
export type PatternNodes<Ps extends readonly unknown[], EP> = {
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
export type JoinParts<A, Ps, EP> = A extends [
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
export type FlatParts<
    Os extends readonly unknown[],
    Ps,
    EP,
> = Os extends readonly [infer H, ...infer R extends readonly unknown[]]
    ? JoinParts<H, Ps, EP> extends infer HP extends readonly unknown[]
        ? FlatParts<R, Ps, EP> extends infer RP extends readonly unknown[]
            ? Capped<[...HP, ...RP]>
            : 'over'
        : 'over'
    : []
export type Capped<T extends readonly unknown[]> = T extends readonly [
    ...PartsCap,
    ...unknown[],
]
    ? 'over'
    : T
export type ObjectParts<
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
export type CrossFields<
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
export type PresenceSlots<M, Parts extends readonly unknown[]> = M extends
    | 'optional'
    | 'undefinable'
    ? [[M, ['never']], ...{ [I in keyof Parts]: ['req', Parts[I]] }]
    : { [I in keyof Parts]: [M, Parts[I]] }
/** The nodes at the name `K` in the slots of the object options. */
export type PatternSlotNodes<Ps, K, EP> = Ps extends [
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
export type PatternElems<Ps, EP> = Ps extends [
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
export type ListParts<
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
export type PositionRows<
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
export type CrossRows<
    Rows extends readonly unknown[],
    Parts extends readonly unknown[],
> = Rows extends readonly [
    infer Row extends readonly unknown[],
    ...infer Rest extends readonly unknown[],
]
    ? [...{ [I in keyof Parts]: [...Row, Parts[I]] }, ...CrossRows<Rest, Parts>]
    : []
export type CrossLists<
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

export type SpecTerm<S> = ObjectTermOf<S, undefined>
/** The term of the member specs of a pattern: one object, or the union of the objects. */
export type SpecsTerm<P> = true extends IsUnion<P>
    ? ['union', SpecTerms<KeyTuple<P>>]
    : SpecTerm<P>
export type SpecTerms<Ps extends readonly unknown[]> = {
    [I in keyof Ps]: SpecTerm<Ps[I]>
}
/** Whether a member spec fits the member specs of a pattern: the fit of the closed object at the opened pattern. */
export type EveryFits<A, P> = BelowT<
    SpecTerm<A>,
    OpenT<SpecsTerm<P>>,
    [],
    [],
    []
>
/** Whether a member spec fits a pattern codec: the pattern must hold objects. */
export type FitsSpec<A, P> = BelowT<
    SpecTerm<A>,
    OpenT<TermOf<Marks<P>>>,
    [],
    [],
    []
>

/** Whether the extraction (`Keep` true) or the exclusion keeps a codec with this fit. */
export type KeepsFit<Keep extends boolean, F extends Fit> = Keep extends true
    ? F extends 'f'
        ? false
        : true
    : F extends 't'
      ? false
      : true

/**
 * **Two literals of one form**: the same base, and the same adapter, or none on either. This is the
 * form of the model's pin (`Calculus.pinForm`), the adapter word and the base.
 */
export const sameForm = (a: NameForm, b: NameForm): boolean =>
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
export const below = (
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
export const presenceParts = (
    field: Field,
): { readonly absent?: Field; readonly present: Field } =>
    field.mark === 'optional' || field.mark === 'undefinable'
        ? {
              absent: { mark: field.mark, t: { kind: 'never' } },
              present: { mark: 'req', t: field.t },
          }
        : { present: field }

/** The codec `held` under the presence mark that {@link presenceParts} splits: `undefinable` keeps the key. */
export const underMark = (mark: Field['mark'], held: AnyCodec) =>
    mark === 'undefinable' ? undefinable(held) : optional(held)

/**
 * The most parts that {@link joinParts} builds for one term. A term past the limit stays one part,
 * and `fits` errs towards no fit. The limit refuses, and the reason is the size: the parts of an
 * object are a product of the parts of its fields, so `n` boolean fields give `2^n` parts, and the
 * union rule walks each part against each option of the pattern.
 */
export const PARTS_LIMIT = 1024

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
export const joinParts = (t: Term): Term[] => {
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
export const fitsNode = (
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
export const objectMembersOf = (
    t: Term,
): readonly Extract<Term, { kind: 'object' }>[] =>
    summandsOf(t).filter(
        (node): node is Extract<Term, { kind: 'object' }> =>
            node.kind === 'object',
    )

/** An object spec, with the open key entry of the object that holds it. */
export type Piece = {
    readonly spec: Record<string, ObjectSlot>
    readonly rest: AnyCodec | undefined
}
export type SpecSlice = {
    readonly keep: readonly Piece[]
    readonly rest: readonly Piece[]
}
export type ObjectNode = Extract<Term, { kind: 'object' }>

/** The object node that a piece is: the declared fields and the open key entry. */
export const nodeOfPiece = (piece: Piece): ObjectNode => {
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
 * **The summands of a term**: the nodes that its nested unions hold, each read through its `ref`s.
 * A chain of `ref`s that names no node gives none.
 */
export const summandsOf = (t: Term): readonly Term[] => {
    const node = resolvedTerm(t)
    if (node === undefined) return []
    return node.kind === 'union' ? node.options.flatMap(summandsOf) : [node]
}
