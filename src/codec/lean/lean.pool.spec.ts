/**
 * **The generated pool: one set of pairs, put to the kernel.**
 *
 * A seeded draw builds codecs through the public constructors, so the pool holds what the
 * library constructs and not what a reader imagined. Each pair of the pool goes to the model as the
 * disjointness and separation vectors, through the same emitter that the hand corpus uses. Each
 * kernel file names its own failing rows.
 *
 * The hand corpus in `lean.spec.ts` stays as the hand-picked part. The pool depends on the seed
 * alone, so a change of the pool counts below is a change of the draw, of the constructors, or
 * of the emitter.
 *
 * A `ref` that no scope binds is an unknown term, and each host check takes its worst case, so a
 * pair has two readings: the guard reads the `ref` as the root of its option, and the other tests
 * read the open term.
 *
 * One route narrows the pool. **No separation vector for two fills at one name.** The model refuses
 * two fills at one name whatever their constants, because the constants of a fill have no decidable
 * equality. The host accepts two fills with equal constants. Such a pair goes to disjointness and
 * to a kernel row of its guard column, and no check reads a compatibility column for the pair.
 */
import { mkdirSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../attribute'
import { DynamoNumber, isNumeral, isStoredNumeral } from '../attribute'
import type { AnyCodec } from '../codec'
import {
    array,
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    exclude,
    extract,
    fits,
    held,
    item,
    list,
    mdunion,
    meet,
    meetOrdered,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    ref,
    refine,
    scope,
    spread,
    string,
    undefinable,
    union,
    withLegacyRead,
} from '../codec'
import { codecOfTerm, termOf } from '../denote'
import type {
    DisjointPair,
    FormerGuard,
    HostAt,
    MeetCover,
    PathStep,
    PathVectors,
    Separation,
    Slice,
} from '../lean'
import {
    hostAt,
    LeanUnemittable,
    leanAttrOf,
    leanClosedOf,
    leanDisjoint,
    leanDisjointRowModule,
    leanFormerGuard,
    leanFormerGuardModule,
    leanGraphOf,
    leanMeetCoverModule,
    leanPath,
    leanPathModules,
    leanSeparation,
    leanSeparationRowModule,
    leanSlice,
    leanSliceModule,
    leanValueOf,
    pairGuardRefusal,
    reachable,
    sliceableOf,
    unionAt,
} from '../lean'
import { failed, orThrow } from '../result'
import { agrees, disjoint, viewsDisjoint } from '../scoped'
import type { Term } from '../term'
import {
    holdsNoValue,
    openRefusal,
    RecursionRefused,
    recursionUse,
    sameTerm,
    targetOf,
} from '../term'
import {
    arbitraryOf,
    checkEquivalent,
    rngFrom,
    structuralEquals,
} from '../testing'
import { typeVectorFiles } from '../typeVectors'

/** The emitter takes the erased codec; the constructors return precise ones. */
const erase = (codec: unknown): AnyCodec => codec as AnyCodec

/** The seeds of the pool. A new seed is a new pool, and the pinned counts move with it. */
const SEEDS = [20261004, 1, 4] as const
/** The number of codecs that the draw makes for each seed. */
const DRAWS = 150
/** The depth of each drawn codec. */
const DEPTH = 3
/** The partners of each codec, drawn from the built codecs, after the codec itself. */
const PARTNERS = 8
/** The values that the meet rows draw from each of the two factors. */
const MEET_SAMPLES = 1

type Entry = { readonly name: string; readonly codec: AnyCodec }

/** The stream of the seed that {@link pool} draws from. */
let rng = rngFrom(SEEDS[0])
const pick = <T>(xs: readonly T[]): T => xs[Math.floor(rng() * xs.length)] as T

/**
 * **No adapter of the library is a leaf.** `number` and `opaque('lossy')` are each a `held`
 * whose adapter converts a JS float. The analysis reads a `held` by its two sides and the identity
 * of its adapter, and a declaration verdict quantifies the adapter, so the `held` former with a
 * caller's adapter stands for every adapter. The former draws its outer side from the leaves, so
 * `held(dynamoNumber, number)` is one of its shapes. The specs of each adapter check what the
 * adapter computes.
 */
const leaves: readonly (readonly [string, () => AnyCodec])[] = [
    ['string', () => erase(string)],
    ['boolean', () => erase(boolean)],
    ['binary', () => erase(binary)],
    ['null', () => erase(nullValue)],
    ['decimal', () => erase(decimal)],
    ['dynamoNumber', () => erase(dynamoNumber)],
    ['lit_s', () => erase(string('a', 'b'))],
    ['lit_s1', () => erase(string('a'))],
    ['lit_d', () => erase(decimal('1', '2.5'))],
    [
        'lit_n',
        () =>
            erase(
                dynamoNumber(
                    orThrow(DynamoNumber.from('1')),
                    orThrow(DynamoNumber.from('2.5')),
                ),
            ),
    ],
    ['lit_b', () => erase(binary(new Uint8Array([1, 2])))],
    ['opaque', () => erase(opaque)],
    ['never', () => erase(never)],
    ['undeclared', () => erase(undeclared)],
]
const setable: readonly (readonly [string, () => AnyCodec])[] = [
    ['string.set', () => erase(string.set())],
    ['lit_s.set', () => erase(string.set('a', 'b'))],
    ['dynamoNumber.set', () => erase(dynamoNumber.set())],
    ['decimal.set', () => erase(decimal.set())],
    ['binary.set', () => erase(binary.set())],
]
/** A `ref` that no scope binds: a free variable, and each codec that reads it an open fragment. */
const undeclared = ref('undeclared')
/** A caller's predicate: the theorem binds the predicate as a variable. */
const callerPredicate = (v: unknown): v is unknown => v !== 'zz'
const names = ['a', 'b', 'c']

/** A union that a constructor accepted, and the discriminators where the union is a dissection. */
type Declared = { readonly codec: AnyCodec; readonly keys: readonly string[] }
/** The unions of the seed under draw: each declared union, then each union of a pair. */
let unions: Declared[] = []

/**
 * **The unions that the draw declares inside one drawn codec.** Each declaration is a host verdict, and
 * a refused declaration refuses the whole draw, so the pool puts each declared pair to the model as
 * well. A recursive option names the union under declaration: where the host refuses, the thunk
 * still throws, and the pair is the declaration itself; where the host accepts, the thunk returns
 * the union, and the pair is the same two options declared later.
 */
let declared: [Entry, Entry][] = []

/**
 * **The terms that a former of the seed under draw refused at its guard.** No union reads such a
 * term, so the pool puts each term to the model's guard alone.
 */
let refused: Term[] = []

/**
 * **Each codec that the seed under draw offers to a pair**, in the order of the offer, before the
 * print decides the pair. The path vectors read this list, so a partner that the print refuses
 * removes no codec from the path coverage.
 */
let offered: AnyCodec[] = []
const declare = (
    a: Entry,
    b: Entry,
    make: () => unknown,
    keys: readonly string[] = [],
): AnyCodec => {
    const pair: [Entry, Entry] = [a, b]
    declared.push(pair)
    const made = erase(make())
    // **A scope closes a copy**, so a fragment of the scope stays open, and the pair reads each
    // option of the entry in place of the fragment
    const t = made.def
    if (t.kind === 'union')
        for (const [at, option] of t.options.entries()) {
            const was = pair[at]
            if (was !== undefined && option !== was.codec.def)
                pair[at] = { ...was, codec: erase(codecOfTerm(option)) }
        }
    unions.push({ codec: made, keys })
    return made
}

/**
 * **The spelling of a leaf and of a tag.** With `thunked`, each one sits behind a `ref` to another
 * entry of its scope, which closes no cycle, so a reader of the host passes a thunk to reach it. The
 * emitter prints the entry as its body and the wrap draws no number, so a seed builds the same pool
 * in both spellings, and every emitted file must come out the same.
 *
 * `never` keeps its plain spelling, because `nullable` reads the declared term: `nullable(never)`
 * is `NULL`, and `nullable` of a `ref` to `never` is a union with `NULL`. `undeclared` keeps its
 * plain spelling, because a scope refuses a `ref` to a name that the scope does not declare.
 */
let thunked = false
const spelled = (codec: unknown): AnyCodec =>
    thunked
        ? erase(scope({ At: ref('It'), It: erase(codec) }).At)
        : erase(codec)

/** One codec, drawn through the public constructors. A constructor can refuse the draw. */
const draw = (depth: number): Entry => {
    if (depth === 0 || rng() < 0.25) {
        const [name, make] = pick(rng() < 0.8 ? leaves : setable)
        return {
            name,
            codec:
                name === 'never' || name === 'undeclared'
                    ? make()
                    : spelled(make()),
        }
    }
    switch (Math.floor(rng() * 20)) {
        case 0: {
            const c = draw(depth - 1)
            return { name: `array(${c.name})`, codec: erase(array(c.codec)) }
        }
        case 1: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            return {
                name: `list(${a.name},${b.name})`,
                codec: erase(list(a.codec, b.codec)),
            }
        }
        case 2: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const c = draw(depth - 1)
            return {
                name: `list(${a.name},...${b.name},${c.name})`,
                codec: erase(list(a.codec, spread(b.codec), c.codec)),
            }
        }
        case 3:
        case 4: {
            const count = 1 + Math.floor(rng() * 3)
            const spec: Record<string, unknown> = {}
            const parts: string[] = []
            for (let i = 0; i < count; i++) {
                const c = draw(depth - 1)
                const at = names[i] as string
                const slot = Math.floor(rng() * 5)
                if (slot === 0) {
                    spec[at] = c.codec
                    parts.push(`${at}:${c.name}`)
                } else if (slot === 1) {
                    spec[at] = optional(c.codec)
                    parts.push(`${at}?:${c.name}`)
                } else if (slot === 2) {
                    let fill: unknown
                    try {
                        fill = arbitraryOf(c.codec, rng, 2)
                    } catch {
                        fill = 'x'
                    }
                    spec[at] = withLegacyRead({
                        current: c.codec,
                        whenMissing: fill as never,
                    })
                    parts.push(`${at}~${JSON.stringify(fill) ?? 'u'}:${c.name}`)
                } else if (slot === 3) {
                    spec[at] = withLegacyRead({
                        current: c.codec,
                        older: { decode: () => 'older' as never },
                    })
                    parts.push(`${at}<older:${c.name}`)
                } else {
                    spec[at] = undefinable(c.codec)
                    parts.push(`${at}?u:${c.name}`)
                }
            }
            const build = object as (...xs: unknown[]) => unknown
            if (rng() < 0.3) {
                const r = draw(depth - 1)
                return {
                    name: `object{${parts.join(',')}}+rest(${r.name})`,
                    codec: erase(build(spec, [string, optional(r.codec)])),
                }
            }
            return {
                name: `object{${parts.join(',')}}`,
                codec: erase(build(spec)),
            }
        }
        case 5:
        case 6: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            return {
                name: `union(${a.name}|${b.name})`,
                codec: declare(a, b, () => union([a.codec, b.codec] as never)),
            }
        }
        case 7: {
            const [name, make] = pick(setable)
            return { name, codec: make() }
        }
        case 8: {
            const shipped = rng()
            if (shipped < 0.17)
                return {
                    name: 'refine(string,isNumeral)',
                    codec: erase(refine(string, isNumeral as never)),
                }
            if (shipped < 0.33)
                return {
                    name: 'refine(decimal,isStoredNumeral)',
                    codec: erase(refine(decimal, isStoredNumeral as never)),
                }
            const c = draw(depth - 1)
            return {
                name: `refine(${c.name},caller)`,
                codec: erase(
                    refine(c.codec as never, callerPredicate as never),
                ),
            }
        }
        case 9: {
            const c = draw(depth - 1)
            const [side, make] = pick(leaves)
            const outer = make()
            return {
                name: `held(${c.name},${side},caller)`,
                codec: erase(
                    held(
                        c.codec as never,
                        outer as never,
                        {
                            encode: (v: never) => v,
                            decode: (t: never) => t,
                        } as never,
                    ),
                ),
            }
        }
        case 10: {
            const c = draw(depth - 1)
            return {
                name: `ref(${c.name})`,
                codec: erase(scope({ At: ref('It'), It: c.codec }).At),
            }
        }
        case 11: {
            const c = draw(depth - 1)
            // the scope runs the guard, so a refusal of the body is a refusal of the draw. The
            // draw is the thunk that closes the cycle, as an entry that is a `ref`
            const { top } = scope({
                top: ref('tree'),
                tree: object({ v: c.codec, kids: array(ref('top')) }),
            })
            return { name: `scope.tree(${c.name})`, codec: erase(top) }
        }
        case 12: {
            const c = draw(depth - 1)
            const kids = {
                name: 'array(self)',
                codec: erase(array(ref('self'))),
            }
            const self: AnyCodec = declare(
                c,
                kids,
                () => scope({ self: union([c.codec, kids.codec]) }).self,
            )
            return { name: `scope.json(${c.name})`, codec: self }
        }
        case 13: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const left = {
                name: `{k:a,x:${a.name}}`,
                codec: erase(object({ k: spelled(string('a')), x: a.codec })),
            }
            const right = {
                name: `{k:b,y:${b.name}}`,
                codec: erase(object({ k: spelled(string('b')), y: b.codec })),
            }
            return {
                name: `dunion(k:a{x:${a.name}}|b{y:${b.name}})`,
                codec: declare(
                    left,
                    right,
                    () =>
                        (discriminatedUnion as (...x: unknown[]) => unknown)(
                            'k',
                            [left.codec, right.codec],
                        ),
                    ['k'],
                ),
            }
        }
        case 14: {
            const c = draw(depth - 1)
            return {
                name: `legacy(${c.name})`,
                codec: erase(
                    withLegacyRead({
                        current: c.codec,
                        older: { decode: () => 'o' as never },
                    }),
                ),
            }
        }
        case 15: {
            const c = draw(depth - 1)
            const node = {
                name: '{m?:self}',
                codec: erase(object({ m: optional(ref('self')) })),
            }
            const self: AnyCodec = declare(
                c,
                node,
                () => scope({ self: union([c.codec, node.codec]) }).self,
            )
            return { name: `scope.opt(${c.name})`, codec: self }
        }
        case 17: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const merge = meet as (...factors: unknown[]) => unknown
            const right = erase(object({ b: b.codec }))
            if (rng() < 0.5)
                return {
                    name: `meet({a:${a.name}},{b:${b.name}})`,
                    codec: erase(merge(object({ a: a.codec }), right)),
                }
            const left = {
                name: `{a:${a.name}}`,
                codec: erase(object({ a: a.codec })),
            }
            const other = {
                name: '{c:string}',
                codec: erase(object({ c: string })),
            }
            const factor = declare(left, other, () =>
                union([left.codec, other.codec] as never),
            )
            return {
                name: `meet(union({a:${a.name}}|{c:string}),{b:${b.name}})`,
                codec: erase(merge(factor, right)),
            }
        }
        case 18: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const small = {
                name: `{k:p,s:x,x:${a.name}}`,
                codec: erase(
                    object({
                        k: spelled(string('p')),
                        s: spelled(string('x')),
                        x: a.codec,
                    }),
                ),
            }
            const large = {
                name: `{k:p,s:y,y:${b.name}}`,
                codec: erase(
                    object({
                        k: spelled(string('p')),
                        s: spelled(string('y')),
                        y: b.codec,
                    }),
                ),
            }
            const name = `mdunion(k,s:${small.name}|${large.name})`
            const whole = declare(
                small,
                large,
                () =>
                    (mdunion as (...x: unknown[]) => unknown)(
                        ['k', 's'],
                        [small.codec, large.codec],
                    ),
                ['k', 's'],
            )
            const slice = rng()
            // `whole` is erased, so its member specs are unknown and the type refuses every
            // pattern on it. The cast on the pattern states that the pool chose a valid one.
            if (slice < 0.33)
                return {
                    name: `extract(s=x,${name})`,
                    codec: erase(
                        extract(whole, object({ s: string('x') }) as AnyCodec),
                    ),
                }
            if (slice < 0.67)
                return {
                    name: `exclude(s=x,${name})`,
                    codec: erase(
                        exclude(whole, object({ s: string('x') }) as AnyCodec),
                    ),
                }
            return { name, codec: whole }
        }
        // **A mutual recursion entered at two members.** Each member is an entry of one scope, and
        // each root of the draw reaches the other member through the cycle
        case 19: {
            const c = draw(depth - 1)
            // the scope runs the guard, so a refusal of a body is a refusal of the draw. Each
            // member is the thunk that closes the cycle, as an entry that is a `ref`
            const mutual = scope({
                A: ref('a'),
                B: ref('b'),
                a: object({ v: c.codec, b: optional(ref('B')) }),
                b: object({ a: optional(ref('A')) }),
            })
            const left = { name: `scope.a(${c.name})`, codec: erase(mutual.A) }
            const right = { name: 'scope.b', codec: erase(mutual.B) }
            if (rng() < 0.5)
                return {
                    name: `{x:${left.name},y:${right.name}}`,
                    codec: erase(object({ x: left.codec, y: right.codec })),
                }
            return {
                name: `union(${left.name}|${right.name})`,
                codec: declare(left, right, () =>
                    union([left.codec, right.codec] as never),
                ),
            }
        }
        default: {
            const c = draw(depth - 1)
            return {
                name: `nullable(${c.name})`,
                codec: erase(nullable(c.codec as never)),
            }
        }
    }
}

/** The field names at which a term holds a fill, at any depth. */
const fillNames = (root: Term): Set<string> => {
    const names = new Set<string>()
    const seen = new Set<Term>()
    const walk = (t: Term): void => {
        if (seen.has(t)) return
        seen.add(t)
        switch (t.kind) {
            case 'set':
                return walk(t.elem)
            case 'list':
                t.pre.forEach(walk)
                t.suf.forEach(walk)
                if (t.spread !== undefined) walk(t.spread)
                return
            case 'held':
                walk(t.inner)
                return walk(t.outer)
            case 'refine':
            case 'legacy':
                return walk(t.inner)
            case 'ref': {
                const target = targetOf(t)
                if (target !== undefined) walk(target)
                return
            }
            case 'object':
                for (const [name, field] of Object.entries(t.body.fields)) {
                    if (field.mark === 'fallback') names.add(name)
                    walk(field.t)
                }
                if (t.body.rest !== undefined) walk(t.body.rest)
                return
            case 'union':
                return t.options.forEach(walk)
            default:
                return
        }
    }
    walk(root)
    return names
}

/** Whether the two terms hold a fill at one field name: the narrowing of the model. */
const fillsMeet = (x: Term, y: Term): boolean => {
    const there = fillNames(y)
    return [...fillNames(x)].some((name) => there.has(name))
}

/** One pair of the pool, with the host verdicts and the two terms that the model reads. */
type PoolPair = {
    readonly name: string
    readonly label: string
    readonly left: AnyCodec
    readonly right: AnyCodec
    /** The host verdicts, in the column order of `poolRow`: disjoint, views, agrees, guard, union. */
    readonly host: string
    /** A fill at one field name on each side: the pair goes to disjointness and to a guard row. */
    readonly fills: boolean
    readonly l: string
    readonly r: string
    readonly closures: readonly string[]
    readonly readers: readonly string[]
}

const bit = (b: boolean): string => (b ? '1' : '0')

/** Where a draw or a pair left the pool, by reason. */
const dropped = new Map<string, number>()
const drop = (why: string) => dropped.set(why, (dropped.get(why) ?? 0) + 1)

/** The pairs of one seed. The names continue after `first`, so the seeds share one name space. */
const pool = (seed: number, first: number): readonly PoolPair[] => {
    rng = rngFrom(seed)
    declared = []
    unions = []
    refused = []
    offered = []
    const built: Entry[] = []
    for (let i = 0; i < DRAWS; i++) {
        try {
            built.push(draw(DEPTH))
        } catch (error) {
            drop('a constructor refused the draw')
            if (error instanceof RecursionRefused) refused.push(error.term)
        }
    }
    const pairs: PoolPair[] = []
    const add = (a: Entry, b: Entry) => {
        offered.push(a.codec, b.codec)
        const name = `pool_${first + pairs.length}`
        const bound = {
            closures: new Map<unknown, string>(),
            adapters: new Map<unknown, string>(),
            readers: new Map<unknown, string>(),
        }
        let l: string
        let r: string
        try {
            l = leanGraphOf(a.codec, name, bound)
            r = leanGraphOf(b.codec, name, bound)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`term: ${error.reason}`)
            return
        }
        const x = a.codec.def
        const y = b.codec.def
        // a union over a `ref` that no scope binds is an open fragment, which refuses each use
        let declared = true
        try {
            const u = erase(union([a.codec, b.codec] as never))
            declared = openRefusal(u.def) === undefined
            if (declared) unions.push({ codec: u, keys: [] })
        } catch {
            declared = false
        }
        const guarded = recursionUse(x) < 2 && recursionUse(y) < 2
        const host = [
            disjoint(x, y),
            viewsDisjoint(x, y),
            agrees(x, y),
            guarded,
            declared,
        ]
            .map(bit)
            .join('')
        pairs.push({
            name,
            label: `${a.name} | ${b.name}`,
            left: a.codec,
            right: b.codec,
            host,
            fills: fillsMeet(x, y),
            l,
            r,
            closures: [...bound.closures.values()],
            readers: [...bound.readers.values()],
        })
    }
    for (const e of built) {
        add(e, e)
        for (let j = 0; j < PARTNERS; j++) add(e, pick(built))
    }
    for (const [a, b] of declared) add(a, b)
    return pairs
}

/**
 * The pairs that each kernel module states; a refusal of the emitter drops the pair by reason. A
 * pair with a fill on each side has no separation vector, so the kernel states its guard column alone.
 */
const kernelPairs = (pairs: readonly PoolPair[]) => {
    const disjoints: DisjointPair[] = []
    const separations: Separation[] = []
    const fillGuards: Separation[] = []
    for (const p of pairs) {
        const one = { name: p.name, left: p.left, right: p.right }
        try {
            leanDisjoint(one)
            disjoints.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`disjoint: ${error.reason}`)
        }
        if (p.fills) {
            const refusal = pairGuardRefusal(one)
            if (refusal === undefined) fillGuards.push(one)
            else drop(`pairGuard: ${refusal}`)
            continue
        }
        try {
            leanSeparation(one)
            separations.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`separation: ${error.reason}`)
        }
    }
    return { disjoints, separations, fillGuards }
}

/** The guard verdicts of one seed. The names continue after `first`, so the seeds share one name space. */
const formerGuards = (terms: readonly Term[], first: number): FormerGuard[] => {
    const guards: FormerGuard[] = []
    for (const term of terms) {
        const one = { name: `former_${first + guards.length}`, term }
        try {
            leanFormerGuard(one)
            guards.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`guard: ${error.reason}`)
        }
    }
    return guards
}

/**
 * **The clauses that the pool puts to each name of a union.** The values that the draw pins,
 * two values that the draw never pins, one literal at each base and form, and one union of
 * two literals.
 */
const clauseVocabulary: readonly (() => AnyCodec)[] = [
    ...['a', 'b', 'p', 'x', 'y', 'A', 'q'].map((s) => () => erase(string(s))),
    () => erase(string('a', 'b')),
    ...['1', '2.5'].map((s) => () => erase(decimal(s))),
    ...['1', '2.5'].map(
        (s) => () => erase(dynamoNumber(orThrow(DynamoNumber.from(s)))),
    ),
    ...[1, 2.5].map((n) => () => erase(number(n))),
    ...[true, false].map((b) => () => erase(boolean(b))),
    () => erase(binary(new Uint8Array([1, 2]))),
]

/**
 * The slices of one seed: each union of object options, once, with each clause that the emitter
 * states. The names continue after `first`, so the seeds share one name space.
 */
const slicesOf = (declared: readonly Declared[], first: number): Slice[] => {
    const seen = new Set<string>()
    const slices: Slice[] = []
    for (const { codec, keys } of declared) {
        const def = codec.def
        if ('mark' in def || def.kind !== 'union') continue
        const fields = def.options.flatMap((t) =>
            t.kind === 'object' ? [Object.keys(t.body.fields)] : [],
        )
        // the class that the pool measured: a union whose options are all objects
        if (fields.length !== def.options.length) continue
        let printed: string
        try {
            printed = leanGraphOf(codec, 'slice', {
                closures: new Map(),
                adapters: new Map(),
                readers: new Map(),
            })
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`slice term: ${error.reason}`)
            continue
        }
        const id = `${keys.join(',')}|${printed}`
        if (seen.has(id)) continue
        seen.add(id)
        const sliceable = sliceableOf(codec)
        const name = `slice_${first + slices.length}`
        const clauses: Readonly<Record<string, AnyCodec>>[] = []
        for (const key of new Set(fields.flat())) {
            for (const make of clauseVocabulary) {
                const clause = { [key]: make() }
                try {
                    leanSlice({ name, codec: sliceable, clauses: [clause] })
                    clauses.push(clause)
                } catch (error) {
                    if (!(error instanceof LeanUnemittable)) throw error
                    drop(`slice: ${error.reason}`)
                }
            }
        }
        let assigned = keys
        try {
            leanSlice({ name, codec: sliceable, clauses: [], keys })
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`assignment: ${error.reason}`)
            assigned = []
        }
        if (clauses.length === 0 && assigned.length === 0) continue
        slices.push({ name, codec: sliceable, clauses, keys: assigned })
    }
    return slices
}

/** A path with no clause. */
const plainPath = (path: readonly PathStep[]): boolean =>
    path.every((step) => typeof step !== 'object')

/** The segments of a path below the codec, at most. */
const PATH_DEPTH = 3

/**
 * The segments of a path below a clause, at most. The clause decides the frontier at the union,
 * and one segment reads the narrowed frontier. A deeper segment walks what a path without the
 * clause walks, and the bridge pays for each row in time.
 */
const NARROW_DEPTH = 1

/**
 * **The paths into one codec.** A step is each name that a reachable object declares, and each
 * position of a reachable prefix with the first position past the prefix. A path grows only where
 * the host lets a codec stand, to {@link PATH_DEPTH} segments. Past a resolved codec, a path tries
 * the steps that the codec declares at its top, one name and one position. A path under a `narrow` starts at each
 * path where the host resolves a union that {@link drawsNarrowing} accepts, with each clause of {@link clauseVocabulary} at each name
 * of an option, and grows under the clause to {@link NARROW_DEPTH} segments.
 */
const pathsOf = (codec: AnyCodec): (readonly PathStep[])[] => {
    const names = new Set<string>()
    let positions = 0
    for (const t of reachable(codec.def)) {
        if (t.kind === 'object')
            for (const name of Object.keys(t.body.fields)) names.add(name)
        if (t.kind === 'list') positions = Math.max(positions, t.pre.length + 1)
    }
    const steps = [...names, ...Array.from({ length: positions }, (_, i) => i)]
    const paths: (readonly PathStep[])[] = []
    // **A `ref` that names a codec not yet declared ends the path.** The walk reads the `ref`,
    // and the `ReferenceError` of the unbound name propagates: the host reads no refusal there. The model reads the
    // variable that no binder binds as an empty frontier, so the two state no common decision
    const decide = (path: readonly PathStep[]) => {
        try {
            return hostAt(codec, path)
        } catch (error) {
            if (!(error instanceof ReferenceError)) throw error
            drop('path: a thunk names a codec not yet declared')
            return undefined
        }
    }
    // one name and one position of the codec stand for each step that the codec at a prefix
    // does not declare: each such step is the same refusal of the store
    const probes = [...[...names].slice(0, 1), 0]
    const next = (decided: HostAt): readonly (string | number)[] => {
        if (decided.kind !== 'resolved') return steps
        const declared = new Set<string | number>(probes)
        for (const t of topTerms(decided.codec.def)) {
            if (t.kind === 'object')
                for (const name of Object.keys(t.body.fields))
                    declared.add(name)
            if (t.kind === 'list')
                for (let i = 0; i <= t.pre.length; i++) declared.add(i)
        }
        return steps.filter((step) => declared.has(step))
    }
    const grow = (path: readonly PathStep[], left: number) => {
        const decided = decide(path)
        if (decided === undefined) return
        paths.push(path)
        if (decided.kind === 'refused' || decided.kind === 'vacant') return
        if (left > 0)
            for (const step of next(decided)) grow([...path, step], left - 1)
    }
    const narrowing = (path: readonly PathStep[], left: number) => {
        const decided = decide(path)
        if (decided === undefined) return
        if (decided.kind === 'resolved' && drawsNarrowing(decided)) {
            const keys = new Set(
                [...reachable(decided.codec.def)].flatMap((t) =>
                    t.kind === 'object' ? Object.keys(t.body.fields) : [],
                ),
            )
            for (const key of keys)
                for (const make of clauseVocabulary)
                    grow(
                        [...path, { narrow: object({ [key]: make() }) }],
                        Math.min(left, NARROW_DEPTH),
                    )
        }
        if (decided.kind === 'refused' || decided.kind === 'vacant') return
        if (left > 0)
            for (const step of next(decided))
                narrowing([...path, step], left - 1)
    }
    grow([], PATH_DEPTH)
    narrowing([], PATH_DEPTH)
    // the wrapper holds the codec at its name, so the path of no step under the name states the
    // codec against itself
    return paths.filter((path) => path.length > 0)
}

/** **A union that the draw narrows**: a union under its `ref`s, recursive or not. */
const drawsNarrowing = (decided: HostAt): boolean => {
    if (!unionAt(decided) || decided.kind !== 'resolved') return false
    const def = decided.codec.def
    if ('mark' in def) return false
    return throughRefs(def) !== undefined
}

/** The term under a chain of `ref`s, or nothing where a `ref` has no target. */
const throughRefs = (t: Term): Term | undefined => {
    if (t.kind !== 'ref') return t
    const target = targetOf(t)
    return target === undefined ? undefined : throughRefs(target)
}

/** The terms at the top of a term, under `ref`s and unions. */
const topTerms = (t: Term): Term[] => {
    const u = throughRefs(t)
    if (u === undefined) return []
    return u.kind === 'union' ? u.options.flatMap(topTerms) : [u]
}

/**
 * The path vectors of one seed: each codec that the seed offered to a pair, once, with the paths
 * into it. The names continue after `first`, so the seeds share one name space. A codec whose
 * theorem prints as the theorem of a codec before it adds nothing, and goes.
 */
const pathVectorsOf = (
    codecs: readonly AnyCodec[],
    first: number,
    seen: Set<string>,
): PathVectors[] => {
    const vectors: PathVectors[] = []
    for (const codec of new Set(codecs)) {
        const one = { name: 'path', codec, paths: pathsOf(codec) }
        let printed: string
        try {
            printed = leanPath(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`path: ${error.reason}`)
            continue
        }
        if (seen.has(printed)) continue
        seen.add(printed)
        vectors.push({ ...one, name: `path_${first + vectors.length}` })
    }
    return vectors
}

/**
 * The decision of `at` at each path into each codec of the pairs, keyed by the term of the codec
 * and the path. Two spellings that print one term key one decision.
 */
const decisionsOf = (
    seeds: ReturnType<typeof buildPool>,
): ReadonlyMap<string, string> => {
    const bound = () => ({
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
        standIn: true,
    })
    const print = (codec: AnyCodec): string =>
        leanGraphOf(codec, 'decision', bound())
    const stepKey = (step: PathStep): string =>
        typeof step === 'object'
            ? `narrow{${Object.entries(step.narrow.spec)
                  .map(([key, c]) => `${key}:${print(c)}`)
                  .join(',')}}`
            : String(step)
    const decided = new Map<string, string>()
    for (const codec of new Set(
        seeds.flatMap((one) => one.pairs.flatMap((p) => [p.left, p.right])),
    )) {
        let root: string
        try {
            root = print(codec)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            continue
        }
        for (const path of pathsOf(codec)) {
            let clause: string
            try {
                clause = path.map(stepKey).join('.')
            } catch (error) {
                if (!(error instanceof LeanUnemittable)) throw error
                continue
            }
            decided.set(`${root}\u0000${clause}`, hostAt(codec, path).kind)
        }
    }
    return decided
}

/**
 * The term a codec prints alone, or nothing where the print binds a caller's function: a bound name
 * is numbered afresh in each print, so two different functions print one name.
 */
const printedAlone = (codec: AnyCodec): string | undefined => {
    const bound = {
        closures: new Map<unknown, string>(),
        adapters: new Map<unknown, string>(),
        readers: new Map<unknown, string>(),
    }
    let printed: string
    try {
        printed = leanGraphOf(codec, 'alone', bound)
    } catch (error) {
        if (!(error instanceof LeanUnemittable)) throw error
        return undefined
    }
    const binds =
        bound.closures.size + bound.adapters.size + bound.readers.size > 0
    return binds ? undefined : printed
}

/** What one half answered: a refusal, or the result. A refusal's wording is not compared. */
const answer = (run: () => unknown): { readonly result?: unknown } => {
    try {
        const result = run()
        return result instanceof CodecError ? {} : { result }
    } catch (error) {
        if (error instanceof CodecError) return {}
        throw error
    }
}

const sameAnswer = (
    a: { readonly result?: unknown },
    b: { readonly result?: unknown },
): boolean =>
    'result' in a === 'result' in b && structuralEquals(a.result, b.result)

/**
 * Each place where two codecs that print one term get two host verdicts: a pair verdict, an encode
 * of a value that one of them generates, or a decode of an attribute that one of them writes. The
 * counts say how much was compared, so a pool that offers no group reads as no check.
 */
const samePrintDisagreements = (
    pairs: readonly PoolPair[],
): {
    readonly disagreements: readonly string[]
    readonly pairGroups: number
    readonly termGroups: number
} => {
    const out: string[] = []
    let pairGroups = 0
    let termGroups = 0
    const byPair = new Map<string, PoolPair>()
    for (const p of pairs) {
        const binds = p.closures.length + p.readers.length > 0
        if (binds || `${p.l}${p.r}`.includes('.caller')) continue
        const key = `${p.l}\u0000${p.r}`
        const seen = byPair.get(key)
        if (seen === undefined) byPair.set(key, p)
        else if (seen.label !== p.label) pairGroups++
        if (seen !== undefined && seen.host !== p.host)
            out.push(
                `pair ${seen.label} (${seen.host}) / ${p.label} (${p.host})`,
            )
    }
    const byTerm = new Map<string, AnyCodec[]>()
    for (const codec of new Set(pairs.flatMap((p) => [p.left, p.right]))) {
        const printed = printedAlone(codec)
        if (printed === undefined) continue
        byTerm.set(printed, [...(byTerm.get(printed) ?? []), codec])
    }
    for (const [printed, codecs] of byTerm) {
        if (codecs.length < 2) continue
        termGroups++
        for (const from of codecs) {
            for (let k = 1; k <= 6; k++) {
                let value: unknown
                try {
                    value = arbitraryOf(from, rngFrom(k), 3)
                } catch {
                    continue
                }
                const written = codecs.map((c) =>
                    answer(() => c.encode(value as never)),
                )
                if (written.some((w) => !sameAnswer(w, written[0] ?? {})))
                    out.push(`encode under ${printed}`)
                const attribute = written[codecs.indexOf(from)]?.result
                if (attribute === undefined) continue
                const read = codecs.map((c) =>
                    answer(() => c.decode(attribute as never)),
                )
                if (read.some((r) => !sameAnswer(r, read[0] ?? {})))
                    out.push(`decode under ${printed}`)
            }
        }
    }
    return { disagreements: [...new Set(out)], pairGroups, termGroups }
}

/** The pool of every seed, with the kernel vectors of each pair. */
const buildPool = () => {
    const seeds: {
        seed: number
        pairs: readonly PoolPair[]
        slices: readonly Slice[]
        guards: readonly FormerGuard[]
        paths: readonly PathVectors[]
    }[] = []
    const printedPaths = new Set<string>()
    for (const seed of SEEDS) {
        const first = seeds.reduce((n, one) => n + one.pairs.length, 0)
        const pairs = pool(seed, first)
        const sliced = seeds.reduce((n, one) => n + one.slices.length, 0)
        const guarded = seeds.reduce((n, one) => n + one.guards.length, 0)
        const pathed = seeds.reduce((n, one) => n + one.paths.length, 0)
        seeds.push({
            seed,
            pairs,
            slices: slicesOf(unions, sliced),
            guards: formerGuards(refused, guarded),
            paths: pathVectorsOf(offered, pathed, printedPaths),
        })
    }
    return seeds.map(({ seed, pairs, slices, guards, paths }) => ({
        seed,
        pairs,
        slices,
        guards,
        paths,
        ...kernelPairs(pairs),
    }))
}

/**
 * **A narrowing at a recursive union**, beside the pool: the option `node` of `Node` returns to
 * `Node`. The draw depends on the seed, so this vector puts the shape to the kernel in every run.
 * The vector goes to the path modules only, and not to the type vectors. The clause `leaf` keeps the option that declares `v`, and the clause `node` keeps the
 * option whose elements return to the union.
 */
const recursiveNarrowing = (): PathVectors => {
    const { Node } = scope({
        Node: union([
            object({ k: string('leaf'), v: string }),
            object({ k: string('node'), c: array(ref('Node')) }),
        ]),
    })
    return {
        name: 'path_recursive_union',
        codec: erase(object({ n: Node })),
        paths: [
            ['n', { narrow: object({ k: erase(string('leaf')) }) }, 'v'],
            [
                'n',
                { narrow: object({ k: erase(string('node')) }) },
                'c',
                0,
                'k',
            ],
        ],
    }
}

/**
 * **A member read across an entry on a cycle**, beside the pool: `B` returns to `A`, so the print
 * reads `B` as a reference under `refine`, and the model's `μG` reads no member at a reference. The
 * walk cannot pass the `refine`, and the row states the refusal of the run time.
 */
const cycleMember = (): PathVectors => {
    const { A } = scope({
        A: object({
            s: union([
                object({ x: string }),
                refine(ref('B'), (v: unknown): v is unknown => v !== null),
            ]),
        }),
        B: array(ref('A')),
    })
    return { name: 'path_cycle_member', codec: erase(A), paths: [['s', 'x']] }
}

/**
 * **A clause key over an older reader**, beside the pool: the clause vocabulary holds literals
 * only. The older reader reads every attribute, so the stored view of the key is `opaque`, and the
 * precondition of the model at the key is `exists`. The row of the precondition puts the host to
 * the model there.
 */
const legacyClause = (): PathVectors => ({
    name: 'path_clause_legacy',
    codec: erase(
        object({
            u: union([object({ a: string }), object({ b: number })]),
        }),
    ),
    paths: [
        [
            'u',
            {
                narrow: object({
                    a: erase(
                        withLegacyRead({ current: string, older: string }),
                    ),
                }),
            },
            'a',
        ],
    ],
})

/**
 * **A nested clause**, beside the pool: the vocabulary holds literals only. The clause is open at
 * each object, so a clause with an object at a key gives the `M` of the object, then the name of
 * each key, at the path of the object. The rows put the order of the claim to the model at one
 * level and at two.
 */
const nestedClause = (): PathVectors => ({
    name: 'path_clause_nested',
    codec: erase(
        object({
            u: union([
                object({
                    data: object({ n: number, k: string }),
                    tag: string,
                }),
                object({ data: string, tag: string }),
            ]),
            v: union([
                object({
                    a: object({ b: object({ n: number }) }),
                    tag: string,
                }),
                object({ a: string, tag: string }),
            ]),
        }),
    ),
    paths: [
        ['u', { narrow: object({ data: object({ n: number }) }) }, 'tag'],
        ['u', { narrow: object({ data: object({ n: number }) }) }, 'data'],
        [
            'v',
            {
                narrow: object({
                    a: object({ b: object({ n: number }) }),
                }),
            },
            'tag',
        ],
    ],
})

/**
 * **The value as the model reads it**: a key that holds `undefined` is an absent key, as
 * `leanValueOf` prints it. `opaque` refuses such a key on a write, so the host value and the
 * printed value must be one value before the host writes it.
 */
const absentUndefined = (value: unknown): unknown =>
    Array.isArray(value)
        ? value.map(absentUndefined)
        : value !== null &&
            typeof value === 'object' &&
            Object.getPrototypeOf(value) === Object.prototype
          ? Object.fromEntries(
                Object.entries(value)
                    .filter(([, x]) => x !== undefined)
                    .map(([k, x]) => [k, absentUndefined(x)]),
            )
          : value

/**
 * **The meet rows of the pool**: each pair in both orders, with the meet that `src/` builds, and
 * each value that a draw from a factor writes. A draw from the meet states nothing: the meet holds
 * the pair, so the row holds wherever each check settles. The draw also reads the spelling of the
 * term, and the meet of a pair of thunks is another spelling of one term. A meet that `src/`
 * refuses states no row. A term with a refinement states no row: the host meets a refinement by its
 * predicate, and the model reads the predicate by name only for the predicates that this library
 * ships, so the refinement is the stated limit of the meet. A term with a cycle states no row: the `#eval` of the
 * module compiles the meaning of the term, and one list with a cycle ran past twenty minutes, where
 * the kernel checks every list in under a minute. A term or a pair that the emitter refuses drops by
 * reason.
 */
const meetCoversOf = (pairs: readonly PoolPair[]): MeetCover[] => {
    const merge = meet as (a: AnyCodec, b: AnyCodec) => unknown
    const covers: MeetCover[] = []
    const seen = new Set<string>()
    const emits = (f: () => unknown): boolean => {
        try {
            f()
            return true
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`meet: ${error.reason}`)
            return false
        }
    }
    for (const p of pairs) {
        const orders =
            p.left.def === p.right.def
                ? ([[p.left, p.right, 'lr']] as const)
                : ([
                      [p.left, p.right, 'lr'],
                      [p.right, p.left, 'rl'],
                  ] as const)
        for (const [left, right, order] of orders) {
            const name = `${p.name}_${order}`
            let met: AnyCodec
            try {
                met = erase(merge(left, right))
            } catch {
                drop('meet: src/ refuses the meet')
                continue
            }
            const three = [left, right, met]
            if (
                three.some(
                    (c) =>
                        'mark' in c.def ||
                        [...reachable(c.def)].some((t) => t.kind === 'refine'),
                )
            ) {
                drop('meet: a refinement, the stated limit')
                continue
            }
            if (three.some((c) => recursionUse(c.def as Term) > 0)) {
                drop(
                    'meet: a cycle, which the diagnostic `#eval` cannot afford',
                )
                continue
            }
            const printed: string[] = []
            if (
                !emits(() =>
                    three.forEach((c) => printed.push(leanClosedOf(c, name))),
                )
            )
                continue
            for (const from of [left, right])
                for (let k = 1; k <= MEET_SAMPLES; k++) {
                    let value: unknown
                    try {
                        value = absentUndefined(
                            arbitraryOf(from, rngFrom(k), 3),
                        )
                    } catch {
                        continue
                    }
                    const attribute = from.encode(value as never)
                    if (failed(attribute)) continue
                    let row = ''
                    if (
                        !emits(() => {
                            row = `${leanValueOf(value)} ${leanAttrOf(attribute as AttributeValue)}`
                        })
                    )
                        continue
                    const key = `${printed.join('|')}|${row}`
                    if (seen.has(key)) continue
                    seen.add(key)
                    covers.push({
                        name: `${name}_${covers.length}`,
                        left,
                        right,
                        meet: met,
                        value,
                        attribute: attribute as AttributeValue,
                    })
                }
        }
    }
    return covers
}

/** The files that the gate elaborates, by name, from one build of the pool. */
const poolModules = (
    perSeed: ReturnType<typeof buildPool>,
): readonly (readonly [string, string])[] => [
    [
        '.pool.disjoints.lean',
        leanDisjointRowModule(perSeed.flatMap((one) => one.disjoints)),
    ],
    [
        '.pool.separations.lean',
        leanSeparationRowModule(
            perSeed.flatMap((one) => one.separations),
            'pool',
            perSeed.flatMap((one) => one.fillGuards),
        ),
    ],
    [
        '.pool.slices.lean',
        leanSliceModule(perSeed.flatMap((one) => one.slices)),
    ],
    ...leanPathModules(
        [
            ...perSeed.flatMap((one) => one.paths),
            recursiveNarrowing(),
            cycleMember(),
            legacyClause(),
            nestedClause(),
        ],
        4,
    ).map((text, i) => [`.pool.paths${i}.lean`, text] as const),
    [
        '.pool.guards.lean',
        leanFormerGuardModule(perSeed.flatMap((one) => one.guards)),
    ],
    [
        '.pool.meets.lean',
        leanMeetCoverModule(meetCoversOf(perSeed.flatMap((one) => one.pairs))),
    ],
]

describe('the generated pool, against the model', () => {
    const perSeed = buildPool()
    const pairs = perSeed.flatMap((one) => one.pairs)

    /**
     * **The item reading and the slice are functions of the term.** The codec that `codecOfTerm`
     * builds from the term of a pool codec, and from a copy of the term, reads each drawn value as
     * the pool codec reads it, and keeps the same term under each clause. A refusal must be the
     * same refusal. The copy shares each `ref`, and a dissection keeps its key set in the builder,
     * so the copy of a dissection is a plain union and the copy check skips it.
     */
    it('reads an item and slices from the term of the codec alone', () => {
        const outcome = (run: () => unknown): unknown => {
            try {
                const out = run()
                return failed(out) ? `refused: ${out.message}` : out
            } catch (error) {
                return `throws: ${error instanceof Error ? error.message : String(error)}`
            }
        }
        const same = (a: unknown, b: unknown): boolean =>
            typeof a === 'string' || typeof b === 'string'
                ? a === b
                : structuralEquals(a, b)
        const copied = new Map<object, unknown>()
        const copy = (t: unknown): unknown => {
            if (typeof t !== 'object' || t === null) return t
            if (
                Object.getPrototypeOf(t) !== Object.prototype &&
                !Array.isArray(t)
            )
                return t
            if ((t as Term).kind === 'ref') return t
            const known = copied.get(t)
            if (known) return known
            const out: Record<string, unknown> = Array.isArray(t)
                ? ([] as unknown as Record<string, unknown>)
                : {}
            copied.set(t, out)
            for (const [k, v] of Object.entries(t)) out[k] = copy(v)
            return out
        }
        const codecs = new Set([
            ...pairs.flatMap((p) => [p.left, p.right]),
            ...perSeed.flatMap((one) => one.slices.map((s) => erase(s.codec))),
        ])
        const rng = rngFrom(20261022)
        const counts = { codecs: 0, copies: 0, values: 0, clauses: 0 }
        const differs: string[] = []
        const compare = (c: AnyCodec, rebuilt: AnyCodec, label: string) => {
            const def = c.def as Term
            const mine = outcome(() => item(c as never))
            const theirs = outcome(() => item(rebuilt as never))
            if (typeof mine === 'string' || typeof theirs === 'string') {
                if (mine !== theirs)
                    differs.push(`${label} reading: ${mine} | ${theirs}`)
                return
            }
            const [a, b] = [mine, theirs] as {
                encode: (v: unknown) => unknown
                decode: (i: unknown) => unknown
            }[]
            for (let k = 0; k < 4; k++) {
                const value = outcome(() => arbitraryOf(c, rng, 2))
                if (typeof value === 'string') continue
                const wa = outcome(() => a?.encode(value))
                const wb = outcome(() => b?.encode(value))
                if (!same(wa, wb)) differs.push(`${label} encode`)
                if (typeof wa === 'string') continue
                if (
                    !same(
                        outcome(() => a?.decode(wa)),
                        outcome(() => b?.decode(wa)),
                    )
                )
                    differs.push(`${label} decode`)
                counts.values++
            }
            const options = def.kind === 'union' ? def.options : [def]
            const keys = new Set(
                options.flatMap((t) =>
                    t.kind === 'object' ? Object.keys(t.body.fields) : [],
                ),
            )
            for (const key of keys) {
                for (const make of clauseVocabulary) {
                    const pattern = object({ [key]: make() })
                    const x = outcome(() =>
                        termOf(extract(c as never, pattern as never)),
                    )
                    const y = outcome(() =>
                        termOf(extract(rebuilt as never, pattern as never)),
                    )
                    const agree =
                        typeof x === 'string' || typeof y === 'string'
                            ? x === y
                            : sameTerm(x as Term, y as Term)
                    if (!agree) differs.push(`${label} slice at ${key}`)
                    counts.clauses++
                }
            }
        }
        for (const c of codecs) {
            const def = c.def
            if (def.kind !== 'object' && def.kind !== 'union') continue
            counts.codecs++
            compare(c, codecOfTerm(termOf(c)) as AnyCodec, 'term')
            const reading = outcome(() => item(c as never))
            if (
                typeof reading === 'object' &&
                reading !== null &&
                'keys' in reading
            )
                continue
            counts.copies++
            compare(c, codecOfTerm(copy(def) as Term) as AnyCodec, 'copy')
        }
        expect(differs).toEqual([])
        expect(counts.values).toBeGreaterThan(0)
        expect(counts.clauses).toBeGreaterThan(0)
        console.log(`term readings: ${JSON.stringify(counts)}`)
    })

    /**
     * **The counts pin the pool, deliberately.** The pool depends on the seed alone, so a count
     * moves only when the draw, a constructor, or the emitter changes. Look at the move.
     *
     * A scope binds no slot of a fragment, so a fragment of a refused scope stays an open term,
     * and the pool drops each pair over such a fragment as an open fragment. At these seeds, three
     * draws of a recursive union put an older reader beside a list that reads the union, and the
     * scope refuses the two options as not shown compatible.
     */
    it('draws a pool that depends on the seed alone', () => {
        expect({
            seeds: perSeed.map((one) => ({
                seed: one.seed,
                pairs: one.pairs.length,
                fills: one.pairs.filter((p) => p.fills).length,
                disjoints: one.disjoints.length,
                separations: one.separations.length,
                slices: one.slices.length,
                clauses: one.slices.reduce((n, s) => n + s.clauses.length, 0),
                assignments: one.slices.filter((s) => s.keys?.length).length,
                guards: one.guards.length,
                codecsPathed: one.paths.length,
                paths: one.paths.reduce(
                    (n, v) => n + v.paths.filter(plainPath).length,
                    0,
                ),
                whenPaths: one.paths.reduce(
                    (n, v) => n + v.paths.filter((p) => !plainPath(p)).length,
                    0,
                ),
            })),
            dropped: Object.fromEntries([...dropped].sort()),
        }).toMatchInlineSnapshot(`
          {
            "dropped": {
              "a constructor refused the draw": 69,
              "path: a wall reaches a cycle: a wall reads its term at any depth, so the term has no scoped form": 1,
              "path: an open fragment: a thunk names a codec not yet declared, so the term has no scoped form": 73,
              "slice term: an open fragment: a thunk names a codec not yet declared, so the term has no scoped form": 17,
              "slice: the clause is a \`number\` literal: the host reads the literal under the float adapter of \`number\`, and the model names no float adapter": 1566,
              "term: an open fragment: a thunk names a codec not yet declared, so the term has no scoped form": 587,
            },
            "seeds": [
              {
                "assignments": 33,
                "clauses": 4005,
                "codecsPathed": 226,
                "disjoints": 1071,
                "fills": 5,
                "guards": 0,
                "pairs": 1071,
                "paths": 1999,
                "seed": 20261004,
                "separations": 1066,
                "slices": 82,
                "whenPaths": 6970,
              },
              {
                "assignments": 26,
                "clauses": 3285,
                "codecsPathed": 171,
                "disjoints": 1048,
                "fills": 6,
                "guards": 0,
                "pairs": 1048,
                "paths": 1740,
                "seed": 1,
                "separations": 1042,
                "slices": 68,
                "whenPaths": 5357,
              },
              {
                "assignments": 39,
                "clauses": 4455,
                "codecsPathed": 175,
                "disjoints": 1078,
                "fills": 11,
                "guards": 0,
                "pairs": 1078,
                "paths": 2149,
                "seed": 4,
                "separations": 1067,
                "slices": 89,
                "whenPaths": 10108,
              },
            ],
          }
        `)
    })

    /**
     * **A union that the host accepts has a warrant that the model proves.** A pair reaches the
     * separation emitter only after its terms print, so the emitter refuses a pair for two reasons:
     * the union is an open fragment, which the scope decides, or the host accepted the pair where
     * the model's decision refuses it. The second must not occur.
     */
    it('accepts no pair on a warrant that the model does not prove', () => {
        expect(
            [...dropped.keys()].filter(
                (why) =>
                    why.startsWith('separation: ') &&
                    !why.includes('the host decides the pair at the scope'),
            ),
        ).toEqual([])
    })

    /**
     * **Codecs that print one term get one host verdict.** The emitter prints a thunk that closes no
     * cycle as its body, and the model reads only the printed term, so it gives both codecs one
     * verdict. Each check above compares one codec with the model; this compares two codecs with
     * each other, and needs no kernel.
     */
    it('gives one host verdict to the codecs that print one term', () => {
        const { disagreements, pairGroups, termGroups } =
            samePrintDisagreements(pairs)
        expect(disagreements).toEqual([])
        expect(pairGroups).toBeGreaterThan(0)
        expect(termGroups).toBeGreaterThan(0)
    })

    /**
     * **A leaf or a tag behind a thunk changes no host verdict.** The same seeds build the pool
     * again with each leaf and each tag literal behind a thunk that closes no cycle. Each term prints
     * the same, so each emitted file and each drop must be the same: a difference is a host reader
     * that stops at a thunk where the model reads the term.
     *
     * **The decision of `at` is the same too.** The path rows of the two spellings are compared by
     * decision, and each difference is counted by its two decisions. The model reads one term in
     * both spellings, so a difference is a reader of `at` that stops at a thunk.
     */
    it('builds the same pool when each leaf and tag sits behind a thunk', () => {
        const plain = [...dropped]
        const withoutPaths = (seeds: ReturnType<typeof buildPool>) =>
            poolModules(seeds.map((one) => ({ ...one, paths: [] })))
        const before = withoutPaths(perSeed)
        const decidedBefore = decisionsOf(perSeed)
        dropped.clear()
        thunked = true
        let wrapped: readonly (readonly [string, string])[]
        let wrappedDrops: [string, number][]
        let decidedWrapped: ReadonlyMap<string, string>
        try {
            const seeds = buildPool()
            wrappedDrops = [...dropped]
            wrapped = withoutPaths(seeds)
            decidedWrapped = decisionsOf(seeds)
        } finally {
            thunked = false
            dropped.clear()
            for (const [why, n] of plain) dropped.set(why, n)
        }
        const firstDifference = (a: string, b: string) => {
            const [x, y] = [a.split('\n'), b.split('\n')]
            const at = x.findIndex((line, i) => line !== y[i])
            return at === -1 && x.length === y.length
                ? 'same'
                : `line ${at + 1}: ${x[at]?.slice(0, 160)} / ${y[at]?.slice(0, 160)}`
        }
        expect(
            wrapped.map(([file, text], i) => [
                file,
                firstDifference(before[i]?.[1] ?? '', text),
            ]),
        ).toEqual(before.map(([file]) => [file, 'same']))
        const notPath = ([why]: [string, number]) => !why.startsWith('path: ')
        expect(wrappedDrops.filter(notPath).sort()).toEqual(
            plain.filter(notPath).sort(),
        )
        const changed = new Map<string, number>()
        for (const [key, kind] of decidedBefore) {
            const other = decidedWrapped.get(key)
            if (other === undefined || other === kind) continue
            const move = `${kind} -> ${other}`
            changed.set(move, (changed.get(move) ?? 0) + 1)
        }
        expect(Object.fromEntries([...changed].sort())).toEqual({})
    })

    /**
     * **Narrowing at a recursive union decides each option as at any union.** Each option prints as
     * a closed codec of its own, so the row reads `narrowC` over the options. The run time keeps the
     * option of `leaf` and resolves `v` to `string`, and the row states that frontier, which the
     * kernel checks in the path module.
     */
    it('narrows at a recursive union as at any union, and the row states the decision of the run time', () => {
        const one = recursiveNarrowing()
        expect(unionAt(hostAt(one.codec, ['n']))).toBe(true)
        const [leaf] = one.paths
        const decided = leaf && hostAt(one.codec, leaf)
        expect(
            decided?.kind === 'resolved' && !('mark' in decided.codec.def)
                ? decided.codec.def.kind
                : decided?.kind,
        ).toBe('string')
        const printed = leanPath(one)
        expect(printed).toContain('NarrowRowsC')
        expect(printed).toContain('([.name "v"], .resolved')
    })

    /**
     * **No column of a pair is checked by `#eval` alone.** A pair with a fill on each side has no
     * separation vector, so the kernel states its guard column in a row of its own. **A pair over
     * an open fragment states no row**: a scope judges the closed copy of the union, so the host
     * decides nothing on the pair. The scoped print refuses an open fragment, so no such
     * pair enters the pool, and the refusal is asserted on a pair that reads `ref('undeclared')`.
     */
    it('states the guard column of each pair of two fills in the kernel, and refuses a pair over an open fragment', () => {
        const fills = pairs.filter((p) => p.fills)
        expect(fills).toHaveLength(22)
        expect(fills.filter((p) => pairGuardRefusal(p) !== undefined)).toEqual(
            [],
        )
        expect(
            pairGuardRefusal({
                name: 'open',
                left: erase(array(undeclared)),
                right: erase(string),
            }),
        ).toContain('no scope binds')
        const module = new Map(poolModules(perSeed)).get(
            '.pool.separations.lean',
        )
        for (const { name } of fills) {
            expect(module).toMatch(
                new RegExp(`\\("${name}", \\([^\\n]*, (true|false)\\)\\)`),
            )
        }
        expect(module).toContain('failing pairGuardOk (pairGuards0 ρ π) = []')
    })

    it('emits the kernel vectors for the gate', () => {
        const modules = poolModules(perSeed)
        if (process.env.EMIT_LEAN_REFUSALS) {
            const formal = join(process.cwd(), 'formal')
            for (const [file, text] of modules)
                writeFileSync(join(formal, file), text)
        }
        expect(modules.map(([file]) => file)).toEqual([
            '.pool.disjoints.lean',
            '.pool.separations.lean',
            '.pool.slices.lean',
            '.pool.paths0.lean',
            '.pool.paths1.lean',
            '.pool.paths2.lean',
            '.pool.paths3.lean',
            '.pool.guards.lean',
            '.pool.meets.lean',
        ])
    })

    /**
     * **The type of a slice and of a path states the decision of the run time.** Each check is one
     * decision of the run time, put to the type checker. The gate compiles the files and holds the
     * set of disagreements to its list. The printer throws at a root that it cannot print, so no
     * root leaves the check in silence.
     */
    it('emits the type vectors for the gate', () => {
        const files = typeVectorFiles({
            slices: perSeed.flatMap((one) => one.slices),
            paths: [...perSeed.flatMap((one) => one.paths), nestedClause()],
            clauses: clauseVocabulary,
        })
        if (process.env.EMIT_LEAN_REFUSALS) {
            const types = join(process.cwd(), 'formal', '.pool.types')
            mkdirSync(types, { recursive: true })
            for (const [file, text] of files)
                writeFileSync(join(types, file), text)
        }
        expect(files.map(([file]) => file)).toEqual([
            'codecs.ts',
            'slices0.ts',
            'slices1.ts',
            'slices2.ts',
            'slices3.ts',
            'slices4.ts',
            'slices5.ts',
            'slices6.ts',
            'slices7.ts',
            'slices8.ts',
            'slices9.ts',
            'paths0.ts',
            'paths1.ts',
            'paths2.ts',
            'rows.json',
            'tsconfig.slices.json',
            'tsconfig.paths0.json',
            'tsconfig.paths1.json',
            'tsconfig.paths2.json',
        ])
    })
})

/**
 * **Fits is the order of the meet.** Over the pool pairs in both orders, `fits(o, P)` holds exactly
 * where the meet that reads `o` as written and `P` open is `o`. The order needs the written reading
 * of the option: a closed option holds no undeclared name, so it lies below a pattern that declares
 * an optional name that the option lacks. A pair whose meet refuses, or whose equivalence the
 * sample cannot decide, decides nothing.
 */
describe('fits is the order of the meet', () => {
    /**
     * Whether two terms hold one set of values: one term, or two codecs that write and read each
     * sampled value alike. `undefined` where the check cannot decide, as at a value that no side
     * writes. The first term samples first: the option is a pool term, and a recursive meet draws
     * slowly, so a difference that the option shows ends the check early.
     */
    const equivalent = (a: Term, b: Term): boolean | undefined => {
        if (sameTerm(a, b)) return true
        if (holdsNoValue(a) !== holdsNoValue(b)) return false
        const x = codecOfTerm<unknown, AttributeValue>(a)
        const y = codecOfTerm<unknown, AttributeValue>(b)
        for (const [one, other] of [
            [x, y],
            [y, x],
        ]) {
            if (one === undefined || other === undefined) return undefined
            try {
                checkEquivalent(one, other, { count: 20 })
            } catch (error) {
                return error instanceof Error &&
                    error.message.startsWith('these codecs')
                    ? false
                    : undefined
            }
        }
        return true
    }

    /**
     * **The stated limits.** Twelve pairs disagree, and each has a named cause.
     *
     * - The refinement limit: `1.224 lr`, `1.394 lr`, `1.470 rl`, `1.471 rl`, `1.472 rl`,
     *   `1.473 rl`, `1.544 lr` and `4.928 rl`. The pattern holds a refinement, of `opaque` or of
     *   a decimal. The meet refines the option by the predicate, and the host cannot read the
     *   predicate, so `fits` answers no, and the sample finds no value that the predicate refuses.
     * - The closure limit: `20261004.648 lr`, `4.604 lr` and `4.605 lr`. The option is an older
     *   reading of the pattern, and the meet is the pattern. The older reader of the pool returns a
     *   value that the current form cannot write, so the older reading holds the pairs of the
     *   pattern and no other pair. An opaque function decides that, and the order cannot read it,
     *   so `fits` answers no.
     * - `1.950 lr`, a sampler miss: an open option whose block holds a number, against a pattern
     *   that holds the optional name `m` at an object. The meet holds `m` at `never`, and the
     *   option holds `m` at its block. The sample draws no value at `m`, so a decode shows the
     *   difference.
     */
    it('holds fits exactly where the meet of the option as written and the pattern open is the option', () => {
        const rows = buildPool().flatMap((one) =>
            one.pairs.flatMap((pair, at) => [
                { key: `${one.seed}.${at} lr`, o: pair.left, p: pair.right },
                { key: `${one.seed}.${at} rl`, o: pair.right, p: pair.left },
            ]),
        )
        const disagree: string[] = []
        let decided = 0
        for (const { key, o, p } of rows) {
            let kept: boolean | undefined
            try {
                kept = equivalent(termOf(o), termOf(meetOrdered(o, p)))
            } catch {
                continue
            }
            if (kept === undefined) continue
            decided++
            if (fits(termOf(o), termOf(p)) !== kept) disagree.push(key)
        }
        expect(decided).toBeGreaterThan(rows.length / 2)
        expect(disagree).toEqual([
            '20261004.648 lr',
            '1.224 lr',
            '1.394 lr',
            '1.470 rl',
            '1.471 rl',
            '1.472 rl',
            '1.473 rl',
            '1.544 lr',
            '1.950 lr',
            '4.604 lr',
            '4.605 lr',
            '4.928 rl',
        ])
        const missed = rows.find((row) => row.key === '1.950 lr')
        expect(missed).toBeDefined()
        if (missed === undefined) return
        const stored = { M: { a: { N: '1' }, m: { N: '1' } } }
        expect(failed(missed.o.decode(stored))).toBe(false)
        expect(failed(meetOrdered(missed.o, missed.p).decode(stored))).toBe(
            true,
        )
    })
})
