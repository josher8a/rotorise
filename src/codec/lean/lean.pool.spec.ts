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
 */
import { mkdirSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../attribute'
import { DynamoNumber, isNumeral, isStoredNumeral } from '../attribute'
import type { AnyCodec } from '../codec'
import {
    array,
    at,
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    exclude,
    extract,
    fill,
    fits,
    held,
    item,
    legacy,
    list,
    mdunion,
    meet,
    meetOrdered,
    narrow,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    opened,
    optional,
    ref,
    refine,
    scope,
    spread,
    string,
    undefinable,
    union,
} from '../codec'
import { codecOfTerm, termOf } from '../denote'
import type {
    DisjointPair,
    FitRow,
    FormerGuard,
    HostAt,
    MeetCover,
    PathStep,
    PathVectors,
    Separation,
    Slice,
} from '../lean'
import {
    disjointRows,
    hostAt,
    LeanUnemittable,
    leanAttrOf,
    leanClosedOf,
    leanClosedOfTerm,
    leanDisjointRowModule,
    leanFitModule,
    leanFormerGuard,
    leanFormerGuardModule,
    leanGraphOf,
    leanMeetCoverModule,
    leanPath,
    leanPathModules,
    leanSeparationRowModule,
    leanShapes,
    leanSlice,
    leanSliceModule,
    leanValueOf,
    reachable,
    separationForm,
    separationRows,
    sliceableOf,
    unionAt,
} from '../lean'
import { Disagreement, failed, orThrow } from '../result'
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
import type { MeetPair } from '../typeVectors'
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
/** The values that the fit rows draw from each option. */
const FIT_SAMPLES = 1

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
                    let filled: unknown
                    try {
                        filled = arbitraryOf(c.codec, rng, 2)
                    } catch {
                        filled = 'x'
                    }
                    spec[at] = fill(c.codec, filled as never)
                    parts.push(
                        `${at}~${JSON.stringify(filled) ?? 'u'}:${c.name}`,
                    )
                } else if (slot === 3) {
                    spec[at] = legacy({
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
                    legacy({
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

/** One pair of the pool, with the host verdicts and the two terms that the model reads. */
type PoolPair = {
    readonly name: string
    readonly label: string
    readonly left: AnyCodec
    readonly right: AnyCodec
    /** The host verdicts, in the order disjoint, views, agrees, guard, union. */
    readonly host: string
    readonly l: string
    readonly r: string
    readonly closures: readonly string[]
    readonly readers: readonly string[]
}

const bit = (b: boolean): string => (b ? '1' : '0')

/** Where a draw or a pair left the pool, by reason. */
const dropped = new Map<string, number>()
const drop = (why: string) => dropped.set(why, (dropped.get(why) ?? 0) + 1)

/**
 * **The covers: a finite base against the union of its literals.** The random draw builds no union
 * of every literal of a base, so a pattern that covers a base by its literals needs a fixed
 * draw. Each cover is a root or a field of a pattern, built through the public constructors.
 * The pairs among the covers hold the cases where a union on the pattern side must split: a base,
 * an object field, two fields against the four combinations, and a tuple position. A list of a
 * base does not split, so `array(boolean)` stands against `array(true) | array(false)` as the
 * pair that must stay refused.
 */
const covers: readonly Entry[] = (() => {
    const both = union([boolean(true), boolean(false)])
    const cell = (a: boolean, b: boolean) =>
        object({ a: boolean(a), b: boolean(b) })
    return [
        ['boolean', boolean],
        ['true', boolean(true)],
        ['true|false', both],
        ['object{k:boolean}', object({ k: boolean })],
        ['object{k:true|false}', object({ k: both })],
        ['object{k:boolean,n:string}', object({ k: boolean, n: string })],
        ['object{a:boolean,b:boolean}', object({ a: boolean, b: boolean })],
        [
            'object{a,b:literal}x4',
            union([
                cell(true, true),
                cell(true, false),
                cell(false, true),
                cell(false, false),
            ]),
        ],
        ['list(boolean,string)', list(boolean, string)],
        [
            'list(true,string)|list(false,string)',
            union([list(boolean(true), string), list(boolean(false), string)]),
        ],
        ['array(boolean)', array(boolean)],
        [
            'array(true)|array(false)',
            union([array(boolean(true)), array(boolean(false))]),
        ],
    ].map(([name, codec]) => ({
        name: name as string,
        codec: erase(codec),
    }))
})()

/**
 * **The fills: two fill values at one name, equal and apart.** The random draw gives each fill a
 * fill value of its own, so it rarely draws two equal ones. Each pair is two objects that declare
 * one name through `fill`: two equal texts, two texts that differ, and two equal objects.
 * The meet of the first and of the third pair is the fill, and the meet of the second is refused.
 */
const fills: readonly (readonly [Entry, Entry])[] = (() => {
    const build = object as unknown as (spec: unknown) => AnyCodec
    const text = (current: AnyCodec, whenMissing: string) =>
        erase(
            build({
                a: fill(current as never, whenMissing as never),
            }),
        )
    const named = (nick: string) =>
        erase(
            object({
                a: fill(object({ nick: string }), { nick }),
            }),
        )
    const entry = (name: string, codec: AnyCodec): Entry => ({ name, codec })
    return [
        [
            entry('object{a~x:x|y}', text(string('x', 'y'), 'x')),
            entry('object{a~x:x|z}', text(string('x', 'z'), 'x')),
        ],
        [
            entry('object{a~x:x|y}', text(string('x', 'y'), 'x')),
            entry('object{a~y:x|y}', text(string('x', 'y'), 'y')),
        ],
        [
            entry('object{a~{rex}}', named('rex')),
            entry('object{a~{rex}}', named('rex')),
        ],
    ]
})()

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
    if (seed === SEEDS[0]) {
        for (let i = 0; i < covers.length; i++) {
            for (let j = i; j < covers.length; j++) {
                add(covers[i] as Entry, covers[j] as Entry)
            }
        }
    }
    if (seed === SEEDS[0]) for (const [a, b] of fills) add(a, b)
    for (const [a, b] of declared) add(a, b)
    return pairs
}

/** The pairs that each kernel module states; a refusal of the emitter drops the pair by reason. */
const kernelPairs = (pairs: readonly PoolPair[]) => {
    const disjoints: DisjointPair[] = []
    const separations: Separation[] = []
    for (const p of pairs) {
        const one = { name: p.name, left: p.left, right: p.right }
        try {
            disjointRows([one]).rows(leanShapes(() => 'f'))
            disjoints.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`disjoint: ${error.reason}`)
        }
        try {
            separationRows([one]).rows(leanShapes(() => 'f'))
            separations.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`separation: ${error.reason}`)
        }
    }
    return { disjoints, separations }
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

/**
 * **The roots that only the type square reads.** A key that a `ref` pins below a union in a field
 * needs a scope in the print. The printer prints a `ref` that closes no cycle as its body, so each
 * root here closes a cycle: the entry that names the literal reaches the entry that holds the
 * field. The model reads these roots through the pool, and the square puts the literals of the
 * root to `extract` and `exclude`.
 */
const typeOnlySlices: readonly Slice[] = (() => {
    const pet = object({ kind: string('pet'), size: string('small') })
    const { Large, Red } = scope({
        Large: object({
            kind: string('pet'),
            size: string('large'),
            colour: union([ref('Red'), string('blue')]),
        }),
        Red: union([string('red'), array(ref('Large'))]),
    })
    const { Wide } = scope({
        Wide: object({
            kind: string('pet'),
            size: string('wide'),
            colour: union([ref('Hot'), ref('Cold')]),
        }),
        Hot: union([string('red'), array(ref('Wide'))]),
        Cold: string('blue'),
    })
    void Red
    return [
        { name: 'type_only_ref_union', codec: union([pet, Large]) },
        { name: 'type_only_ref_refs', codec: union([pet, Wide]) },
    ].map(({ name, codec }) => ({
        name,
        codec: sliceableOf(erase(codec)),
        clauses: [],
    }))
})()

/**
 * **The meets that only the type square reads**, each pinned so that the first roots of the pool
 * never drop it. A plain part against an opaque part fits neither side, and the two views overlap,
 * so the run time refuses the pair. A plain part against a plain part that the views keep apart
 * meets at the bottom. Two literal sets under one adapter meet at the common literals.
 */
const typeOnlyMeets: readonly MeetPair[] = (() => {
    const widened = legacy({ current: string, older: decimal })
    return [
        [string, opaque('lossy')],
        [opaque('lossy'), string],
        [string, number],
        [decimal('1', '2'), decimal('2', '3')],
        [decimal, decimal],
        [widened, decimal('1')],
    ].map(([left, right]) => ({
        left: erase(left),
        right: erase(right),
        pinned: true,
    }))
})()

/**
 * **The roots whose slots differ in presence, adapter and layout**, against the patterns that the
 * square puts to them: an `undefinable` or an `optional` slot, a `held` slot, a base slot, a list
 * with a prefix and a spread, a decimal literal set against a union of decimal literals, and a
 * pattern of two keys. The members hold an older reading, a fill value, a list and a decimal union.
 */
const presenceAndHolds: Slice = (() => {
    const dog = object({
        kind: string('dog'),
        name: string,
        petIds: list(string),
        price: union([decimal('1'), decimal('2')]),
    })
    const cat = object({
        kind: string('cat'),
        nickname: optional(string),
        name: legacy({ current: string, older: decimal }),
        petIds: list(string, spread(string)),
    })
    const fish = object({
        kind: string('fish'),
        name: fill(string, 'unnamed'),
        price: string('free'),
    })
    return {
        name: 'presence_and_holds',
        codec: sliceableOf(erase(union([dog, cat, fish]))),
        clauses: [],
        shapes: [
            { nickname: erase(undefinable(string)) },
            { nickname: erase(optional(string)) },
            { name: erase(opaque('lossy')) },
            { name: erase(string) },
            { kind: erase(string) },
            { petIds: erase(list(string, spread(string))) },
            { petIds: erase(list(string)) },
            { price: erase(decimal('1', '2')) },
            { kind: erase(string('dog')), name: erase(string) },
        ],
    }
})()

/**
 * **The roots whose member reads an object through a `ref`**, bare in a slot, below a `list`, below an
 * `array`, and in a recursive entry. Each cat and dog names its basket back through an optional
 * slot, so the `ref` closes a cycle and the print keeps it. The patterns are the shapes that the
 * square puts to the roots: an object pattern, a `list` pattern and an `array` pattern of one
 * object.
 */
const refObjects: readonly Slice[] = (() => {
    const kind = (name: string) => erase(object({ kind: string(name) }))
    const tagged = (name: string) => erase(object({ tag: string(name) }))
    const roots = (
        slot: (name: string) => AnyCodec,
        key: string,
        shape: (c: AnyCodec) => AnyCodec,
        [a, b]: readonly [string, string],
    ): Slice => {
        const entries = scope({
            Cat: object({ kind: string('cat'), home: optional(ref(a)) }),
            Dog: object({ kind: string('dog'), home: optional(ref(b)) }),
            [a]: object({ tag: string(a), [key]: slot('Cat') }),
            [b]: object({ tag: string(b), [key]: slot('Dog') }),
        } as never) as unknown as Record<string, AnyCodec>
        return {
            name: `through_ref_${key}`,
            codec: sliceableOf(erase(union([entries[a], entries[b]] as never))),
            clauses: [],
            shapes: [
                { [key]: shape(kind('cat')) },
                { [key]: shape(kind('dog')) },
            ],
        }
    }
    const one = (c: AnyCodec) => c
    const first = (name: string) => erase(ref(name))
    const many = (name: string) => erase(list(ref(name)))
    const each = (name: string) => erase(array(ref(name)))
    const { Mother, Stray } = scope({
        Mother: object({ tag: string('mother'), kits: list(ref('Mother')) }),
        Stray: object({ tag: string('stray'), kits: list(ref('Stray')) }),
    })
    const unions = (nested: boolean): Slice => {
        const entries = scope({
            Cat: object({ kind: string('cat'), home: optional(ref('Basket')) }),
            Dog: object({ kind: string('dog'), home: optional(ref('Crate')) }),
            Bird: object({
                kind: string('bird'),
                home: optional(ref('Basket')),
            }),
            Pets: union([ref('Cat'), ref('Dog')]),
            Zoo: union([ref('Pets'), ref('Bird')]),
            Basket: object({
                tag: string('basket'),
                pet: ref(nested ? 'Zoo' : 'Pets'),
            }),
            Crate: object({ tag: string('crate'), pet: ref('Dog') }),
        })
        return {
            name: `through_ref_${nested ? 'zoo' : 'pets'}`,
            codec: sliceableOf(erase(union([entries.Basket, entries.Crate]))),
            clauses: [],
            shapes: [
                { pet: erase(union([kind('cat'), kind('dog')])) },
                { pet: kind('dog') },
                ...(nested
                    ? [
                          {
                              pet: erase(
                                  union([
                                      kind('cat'),
                                      kind('dog'),
                                      kind('bird'),
                                  ]),
                              ),
                          },
                      ]
                    : []),
            ],
        }
    }
    return [
        roots(first, 'pet', one, ['Basket', 'Crate']),
        unions(false),
        unions(true),
        roots(many, 'pets', (c) => erase(list(c)), ['Kennel', 'Run']),
        roots(each, 'herd', (c) => erase(array(c)), ['Herd', 'Pack']),
        {
            name: 'through_ref_cycle',
            codec: sliceableOf(erase(union([Mother, Stray]))),
            clauses: [],
            shapes: [
                { kits: erase(list(tagged('mother'))) },
                {
                    kits: erase(
                        list(
                            object({
                                tag: string('mother'),
                                kits: list(tagged('mother')),
                            }),
                        ),
                    ),
                },
            ],
        },
    ]
})()

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
                    a: erase(legacy({ current: string, older: string })),
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

/**
 * **The fit rows of the pool**: each pair in both orders, with the verdict of `fits` of the option
 * against the pattern, and the value that a draw from the option writes. A row where `fits` says
 * yes states that the model's opened pattern writes the value, and the sample finds no value that
 * the opened pattern refuses where `fits` says yes: a refusal there is a failure of the row. A row
 * where `fits` says no is a witness only where `src/` itself refuses the value through the opened
 * pattern, so the kernel checks that the model refuses the same value. A term with a refinement or
 * a cycle states no row, for the reasons of {@link meetCoversOf}.
 */
const fitRowsOf = (pairs: readonly PoolPair[]): FitRow[] => {
    const rows: FitRow[] = []
    const seen = new Set<string>()
    const emits = (f: () => unknown): boolean => {
        try {
            f()
            return true
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`fit: ${error.reason}`)
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
        for (const [option, pattern, order] of orders) {
            const name = `${p.name}_${order}`
            const two = [option, pattern]
            if (
                two.some(
                    (c) =>
                        'mark' in c.def ||
                        [...reachable(c.def)].some((t) => t.kind === 'refine'),
                )
            ) {
                drop('fit: a refinement, the stated limit')
                continue
            }
            if (two.some((c) => recursionUse(c.def as Term) > 0)) {
                drop('fit: a cycle, which the diagnostic `#eval` cannot afford')
                continue
            }
            const opening = opened(termOf(pattern))
            const holds = fits(termOf(option), termOf(pattern))
            // the opened pattern may have no codec: a refusal states no witness
            const refuses = (() => {
                try {
                    return codecOfTerm<unknown, AttributeValue>(opening)
                } catch {
                    return undefined
                }
            })()
            const printed: string[] = []
            if (
                !emits(() => {
                    printed.push(leanClosedOf(option, name))
                    printed.push(leanClosedOfTerm(opening, name))
                })
            )
                continue
            for (let k = 1; k <= FIT_SAMPLES; k++) {
                let value: unknown
                try {
                    value = absentUndefined(arbitraryOf(option, rngFrom(k), 3))
                } catch {
                    continue
                }
                const attribute = option.encode(value as never)
                if (failed(attribute)) continue
                if (
                    !holds &&
                    (refuses === undefined ||
                        !failed(refuses.encode(value as never)))
                ) {
                    continue
                }
                let row = ''
                if (
                    !emits(() => {
                        row = `${leanValueOf(value)} ${leanAttrOf(attribute as AttributeValue)} ${holds}`
                    })
                )
                    continue
                const key = `${printed.join('|')}|${row}`
                if (seen.has(key)) continue
                seen.add(key)
                rows.push({
                    name: `${name}_${rows.length}`,
                    option,
                    pattern: opening,
                    value,
                    attribute: attribute as AttributeValue,
                    holds,
                })
            }
        }
    }
    return rows
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
        '.pool.fits.lean',
        leanFitModule(fitRowsOf(perSeed.flatMap((one) => one.pairs))),
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
              "a constructor refused the draw": 70,
              "path: a wall reaches a cycle: a wall reads its term at any depth, so the term has no scoped form": 1,
              "path: an open fragment: a thunk names a codec not yet declared, so the term has no scoped form": 75,
              "slice term: an open fragment: a thunk names a codec not yet declared, so the term has no scoped form": 19,
              "slice: the clause is a \`number\` literal: the host reads the literal under the float adapter of \`number\`, and the model names no float adapter": 1628,
              "term: an open fragment: a thunk names a codec not yet declared, so the term has no scoped form": 613,
            },
            "seeds": [
              {
                "assignments": 33,
                "clauses": 4380,
                "codecsPathed": 241,
                "disjoints": 1152,
                "guards": 0,
                "pairs": 1152,
                "paths": 2043,
                "seed": 20261004,
                "separations": 1152,
                "slices": 95,
                "whenPaths": 7012,
              },
              {
                "assignments": 24,
                "clauses": 3285,
                "codecsPathed": 163,
                "disjoints": 1006,
                "guards": 0,
                "pairs": 1006,
                "paths": 1846,
                "seed": 1,
                "separations": 1006,
                "slices": 69,
                "whenPaths": 5347,
              },
              {
                "assignments": 39,
                "clauses": 4545,
                "codecsPathed": 174,
                "disjoints": 1078,
                "guards": 0,
                "pairs": 1078,
                "paths": 2143,
                "seed": 4,
                "separations": 1078,
                "slices": 93,
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
     * **A pair over an open fragment states no row**: a scope judges the closed copy of the union,
     * so the host decides nothing on the pair. The scoped print refuses an open fragment, so no such
     * pair enters the pool, and the refusal is asserted on a pair that reads `ref('undeclared')`.
     */
    it('refuses a pair over an open fragment', () => {
        expect(() =>
            separationForm({
                name: 'open',
                left: erase(array(undeclared)),
                right: erase(string),
            }),
        ).toThrow(/no scope binds/)
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
            '.pool.fits.lean',
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
            slices: [
                ...perSeed.flatMap((one) => one.slices),
                ...typeOnlySlices,
                presenceAndHolds,
                ...refObjects,
            ],
            paths: [...perSeed.flatMap((one) => one.paths), nestedClause()],
            meets: [...pairs, ...typeOnlyMeets],
            clauses: clauseVocabulary,
        })
        if (process.env.EMIT_LEAN_REFUSALS) {
            const types = join(process.cwd(), 'formal', '.pool.types')
            mkdirSync(types, { recursive: true })
            for (const [file, text] of files)
                writeFileSync(join(types, file), text)
        }
        // a resolved path row has a `decoded` row, but where the codec draws no value
        const rows: readonly { readonly id: string }[] = JSON.parse(
            files.find(([file]) => file === 'rows.json')?.[1] ?? '[]',
        )
        const rowsOf = (group: string) =>
            rows.filter((row) => row.id.startsWith(`${group}|accept|`)).length
        expect({
            resolvedPathRows: rowsOf('path'),
            decodedRows: rowsOf('decoded'),
        }).toEqual({ resolvedPathRows: 7359, decodedRows: 7210 })
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
            'meets0.ts',
            'rows.json',
            'tsconfig.slices0.json',
            'tsconfig.slices1.json',
            'tsconfig.slices2.json',
            'tsconfig.slices3.json',
            'tsconfig.slices4.json',
            'tsconfig.slices5.json',
            'tsconfig.slices6.json',
            'tsconfig.slices7.json',
            'tsconfig.slices8.json',
            'tsconfig.slices9.json',
            'tsconfig.paths0.json',
            'tsconfig.paths1.json',
            'tsconfig.paths2.json',
            'tsconfig.meets0.json',
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
                return error instanceof Disagreement ? false : undefined
            }
        }
        return true
    }

    /**
     * **The stated limits.** Twenty-four pairs disagree, and each has a named cause.
     *
     * - The refinement limit: `1.198 lr`, `1.428 rl`, `1.429 rl`, `1.431 rl`, `1.433 rl`,
     *   `1.434 rl`, `1.435 rl`, `1.456 lr`, `1.561 rl`, `1.681 lr`, `1.743 lr`, `4.848 rl`,
     *   `4.850 lr`, `4.850 rl` and `4.928 rl`. The pattern holds a refinement. The meet refines the option
     *   by the predicate, and the host cannot read the predicate, so `fits` answers no, and the
     *   sample finds no value that the predicate refuses.
     * - The closure limit: `20261004.648 lr`, `20261004.969 rl`, `20261004.972 rl`, `4.590 rl`,
     *   `4.604 lr`, `4.605 lr`, `4.720 lr` and `4.901 lr`. The option holds an older reading of a
     *   part of the pattern, and the meet holds that part of the pattern. The older reader of the
     *   pool returns a value that the current form cannot write, so the older reading holds the
     *   pairs of the current form and no other pair. An opaque function decides that, and the
     *   order cannot read it, so `fits` answers no.
     * - `1.925 lr`, a sampler miss: an open option whose block holds a number, against a pattern
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
        let sampledNo = 0
        for (const { key, o, p } of rows) {
            let kept: boolean | undefined
            let sampled = false
            try {
                const meet = termOf(meetOrdered(o, p))
                kept = equivalent(termOf(o), meet)
                sampled = holdsNoValue(termOf(o)) === holdsNoValue(meet)
            } catch {
                continue
            }
            if (kept === undefined) continue
            decided++
            if (sampled && !kept) sampledNo++
            if (fits(termOf(o), termOf(p)) !== kept) disagree.push(key)
        }
        expect(decided).toBeGreaterThan(rows.length / 2)
        // the sample decides no as well as yes: a check that never sees a disagreement decides no
        // only where one side holds no value
        expect(sampledNo).toBeGreaterThan(0)
        expect(disagree).toEqual([
            '20261004.648 lr',
            '20261004.969 rl',
            '20261004.972 rl',
            '1.23 lr',
            '1.147 lr',
            '1.273 lr',
            '1.436 lr',
            '1.449 rl',
            '1.450 rl',
            '1.451 rl',
            '1.453 rl',
            '1.454 rl',
            '1.455 rl',
            '1.476 lr',
            '1.478 lr',
            '1.743 lr',
            '1.856 lr',
            '1.885 lr',
            '1.918 lr',
            '4.590 rl',
            '4.604 lr',
            '4.605 lr',
            '4.720 lr',
            '4.848 rl',
            '4.850 lr',
            '4.850 rl',
            '4.901 lr',
            '4.928 rl',
        ])
        const missed = rows.find((row) => row.key === '1.918 lr')
        expect(missed).toBeDefined()
        if (missed === undefined) return
        const stored = { M: { a: { N: '1' }, m: { N: '1' } } }
        expect(failed(missed.o.decode(stored))).toBe(false)
        expect(failed(meetOrdered(missed.o, missed.p).decode(stored))).toBe(
            true,
        )
    })
})

/**
 * **The algebraic laws of `narrow` and of the meet**, over the pool. The model states each operation
 * as a relation of rows and values, and each law is a fact of that relation that the host must keep:
 *
 * - **`narrow` is idempotent**, and keeps what `extract` keeps. `narrow` keeps an option that the
 *   clause does not separate, and `extract` keeps an option that fits the clause, so `narrow` keeps
 *   more. The law is the inclusion.
 * - **The meet commutes.** `meet(a, b)` and `meet(b, a)` write and read one set of rows: one term,
 *   or two terms that agree on a sample.
 *
 * A law that skips every case proves nothing, so each asserts the number of cases that it decides
 * and pins the cases that it skips and the cases that it cannot decide. A pool change that moves a
 * count is a change of the draw, and it names itself.
 */
describe('the algebraic laws of narrow and of the meet, over the pool', () => {
    // built at the first law that runs, and not at collection: the draw writes the module state
    // that the first describe of this file reads, so a second build at collection would move it
    let built: ReturnType<typeof buildPool> | undefined
    const poolOf = () => {
        built ??= buildPool()
        return {
            pairs: built.flatMap((one) => one.pairs),
            slices: built.flatMap((one) => one.slices),
        }
    }
    const merge = meet as unknown as (a: AnyCodec, b: AnyCodec) => unknown
    /** A term that states no row of the pool, for the reasons of {@link meetCoversOf}. */
    const stated = (c: AnyCodec): boolean =>
        !('mark' in c.def) &&
        ![...reachable(c.def)].some((t) => t.kind === 'refine') &&
        recursionUse(c.def as Term) === 0
    const shown = (value: unknown): string =>
        JSON.stringify(value, (_, x) =>
            typeof x === 'bigint' ? `${x}n` : x instanceof Set ? [...x] : x,
        )?.slice(0, 160) ?? 'undefined'
    const drawn = (codec: AnyCodec, seed: number): unknown | undefined => {
        try {
            return arbitraryOf(codec, rngFrom(seed), 3)
        } catch {
            return undefined
        }
    }

    it('narrow is idempotent, and keeps what extract keeps', () => {
        const { slices } = poolOf()
        const count = { slices: 0, unrooted: 0, values: 0, wider: 0 }
        const broken: string[] = []
        for (const s of slices) {
            const c = s.codec as AnyCodec
            let root: unknown
            try {
                root = item(c as never)
            } catch {
                count.unrooted++
                continue
            }
            for (const clause of s.clauses) {
                const pattern = erase(object(clause as never))
                let kept: AnyCodec
                let once: { encode: (v: unknown) => unknown }
                let twice: { encode: (v: unknown) => unknown }
                try {
                    kept = erase(extract(c as never, pattern as never))
                    once = (
                        narrow as never as (
                            l: unknown,
                            p: unknown,
                        ) => typeof once
                    )(
                        (
                            at as never as (
                                c: unknown,
                                p: readonly never[],
                            ) => unknown
                        )(root, []),
                        pattern,
                    )
                    twice = (
                        narrow as never as (
                            l: unknown,
                            p: unknown,
                        ) => typeof twice
                    )(once, pattern)
                } catch {
                    count.unrooted++
                    continue
                }
                count.slices++
                for (let seed = 1; seed <= 6; seed++) {
                    const value = drawn(c, seed)
                    if (value === undefined || failed(c.encode(value as never)))
                        continue
                    count.values++
                    const first = once.encode(value)
                    const second = twice.encode(value)
                    if (
                        failed(first) !== failed(second) ||
                        (!failed(first) && !structuralEquals(first, second))
                    ) {
                        broken.push(`${s.name} idempotent ${shown(value)}`)
                    }
                    const inKept = !failed(kept.encode(value as never))
                    if (inKept && failed(first)) {
                        broken.push(
                            `${s.name} extract keeps ${shown(value)}, narrow refuses`,
                        )
                    }
                    if (!inKept && !failed(first)) count.wider++
                }
            }
        }
        expect(broken).toEqual([])
        expect(count.values).toBeGreaterThan(count.slices)
        expect(count).toEqual({
            slices: 12210,
            unrooted: 0,
            values: 70920,
            wider: 4234,
        })
    })

    it('the meet commutes, as one term or as two terms that agree', () => {
        const { pairs } = poolOf()
        const count = {
            pairs: 0,
            sameTerm: 0,
            sameAccepts: 0,
            undecided: 0,
            bothRefused: 0,
            skipped: 0,
        }
        const broken: string[] = []
        const built = (a: AnyCodec, b: AnyCodec): AnyCodec | undefined => {
            try {
                return erase(merge(a, b))
            } catch {
                return undefined
            }
        }
        for (const p of pairs) {
            const ab = built(p.left, p.right)
            const ba = built(p.right, p.left)
            if (ab === undefined && ba === undefined) {
                count.bothRefused++
                continue
            }
            if (ab === undefined || ba === undefined) {
                broken.push(`${p.name} refused in one order only`)
                continue
            }
            if (!stated(ab) || !stated(ba)) {
                count.skipped++
                continue
            }
            count.pairs++
            if (sameTerm(termOf(ab), termOf(ba))) {
                count.sameTerm++
                continue
            }
            try {
                checkEquivalent(ab as never, ba as never, { count: 20 })
                count.sameAccepts++
            } catch (error) {
                if (error instanceof Disagreement) {
                    broken.push(
                        `${p.name} ${(error as Error).message.slice(0, 160)}`,
                    )
                } else count.undecided++
            }
        }
        expect(broken).toEqual([])
        expect(count.sameTerm).toBeGreaterThan(count.pairs / 2)
        expect(count).toEqual({
            pairs: 2758,
            sameTerm: 2751,
            sameAccepts: 6,
            undecided: 1,
            bothRefused: 20,
            skipped: 458,
        })
    })
})
