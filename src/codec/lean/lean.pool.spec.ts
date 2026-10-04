/**
 * **The generated pool: one set of pairs, put to two checkers.**
 *
 * A seeded generator builds codecs through the public constructors, so the pool holds what the
 * library constructs and not what a reader imagined. Each pair of the pool goes to the model two
 * times. The first checker is an `#eval` file: each row compares the host verdicts with the
 * model's decisions, and prints only a mismatch. The second checker is the kernel: the disjointness
 * and separation vectors, through the same emitter that the hand corpus uses. The gate runs both.
 *
 * The hand corpus in `lean.spec.ts` stays as the hand-picked part. The pool depends on the seed
 * alone, so a change of the pool counts below is a change of the generator, of the constructors, or
 * of the emitter.
 *
 * A thunk that throws is an unknown term, and each host check takes its worst case, so a pair has
 * two readings: the guard reads the thunk as the root of its option, and the other tests read the
 * open term.
 *
 * One route narrows the pool. **No separation vector for two fills at one name.** The model refuses
 * two fills at one name whatever their constants, because the constants of a fill have no decidable
 * equality. The host accepts two fills with equal constants. Such a pair goes to disjointness only,
 * and the pre-check reads no compatibility column for the pair.
 */
import { writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import { DynamoNumber, isNumeral, isStoredNumeral } from '../attribute'
import type { AnyCodec } from '../codec'
import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    held,
    lazy,
    list,
    mdunion,
    never,
    nullable,
    nullValue,
    object,
    opaque,
    optional,
    product,
    refine,
    spread,
    string,
    undefinable,
    union,
    withLegacyRead,
} from '../codec'
import type { DisjointPair, Separation } from '../lean'
import {
    LeanUnemittable,
    leanDisjoint,
    leanDisjointModule,
    leanRooted,
    leanSeparation,
    leanSeparationModule,
    leanString,
    leanTermOf,
} from '../lean'
import { orThrow } from '../result'
import type { Term } from '../term'
import {
    agrees,
    disjoint,
    force,
    readsFreeVariable,
    recursionUse,
    viewsDisjoint,
} from '../term'
import { arbitraryOf, rngFrom } from '../testing'

/** The emitter takes the erased codec; the constructors return precise ones. */
const erase = (codec: unknown): AnyCodec => codec as AnyCodec

/** The seeds of the pool. A new seed is a new pool, and the pinned counts move with it. */
const SEEDS = [20261004, 1, 4] as const
/** The number of codecs that the generator draws. */
const DRAWS = 150
/** The depth of each drawn codec. */
const DEPTH = 3
/** The partners of each codec, drawn from the built codecs, after the codec itself. */
const PARTNERS = 8

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
/** A thunk that names a codec not yet declared: forced, it throws. */
const undeclared = lazy((): never => {
    throw new ReferenceError('the constant under declaration')
})
/** A caller's predicate: the theorem binds the predicate as a variable. */
const callerPredicate = (v: unknown): v is unknown => v !== 'zz'
const names = ['a', 'b', 'c']

/**
 * **The unions that the generator declares inside a draw.** Each declaration is a host verdict, and
 * a refused declaration refuses the whole draw, so the pool puts each declared pair to the model as
 * well. A recursive option names the union under declaration: where the host refuses, the thunk
 * still throws, and the pair is the declaration itself; where the host accepts, the thunk returns
 * the union, and the pair is the same two options declared later.
 */
let declared: [Entry, Entry][] = []
const declare = (a: Entry, b: Entry, make: () => unknown): AnyCodec => {
    declared.push([a, b])
    return erase(make())
}

/** The two slices of a dissection, which `mdunion` returns. */
type Slices = {
    readonly extract: (clause: Readonly<Record<string, unknown>>) => unknown
    readonly exclude: (clause: Readonly<Record<string, unknown>>) => unknown
}

/** One codec, drawn through the public constructors. A constructor can refuse the draw. */
const draw = (depth: number): Entry => {
    if (depth === 0 || rng() < 0.25) {
        const [name, make] = pick(rng() < 0.8 ? leaves : setable)
        return { name, codec: make() }
    }
    switch (Math.floor(rng() * 19)) {
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
                name: `lazy(${c.name})`,
                codec: erase(lazy(() => c.codec as never)),
            }
        }
        case 11: {
            const c = draw(depth - 1)
            const tree = lazy(
                () => object({ v: c.codec, kids: array(self) }) as never,
            )
            const self: AnyCodec = erase(tree)
            // the thunk runs the constructor, so a refusal of the body is a refusal of the draw
            if (tree.def.kind === 'lazy') tree.def.get()
            return { name: `mu.tree(${c.name})`, codec: self }
        }
        case 12: {
            const c = draw(depth - 1)
            const kids = {
                name: 'array(self)',
                codec: erase(array(lazy(() => self as never))),
            }
            const self: AnyCodec = declare(c, kids, () =>
                union([c.codec, kids.codec] as never),
            )
            return { name: `mu.json(${c.name})`, codec: self }
        }
        case 13: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const left = {
                name: `{k:a,x:${a.name}}`,
                codec: erase(object({ k: string('a'), x: a.codec })),
            }
            const right = {
                name: `{k:b,y:${b.name}}`,
                codec: erase(object({ k: string('b'), y: b.codec })),
            }
            return {
                name: `dunion(k:a{x:${a.name}}|b{y:${b.name}})`,
                codec: declare(left, right, () =>
                    (discriminatedUnion as (...x: unknown[]) => unknown)('k', [
                        left.codec,
                        right.codec,
                    ]),
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
                codec: erase(
                    object({ m: optional(lazy(() => self as never)) }),
                ),
            }
            const self: AnyCodec = declare(c, node, () =>
                union([c.codec, node.codec] as never),
            )
            return { name: `mu.opt(${c.name})`, codec: self }
        }
        case 17: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const merge = product as (...factors: unknown[]) => unknown
            const right = erase(object({ b: b.codec }))
            if (rng() < 0.5)
                return {
                    name: `product({a:${a.name}},{b:${b.name}})`,
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
                name: `product(union({a:${a.name}}|{c:string}),{b:${b.name}})`,
                codec: erase(merge(factor, right)),
            }
        }
        case 18: {
            const a = draw(depth - 1)
            const b = draw(depth - 1)
            const small = {
                name: `{k:p,s:x,x:${a.name}}`,
                codec: erase(
                    object({ k: string('p'), s: string('x'), x: a.codec }),
                ),
            }
            const large = {
                name: `{k:p,s:y,y:${b.name}}`,
                codec: erase(
                    object({ k: string('p'), s: string('y'), y: b.codec }),
                ),
            }
            const name = `mdunion(k,s:${small.name}|${large.name})`
            const whole = declare(small, large, () =>
                (mdunion as (...x: unknown[]) => unknown)(
                    ['k', 's'],
                    [small.codec, large.codec],
                ),
            ) as AnyCodec & Slices
            const slice = rng()
            if (slice < 0.33)
                return {
                    name: `extract(s=x,${name})`,
                    codec: erase(whole.extract({ s: string('x') })),
                }
            if (slice < 0.67)
                return {
                    name: `exclude(s=x,${name})`,
                    codec: erase(whole.exclude({ s: string('x') })),
                }
            return { name, codec: whole }
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
            case 'lazy': {
                const target = force(t)
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
    /** A fill at one field name on each side: the pair goes to disjointness only. */
    readonly fills: boolean
    /** A thunk that throws on a side: the compatibility test reads the open term in both halves. */
    readonly open: boolean
    readonly l: string
    readonly r: string
    /** The two terms that the guard reads. */
    readonly gl: string
    readonly gr: string
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
    const built: Entry[] = []
    for (let i = 0; i < DRAWS; i++) {
        try {
            built.push(draw(DEPTH))
        } catch {
            drop('a constructor refused the draw')
        }
    }
    const pairs: PoolPair[] = []
    const add = (a: Entry, b: Entry) => {
        const name = `pool_${first + pairs.length}`
        const bound = {
            closures: new Map<unknown, string>(),
            adapters: new Map<unknown, string>(),
            readers: new Map<unknown, string>(),
        }
        let l: string
        let r: string
        try {
            l = leanTermOf(a.codec, name, bound)
            r = leanTermOf(b.codec, name, bound)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`term: ${error.reason}`)
            return
        }
        const x = a.codec.def
        const y = b.codec.def
        let declared = true
        try {
            union([a.codec, b.codec] as never)
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
            open: readsFreeVariable(x) || readsFreeVariable(y),
            l,
            r,
            gl: leanRooted(l, a.codec),
            gr: leanRooted(r, b.codec),
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

/** The two instances of each caller function that the `#eval` rows run, where the kernel binds them. */
const stands = [
    { q: 'fun _ => true', r: 'fun _ => none' },
    { q: 'fun _ => false', r: 'fun _ => some Value.null' },
] as const

/** One `#eval` row per instance: the row prints only on a mismatch. */
const evalRows = (p: PoolPair): string[] => {
    // the compatibility columns of a pair with a fill on each side are the known narrowing
    const expected = p.fills ? `${p.host.slice(0, 2)}-${p.host[3]}-` : p.host
    const label = leanString(`${p.name} ${p.label}`)
    const call = p.open
        ? `poolCheckOpen ${label} "${expected}" (${p.l}) (${p.r}) (${p.gl}) (${p.gr})`
        : `poolCheck ${label} "${expected}" (${p.l}) (${p.r})`
    if (p.closures.length + p.readers.length === 0) return [`#eval ${call}`]
    return stands.map((stand) => {
        const lets = [
            ...p.closures.map((q) => `let ${q} : Value → Bool := ${stand.q}; `),
            ...p.readers.map(
                (r) => `let ${r} : Attr → Option Value := ${stand.r}; `,
            ),
        ].join('')
        return `#eval ${lets}${call}`
    })
}

/** The sentinel that the gate reads: the only line of a clean run. */
const sentinel = (count: number) => `pool: ${count} pairs checked`

const evalModule = (pairs: readonly PoolPair[]): string =>
    `import Calculus.Dynamo.Analysis.Meet
import Calculus.Dynamo.Analysis.Compat
import Calculus.Dynamo.Lang.Store

/-!
# The pre-check of the generated pool

**Generated — do not edit.** One row per pair and instance of the caller functions. A row compares
the host verdicts with the model's decisions, and prints only a mismatch. A \`-\` reads no column.
-/

set_option maxRecDepth 8192
set_option linter.unusedVariables false

namespace Calculus

/-- Print the pair when a column that the host states differs from the model's. The host columns
are disjoint, views, compatible, guarded, and the union decision. The guard reads \`gl\` and \`gr\`,
and the other tests read \`l\` and \`r\`. A refusal of an open pair is the refusal of either half,
as the separation vector states it. The compatibility column counts only where the guard accepts,
because the host reads no compatibility after a guard refusal. -/
def poolCheckOpen (name host : String) (l r gl gr : Term) (isOpen : Bool := true) : IO Unit := do
  let bit (b : Bool) : String := if b then "1" else "0"
  let d := Alg.Term.disjoint pair0 l r
  let v := viewsDisjoint l r
  let c := Alg.compatPair dynOracle l r
  let halves := Alg.Term.compat dynOracle true pair0 false false l r &&
    Alg.Term.compat dynOracle false pair0 false false l r
  let refuses := if isOpen then !halves else !c
  let g := Alg.Term.guarded gl && Alg.Term.guarded gr
  let hostAt (i : Nat) : Char := host.toList.getD i '-'
  let col (i : Nat) (yes no : Bool) : Bool :=
    hostAt i == '-' || (hostAt i == '1' && yes) || (hostAt i == '0' && no)
  let ok := col 0 d (!d) && col 1 v (!v) && (hostAt 3 == '0' || col 2 c refuses) &&
    col 3 g (!g) && col 4 (g && c) (!g || refuses)
  unless ok do
    IO.println s!"mismatch {name}: host {host} model {bit d}{bit v}{bit c}{bit halves}{bit g}"

/-- A closed pair: one reading. -/
def poolCheck (name host : String) (l r : Term) : IO Unit :=
  poolCheckOpen name host l r l r false

${pairs.flatMap(evalRows).join('\n')}

#eval IO.println ${leanString(sentinel(pairs.length))}

end Calculus
`

/** The pairs that each kernel module states; a refusal of the emitter drops the pair by reason. */
const kernelPairs = (pairs: readonly PoolPair[]) => {
    const disjoints: DisjointPair[] = []
    const separations: Separation[] = []
    for (const p of pairs) {
        const one = { name: p.name, left: p.left, right: p.right }
        try {
            leanDisjoint(one)
            disjoints.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`disjoint: ${error.reason}`)
        }
        if (p.fills) continue
        try {
            leanSeparation(one)
            separations.push(one)
        } catch (error) {
            if (!(error instanceof LeanUnemittable)) throw error
            drop(`separation: ${error.reason}`)
        }
    }
    return { disjoints, separations }
}

describe('the generated pool, against the model', () => {
    const seeds: { seed: number; pairs: readonly PoolPair[] }[] = []
    for (const seed of SEEDS) {
        const first = seeds.reduce((n, one) => n + one.pairs.length, 0)
        seeds.push({ seed, pairs: pool(seed, first) })
    }
    const perSeed = seeds.map(({ seed, pairs }) => ({
        seed,
        pairs,
        ...kernelPairs(pairs),
    }))
    const pairs = perSeed.flatMap((one) => one.pairs)
    const disjoints = perSeed.flatMap((one) => one.disjoints)
    const separations = perSeed.flatMap((one) => one.separations)

    /**
     * **The counts pin the pool, deliberately.** The pool depends on the seed alone, so a count
     * moves only when the generator, a constructor, or the emitter changes. Look at the move.
     */
    it('draws a pool that depends on the seed alone', () => {
        expect({
            seeds: perSeed.map((one) => ({
                seed: one.seed,
                pairs: one.pairs.length,
                fills: one.pairs.filter((p) => p.fills).length,
                disjoints: one.disjoints.length,
                separations: one.separations.length,
            })),
            dropped: Object.fromEntries([...dropped].sort()),
        }).toMatchInlineSnapshot(`
          {
            "dropped": {
              "a constructor refused the draw": 71,
            },
            "seeds": [
              {
                "disjoints": 1285,
                "fills": 7,
                "pairs": 1285,
                "seed": 20261004,
                "separations": 1278,
              },
              {
                "disjoints": 1272,
                "fills": 7,
                "pairs": 1272,
                "seed": 1,
                "separations": 1265,
              },
              {
                "disjoints": 1198,
                "fills": 14,
                "pairs": 1198,
                "seed": 4,
                "separations": 1184,
              },
            ],
          }
        `)
    })

    /**
     * **A union that the host accepts has a warrant that the model proves.** A pair reaches the
     * separation emitter only after its terms print, so the emitter refuses a pair for one reason:
     * the host accepted it where the model's decision refuses it.
     */
    it('accepts no pair on a warrant that the model does not prove', () => {
        expect(
            [...dropped.keys()].filter((why) => why.startsWith('separation: ')),
        ).toEqual([])
    })

    it('emits the pre-check and the kernel vectors for the gate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            const formal = join(process.cwd(), 'formal')
            writeFileSync(join(formal, '.pool.eval.lean'), evalModule(pairs))
            writeFileSync(
                join(formal, '.pool.disjoints.lean'),
                leanDisjointModule(disjoints),
            )
            writeFileSync(
                join(formal, '.pool.separations.lean'),
                leanSeparationModule(separations),
            )
        }
        expect(evalModule([])).toContain(sentinel(0))
    })
})
