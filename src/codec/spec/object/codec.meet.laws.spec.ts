/**
 * **The lattice laws of `meet`**, over a grounded pool of codecs.
 *
 * The pool holds unions of tagged objects and patterns that name literals, built through the public
 * constructors. Each law compares two routes to one codec: the terms are equal, or both routes
 * refuse. A pair that both routes refuse proves nothing, so each law counts the pairs where a codec
 * came back and requires at least one.
 *
 * The laws that hold with `meet` are the meet laws (commute, associate, idempotent, covariant, bottom
 * is the disjoint pair, path), and the laws of `extract` that read `meet` (the meet of two patterns,
 * the order of fit). The laws that need a total `extract` are not here. `extract` refuses a key that
 * no current member declares, so a pair whose first route refuses is skipped: the law is open there,
 * and the other route may return a codec or `never`.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec } from '../../codec'
import {
    array,
    at,
    boolean,
    extract,
    list,
    meet,
    never,
    object,
    optional,
    string,
    union,
} from '../../codec'
import { codecOfTerm } from '../../denote'
import { disjoint } from '../../scoped'
import type { Term } from '../../term'
import { sameTerm } from '../../term'

/**
 * The erased forms of the operators. The constructors return precise codecs and refuse a pair at the
 * type; a pool holds codecs of one erased type, so the law reads the run time that a cast or a
 * JavaScript caller reaches.
 */
const meetOf = meet as unknown as (a: AnyCodec, b: AnyCodec) => AnyCodec
const extractOf = extract as unknown as (t: AnyCodec, p: AnyCodec) => AnyCodec
const atOf = at as unknown as (c: AnyCodec, path: readonly string[]) => AnyCodec

type Outcome = { readonly kind: 'codec'; readonly codec: AnyCodec } | 'refused'

const run = (f: () => AnyCodec): Outcome => {
    try {
        return { kind: 'codec', codec: f() }
    } catch {
        return 'refused'
    }
}

const same = (x: Outcome, y: Outcome): boolean =>
    x === 'refused' || y === 'refused'
        ? x === y
        : sameTerm(x.codec.def as Term, y.codec.def as Term)

const then = (o: Outcome, f: (c: AnyCodec) => AnyCodec): Outcome =>
    o === 'refused' ? o : run(() => f(o.codec))

const isNever = (o: Outcome): boolean =>
    o !== 'refused' && (o.codec.def as Term).kind === 'never'

/** The two extracts in a row, or nothing where a route refuses a key that no member declares. */
const twiceOf = (
    t: AnyCodec,
    first: AnyCodec,
    second: AnyCodec,
): Outcome | undefined => {
    const twice = then(
        run(() => extractOf(t, first)),
        (e) => extractOf(e, second),
    )
    return twice === 'refused' ? undefined : twice
}

/** The open reading of an object, which `meet` takes: an undeclared name may hold any value. */
const open = (t: Term): Term =>
    t.kind === 'object'
        ? {
              kind: 'object',
              body: { fields: t.body.fields, rest: { kind: 'opaq' } },
          }
        : t

const TAGGED: readonly AnyCodec[] = [
    union([
        object({ kind: string('a'), x: string }),
        object({ kind: string('b'), y: boolean }),
    ]),
    union([
        object({ kind: string('a'), n: string('p', 'q') }),
        object({ kind: string('b'), n: string('q') }),
        object({ kind: string('c') }),
    ]),
]

const PATTERNS: readonly AnyCodec[] = [
    object({ kind: string('a') }),
    object({ kind: string('b') }),
    object({ kind: string('a', 'b') }),
    object({ x: string }),
    object({ y: boolean }),
    object({ n: string('q') }),
    object({ n: string('p') }),
    object({ n: string('p', 'q') }),
]

/** The leaves that two meets compare: the bases, a literal set, and a literal inside it. */
const LEAVES: readonly AnyCodec[] = [
    string,
    boolean,
    string('a', 'b'),
    string('a'),
    string('b'),
    string('b', 'c'),
]

const pairs = <X>(xs: readonly X[]): readonly (readonly [X, X])[] =>
    xs.flatMap((x) => xs.map((y) => [x, y] as const))

const triples = <X>(xs: readonly X[]): readonly (readonly [X, X, X])[] =>
    pairs(xs).flatMap(([a, b]) => xs.map((c) => [a, b, c] as const))

describe('the meet is a lattice operation over the pool', () => {
    /** `meet(A, B)` and `meet(B, A)` hold the same values, so the terms are one term. */
    it('commutes', () => {
        let compared = 0
        for (const [a, b] of pairs(PATTERNS)) {
            const left = run(() => meetOf(a, b))
            const right = run(() => meetOf(b, a))
            expect(same(left, right)).toBe(true)
            if (left !== 'refused') compared++
        }
        for (const [a, b] of pairs(LEAVES)) {
            expect(
                same(
                    run(() => meetOf(a, b)),
                    run(() => meetOf(b, a)),
                ),
            ).toBe(true)
        }
        expect(compared).toBeGreaterThan(0)
    })

    it('associates', () => {
        let compared = 0
        for (const [a, b, c] of triples([...PATTERNS, ...LEAVES])) {
            const left = then(
                run(() => meetOf(a, b)),
                (ab) => meetOf(ab, c),
            )
            const right = then(
                run(() => meetOf(b, c)),
                (bc) => meetOf(a, bc),
            )
            expect(same(left, right)).toBe(true)
            if (left !== 'refused') compared++
        }
        expect(compared).toBeGreaterThan(0)
    })

    it('is idempotent: a codec meets itself at itself', () => {
        let compared = 0
        for (const a of [...PATTERNS, ...LEAVES, ...TAGGED]) {
            const one = run(() => meetOf(a, a))
            expect(same(one, { kind: 'codec', codec: a })).toBe(true)
            compared++
        }
        expect(compared).toBeGreaterThan(0)
    })

    /** The meet of two patterns keeps the options that each pattern keeps: extract twice is extract once. */
    it('makes extract by two patterns the extract by their meet', () => {
        let compared = 0
        for (const t of TAGGED) {
            for (const [a, b] of pairs(PATTERNS)) {
                const twice = twiceOf(t, a, b)
                if (twice === undefined) continue
                const once = then(
                    run(() => meetOf(a, b)),
                    (m) => extractOf(t, m),
                )
                expect(same(twice, once)).toBe(true)
                compared++
            }
        }
        expect(compared).toBeGreaterThan(0)
    })

    it('makes extract by two patterns commute', () => {
        let compared = 0
        for (const t of TAGGED) {
            for (const [a, b] of pairs(PATTERNS)) {
                const left = twiceOf(t, a, b)
                const right = twiceOf(t, b, a)
                if (left === undefined || right === undefined) continue
                expect(same(left, right)).toBe(true)
                compared++
            }
        }
        expect(compared).toBeGreaterThan(0)
    })

    it('makes extract by one pattern idempotent', () => {
        let compared = 0
        for (const t of TAGGED) {
            for (const a of PATTERNS) {
                const once = run(() => extractOf(t, a))
                const twice = twiceOf(t, a, a)
                if (twice === undefined) continue
                expect(same(twice, once)).toBe(true)
                compared++
            }
        }
        expect(compared).toBeGreaterThan(0)
    })
})

describe('the meet orders the options by fit', () => {
    /** An option that `extract` keeps is the option that meets the pattern at itself, and no other. */
    it('keeps exactly the options that meet the pattern at themselves', () => {
        let compared = 0
        for (const t of TAGGED) {
            const options = (t.def as Extract<Term, { kind: 'union' }>).options
            for (const p of PATTERNS) {
                const kept = run(() => extractOf(t, p))
                if (kept === 'refused') continue
                const keptOptions = isNever(kept)
                    ? []
                    : (kept as { codec: AnyCodec }).codec.def.kind === 'union'
                      ? (
                            (kept as { codec: AnyCodec }).codec.def as Extract<
                                Term,
                                { kind: 'union' }
                            >
                        ).options
                      : [(kept as { codec: AnyCodec }).codec.def as Term]
                for (const option of options) {
                    const isKept = keptOptions.some((one) =>
                        sameTerm(one, option),
                    )
                    const meetsAtItself = same(
                        run(() => meetOf(codecOfTerm(option), p)),
                        { kind: 'codec', codec: codecOfTerm(option) },
                    )
                    expect(isKept).toBe(meetsAtItself)
                    compared++
                }
            }
        }
        expect(compared).toBeGreaterThan(0)
    })
})

describe('the meet commutes with the covariant formers', () => {
    const forms: readonly (readonly [string, (c: AnyCodec) => AnyCodec])[] = [
        ['an object field', (c) => object({ k: c }) as unknown as AnyCodec],
        [
            'an optional field',
            (c) => object({ k: optional(c) }) as unknown as AnyCodec,
        ],
        ['an array', (c) => array(c) as unknown as AnyCodec],
        ['a list of one position', (c) => list(c) as unknown as AnyCodec],
    ]

    for (const [name, wrap] of forms) {
        it(`meets ${name} where the element meets`, () => {
            let compared = 0
            for (const [x, y] of pairs(LEAVES)) {
                const outer = run(() => meetOf(wrap(x), wrap(y)))
                const inner = then(
                    run(() => meetOf(x, y)),
                    wrap,
                )
                // an element at `never` makes a slot at `never`, which the constructor refuses,
                // and a meet at `never` of the wrapped codecs is the same bottom
                if (inner === 'refused') {
                    expect(isNever(outer) || outer === 'refused').toBe(true)
                    continue
                }
                expect(same(outer, inner)).toBe(true)
                compared++
            }
            expect(compared).toBeGreaterThan(0)
        })
    }
})

describe('the meet of two codecs that share no value', () => {
    /** A pair that no value fits is the bottom, and `never` is the bottom, as the owner rules. */
    it('is never exactly where the two codecs are disjoint', () => {
        let compared = 0
        for (const [a, b] of pairs(PATTERNS)) {
            const apart = disjoint(open(a.def as Term), open(b.def as Term))
            const met = run(() => meetOf(a, b))
            expect(apart).toBe(isNever(met))
            compared++
        }
        expect(compared).toBeGreaterThan(0)
    })

    it('is never where a name meets at never, and never absorbs the rest', () => {
        const apart = meetOf(
            object({ a: string('x') }),
            object({ a: string('y') }),
        )
        expect(apart.def).toEqual(never.def)
        expect(meetOf(apart, object({ b: string })).def).toEqual(never.def)
        expect(meetOf(object({ b: string }), apart).def).toEqual(never.def)
    })
})

describe('the meet commutes with a path', () => {
    /** `at` the one name of two objects reads the meet of the two slots there. */
    it('reads at a name the meet of the two slots', () => {
        let compared = 0
        for (const [x, y] of pairs(LEAVES)) {
            const a = object({ k: x }) as unknown as AnyCodec
            const b = object({ k: y }) as unknown as AnyCodec
            const through = then(
                run(() => meetOf(a, b)),
                (m) => atOf(m, ['k']),
            )
            const slot = run(() => meetOf(x, y))
            if (isNever(slot) || slot === 'refused') continue
            expect(through === 'refused').toBe(false)
            if (through !== 'refused') {
                expect(
                    sameTerm(through.codec.def as Term, slot.codec.def as Term),
                ).toBe(true)
                compared++
            }
        }
        expect(compared).toBeGreaterThan(0)
    })
})
