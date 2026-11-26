/**
 * The key set is part of the term of a dissection, so each function that builds a codec from a codec
 * keeps the dissection where the result is a union of two or more objects. A dissection has
 * `encodePartial`, `variantOf` and `variants`, and a join of objects has none of the three. A copy
 * of the term that drops the key set turns a dissection into a join, and nothing else shows it.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec } from '../../codec'
import {
    discriminatedUnion,
    exclude,
    extract,
    item,
    meet,
    number,
    object,
    optional,
    ref,
    scope,
    string,
    union,
} from '../../codec'
import { resolvedTerm } from '../../term'

const one = () =>
    discriminatedUnion('t', [
        object({ t: string('A'), a: number }),
        object({ t: string('B'), b: number }),
    ])
const two = () =>
    discriminatedUnion(
        ['t', 'u'],
        [
            object({ t: string('A'), u: string('x'), a: number }),
            object({ t: string('A'), u: string('y'), b: number }),
            object({ t: string('B'), u: string('x'), c: number }),
        ],
    )
const oneRecursive = () =>
    scope({
        D: discriminatedUnion('t', [
            object({ t: string('A'), next: optional(ref('D')) }),
            object({ t: string('B'), b: number }),
        ]),
    }).D
const twoRecursive = () =>
    scope({
        D: discriminatedUnion(
            ['t', 'u'],
            [
                object({
                    t: string('A'),
                    u: string('x'),
                    next: optional(ref('D')),
                }),
                object({ t: string('A'), u: string('y'), b: number }),
                object({ t: string('B'), u: string('x'), c: number }),
            ],
        ),
    }).D
/** A member by `ref` has no spec for the type of the call to read, so these two calls go untyped. */
const dissect = discriminatedUnion as unknown as (
    keys: string | readonly string[],
    options: readonly AnyCodec[],
) => AnyCodec
const oneByRef = () =>
    scope({
        M: object({ t: string('A'), a: number }),
        D: dissect('t', [ref('M'), object({ t: string('B'), b: number })]),
    }).D
const twoByRef = () =>
    scope({
        M: object({ t: string('A'), u: string('x'), a: number }),
        D: dissect(
            ['t', 'u'],
            [ref('M'), object({ t: string('B'), u: string('x'), c: number })],
        ),
    }).D

const sources: readonly (readonly [string, () => AnyCodec])[] = [
    ['one key', one],
    ['two keys', two],
    ['one key, in a recursive scope', oneRecursive],
    ['two keys, in a recursive scope', twoRecursive],
    ['one key, a member by ref', oneByRef],
    ['two keys, a member by ref', twoByRef],
]

/** Each function takes the codec as `AnyCodec` and the factors of a meet as `never`: the types of a meet are not the subject. */
const functions: readonly (readonly [string, (d: AnyCodec) => AnyCodec])[] = [
    ['identity', (d) => d],
    ['extract of every option', (d) => extract(d as never, object({}))],
    [
        'exclude of no option',
        (d) => exclude(d as never, object({ t: string('Z') })),
    ],
    [
        'extract of one tag',
        (d) => extract(d as never, object({ t: string('A') })),
    ],
    [
        'exclude of one tag',
        (d) => exclude(d as never, object({ t: string('B') })),
    ],
    ['meet with itself', (d) => meet(d as never, d as never) as AnyCodec],
    [
        'meet with an open pattern',
        (d) =>
            meet(
                d as never,
                object({ t: string('A', 'B') }) as never,
            ) as AnyCodec,
    ],
    [
        'meet with one tag',
        (d) =>
            meet(d as never, object({ t: string('A') }) as never) as AnyCodec,
    ],
    [
        'meet with one tag, on the left',
        (d) =>
            meet(object({ t: string('A') }) as never, d as never) as AnyCodec,
    ],
    [
        'meet with an attribute',
        (d) => meet(d as never, object({ a: number }) as never) as AnyCodec,
    ],
    ['union of the codec alone', (d) => union([d]) as AnyCodec],
]

/** Whether the result is a union of two or more objects, each read through its `ref`s. */
const unionOfObjects = (codec: AnyCodec): boolean => {
    const node = resolvedTerm(codec.def)
    return (
        node?.kind === 'union' &&
        node.options.length >= 2 &&
        node.options.every((option) => resolvedTerm(option)?.kind === 'object')
    )
}

type Reading = {
    readonly encodePartial?: unknown
    readonly variantOf?: unknown
    readonly variants?: unknown
}

describe('a function of a dissection keeps the dissection', () => {
    let applied = 0
    for (const [sourceName, source] of sources) {
        for (const [functionName, apply] of functions) {
            it(`${functionName}, over ${sourceName}`, () => {
                const result = apply(source())
                if (!unionOfObjects(result)) return
                applied += 1
                const reading = item(result as never) as Reading
                expect(typeof reading.encodePartial).toBe('function')
                expect(typeof reading.variantOf).toBe('function')
                expect(typeof reading.variants).toBe('function')
            })
        }
    }

    /** A law that no case applies to holds of nothing: the cases that give a union of objects are counted. */
    it('applies to a union of objects in at least 44 of the 66 cases', () => {
        expect(applied).toBeGreaterThanOrEqual(44)
    })
})

/**
 * A meet keeps the key set of a dissection factor exactly where each option of that factor gives at
 * most one option of the result, because the index needs one result option for each assignment.
 */
describe('a meet keeps the key set where each option of the dissection gives one result', () => {
    const keysOf = (codec: AnyCodec): unknown =>
        (item(codec as never) as { readonly keys?: unknown }).keys
    const join = union([object({ x: number }), object({ y: number })])

    it('gives a join where one tag option meets two options of a join', () => {
        const left = meet(one() as never, join as never) as AnyCodec
        const right = meet(join as never, one() as never) as AnyCodec
        for (const result of [left, right]) {
            const node = resolvedTerm(result.def)
            expect(node?.kind === 'union' && node.options.length).toBe(4)
            expect(node?.kind === 'union' && node.keys).toBeUndefined()
        }
    })

    it('gives the union of the key sets, left then right, where each factor passes', () => {
        const byTag = discriminatedUnion('t', [
            object({ t: string('A'), u: string('x'), a: number }),
            object({ t: string('B'), u: string('y'), b: number }),
        ])
        const byUnit = discriminatedUnion('u', [
            object({ u: string('x'), c: number }),
            object({ u: string('y'), e: number }),
        ])
        expect(
            keysOf(meet(byTag as never, byUnit as never) as AnyCodec),
        ).toEqual(['t', 'u'])
        expect(
            keysOf(meet(byUnit as never, byTag as never) as AnyCodec),
        ).toEqual(['u', 't'])
    })

    it('keeps the key set of a meet with itself', () => {
        const d = one()
        expect(keysOf(meet(d as never, d as never) as AnyCodec)).toEqual(['t'])
    })
})
