/**
 * The comparator the property harness runs on.
 *
 * It exists because a comparator that walks own enumerable keys reports every `Set` as equal to
 * every other — a `Set` has none — and {@link unknown} decodes `SS`/`NS`/`BS` into one.
 * A round-trip check using such a comparator passes whatever the codec does to a native set.
 */
import { isDeepStrictEqual } from 'node:util'
import { describe, expect, it } from 'vitest'
import { structuralEquals } from './testing'

const cases: [string, unknown, unknown, boolean][] = [
    ['equal sets', new Set([1, 2]), new Set([2, 1]), true],
    ['different sets', new Set([1, 2]), new Set([9]), false],
    ['sets of different size', new Set([1]), new Set([1, 2]), false],
    ['sets of objects', new Set([{ a: 1 }]), new Set([{ a: 1 }]), true],
    ['equal maps', new Map([['a', 1]]), new Map([['a', 1]]), true],
    ['different maps', new Map([['a', 1]]), new Map([['a', 2]]), false],
    ['equal dates', new Date(0), new Date(0), true],
    ['different dates', new Date(0), new Date(1), false],
    ['equal bytes', Uint8Array.from([1, 2]), Uint8Array.from([1, 2]), true],
    ['different bytes', Uint8Array.from([1]), Uint8Array.from([2]), false],
    [
        'nested objects',
        { a: { b: [1, { c: 2 }] } },
        { a: { b: [1, { c: 2 }] } },
        true,
    ],
    ['missing key', { a: 1 }, { b: 1 }, false],
    ['extra key', { a: 1 }, { a: 1, b: 2 }, false],
    ['undefined vs absent', { a: undefined }, {}, false],
    ['null vs undefined', null, undefined, false],
    ['NaN is NaN', Number.NaN, Number.NaN, true],
    ['zero signs differ', 0, -0, false],
    ['array vs object', [1], { 0: 1 }, false],
]

describe('structuralEquals', () => {
    for (const [name, a, b, expected] of cases) {
        it(`${expected ? 'equates' : 'separates'} ${name}`, () => {
            expect(structuralEquals(a, b)).toBe(expected)
        })
    }

    it('agrees with node:util.isDeepStrictEqual on every case', () => {
        for (const [name, a, b] of cases) {
            expect([name, structuralEquals(a, b)]).toEqual([
                name,
                isDeepStrictEqual(a, b),
            ])
        }
    })
})
