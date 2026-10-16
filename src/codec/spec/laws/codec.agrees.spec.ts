/**
 * Agreement over terms: `Calculus.Closed.compatPair` on this side of the bridge.
 *
 * `true` says that the two meanings agree at both halves. `false` states nothing: the test is sound,
 * not complete. Two lists compare the aligned rows at each common length, so a position meets only
 * the position at the same index in a row of the other list.
 */
import { describe, expect, it } from 'vitest'
import { decimal, list, spread, string } from '../../codec'
import { agrees } from '../../scoped'
import type { Term } from '../../term'

const termOf = (codec: { readonly def: Term }): Term => codec.def

/** The test in both orders: the answer of a sound test does not read the order. */
const agree = (x: Term, y: Term): boolean => {
    const one = agrees(x, y)
    expect(agrees(y, x)).toBe(one)
    return one
}

describe('a list that mixes an adapter and a plain term agrees with itself', () => {
    const shapes = {
        'a fixed arity': list(decimal, string),
        'a plain term first': list(string, decimal),
        'a plain spread': list(decimal, spread(string)),
        'an adapter spread between two ends': list(
            decimal,
            spread(decimal),
            string,
        ),
        'a plain spread before an adapter': list(spread(string), decimal),
    }

    for (const [name, shape] of Object.entries(shapes))
        it(`holds for ${name}`, () => {
            expect(agree(termOf(shape), termOf(shape))).toBe(true)
        })
})

describe('two lists agree where each aligned pair of positions agrees', () => {
    it('refuses two lists whose positions at one index disagree', () => {
        expect(
            agree(termOf(list(decimal, string)), termOf(list(string, decimal))),
        ).toBe(false)
        expect(
            agree(
                termOf(list(decimal, spread(string))),
                termOf(list(spread(string), decimal)),
            ),
        ).toBe(false)
    })

    it('accepts two fixed lists of different arity, which share no length', () => {
        expect(
            agree(
                termOf(list(decimal, string)),
                termOf(list(decimal, string, string)),
            ),
        ).toBe(true)
    })
})
