/**
 * A tuple with a tail: some fixed positions, and then any number of one more thing.
 *
 * `rest(c)` is the counterpart of `...T[]` in a tuple type, and it is a marker for a *position* in
 * the same way `optional` is a marker for a *name* — so it means something in exactly one place, and
 * every other place refuses it. What it buys over `array` is the fixed head: a list whose first two
 * elements are a `string` and a number and whose remainder is digits is not expressible as either a
 * tuple or an array on its own.
 */

import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { L, N, S } from './attribute'
import {
    array,
    CodecError,
    decimal,
    deeper,
    number,
    object,
    rest,
    string,
    tuple,
    union,
    writes,
} from './codec'
import { checkEncodePaths, checkRoundTrip } from './testing'

const path = tuple(string, number, rest(decimal))

describe('a tuple with a tail', () => {
    it('is still an L', () => {
        expect(writes(path)).toBe('L')
        const written = path.unsafeEncode(['a', 1])
        attest<L<readonly [S, N, ...N[]]>>(written)
        expect(written).toEqual({ L: [{ S: 'a' }, { N: '1' }] })
    })

    /**
     * Asserted with `attest` and not with an assignment, which is the lesson this pair taught.
     *
     * A fixed `[S, N, N]` *is* assignable to `readonly [S, N, ...N[]]` — three elements satisfy a
     * pattern demanding at least two — so the first version of this shipped a tail typed as a single
     * element and every assignment passed. Only strict equality sees it, on either side.
     */
    it('holds the head by position and the tail by repetition', () => {
        const held = path.unsafeDecode({
            L: [{ S: 'a' }, { N: '1' }, { N: '2.5' }, { N: '3' }],
        })
        attest<readonly [string, number, ...string[]]>(held)
        expect(held).toEqual(['a', 1, '2.5', '3'])
    })

    it('and a tuple without a tail is typed as tightly as it always was', () => {
        const fixed = tuple(string, number)
        attest<readonly [string, number]>(
            fixed.unsafeDecode({ L: [{ S: 'a' }, { N: '1' }] }),
        )
        attest<L<readonly [S, N]>>(fixed.unsafeEncode(['a', 1]))
    })

    it('writes as many tail elements as it is given', () => {
        expect(path.unsafeEncode(['a', 1, '2.5', '3'])).toEqual({
            L: [{ S: 'a' }, { N: '1' }, { N: '2.5' }, { N: '3' }],
        })
    })

    it('requires the head, and says so as a minimum', () => {
        expect(() => path.unsafeEncode(['a'] as never)).toThrow(CodecError)
        expect(() => path.unsafeDecode({ L: [{ S: 'a' }] })).toThrow(CodecError)
    })

    /**
     * **Pins wording no law has, deliberately.** That a tail element's failure carries its
     * *index* is the claim — `at [2]`, not merely that the tuple refused — so the position is the
     * subject rather than a stand-in for a refusal.
     */
    it('checks a tail element, naming its position', () => {
        expect(() =>
            path.unsafeDecode({
                L: [{ S: 'a' }, { N: '1' }, { S: 'x' }],
            }),
        ).toThrow(/at \[2\]: expected attribute member 'N', found 'S'/)
    })

    it('leaves a tuple without one exactly as strict as it was', () => {
        const fixed = tuple(string, number)
        expect(() =>
            fixed.unsafeDecode({ L: [{ S: 'a' }, { N: '1' }, { N: '2' }] }),
        ).toThrow(CodecError)
    })

    it('admits a tail and nothing else', () => {
        const every = tuple(rest(string))
        expect(every.unsafeEncode(['a', 'b'])).toEqual({
            L: [{ S: 'a' }, { S: 'b' }],
        })
        expect(every.unsafeDecode({ L: [] })).toEqual([])
    })

    it('walks to the tail by any position past the head', () => {
        expect(deeper(path, 0)?.def?.kind).toBe('string')
        expect(deeper(path, 2)?.def?.kind).toBe('decimal')
        expect(deeper(path, 9)?.def?.kind).toBe('decimal')
    })

    it('round-trips, tails included', () => {
        checkRoundTrip(object({ path }).item, { count: 200, seed: 20260828 })
        checkEncodePaths(object({ path }).item, { count: 100, seed: 20260828 })
    })
})

describe('where a tail cannot go', () => {
    /**
     * "The rest" is only a thing to be once, and only at the end. Everywhere else it is a marker with
     * nothing to mark — a list has no head to be the tail of, and a map has names rather than
     * positions.
     */
    it('is refused anywhere but last', () => {
        const _wrong = () => [
            // @ts-expect-error a tail goes last
            tuple(rest(string), number),
            // @ts-expect-error and only once
            tuple(rest(string), rest(number)),
        ]
        expect(typeof _wrong).toBe('function')
    })

    it('is refused where there is no head at all', () => {
        const _wrong = () => [
            // @ts-expect-error an array is already every element
            array(rest(string)),
            // @ts-expect-error an item has names, not positions
            object({ a: rest(string) }),
            // @ts-expect-error nor is a union option a position
            union([rest(string), number]),
        ]
        expect(typeof _wrong).toBe('function')
    })

    it('but the codec underneath is untouched by the mark', () => {
        // the mark is about position; what it wraps still writes what it wrote
        expect(writes(rest(decimal))).toBe('N')
        expect(writes(rest(string))).toBe('S')
    })
})
