/**
 * A list with a spread: some declared positions, and any number of one more thing among them.
 *
 * `spread(c)` is the counterpart of `...T[]` in a tuple type, and it is a marker for a *position* in
 * the same way `optional` is a marker for a *name* — so it means something in exactly one place, and
 * every other place refuses it. What it buys over `array` is the declared positions: a list whose
 * first two elements are a `string` and a number and whose remainder is digits is not expressible
 * as a fixed arity or as an array on its own.
 */

import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { L, N, S } from '../../attribute'
import {
    array,
    CodecError,
    decimal,
    item,
    list,
    number,
    object,
    spread,
    string,
    union,
} from '../../codec'
import { checkEncodePaths, checkRoundTrip } from '../../testing'

const path = list(string, number, spread(decimal))

describe('a tuple with a tail', () => {
    it('is still an L', () => {
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
        const fixed = list(string, number)
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
        const fixed = list(string, number)
        expect(() =>
            fixed.unsafeDecode({ L: [{ S: 'a' }, { N: '1' }, { N: '2' }] }),
        ).toThrow(CodecError)
    })

    it('admits a tail and nothing else', () => {
        const every = list(spread(string))
        expect(every.unsafeEncode(['a', 'b'])).toEqual({
            L: [{ S: 'a' }, { S: 'b' }],
        })
        expect(every.unsafeDecode({ L: [] })).toEqual([])
    })

    it('round-trips, tails included', () => {
        checkRoundTrip(item(object({ path })), { count: 200, seed: 20260828 })
        checkEncodePaths(item(object({ path })), { count: 100, seed: 20260828 })
    })
})

describe('where a tail cannot go', () => {
    /**
     * A spread is only a thing to be **once**. It used to have to be last as well, which was never
     * the rule: it held only because the one container taking a spread had no positions after it.
     * A list has a suffix, so a spread before a fixed position is an ordinary shape.
     */
    it('is refused a second time, and admitted before a fixed position', () => {
        expect(() => list(spread(string), number)).not.toThrow()
        const _wrong = () => [
            // @ts-expect-error a list has at most one spread
            list(spread(string), spread(number)),
        ]
        expect(typeof _wrong).toBe('function')
    })

    it('is refused where there are no positions at all', () => {
        const _wrong = () => [
            // @ts-expect-error an array is already every element
            array(spread(string)),
            // @ts-expect-error an item has names, not positions
            object({ a: spread(string) }),
            // @ts-expect-error nor is a union option a position
            union([spread(string), number]),
        ]
        expect(typeof _wrong).toBe('function')
    })

    /**
     * The rule is that marking an element changes nothing about the element, and the tuple is
     * where it can be seen — a rest is a *position*, so it means nothing anywhere else.
     *
     * This used to read `writes(spread(decimal))`, asking a marker what it writes. That worked
     * because `spread(c)` was `c` with a definition stamped on it, so a bare rest had an `encode`
     * and answered as its element. It is a marker now and answers nothing, which is the point:
     * asking a position what it writes is a question with no subject.
     */
    it('but the element underneath is untouched by the mark', () => {
        expect(
            list(string, spread(decimal)).unsafeEncode(['a', '1.5', '2']),
        ).toEqual({ L: [{ S: 'a' }, { N: '1.5' }, { N: '2' }] })
    })
})
