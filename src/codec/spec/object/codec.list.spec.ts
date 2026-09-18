/**
 * The one positional container: a prefix, at most one spread, and a suffix.
 *
 * `array` and `tuple` name two shapes of it, and neither can say `[A, ...B[], C]` — a fixed
 * position *after* a spread. `list` is the constructor of the term both build, so it says every
 * shape they say and that one too. The model carries the same constructor, with `Term.array` and
 * `Term.tuple` as definitions over it.
 */

import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { BOOL, L, N, S } from '../../attribute'
import {
    array,
    boolean,
    CodecError,
    decimal,
    list,
    never as nothing,
    object,
    spread,
    string,
} from '../../codec'
import { checkEncodePaths, checkRoundTrip } from '../../testing'

const framed = list(string, spread(decimal), boolean)

describe('a list with a fixed position after the spread', () => {
    it('holds the shape no array and no tuple can state', () => {
        const held = framed.unsafeDecode({
            L: [{ S: 'a' }, { N: '1' }, { N: '2' }, { BOOL: true }],
        })
        attest<readonly [string, ...string[], boolean]>(held)
        expect(held).toEqual(['a', '1', '2', true])
    })

    it('is still an L', () => {
        const written = framed.unsafeEncode(['a', '1', true])
        attest<L<readonly [S, ...N[], BOOL]>>(written)
        expect(written).toEqual({ L: [{ S: 'a' }, { N: '1' }, { BOOL: true }] })
    })

    /**
     * **The suffix aligns from the right**, so which term reads a position depends on the length of
     * the value. This is the whole content of the shape: at length two the boolean is at index one,
     * and at length four it is at index three, with the spread reading everything between.
     */
    it('reads the suffix from the right at every length', () => {
        expect(
            framed.unsafeDecode({ L: [{ S: 'a' }, { BOOL: false }] }),
        ).toEqual(['a', false])
        expect(
            framed.unsafeDecode({
                L: [{ S: 'a' }, { N: '1' }, { N: '2' }, { BOOL: true }],
            }),
        ).toEqual(['a', '1', '2', true])
    })

    it('refuses a value shorter than the declared positions', () => {
        expect(() => framed.unsafeDecode({ L: [{ S: 'a' }] })).toThrow(
            CodecError,
        )
    })

    /**
     * A position is read by the term declared for it and by no other, which the suffix is where a
     * reader can see: a `BOOL` at the last position and an `N` before it are two different terms
     * inside one value.
     */
    it('reads each position by the term declared for it', () => {
        expect(() =>
            framed.unsafeDecode({
                L: [{ S: 'a' }, { BOOL: true }, { BOOL: true }],
            }),
        ).toThrow(/at \[1\]/)
    })

    it('round-trips, the suffix included', () => {
        checkRoundTrip(object({ framed }).item, { count: 200, seed: 20260918 })
        checkEncodePaths(object({ framed }).item, {
            count: 100,
            seed: 20260918,
        })
    })
})

describe('the shapes a builder already names', () => {
    /**
     * `array` and `tuple` are builders over this term, so a declaration written either way and the
     * same declaration written as a `list` are one codec. The model states the same two equations
     * as definitions.
     */
    it('is what array builds', () => {
        expect(list(spread(string)).def).toEqual(array(string).def)
    })

    it('counts exactly the declared positions where there is no spread', () => {
        const pair = list(string, boolean)
        expect(pair.unsafeDecode({ L: [{ S: 'a' }, { BOOL: true }] })).toEqual([
            'a',
            true,
        ])
        expect(() =>
            pair.unsafeDecode({ L: [{ S: 'a' }, { BOOL: true }, { S: 'b' }] }),
        ).toThrow(CodecError)
    })
})

describe('what a list refuses at the declaration', () => {
    /**
     * **A declared position at the bottom holds no value, so the list holds none.** `never` already
     * names that term, and a declaration with two spellings, one of them a trap, is the shape a
     * constructor should not have.
     */
    it('refuses a declared position at never', () => {
        // the type refuses it first, and a cast is the only way to reach the constructor
        expect(() =>
            // @ts-expect-error a declared position holds no value
            list(string, nothing, spread(decimal)),
        ).toThrow(CodecError)
        expect(() =>
            // @ts-expect-error and a position after the spread is declared too
            list(string, spread(decimal), nothing),
        ).toThrow(CodecError)
    })

    /**
     * **A spread at the bottom is not the bottom, so it is admitted.**
     *
     * A value of exactly the declared length omits every spread position, so a list whose spread
     * holds nothing is the list of its declared positions, and that is a value. The declared
     * positions are slots and refuse `never`; the spread is not a slot and does not. `Term.listOf`
     * draws the same line, and `array(never)` is the same fact under the one-word name.
     */
    it('admits a spread at never, which holds the declared positions alone', () => {
        const bare = list(string, spread(nothing))
        expect(bare.unsafeDecode({ L: [{ S: 'a' }] })).toEqual(['a'])
    })

    /**
     * **A second spread has no reading, because the positions between the two belong to both.**
     *
     * `SpreadOnce` refuses it at the type and the constructor refuses it again, because a cast
     * defeats the type. That is the shape a structural guarantee the host cannot express owes: a
     * refusal at construction, a test that pins it, and the reason written down.
     */
    it('refuses a second spread, whose positions would belong to both', () => {
        expect(() =>
            // @ts-expect-error a list has at most one spread
            list(string, spread(decimal), decimal, spread(string)),
        ).toThrow(/at most one spread/)
    })
})
