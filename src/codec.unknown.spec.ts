/**
 * `unknown` obeys the laws, or refuses.
 *
 * It is the escape hatch, and the temptation is to accept anything and do its best. That is how `1`
 * becomes `'1'`, a `Date` becomes `{}` and a class instance loses its prototype — silently, in
 * production, at the one place nothing else is checking. The domain is therefore exactly the values
 * whose type is recoverable from what is stored, and everything else is named and refused.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from './attribute'
import type { AttributeCodec } from './codec'
import { CodecError, opaque } from './codec'
import {
    type Checkable,
    checkMembersStable,
    checkRoundTrip,
    checkStable,
    structuralEquals,
} from './testing'

/**
 * The attribute on its own, as a checkable subject.
 *
 * Not via `object({ v: ... })`: an `unknown` attribute has to be declared with `optional`, because
 * `undefined extends unknown` and nothing distinguishes a required `unknown` from an absent one — so
 * the codec really is optional, and the generator would leave the attribute out half the time.
 */
const holderFor = (attribute: AttributeCodec<unknown>): Checkable<unknown> => ({
    unsafeEncode: (value) => ({ v: attribute.unsafeEncode(value) }),
    unsafeDecode: (item) => attribute.unsafeDecode(item.v as AttributeValue),
    def: attribute.def,
})

const through = (value: unknown) =>
    opaque.unsafeDecode(opaque.unsafeEncode(value))

describe('what round-trips', () => {
    const accepted: [string, unknown][] = [
        ['null', null],
        ['a string', 'x'],
        ['the empty string', ''],
        ['true', true],
        ['false', false],
        ['binary', Uint8Array.from([0, 255])],
        ['an array', ['a', true, null]],
        ['an object', { a: 'x', b: false }],
        ['a set of strings', new Set(['a', 'b'])],
        ['a set of binary', new Set([Uint8Array.from([1])])],
        ['nested everything', { a: [{ b: new Set(['c']) }, null], d: '' }],
        ['an empty array', []],
        ['an empty object', {}],
    ]

    for (const [name, value] of accepted) {
        it(`round-trips ${name}`, () => {
            expect(structuralEquals(through(value), value)).toBe(true)
        })
    }

    it('holds for every generated value', () => {
        checkRoundTrip(holderFor(opaque), {
            count: 500,
            seed: 20260826,
        })
    })
})

describe('what it refuses, and what it tells you instead', () => {
    const refused: [string, unknown, RegExp][] = [
        ['a number', 1, /opt in with `opaque\('lossy'\)`/],
        ['a fraction', 1.5, /changing the attribute's stored type/],
        ['a bigint', 1n, /Use `decimal` and pass `value.toString\(\)`/],
        ['NaN', Number.NaN, /no number for NaN/],
        ['Infinity', Number.POSITIVE_INFINITY, /no number for Infinity/],
        ['a Map', new Map([['a', 'b']]), /use `record\(\.\.\.\)`/],
        ['a set of numbers', new Set([1, 2]), /NS decodes as strings/],
        ['a Date', new Date(0), /faithful as an ISO string/],
        [
            'a class instance',
            new (class Thing {
                x = 'y'
            })(),
            /Only plain objects survive/,
        ],
        ['undefined in an object', { a: undefined }, /Omit the key/],
        ['undefined', undefined, /No DynamoDB member carries it/],
    ]

    for (const [name, value, message] of refused) {
        it(`refuses ${name}`, () => {
            expect(() => opaque.unsafeEncode(value)).toThrow(CodecError)
            expect(() => opaque.unsafeEncode(value)).toThrow(message)
        })
    }

    it('refuses an empty set, which DynamoDB has no representation for', () => {
        expect(() => opaque.unsafeEncode(new Set())).toThrow(/no empty set/)
    })

    it('refuses a bigint nested deep, not just at the top', () => {
        expect(() => opaque.unsafeEncode({ a: [{ b: 1n }] })).toThrow(
            CodecError,
        )
    })
})

describe('reading an N somebody else wrote', () => {
    it('refuses rather than choose a reading nobody asked for', () => {
        expect(() => opaque.unsafeDecode({ N: '1.50' })).toThrow(
            /opt in with `opaque\('lossy'\)`/,
        )
    })

    /**
     * Why refusing is right, and why the value-level laws could not see it.
     *
     * Decoding `N` to a string and re-encoding produces an `S`. The digits survive, so both
     * `checkRoundTrip` and `checkStable` are satisfied — while every read-modify-write quietly
     * rewrites the attribute from a number to a string, and any numeric sort key or `>` condition
     * over it stops working.
     */
    it('would change the stored member if it decoded N as a string', () => {
        const guessing: Checkable<unknown> = {
            unsafeEncode: (v) => ({ v: opaque.unsafeEncode(v) }),
            unsafeDecode: (i) => {
                const carried = i.v as { N?: string; S?: string }
                return carried.N ?? carried.S ?? null
            },
            def: opaque.def,
        }

        // the value-level law is satisfied: the digits come back
        expect(() => checkStable(guessing, [{ v: { N: '1.5' } }])).not.toThrow()

        // the member law is not: `N` went in and `S` comes out
        expect(() =>
            checkMembersStable(guessing, [{ v: { N: '1.5' } }]),
        ).toThrow(CodecError)
    })
})

describe('with numbers opted into as lossy', () => {
    const lossy = opaque('lossy')

    it('round-trips numbers, including the generated ones', () => {
        checkRoundTrip(holderFor(lossy), { count: 500, seed: 20260826 })
    })

    it('keeps N as N on a read-modify-write, which is the point', () => {
        expect(() =>
            checkMembersStable(holderFor(lossy), [
                { v: { N: '1.50' } },
                { v: { N: '12345678901234567890' } },
                { v: { N: '0' } },
            ]),
        ).not.toThrow()
    })

    it('loses digits a float cannot hold — which is what lossy means', () => {
        expect(lossy.unsafeDecode({ N: '1.50' })).toBe(1.5)
        expect(lossy.unsafeDecode({ N: '12345678901234567890' })).toBe(
            12345678901234567890,
        )
    })

    it('still refuses a bigint, which decodes as a number and would not come back', () => {
        expect(() => lossy.unsafeEncode(1n)).toThrow(CodecError)
    })
})
