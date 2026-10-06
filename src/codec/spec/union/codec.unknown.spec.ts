/**
 * `unknown` obeys the laws, or refuses.
 *
 * It is the escape hatch, and the temptation is to accept anything and do its best. That is how `1`
 * becomes `'1'`, a `Date` becomes `{}` and a class instance loses its prototype — silently, in
 * production, at the one place nothing else is checking. The domain is therefore exactly the values
 * whose type is recoverable from what is stored, and everything else is named and refused.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import { DynamoNumber } from '../../attribute'
import type { AttributeCodec } from '../../codec'
import { CodecError, opaque, orThrow } from '../../codec'
import {
    type Checkable,
    checkDecodesAreWritable,
    checkMembersStable,
    checkRoundTrip,
    checkStable,
    structuralEquals,
} from '../../testing'

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
        ['a DynamoNumber', orThrow(DynamoNumber.from('1.5'))],
        [
            'a set of DynamoNumbers',
            new Set([
                orThrow(DynamoNumber.from('1')),
                orThrow(DynamoNumber.from('2.5')),
            ]),
        ],
        ['a DynamoNumber nested', { a: [orThrow(DynamoNumber.from('-7'))] }],
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
    /** Refused by the canonical codec and by both numeric policies, with one text. */
    const refusedByEvery: [string, unknown, RegExp][] = [
        [
            'a Map',
            new Map([['a', 'b']]),
            /use `object\(\[string, optional\(\.\.\.\)\]\)`/,
        ],
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

    for (const [name, value, message] of refusedByEvery) {
        for (const [policy, codec] of [
            ['canonical', opaque],
            ['refuse', opaque('refuse')],
            ['lossy', opaque('lossy')],
        ] as const) {
            it(`refuses ${name} under ${policy}`, () => {
                expect(() => codec.unsafeEncode(value)).toThrow(CodecError)
                expect(() => codec.unsafeEncode(value)).toThrow(message)
            })
        }
    }

    /**
     * **The canonical codec holds a number exactly, so a float is not a number it holds.** The
     * message names the exact carrier and the policy that converts a float, so the caller has the
     * two ways forward.
     */
    const refusedByCanonical: [string, unknown, RegExp][] = [
        ['a JS number', 1, /`DynamoNumber`.*opt in with `opaque\('lossy'\)`/],
        ['a fraction', 1.5, /binary64 float/],
        ['NaN', Number.NaN, /binary64 float/],
        ['a bigint', 1n, /Pass `DynamoNumber\.from\(value\.toString\(\)\)`/],
        ['a set of JS numbers', new Set([1, 2]), /each holds one kind/],
        [
            'a set that holds one number two times',
            new Set([
                orThrow(DynamoNumber.from('1.5')),
                orThrow(DynamoNumber.from('1.50')),
            ]),
            /one number two times/,
        ],
    ]

    for (const [name, value, message] of refusedByCanonical) {
        it(`refuses ${name}, which is not an exact number`, () => {
            expect(() => opaque.unsafeEncode(value)).toThrow(CodecError)
            expect(() => opaque.unsafeEncode(value)).toThrow(message)
        })
    }

    /** The refusing policy keeps the texts it had before it was a `held` over the canonical codec. */
    const refusedByRefuse: [string, unknown, RegExp][] = [
        ['a number', 1, /opt in with `opaque\('lossy'\)`/],
        ['a fraction', 1.5, /changing the attribute's stored type/],
        ['a bigint', 1n, /Use `decimal` and pass `value.toString\(\)`/],
        ['NaN', Number.NaN, /no number for NaN/],
        ['Infinity', Number.POSITIVE_INFINITY, /no number for Infinity/],
        ['a set of numbers', new Set([1, 2]), /NS decodes as strings/],
        [
            'a DynamoNumber',
            orThrow(DynamoNumber.from('1')),
            /an instance of DynamoNumber/,
        ],
    ]

    for (const [name, value, message] of refusedByRefuse) {
        it(`refuses ${name} under refuse, with the text it had`, () => {
            expect(() => opaque('refuse').unsafeEncode(value)).toThrow(
                CodecError,
            )
            expect(() => opaque('refuse').unsafeEncode(value)).toThrow(message)
        })
    }

    it('names the path of a refused number under refuse', () => {
        expect(() => opaque('refuse').unsafeEncode({ a: ['x', 1] })).toThrow(
            /^at a\[1\]: a number cannot be stored/,
        )
    })

    /**
     * **A policy refuses its numbers first, then the canonical codec refuses the rest.** So a
     * value with two defects can report a later one first: the policy walks the whole value
     * before the canonical codec sees the `Map` at `[0]`.
     */
    it('reports the number under refuse before a defect that the canonical codec finds', () => {
        expect(() =>
            opaque('refuse').unsafeEncode([new Map([['a', 'b']]), 1]),
        ).toThrow(/^at \[1\]: a number cannot be stored/)
    })

    it('refuses an empty set, which DynamoDB has no representation for', () => {
        expect(() => opaque.unsafeEncode(new Set())).toThrow(CodecError)
    })

    it('refuses to read one back, for the same reason', () => {
        expect(() => opaque.unsafeDecode({ SS: [] })).toThrow(CodecError)
        expect(() => opaque.unsafeDecode({ BS: [] })).toThrow(CodecError)
        expect(() => opaque.unsafeDecode({ NS: [] })).toThrow(/no empty NS/)
    })

    /**
     * Under a policy, `NS` is refused by a stronger rule: the policy has no `NS` **write** path
     * at all, so reading one would re-encode as `SS` and change the attribute's stored type. A
     * member a codec cannot write is a member it cannot read —
     * `Calculus.Alg.Lawful.no_read_without_write`.
     *
     * **An empty `NS` gets the empty-set text now**, because the canonical codec reads first and
     * refuses it before the policy sees a set.
     */
    it('refuses NS under refuse, because the policy cannot write one', () => {
        expect(() => opaque('refuse').unsafeDecode({ NS: [] })).toThrow(
            /no empty NS/,
        )
        expect(() => opaque('refuse').unsafeDecode({ NS: ['1', '2'] })).toThrow(
            /no counterpart this codec can write/,
        )
    })

    it('refuses a bigint nested deep, not just at the top', () => {
        expect(() => opaque.unsafeEncode({ a: [{ b: 1n }] })).toThrow(
            CodecError,
        )
    })
})

describe('reading an N somebody else wrote', () => {
    /** The canonical codec reads the exact number, so it chooses no reading. */
    it('reads the exact DynamoNumber, which writes back as N', () => {
        const read = opaque.unsafeDecode({ N: '1.5' })
        expect(read).toEqual(orThrow(DynamoNumber.from('1.5')))
        expect(opaque.unsafeEncode(read)).toEqual({ N: '1.5' })
    })

    it('reads an NS as a set of DynamoNumbers, which writes back as NS', () => {
        const read = opaque.unsafeDecode({ NS: ['2', '1.5'] })
        expect(opaque.unsafeEncode(read)).toEqual({ NS: ['1.5', '2'] })
    })

    /**
     * Under `'refuse'`, the stored-number text quotes the normal form of the digits, because the
     * policy sees the `DynamoNumber` that the canonical codec read, and not the stored text.
     */
    it('refuses under refuse rather than choose a reading nobody asked for', () => {
        expect(() => opaque('refuse').unsafeDecode({ N: '1.5' })).toThrow(
            /the stored number '1\.5' cannot be stored/,
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

describe('with numbers held exactly', () => {
    /** (C) on the canonical codec, whose read is the widest in the library. */
    it('decodes only what it can write back', () => {
        checkDecodesAreWritable(holderFor(opaque), {
            count: 80,
            seed: 20260829,
        })
    })

    /** (MP) holds at `N` and `NS`, which is what the total codec is for. */
    it('keeps N and NS on a read-modify-write', () => {
        expect(() =>
            checkMembersStable(holderFor(opaque), [
                { v: { N: '1.5' } },
                { v: { N: '12345678901234567890123456789012345678' } },
                { v: { NS: ['1', '2'] } },
            ]),
        ).not.toThrow()
    })
})

describe('with numbers refused', () => {
    /** The same law, on the policy that refuses `N` outright. */
    it('decodes only what it can write back', () => {
        checkDecodesAreWritable(holderFor(opaque('refuse')), {
            count: 80,
            seed: 20260829,
        })
    })

    it('round-trips every generated value', () => {
        checkRoundTrip(holderFor(opaque('refuse')), {
            count: 200,
            seed: 20260826,
        })
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
                { v: { N: '1.5' } },
                { v: { N: '12345678901234567890' } },
                { v: { N: '0' } },
            ]),
        ).not.toThrow()
    })

    /**
     * **(C) for `opaque`, which nobody had ever asked.**
     *
     * `checkDecodesAreWritable` exists for exactly this — it generates *attributes* rather
     * than values, because the attribute that breaks (C) is by definition one `encode` would
     * never make. It had been pointed at `Pet`, at `Listing`, at planted counterexamples, and
     * never at `opaque`, which is the term with the widest read of any in the library.
     *
     * It fails on the pre-fix codec at case 21 of this seed, on the mutation "an N with a
     * leading zero": `{ v: { N: '0-1' } }` decoded to `NaN`, and `NaN` cannot be encoded.
     * `Number` reads far more than an `N` carries, so the read had to gate on the numeral
     * grammar the way `number`'s does.
     */
    it('decodes only what it can write back', () => {
        checkDecodesAreWritable(holderFor(lossy), { count: 80, seed: 20260829 })
    })

    it('loses digits a float cannot hold — which is what lossy means', () => {
        expect(lossy.unsafeDecode({ N: '1.5' })).toBe(1.5)
        expect(lossy.unsafeDecode({ N: '12345678901234567890' })).toBe(
            12345678901234567890,
        )
    })

    it('still refuses a bigint, which decodes as a number and would not come back', () => {
        expect(() => lossy.unsafeEncode(1n)).toThrow(CodecError)
    })
})
