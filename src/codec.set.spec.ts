/**
 * Sets, whose member follows from their element.
 *
 * `stringSet` was fixed to `readonly string[]`, so a branded element could not survive it — a set of
 * `Price` came back as a set of `string`, and checking them again was yours to do. Which set
 * DynamoDB writes is decided by what the members are, so taking the element codec is both the more
 * general thing and the more accurate one.
 *
 * Held as a `Set`, which is what it is. An array was the earlier reading and it cost the distinction
 * that matters most here: a set and a list are given the same array, so nothing about a value said
 * which was meant — `union([set(string), array(string)])` could not be resolved, and the marshaller
 * this library mirrors reads `SS` back as a `Set` besides.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    binary,
    CodecError,
    decimal,
    nullable,
    number,
    object,
    refine,
    set,
    string,
} from './codec'
import { checkRoundTrip } from './testing'

declare const brand: unique symbol
type Price = string & { [brand]: 'amount' }
const isAmount = (v: string): v is Price =>
    v.length > 0 && Number.isFinite(Number(v)) && Number(v) >= 0

const amount = refine(decimal, isAmount, {
    describe: 'a non-negative amount',
    arbitrary: (rng) =>
        (['0', '1', '2.5', '100'] as Price[])[Math.floor(rng() * 4)] as Price,
})

describe('the member follows from the element', () => {
    it('writes SS for strings', () => {
        expect(set(string).unsafeEncode(new Set(['b', 'a']))).toEqual({
            SS: ['a', 'b'],
        })
    })

    it('writes NS for numbers', () => {
        expect(set(number).unsafeEncode(new Set([2, 1]))).toEqual({
            NS: ['1', '2'],
        })
    })

    it('writes BS for binary', () => {
        const encoded = set(binary).unsafeEncode(
            new Set([Uint8Array.from([1])]),
        )
        expect(Object.keys(encoded)).toEqual(['BS'])
    })

    it('refuses an element that writes no single member', () => {
        // `nullable` writes its inner member or NULL, so it cannot be a set's element
        expect(() => set(nullable(string))).toThrow(CodecError)
        expect(() => set(nullable(string))).toThrow(
            /a set holds strings, numbers or binary/,
        )
    })

    it('refuses an element that is not a scalar at all', () => {
        expect(() => set(array(string))).toThrow(CodecError)
    })
})

describe('a set of a branded element', () => {
    const Pet = object({
        id: string,
        amounts: set(amount),
    }).item

    it('stores the brand as N, because that is what the element writes', () => {
        expect(
            Pet.unsafeEncode({
                id: 'w',
                amounts: new Set(['2.5', '1'] as Price[]),
            }),
        ).toEqual({ id: { S: 'w' }, amounts: { NS: ['1', '2.5'] } })
    })

    it('decodes back as the brand, not as plain strings', () => {
        const back = Pet.unsafeDecode({
            id: { S: 'w' },
            amounts: { NS: ['1', '2.5'] },
        })
        // the assertion is the type: these are Prices, checked on the way in
        const amounts: ReadonlySet<Price> = back.amounts
        expect([...amounts]).toEqual(['1', '2.5'])
    })

    it("runs the brand's predicate on every member", () => {
        expect(() =>
            Pet.unsafeDecode({ id: { S: 'w' }, amounts: { NS: ['1', '-5'] } }),
        ).toThrow(/is not a non-negative amount/)
    })

    it('round-trips over generated values', () => {
        checkRoundTrip(Pet, { count: 200, seed: 20260826 })
    })
})

describe('what a set cannot hold', () => {
    it('refuses to write an empty one', () => {
        expect(() => set(string).unsafeEncode(new Set())).toThrow(/no empty SS/)
        expect(() => set(number).unsafeEncode(new Set())).toThrow(/no empty NS/)
    })

    /**
     * The read side of the same refusal, and the one that can actually be reached: DynamoDB never
     * stores an empty `SS`, so an item carrying one came from somewhere else — a migration, a
     * hand-built fixture, another writer. Decoding it used to hand back a `Set` that this codec's
     * own `encode` refuses, so an item could be read and not written back.
     */
    it('refuses to read an empty one, which its own encode would refuse', () => {
        expect(() => set(string).unsafeDecode({ SS: [] })).toThrow(
            /no empty SS/,
        )
        expect(() => set(number).unsafeDecode({ NS: [] })).toThrow(
            /no empty NS/,
        )
    })

    it('reads back a set, whatever order it arrives in', () => {
        expect(set(string).unsafeDecode({ SS: ['b', 'a'] })).toEqual(
            new Set(['a', 'b']),
        )
        expect(set(string).unsafeDecode({ SS: ['a', 'b'] })).toEqual(
            new Set(['a', 'b']),
        )
    })

    it('writes sorted, so what is stored does not depend on insertion order', () => {
        expect(set(string).unsafeEncode(new Set(['b', 'a']))).toEqual({
            SS: ['a', 'b'],
        })
    })

    it('deduplicates by what is stored, which a Set alone does not', () => {
        // two distinct members that write the same `N`: the set has two, the table holds one
        expect(set(number).unsafeEncode(new Set([1, 1.0]))).toEqual({
            NS: ['1'],
        })
    })
})
