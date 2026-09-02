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
 * which was meant — `union([string.set(), array(string)])` could not be resolved, and the marshaller
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
    string,
} from './codec'
import { checkRoundTrip } from './testing'

declare const brand: unique symbol
type Price = string & { [brand]: 'amount' }
const isAmount = (v: string): v is Price =>
    v.length > 0 && Number.isFinite(Number(v)) && Number(v) >= 0

/**
 * Two predicates that decide nothing, used only to reach `set`'s refusals.
 *
 * The set builder is no longer part of the public surface — `.set()` is — so the only way to hand
 * it an element it must refuse is across a refinement, which is where `.set()` propagates to.
 * These are honest about being trivial: what is under test is the refusal, not the predicate.
 */
const isText = (value: unknown): value is string => typeof value === 'string'
const isTexts = (value: unknown): value is readonly string[] =>
    Array.isArray(value)

const amount = refine(decimal, isAmount, {
    describe: 'a non-negative amount',
    arbitrary: (rng) =>
        (['0', '1', '2.5', '100'] as Price[])[Math.floor(rng() * 4)] as Price,
})

describe('the member follows from the element', () => {
    it('writes SS for strings', () => {
        expect(string.set().unsafeEncode(new Set(['b', 'a']))).toEqual({
            SS: ['a', 'b'],
        })
    })

    it('writes NS for numbers', () => {
        expect(number.set().unsafeEncode(new Set([2, 1]))).toEqual({
            NS: ['1', '2'],
        })
    })

    it('writes BS for binary', () => {
        const encoded = binary
            .set()
            .unsafeEncode(new Set([Uint8Array.from([1])]))
        expect(Object.keys(encoded)).toEqual(['BS'])
    })

    /**
     * The refusals are reached through `refine`, because that is the only way left to hand the set
     * builder an element: `.set()` propagates across a refinement, and the *type* gate there is the
     * attribute — `S`, `N` or `B` — which is as far as a codec's type can see. So each of these
     * pins both halves at once: `@ts-expect-error` says the type declined, and the `toThrow` says
     * the runtime did too.
     */
    it('refuses an element that writes no single member', () => {
        // `nullable` writes its inner member or NULL, so it cannot be a set's element
        const maybe = refine(nullable(string), isText)
        // @ts-expect-error `nullable` writes no single member
        expect(() => maybe.set()).toThrow(CodecError)
        // @ts-expect-error and the runtime says why
        expect(() => maybe.set()).toThrow(
            /a set holds strings, numbers or binary/,
        )
    })

    it('refuses an element that is not a scalar at all', () => {
        const list = refine(array(string), isTexts)
        // @ts-expect-error an `L` is not one of the three members a set is built from
        expect(() => list.set()).toThrow(CodecError)
    })
})

describe('a set of a branded element', () => {
    const Pet = object({
        id: string,
        amounts: amount.set(),
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
        expect(() => string.set().unsafeEncode(new Set())).toThrow(
            /no empty SS/,
        )
        expect(() => number.set().unsafeEncode(new Set())).toThrow(
            /no empty NS/,
        )
    })

    /**
     * The read side of the same refusal, and the one that can actually be reached: DynamoDB never
     * stores an empty `SS`, so an item carrying one came from somewhere else — a migration, a
     * hand-built fixture, another writer. Decoding it used to hand back a `Set` that this codec's
     * own `encode` refuses, so an item could be read and not written back.
     */
    it('refuses to read an empty one, which its own encode would refuse', () => {
        expect(() => string.set().unsafeDecode({ SS: [] })).toThrow(
            /no empty SS/,
        )
        expect(() => number.set().unsafeDecode({ NS: [] })).toThrow(
            /no empty NS/,
        )
    })

    it('reads back a set, whatever order it arrives in', () => {
        expect(string.set().unsafeDecode({ SS: ['b', 'a'] })).toEqual(
            new Set(['a', 'b']),
        )
        expect(string.set().unsafeDecode({ SS: ['a', 'b'] })).toEqual(
            new Set(['a', 'b']),
        )
    })

    it('writes sorted, so what is stored does not depend on insertion order', () => {
        expect(string.set().unsafeEncode(new Set(['b', 'a']))).toEqual({
            SS: ['a', 'b'],
        })
    })

    it('deduplicates by what is stored, which a Set alone does not', () => {
        // two distinct members that write the same `N`: the set has two, the table holds one
        expect(number.set().unsafeEncode(new Set([1, 1.0]))).toEqual({
            NS: ['1'],
        })
    })
})
