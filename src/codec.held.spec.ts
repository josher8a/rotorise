/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart. An attribute is **stored** as `S`, `N`, `SS`; it is **held**,
 * in code, as a `string`, a `Date`, an array. `held` changes only the second, which makes it the
 * answer to "my values arrive as an array and `set(...)` wants a `Set`" — nothing about the table has
 * to change for that, so nothing about what is written does either.
 */
import { describe, expect, it } from 'vitest'
import type { N, S, SS } from './attribute'
import type { Encoded } from './codec'
import {
    array,
    CodecError,
    decimal,
    failed,
    held,
    number,
    object,
    optional,
    refine,
    set,
    string,
    union,
    writes,
} from './codec'
import { checkEncodePaths, checkRoundTrip } from './testing'

/** The case that prompted it: values arrive as an array, the table holds a set. */
const tags = held(set(string), {
    encode: (tags: readonly string[]) => new Set(tags),
    decode: (tags) => [...tags],
})

describe('an array held where the table holds a set', () => {
    const Pet = object({ id: string, tags }).item

    it('writes SS, because that is what the inner codec writes', () => {
        expect(Pet.unsafeEncode({ id: 'p', tags: ['b', 'a'] })).toEqual({
            id: { S: 'p' },
            tags: { SS: ['a', 'b'] },
        })
    })

    it('reads back an array, not a Set', () => {
        const back = Pet.unsafeDecode({
            id: { S: 'p' },
            tags: { SS: ['a', 'b'] },
        })
        const held: readonly string[] = back.tags
        expect(held).toEqual(['a', 'b'])
        expect(back.tags).not.toBeInstanceOf(Set)
    })

    it('types the attribute as the inner codec does', () => {
        // the assertion is the type: `SS`, unchanged by the adapter
        const written: { readonly id: S; readonly tags: SS } = {} as Encoded<{
            id: typeof string
            tags: typeof tags
        }>
        expect(typeof written).toBe('object')
    })

    it('is still an SS to everything that asks the definition', () => {
        expect(writes(tags)).toBe('SS')
    })

    it('round-trips, with values generated through the adapter', () => {
        checkRoundTrip(Pet, { count: 200, seed: 20260827 })
    })

    it('and the encode paths agree', () => {
        checkEncodePaths(Pet, { count: 100, seed: 20260827 })
    })

    it('still refuses what the inner codec refuses', () => {
        expect(() => Pet.unsafeEncode({ id: 'p', tags: [] })).toThrow(
            /no empty SS/,
        )
    })
})

describe('a Date held where the table holds a string', () => {
    const when = held(string, {
        encode: (at: Date) => at.toISOString(),
        decode: (at) => new Date(at),
    })
    const Visit = object({ id: string, at: when }).item

    it('stores the ISO string', () => {
        expect(
            Visit.unsafeEncode({
                id: 'v',
                at: new Date('2026-01-01T00:00:00.000Z'),
            }).at,
        ).toEqual({ S: '2026-01-01T00:00:00.000Z' })
    })

    it('reads back a Date', () => {
        const back = Visit.unsafeDecode({
            id: { S: 'v' },
            at: { S: '2026-01-01T00:00:00.000Z' },
        })
        expect(back.at).toBeInstanceOf(Date)
        expect(back.at.getTime()).toBe(Date.parse('2026-01-01T00:00:00.000Z'))
    })
})

describe('a number held where the table holds digits', () => {
    /**
     * `decimal` exists so money never becomes a float, and holds a `string` for that reason. Where a
     * count really is a number and the digits still matter, the adapter says so locally.
     */
    const counted = held(decimal, {
        encode: (n: number) => String(n),
        decode: Number,
    })

    it('writes N and reads back a number', () => {
        expect(counted.unsafeEncode(42)).toEqual({ N: '42' })
        expect(counted.unsafeDecode({ N: '42' })).toBe(42)
    })
})

describe('failure belongs to the inner codec', () => {
    /**
     * Both halves of an adapter are total, so a conversion that can fail is narrowed first — and the
     * error then names what was wrong with the *value* rather than what went wrong converting it.
     */
    const isIso = (v: string): v is string => !Number.isNaN(Date.parse(v))
    const when = held(refine(string, isIso, { describe: 'an ISO timestamp' }), {
        encode: (at: Date) => at.toISOString(),
        decode: (at) => new Date(at),
    })

    it('reports the stored value, not the conversion', () => {
        expect(() => when.unsafeDecode({ S: 'not a date' })).toThrow(CodecError)
        expect(() => when.unsafeDecode({ S: 'not a date' })).toThrow(
            /is not an ISO timestamp/,
        )
    })
})

describe('a conversion that throws', () => {
    /**
     * The two halves are the one place in a codec where code this library did not write runs, so the
     * throw is contained where it happens.
     *
     * It has to be. A conversion is ordinary code and ordinary code throws — and a codec that let
     * that escape would make every caller defensive about it. One of them already was: a union tries
     * an option to find out whether it is the right one, and catching there also swallowed failures
     * that had nothing to do with an adapter.
     */
    const broken = held(string, {
        encode: (value: { toString(): string }) => value.toString(),
        decode: (raw) => JSON.parse(raw) as { toString(): string },
    })

    it('fails as a Result on the way in, rather than throwing', () => {
        const written = broken.encode(null as never)
        expect(failed(written)).toBe(true)
        expect((written as CodecError).message).toMatch(
            /the conversion for writing this attribute threw/,
        )
    })

    it('fails as a Result on the way out, rather than throwing', () => {
        const read = broken.decode({ S: 'not json' })
        expect(failed(read)).toBe(true)
        expect((read as CodecError).message).toMatch(
            /the conversion for reading this attribute threw/,
        )
    })

    it('so `unsafe` still throws a CodecError, like every other codec', () => {
        expect(() => broken.unsafeDecode({ S: 'not json' })).toThrow(CodecError)
    })

    it('and a union can try it without catching anything itself', () => {
        // `tags` reaches `new Set(4)` for a number, which throws inside the conversion
        const Either = union([tags, number])
        expect(Either.unsafeEncode(4)).toEqual({ N: '4' })
        expect(Either.unsafeEncode(['a'])).toEqual({ SS: ['a'] })
    })
})

describe('composing with the rest', () => {
    it('is optional like anything else', () => {
        const Pet = object({ id: string, tags: optional(tags) }).item
        expect(Pet.unsafeEncode({ id: 'p' })).toEqual({ id: { S: 'p' } })
        expect(Pet.unsafeDecode({ id: { S: 'p' } })).toEqual({ id: 'p' })
    })

    it('nests inside a map', () => {
        const Held = object({ inner: object({ tags }) })
        expect(Held.unsafeEncode({ inner: { tags: ['a'] } })).toEqual({
            M: { inner: { M: { tags: { SS: ['a'] } } } },
        })
    })

    /**
     * And it is the one codec a union cannot filter by kind.
     *
     * `carries` refuses to read through an adapter, because reading through is exactly wrong: the
     * inner codec takes a `Set` and this takes an array. With nothing declared, the union tries it —
     * which still resolves, because only one option can carry a number.
     */
    it('is tried by a union rather than filtered, and still resolves', () => {
        const Either = union([tags, number])
        expect(Either.unsafeDecode({ SS: ['a'] })).toEqual(['a'])
        expect(Either.unsafeDecode({ N: '4' })).toBe(4)
    })

    /**
     * And the limit, which is where a union stops being able to help.
     *
     * `readonly string[]` and `readonly number[]` are disjoint *types*, so the declaration is
     * allowed — but they are the same kind of runtime value, and neither `array(number)` nor the
     * adapter validates what it is given. So both succeed on `['a']` and the ambiguity is real.
     *
     * Reported rather than guessed, which is the only useful thing left to do about it. The way out
     * is a discriminator, as the message says.
     */
    it('cannot be told apart from a list of another element', () => {
        const Either = union([tags, array(number)])
        // `'1'` and not `'a'`: since `number` gates on what DynamoDB stores, `'a'` is refused by
        // the array option and the union resolves. The ambiguity is real for numeric text, which
        // is the sharper witness anyway — both options genuinely admit it
        expect(() => Either.unsafeEncode(['1'])).toThrow(
            /held and array both admit this value/,
        )
        // and reading is fine, because `SS` and `L` say which
        expect(Either.unsafeDecode({ SS: ['a'] })).toEqual(['a'])
        expect(Either.unsafeDecode({ L: [{ N: '1' }] })).toEqual([1])
    })
})
