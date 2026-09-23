/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart. An attribute is **stored** as `S`, `N`, `SS`; it is **held**,
 * in code, as a `string`, a `Date`, an array. `held` changes only the second, which makes it the
 * answer to "my values arrive as an array and `.set()` wants a `Set`" — nothing about the table has
 * to change for that, so nothing about what is written does either.
 */
import { describe, expect, it } from 'vitest'
import type { S, SS } from '../../attribute'
import type { AnyCodec, Encoded } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    failed,
    held,
    number,
    object,
    optional,
    refine,
    string,
    union,
} from '../../codec'
import type { StandardSchemaV1 } from '../../standard'
import { checkEncodePaths, checkRoundTrip } from '../../testing'

/** A Standard Schema v1 written by hand: a foreign held side that admits a `Date`. */
const date: StandardSchemaV1<Date> = {
    '~standard': {
        version: 1,
        vendor: 'handwritten',
        validate: (value) =>
            value instanceof Date
                ? { value }
                : { issues: [{ message: 'expected a Date' }] },
    },
}

/** …and one that admits every value, for a test whose subject is the conversion alone. */
const anything = <T>(): StandardSchemaV1<T> => ({
    '~standard': {
        version: 1,
        vendor: 'handwritten',
        validate: (value) => ({ value: value as T }),
    },
})

/** The case that prompted it: values arrive as an array, the table holds a set. */
const tags = held(string.set(), array(string), {
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

    it('round-trips, with values generated through the adapter', () => {
        checkRoundTrip(Pet, { count: 200, seed: 20260827 })
    })

    it('and the encode paths agree', () => {
        checkEncodePaths(Pet, { count: 100, seed: 20260827 })
    })

    it('still refuses what the inner codec refuses', () => {
        expect(() => Pet.unsafeEncode({ id: 'p', tags: [] })).toThrow(
            CodecError,
        )
    })
})

describe('a Date held where the table holds a string', () => {
    const when = held(string, date, {
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
    const counted = held(decimal, number, {
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
    const when = held(
        refine(string, isIso, { describe: 'an ISO timestamp' }),
        date,
        {
            encode: (at: Date) => at.toISOString(),
            decode: (at) => new Date(at),
        },
    )

    /**
     * **Pins wording no law has, deliberately.** The refusal is asserted as a `CodecError` beside
     * it; what the regex adds is the diagnostic, which is this test's subject. Here it is which of the two
     * halves is blamed: an adapter's failure has to name the value that was *stored*, because the
     * conversion is the caller's code and its own message would say nothing about the row.
     */
    it('reports the stored value, not the conversion', () => {
        expect(() => when.unsafeDecode({ S: 'not a date' })).toThrow(CodecError)
        expect(() => when.unsafeDecode({ S: 'not a date' })).toThrow(
            /is not an ISO timestamp/,
        )
    })
})

describe('a conversion that cannot convert', () => {
    /**
     * A half that has nothing to hand over returns a {@link CodecError}, and the signature says so.
     * A refusal is a value on this surface, so declining a conversion is a refusal like any other:
     * the caller reads it the way it reads every other one, and nothing has to catch.
     *
     * This is what an adapter over a narrower carrier needs. A text-to-number adapter meets text
     * that is not a number, and it owes the caller a reason rather than an exception.
     */
    // every number, `NaN` included, so the refusal under test is the conversion's own
    const digits = held(string, anything<number>(), {
        encode: (value: number) =>
            Number.isFinite(value)
                ? String(value)
                : new CodecError(`${value} has no digits to write`),
        decode: (raw) => {
            const read = Number(raw)
            return Number.isNaN(read)
                ? new CodecError(`'${raw}' is not a number`)
                : read
        },
    })

    it('refuses on the way in with the reason the half gave', () => {
        const written = digits.encode(Number.NaN)
        expect(failed(written)).toBe(true)
        expect((written as CodecError).message).toBe(
            'NaN has no digits to write',
        )
    })

    it('refuses on the way out with the reason the half gave', () => {
        const read = digits.decode({ S: 'abc' })
        expect(failed(read)).toBe(true)
        expect((read as CodecError).message).toBe("'abc' is not a number")
    })

    it('does not dress the refusal as a throw, which is what a caller reads', () => {
        const written = digits.encode(Number.NaN)
        expect((written as CodecError).message).not.toMatch(/threw/)
    })

    it('still writes and reads the values it can convert', () => {
        expect(digits.encode(1.5)).toEqual({ S: '1.5' })
        expect(digits.decode({ S: '1.5' })).toBe(1.5)
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
    const broken = held(string, anything<{ toString(): string }>(), {
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
        // the held side of `tags` is `array(string)`, so a number never reaches the conversion
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
     * And a union filters it by the kind of its held side, not of its inner codec.
     *
     * Reading through to the inner codec is exactly wrong: the inner codec takes a `Set` and this
     * takes an array. The held side, `array(string)`, is the kind the union reads.
     */
    it('is filtered by a union through its held side, and resolves', () => {
        const Either = union([tags, number])
        expect(Either.unsafeDecode({ SS: ['a'] })).toEqual(['a'])
        expect(Either.unsafeDecode({ N: '4' })).toBe(4)
    })

    /**
     * **A list beside a list of another element is refused at the declaration.**
     *
     * The guard reads the declared held side. `tags` declares `array(string)`, which admits `[]`,
     * and `array(number)` admits `[]` too, so the two held sides are not disjoint and nothing
     * certifies the pair. `tags` itself refuses `[]`, because its inner set has no empty value, so
     * the refusal is conservative: a precise held side would state a non-empty list.
     */
    it('refuses a list of another element beside it, because both admit the empty list', () => {
        // declared through a cast, as a caller bypassing the compile-time check would
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => unknown
        expect(() => declare([tags, array(number)])).toThrow(CodecError)
    })
})

describe('the held side restricts both halves', () => {
    /**
     * `held` is the one codec that runs caller code, and a TypeScript type does not exist at run
     * time. Without the check, a string typed as a `Date` reached `.toISOString()`, and the refusal
     * named a thrown `TypeError` rather than the value. The held side answers first, by name.
     */
    it('refuses a value outside the held side by name, before encode runs', () => {
        let calls = 0
        const when = held(string, date, {
            encode: (at: Date) => {
                calls += 1
                return at.toISOString()
            },
            decode: (at) => new Date(at),
        })
        const written = when.encode('2020-01-01' as never)
        expect(failed(written)).toBe(true)
        expect((written as CodecError).reason).toMatch(
            /the held side of this `held`, a handwritten schema, refuses the value before `encode` runs: expected a Date/,
        )
        expect(calls).toBe(0)
    })

    it('refuses a value outside a held side of this library with the reason of that codec', () => {
        const written = tags.encode('a' as never)
        expect(failed(written)).toBe(true)
        expect((written as CodecError).reason).toMatch(
            /a codec of this library, refuses the value before `encode` runs: string `a` is not an array/,
        )
    })

    it('refuses a decoded value outside the held side, because the read must be writable', () => {
        const lying = held(string, date, {
            encode: (at: Date) => at.toISOString(),
            decode: (at) => at as unknown as Date,
        })
        const read = lying.decode({ S: '2020-01-01' })
        expect(failed(read)).toBe(true)
        expect((read as CodecError).reason).toMatch(
            /refuses the value that `decode` returned: expected a Date/,
        )
    })

    it('refuses an asynchronous schema as a value, because a codec answers synchronously', () => {
        const later: StandardSchemaV1<Date> = {
            '~standard': {
                version: 1,
                vendor: 'handwritten',
                validate: (value) => Promise.resolve({ value: value as Date }),
            },
        }
        const when = held(string, later, {
            encode: (at: Date) => at.toISOString(),
            decode: (at) => new Date(at),
        })
        const written = when.encode(new Date(0))
        expect(failed(written)).toBe(true)
        expect((written as CodecError).reason).toMatch(
            /answered with a Promise/,
        )
    })

    it('refuses a schema that throws as a value', () => {
        const thrower: StandardSchemaV1<Date> = {
            '~standard': {
                version: 1,
                vendor: 'handwritten',
                validate: () => {
                    throw new Error('boom')
                },
            },
        }
        const when = held(string, thrower, {
            encode: (at: Date) => at.toISOString(),
            decode: (at) => new Date(at),
        })
        expect(failed(when.encode(new Date(0)))).toBe(true)
    })
})

describe('the held side is the write occupancy of a union option', () => {
    // declared through a cast, as a caller bypassing the compile-time check would
    const declare = union as unknown as (
        options: readonly AnyCodec[],
    ) => unknown

    /**
     * `decimal` holds text and stores `N`. `boolean` holds a boolean and stores `BOOL`. The two
     * are disjoint on both sides, and the model certifies the pair: `Orth1 decimalHeld boolean`.
     */
    it('accepts decimal beside boolean, because the held sides are disjoint', () => {
        const either = union([decimal, boolean])
        expect(either.unsafeEncode('1.5')).toEqual({ N: '1.5' })
        expect(either.unsafeEncode(true)).toEqual({ BOOL: true })
    })

    it('refuses decimal beside string, because both hold text', () => {
        expect(() => declare([decimal, string])).toThrow(CodecError)
    })

    it('refuses a foreign held side beside a codec, because the top meets every kind', () => {
        const when = held(string, date, {
            encode: (at: Date) => at.toISOString(),
            decode: (at) => new Date(at),
        })
        expect(() => declare([when, number])).toThrow(CodecError)
    })
})
