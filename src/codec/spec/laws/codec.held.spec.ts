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
import { memberOf } from '../../attribute'
import type { AnyCodec, Encoded } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    failed,
    held,
    list,
    number,
    object,
    optional,
    refine,
    spread,
    string,
    union,
    valueKinds,
    withLegacyRead,
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

/**
 * The case that prompted it: values arrive as an array, the table holds a set. The held side
 * states a non-empty array, because the store has no empty set.
 */
const tags = held(string.set(), list(string, spread(string)), {
    encode: (tags: readonly [string, ...string[]]) => new Set(tags),
    decode: (tags) => {
        const [first, ...rest] = tags
        if (first === undefined)
            return new CodecError('a string set has no empty value')
        const read: readonly [string, ...string[]] = [first, ...rest]
        return read
    },
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
        expect(() => Pet.unsafeEncode({ id: 'p', tags: [] as never })).toThrow(
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
        // the held side of `tags` is a list of strings, so a number never reaches the conversion
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
     * takes an array. The held side, a list of strings, is the kind the union reads.
     */
    it('is filtered by a union through its held side, and resolves', () => {
        const Either = union([tags, number])
        expect(Either.unsafeDecode({ SS: ['a'] })).toEqual(['a'])
        expect(Either.unsafeDecode({ N: '4' })).toBe(4)
    })

    /**
     * **A list beside a list of another element is told apart by its elements.**
     *
     * The guard reads the two views of `tags`. The held side of `tags` requires one string or
     * more, and `array(number)` admits `[]` and lists of numbers, so no caller value is admitted by
     * both. `tags` stores `SS` and `array(number)` stores `L`, so no attribute is read by both.
     */
    it('is told apart from a list of another element, by its elements', () => {
        const Either = union([tags, array(number)])
        expect(Either.unsafeEncode(['1'])).toEqual({ SS: ['1'] })
        // and the array arm still writes what it owns
        expect(Either.unsafeEncode([1])).toEqual({ L: [{ N: '1' }] })
        // reading was never the problem, because `SS` and `L` say which
        expect(Either.unsafeDecode({ SS: ['a'] })).toEqual(['a'])
        expect(Either.unsafeDecode({ L: [{ N: '1' }] })).toEqual([1])
    })

    /**
     * **A held side that admits `[]` is refused beside a list of another element.** The caller
     * views `array(string)` and `array(number)` both admit `[]`, and the declaration cannot show
     * that the adapter writes `[]` where `array(number)` writes it.
     */
    it('refuses a list of another element beside a held side that admits the empty list', () => {
        const loose = held(string.set(), array(string), {
            encode: (tags: readonly string[]) => new Set(tags),
            decode: (tags) => [...tags],
        })
        // declared through a cast, as a caller passing an erased list would
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => unknown
        expect(() => declare([loose, array(number)])).toThrow(
            /are not shown compatible/,
        )
    })
})

describe('two adapters in one union', () => {
    // a switch that the caller holds as `'on'` or `'off'`, and that the table stores as `BOOL`
    const onOff = held(boolean, string('on', 'off'), {
        encode: (s: 'on' | 'off') => s === 'on',
        decode: (b) => (b ? 'on' : 'off'),
    })
    // declared through a cast, as a caller passing an erased list would
    const declare = union as unknown as (
        options: readonly AnyCodec[],
    ) => unknown

    /**
     * **Two adapters are told apart where their held sides and their inner terms are each
     * disjoint.** The two conversions differ, so one bare comparison of the two options proves
     * nothing. The two views do: no caller value is in both held sides, and no attribute is in both
     * inner terms.
     */
    it('is declared where the held sides and the inner terms are each disjoint', () => {
        const auto = held(string('AUTO'), string('auto'), {
            encode: (_: 'auto') => 'AUTO' as const,
            decode: (_) => 'auto' as const,
        })
        const Mode = union([onOff, auto])
        expect(Mode.unsafeEncode('on')).toEqual({ BOOL: true })
        expect(Mode.unsafeEncode('auto')).toEqual({ S: 'AUTO' })
        expect(Mode.unsafeDecode({ BOOL: false })).toBe('off')
        expect(Mode.unsafeDecode({ S: 'AUTO' })).toBe('auto')
    })

    /**
     * **Two adapters over one inner term are refused, although their held sides are disjoint.**
     * Both read a stored `BOOL`, to two different values.
     */
    it('is refused where both inner terms read one attribute', () => {
        const auto = held(boolean, string('auto'), {
            encode: (_: 'auto') => true,
            decode: (_) => 'auto' as const,
        })
        expect(() => declare([onOff, auto])).toThrow(/are not shown compatible/)
    })

    /**
     * **A boolean beside its negation is refused.** The two options admit every boolean, and they
     * write `true` to two attributes, so the option order would decide what the union stores.
     */
    it('refuses a boolean beside its own negation, because the order would decide the attribute', () => {
        const flipped = held(boolean, boolean, {
            encode: (b: boolean) => !b,
            decode: (b) => !b,
        })
        expect(() => declare([boolean, flipped])).toThrow(
            /are not shown compatible/,
        )
        expect(() => declare([flipped, boolean])).toThrow(
            /are not shown compatible/,
        )
    })
})

describe('a literal beside an adapter', () => {
    // declared through a cast, as a caller passing an erased list would
    const declare = union as unknown as (
        options: readonly AnyCodec[],
    ) => unknown

    /**
     * **The adapter reads the stored `S` to a lower-case value, and the literal reads the same
     * `S` to itself.** `encode('x')` writes `{ S: 'X' }`, and both options admit that attribute,
     * so the union cannot read back the value that it wrote.
     */
    it('a literal beside an adapter that reads the same attribute to another value is refused', () => {
        const upper = refine(
            string,
            (s: string): s is string =>
                s === s.toUpperCase() && s !== s.toLowerCase(),
            { describe: 'upper case' },
        )
        const lower = refine(
            string,
            (s: string): s is string =>
                s === s.toLowerCase() && s !== s.toUpperCase(),
            { describe: 'lower case' },
        )
        const shout = held(upper, lower, {
            encode: (s) => s.toUpperCase(),
            decode: (s) => s.toLowerCase(),
        })
        expect(shout.unsafeDecode(shout.unsafeEncode('x'))).toBe('x')
        expect(() => declare([shout, string('X')])).toThrow(
            /are not shown compatible/,
        )
    })

    /**
     * **`decimal` and the literal both take the caller's `'1'`.** `decimal` writes it as `{ N: '1' }`
     * and the literal writes it as `{ S: '1' }`, so the option order would decide the attribute.
     */
    it('a literal beside an adapter that shares a caller value with it is refused', () => {
        expect(() => declare([decimal, string('1')])).toThrow(
            /are not shown compatible/,
        )
    })

    /**
     * **The host cannot show that the two options are compatible.** The held side of `decimal` is
     * `string`, not a data predicate for numerals, so the declaration cannot see that `'a'` is
     * outside it.
     */
    it('a literal beside an adapter is refused, because the held side of the adapter is not a data predicate', () => {
        expect(() => declare([decimal, string('a')])).toThrow(
            /are not shown compatible/,
        )
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
    // declared through a cast, as a caller passing an erased list would
    const declare = union as unknown as (
        options: readonly AnyCodec[],
    ) => unknown

    /**
     * `decimal` holds text and stores `N`. `boolean` holds a boolean and stores `BOOL`. The two
     * are disjoint on both sides, and the model certifies the pair: the caller views and the
     * stored views meet at the bottom (`viewsNever`).
     */
    it('accepts decimal beside boolean, because the held sides are disjoint', () => {
        const either = union([decimal, boolean])
        expect(either.unsafeEncode('1.5')).toEqual({ N: '1.5' })
        expect(either.unsafeEncode(true)).toEqual({ BOOL: true })
    })

    it('refuses decimal beside string, because both hold text', () => {
        expect(() => declare([decimal, string])).toThrow(CodecError)
    })

    /**
     * A legacy read over `decimal` has no views: the legacy read reads an attribute to a held
     * value. The meet still answers the bottom, because the tags `'x'` and `'y'` meet at the
     * bottom, and a slot at the bottom decides before a slot that refuses. The decision keeps the
     * row of the raw terms, `disjoint`, for this pair.
     */
    it('accepts two objects whose tags differ, where one object reads a legacy form of decimal', () => {
        const tagged = union([
            object({
                a: withLegacyRead({ current: decimal, older: string }),
                k: string('x'),
            }),
            object({ a: string, k: string('y') }),
        ])
        expect(tagged.unsafeEncode({ a: '1.5', k: 'x' })).toEqual({
            M: { a: { N: '1.5' }, k: { S: 'x' } },
        })
        expect(tagged.unsafeEncode({ a: '1.5', k: 'y' })).toEqual({
            M: { a: { S: '1.5' }, k: { S: 'y' } },
        })
    })

    it('refuses a foreign held side beside a codec, because the top meets every kind', () => {
        const when = held(string, date, {
            encode: (at: Date) => at.toISOString(),
            decode: (at) => new Date(at),
        })
        expect(() => declare([when, number])).toThrow(CodecError)
    })

    it('stores a foreign held side in the member of the inner codec, and takes every kind', () => {
        const at = held(decimal, date, {
            encode: (at: Date) => String(at.getTime()),
            decode: (at: string) => new Date(Number(at)),
        })
        expect(memberOf(at.encode(new Date(0)) as never)).toBe('N')
        expect(valueKinds(at.def)).toEqual(valueKinds({ kind: 'opaq' }))
    })
})
