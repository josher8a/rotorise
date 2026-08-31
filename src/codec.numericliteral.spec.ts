/**
 * Literals over numbers, which is how an enum indexed by number is expressed.
 *
 * A literal is the one ground term whose stored member follows from its *values* rather than from its
 * name: text is `S`, digits are `N`. So the same constructor covers a string enum and a numeric one,
 * and a mix of the two is refused — one codec cannot write two members.
 *
 * The held value is the number, not its text. `N` carries digits on the wire, and reading one back as
 * `'0'` would make the literal type a lie.
 */
import { describe, expect, it } from 'vitest'
import type { N, NS, S, SS } from './attribute'
import {
    CodecError,
    carries,
    decides,
    discriminatedUnion,
    literal,
    number,
    object,
    set,
    string,
    union,
    writes,
} from './codec'
import { checkRoundTrip } from './testing'

/** The shape these are usually written in. */
const Status = { DRAFT: 0, LISTED: 1, SOLD: 2 } as const
type Status = (typeof Status)[keyof typeof Status]

const status = literal(...(Object.values(Status) as Status[]))

describe('a numeric literal', () => {
    it('is stored as N', () => {
        expect(writes(status)).toBe('N')
        expect(status.unsafeEncode(1)).toEqual({ N: '1' })
    })

    it('is held as the number, not as its digits', () => {
        const back: Status = status.unsafeDecode({ N: '2' })
        expect(back).toBe(2)
        expect(typeof back).toBe('number')
    })

    it('types the attribute as N, and a string literal as S', () => {
        const numeric: N = status.unsafeEncode(0)
        const text: S = literal('DRAFT').unsafeEncode('DRAFT')
        expect([numeric, text]).toHaveLength(2)
    })

    it('checks the admissible set in both directions', () => {
        expect(() => status.unsafeDecode({ N: '7' })).toThrow(
            /7 is not one of 0, 1, 2/,
        )
        expect(() => status.unsafeEncode(7 as Status)).toThrow(CodecError)
    })

    it('refuses the digits stored as text', () => {
        expect(() => status.unsafeDecode({ S: '1' })).toThrow(
            /expected attribute member 'N', found 'S'/,
        )
    })

    it('keeps the constant brand for a single value', () => {
        const draft = literal(0)
        // the brand is type-level, and the annotation is the assertion; `decides` is what reads the
        // value back at runtime, and is what a key component is built from
        type Only = typeof draft.constant
        const _narrowed: 0 = null as unknown as Only
        expect(decides(draft)).toBe(0)
        // and two admissible values decide nothing, which is the point of `decides`
        expect(decides(status)).toBeUndefined()
    })

    it('takes a number, which is what a union filters on', () => {
        expect(carries(status)).toEqual(['number'])
    })

    it('round-trips', () => {
        checkRoundTrip(object({ status }).item, { count: 100, seed: 20260828 })
    })
})

describe('a numeric tag', () => {
    /**
     * `readTag` always accepted `S` or `N` — a tag is stored as one or the other — so the only thing
     * standing between a numeric enum and a discriminated union was the literal.
     */
    type Row = { kind: 0; draftedAt: string } | { kind: 1; listedAt: string }

    const Rows = discriminatedUnion('kind', [
        object({ kind: literal(0), draftedAt: string }),
        object({ kind: literal(1), listedAt: string }),
    ])

    it('chooses the variant', () => {
        expect(Rows.item.unsafeEncode({ kind: 1, listedAt: 'now' })).toEqual({
            kind: { N: '1' },
            listedAt: { S: 'now' },
        })
    })

    it('and reads it back, tag included, as a number', () => {
        const back: Row = Rows.item.unsafeDecode({
            kind: { N: '0' },
            draftedAt: { S: 'x' },
        })
        expect(back).toEqual({ kind: 0, draftedAt: 'x' })
    })

    it('reaches a variant by its numeric tag', () => {
        expect(
            Rows.item.variant(0).field('draftedAt').unsafeEncode('t'),
        ).toEqual({ S: 't' })
    })

    it('refuses a tag no variant names', () => {
        expect(() =>
            Rows.item.unsafeDecode({ kind: { N: '9' }, draftedAt: { S: 'x' } }),
        ).toThrow(/'9' is not a variant of 'kind'/)
    })
})

/**
 * A set of a literal, which is how a fixed vocabulary is stored.
 *
 * The member follows all the way up: a literal of text is `S`, so a set of it is `SS`; a literal of
 * digits is `N`, so a set of it is `NS`. Nothing new was needed for this — `set` reads its element's
 * member, and the element now has one either way.
 */
describe('a set of a literal', () => {
    const tags = set(literal('a', 'b', 'c'))
    const codes = set(literal(1, 2, 3, 4))

    it('writes SS for text and NS for digits', () => {
        expect(writes(tags)).toBe('SS')
        expect(writes(codes)).toBe('NS')
        const asSS: SS = tags.unsafeEncode(new Set(['c', 'a']))
        const asNS: NS = codes.unsafeEncode(new Set([3, 1]))
        expect(asSS).toEqual({ SS: ['a', 'c'] })
        expect(asNS).toEqual({ NS: ['1', '3'] })
    })

    it('holds a set of the literal union', () => {
        const back: ReadonlySet<1 | 2 | 3 | 4> = codes.unsafeDecode({
            NS: ['1', '3'],
        })
        expect(back).toEqual(new Set([1, 3]))
    })

    it('checks each member, naming where it failed', () => {
        expect(() => codes.unsafeDecode({ NS: ['9'] })).toThrow(
            /at \[0\]: 9 is not one of 1, 2, 3, 4/,
        )
        expect(() => tags.unsafeDecode({ SS: ['z'] })).toThrow(
            /at \[0\]: 'z' is not one of 'a', 'b', 'c'/,
        )
    })

    /**
     * `NS` is sorted as text, so `10` precedes `2` in the table — and a set is unordered, so the law
     * holds anyway. This is the case that would break if a set were an array.
     */
    it('round-trips digits that do not sort numerically', () => {
        const codec = set(literal(1, 2, 10))
        const value = new Set([10, 2] as const)
        expect(codec.unsafeEncode(value)).toEqual({ NS: ['10', '2'] })
        expect(codec.unsafeDecode(codec.unsafeEncode(value))).toEqual(value)
    })

    it('round-trips over generated values', () => {
        checkRoundTrip(object({ tags, codes }).item, {
            count: 100,
            seed: 20260828,
        })
    })

    /**
     * And a union of two such sets is allowed, which is the interesting part.
     *
     * Both options are given a `Set`, so the kind cannot choose between them — but a literal element
     * *refuses* a value that is not its own, so trying can. `union(set(string), set(number))` stays
     * refused for exactly the reason this one is not: those elements check nothing.
     */
    it('and a union of two literal sets resolves, where a union of plain sets cannot', () => {
        const either = union([set(literal('a', 'b')), set(literal(1, 2))])
        expect(either.unsafeEncode(new Set<'a' | 'b'>(['a']))).toEqual({
            SS: ['a'],
        })
        expect(either.unsafeEncode(new Set<1 | 2>([2]))).toEqual({ NS: ['2'] })
        expect(either.unsafeDecode({ NS: ['1'] })).toEqual(new Set([1]))

        expect(() => union([set(string), set(number)])).toThrow(
            /both take the same kind of value — set — and neither checks/,
        )
    })
})

describe('what mixing kinds would ask for', () => {
    it('is refused, because one codec writes one member', () => {
        const _wrong = () =>
            // @ts-expect-error a literal is stored as S or as N and cannot be both
            literal('A', 0)
        expect(_wrong).toThrow(
            /a literal is stored as 'S' or as 'N' and cannot be both/,
        )
    })

    it('though a union of the two is fine, since the kinds differ', () => {
        const either = union([literal('A'), literal(0)])
        expect(either.unsafeEncode('A')).toEqual({ S: 'A' })
        expect(either.unsafeEncode(0)).toEqual({ N: '0' })
        expect(either.unsafeDecode({ N: '0' })).toBe(0)
    })
})

describe('a literal with no alternatives', () => {
    /**
     * `ℓ` non-empty, which the model now carries in the type (`NEFinset`) and this carries at the
     * construction site.
     *
     * `literal()` typechecked — a rest parameter accepts zero arguments — and was not the codec it
     * looked like: the admission check was guarded by `allowed.length &&`, and a truthiness guard in
     * front of a membership test inverts it exactly when the set is empty. So `literal()` admitted
     * *everything*: any string written as `S`, any `S` read back. The caller asked for an enum and
     * silently got `string`, and there is no term in the model that denotes it.
     */
    it('is refused, rather than admitting everything', () => {
        expect(() => literal()).toThrow(/names none/)
    })

    /** And the honest caller the type could not be tightened for is still honest. */
    it('still takes a spread of values the type cannot see as a tuple', () => {
        const values: string[] = ['A', 'B']
        const either = literal(...values)
        expect(either.unsafeEncode('A')).toEqual({ S: 'A' })
        expect(either.decode({ S: 'C' })).toBeInstanceOf(CodecError)
    })
})

describe('the admissible set is what DynamoDB stores', () => {
    /**
     * §3's `(literal-N)` premise `ℓ ⊆ D`, and the defect that made it more than bookkeeping.
     *
     * `number` has refused `NaN`, `Infinity` and anything outside `D` on both halves since the
     * numeral domain was tightened. `literal` had not, and it is the other term that writes `N`:
     * `literal(NaN)` produced `{ N: 'NaN' }` and `literal(1e400)` produced `{ N: 'Infinity' }`,
     * both reachable with no cast, `tsc` clean, and both rejected by the service. An attribute
     * outside §1's `Numerals` is the one thing a term may never write.
     *
     * Refused at the declaration rather than per encode, because that is where the premise lives —
     * `ℓ` is data this library owns, so the check is decidable when the codec is built.
     */
    it('refuses NaN and Infinity, which is where the defect was', () => {
        expect(() => literal(NaN)).toThrow(/has no NaN or Infinity/)
        expect(() => literal(1e400)).toThrow(/has no NaN or Infinity/)
        expect(() => literal(-1e400)).toThrow(/has no NaN or Infinity/)
    })

    it('refuses one bad value among good ones, and names it', () => {
        expect(() => literal(0, 1, NaN)).toThrow(/NaN is not a number/)
    })

    it('names all of them when several are outside', () => {
        expect(() => literal(NaN, 1e400)).toThrow(/NaN, Infinity are not numbers/)
    })

    /** The magnitude range is DynamoDB's, not JavaScript's — `1e200` is a fine double. */
    it('refuses a magnitude past what an N holds', () => {
        expect(() => literal(1e200)).toThrow(/magnitude 1e-130 to 9.9e125/)
        expect(() => literal(1e-200)).toThrow(/magnitude 1e-130 to 9.9e125/)
    })

    /**
     * `5e-324` is the specification's own example of the precondition going unchecked — "the
     * implementation writes whatever `String` produces, so `5e-324` is written and the service
     * rejects it on arrival". Both terms that write an `N` from a double now refuse it here,
     * which is where it is still local.
     */
    it('refuses the denormal the specification named as the unchecked case', () => {
        expect(() => literal(5e-324)).toThrow(/magnitude 1e-130 to 9.9e125/)
        expect(() => number.unsafeEncode(5e-324)).toThrow(
            /magnitude 1e-130 to 9.9e125/,
        )
    })

    it('admits the range that is actually stored, including the ends', () => {
        expect(writes(literal(0, 1, -1, 1e125, 1e-130))).toBe('N')
    })

    /** A string literal is unaffected: `S` carries any text, and the premise is `(literal-N)`'s. */
    it('says nothing about a string literal', () => {
        expect(writes(literal('NaN', 'Infinity'))).toBe('S')
    })
})

describe('the read side reads through the same gate as number', () => {
    /**
     * **The defect the `ℓ ⊆ D` premise did not cover, and was claimed to.**
     *
     * `decode` was `Number(carried)` then a membership test, and `Number` is far wider than an
     * `N`: it reads `''`, whitespace, `0x10`, `0b11`. Membership does not filter those — it only
     * rejects the ones whose numeric value happens to miss the set — so an attribute DynamoDB
     * could never have written decoded to a value the type calls legitimate:
     *
     * ```
     * literal(0, 1, 2).decode({ N: '' })      → 0
     * literal(0, 16).decode({ N: '0x10' })    → 16
     * ```
     *
     * No law in §2 catches it. (C) holds — `0` re-encodes fine — and so does (R). What it breaks
     * is §1: `Carries('N')` is `Numerals`, and `''` is not one, so `p` was defined on something
     * that is not an attribute. `decimal` and `number` both check this on the way in; `literal`
     * is the third term that writes an `N` and it did not.
     *
     * The general form, since it is the second time this arc has met it: **a premise bounds the
     * values this library owns, and a stored attribute is not one of them.** `ℓ ⊆ D` genuinely
     * discharges the write side, because `ℓ` is frozen at construction. Nothing discharges a read.
     */
    it('refuses an N that is not a numeral, whatever Number would make of it', () => {
        const status = literal(0, 1, 2)
        for (const text of ['', ' ', '\n', '0b11', '0o7', '1_0']) {
            expect(() => status.unsafeDecode({ N: text })).toThrow(
                /is not a numeral, so this attribute was not written by DynamoDB/,
            )
        }
        expect(() => literal(0, 16).unsafeDecode({ N: '0x10' })).toThrow(
            /is not a numeral/,
        )
    })

    it('agrees with number on every one of them', () => {
        for (const text of ['', ' ', '0x10', '0b11', 'Infinity', 'NaN', 'abc']) {
            expect(() => number.unsafeDecode({ N: text })).toThrow()
            expect(() => literal(0, 1, 2).unsafeDecode({ N: text })).toThrow()
        }
    })

    /** The forms DynamoDB does accept still read, which is what keeps the store round trip. */
    it('still reads the denormalised forms the service normalises', () => {
        const status = literal(0, 1, 2)
        for (const text of ['1', '1.0', '01', '+1', '1e0']) {
            expect(status.unsafeDecode({ N: text })).toBe(1)
        }
    })

    /**
     * `number` needs a second gate on the round-tripped value, because
     * `Number('9.9…E+125')` rounds *up* to `1e126`. A literal does not: the rounded value is
     * outside `D`, and `ℓ ⊆ D`, so membership refuses it. This is the subsumption argument that
     * *is* sound — it is about a value landing in a set fixed at construction, not about an
     * attribute — and it is pinned here rather than believed.
     */
    it('needs no second gate, because the rounded value cannot be in the set', () => {
        const past = '9.9999999999999999999999999999999999999E+125'
        expect(Number(past)).toBe(1e126)
        expect(() => literal(1e125).unsafeDecode({ N: past })).toThrow(
            /is not one of/,
        )
        expect(() => number.unsafeDecode({ N: past })).toThrow()
    })
})
