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
import type { N, NS, S, SS } from '../../attribute'
import {
    CodecError,
    discriminatedUnion,
    number,
    object,
    string,
    union,
    valueKinds,
} from '../../codec'
import { accepts, readsBack } from '../../denote'
import { checkRoundTrip } from '../../testing'

/** The shape these are usually written in. */
const Status = { DRAFT: 0, LISTED: 1, SOLD: 2 } as const
type Status = (typeof Status)[keyof typeof Status]

const status = number(...(Object.values(Status) as Status[]))

describe('a numeric literal', () => {
    it('is stored as N', () => {
        expect(status.unsafeEncode(1)).toEqual({ N: '1' })
    })

    it('is held as the number, not as its digits', () => {
        const back: Status = status.unsafeDecode({ N: '2' })
        expect(back).toBe(2)
        expect(typeof back).toBe('number')
    })

    it('types the attribute as N, and a string literal as S', () => {
        const numeric: N = status.unsafeEncode(0)
        const text: S = string('DRAFT').unsafeEncode('DRAFT')
        expect([numeric, text]).toHaveLength(2)
    })

    it('checks the admissible set in both directions', () => {
        expect(readsBack(status, { N: '1' })).toBe(true)
        expect(readsBack(status, { N: '7' })).toBe(false)
        expect(() => status.unsafeDecode({ N: '7' })).toThrow(CodecError)
        expect(() => status.unsafeEncode(7 as Status)).toThrow(CodecError)
    })

    it('refuses the digits stored as text', () => {
        // (W) is the content: `1` is admissible and `⟨S, '1'⟩` is not the attribute it is
        // admissible *at*, so the member decides this before the set is consulted
        expect(readsBack(status, { N: '1' })).toBe(true)
        expect(readsBack(status, { S: '1' })).toBe(false)
        expect(() => status.unsafeDecode({ S: '1' })).toThrow(CodecError)
    })

    it('keeps the constant brand for a single value', () => {
        const draft = number(0)
        // the brand is type-level, and the annotation is the assertion; `constantOf` is what reads
        // the value back at runtime, and is what a key component is built from
        type Only = typeof draft.constant
        const _narrowed: 0 = null as unknown as Only
        void _narrowed
        // and two admissible values decide nothing, which is the point of `constantOf`
    })

    it('takes a number, which is what a union filters on', () => {
        expect(valueKinds(status.def)).toEqual(['number'])
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
        object({ kind: number(0), draftedAt: string }),
        object({ kind: number(1), listedAt: string }),
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
        // the two tags the declaration names do resolve, and nothing else does — which is the
        // lookup being a lookup rather than an attempt
        expect(
            Rows.item.unsafeDecode({ kind: { N: '0' }, draftedAt: { S: 'x' } }),
        ).toEqual({ kind: 0, draftedAt: 'x' })
        expect(
            Rows.item.unsafeDecode({ kind: { N: '1' }, listedAt: { S: 'x' } }),
        ).toEqual({ kind: 1, listedAt: 'x' })
        expect(() =>
            Rows.item.unsafeDecode({ kind: { N: '9' }, draftedAt: { S: 'x' } }),
        ).toThrow(CodecError)
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
    const tags = string.set('a', 'b', 'c')
    const codes = number.set(1, 2, 3, 4)

    it('writes SS for text and NS for digits', () => {
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

    /**
     * **Pins wording no law has, deliberately.** That a set reports *which element* failed is the
     * claim — the position in the path, not the refusal — so `at [0]` is the subject rather than a
     * stand-in for it. Every other refusal in this file asserts `CodecError` and the admission;
     * these two stay.
     */
    it('checks each member, naming where it failed', () => {
        // the element is a union of numeric literals, so the element's own refusal names them
        expect(() => codes.unsafeDecode({ NS: ['9'] })).toThrow(
            /at \[0\]: no option admits this attribute; options are dynamoNumber\(1\) \| dynamoNumber\(2\) \| dynamoNumber\(3\) \| dynamoNumber\(4\)/,
        )
        expect(() => tags.unsafeDecode({ SS: ['z'] })).toThrow(
            /at \[0\]: no option admits this attribute; options are string\('a'\) \| string\('b'\) \| string\('c'\)/,
        )
    })

    /**
     * `NS` is sorted as text, so `10` precedes `2` in the table — and a set is unordered, so the law
     * holds anyway. This is the case that would break if a set were an array.
     */
    it('round-trips digits that do not sort numerically', () => {
        const codec = number.set(1, 2, 10)
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
     * And a union of two such sets is allowed, which used to be the interesting part.
     *
     * Both options are given a `Set`, so the kind cannot choose between them — but a literal element
     * *refuses* a value that is not its own, so the resolver can. This was the contrast:
     * `union(string.set(), number.set())` was refused because "those elements check nothing".
     *
     * They check now, so the contrast is gone and the plain pair resolves too. What is left worth
     * pinning here is that a **literal** element narrows further than its base — `string.set('a','b')`
     * refuses `'c'`, which `string.set()` admits — so the two are still not the same codec.
     */
    it('and a union of two literal sets resolves, narrowing further than its base', () => {
        const either = union([string.set('a', 'b'), number.set(1, 2)])
        expect(either.unsafeEncode(new Set<'a' | 'b'>(['a']))).toEqual({
            SS: ['a'],
        })
        expect(either.unsafeEncode(new Set<1 | 2>([2]))).toEqual({ NS: ['2'] })
        expect(either.unsafeDecode({ NS: ['1'] })).toEqual(new Set([1]))

        // the literal is the narrowing: a value outside `ℓ` is admitted by neither option
        expect(accepts(either, new Set(['a']))).toBe(true)
        expect(accepts(either, new Set(['c']))).toBe(false)
        expect(() => either.unsafeEncode(new Set(['c']) as never)).toThrow(
            CodecError,
        )

        // and the plain pair, which this test used to contrast against, is allowed now
        expect(() => union([string.set(), number.set()])).not.toThrow()
    })
})

describe('what mixing kinds would ask for', () => {
    /**
     * The message changed when `literal(...)` was removed, and the new one is better.
     *
     * The guessing constructor picked a base from the first value and then reported the *mixing*
     * — "a literal is stored as 'S' or as 'N' and cannot be both" — because the mixing was what a
     * caller of *that* constructor got wrong. `string('A', 0)` has already named the base, so what
     * is wrong is one value, and naming it is what the caller needs.
     *
     * **Pins wording no law has, deliberately.** The whole subject of this describe is which of two
     * messages a caller meets, so the regex is the claim and not a stand-in for a refusal.
     */
    it('is refused, because one codec writes one member', () => {
        const _wrong = () =>
            // @ts-expect-error `string(...)` admits strings, and 0 is not one
            string('A', 0)
        expect(_wrong).toThrow(
            /`string\(\.\.\.\)` admits string values, and 0 is not one/,
        )
    })

    it('though a union of the two is fine, since the kinds differ', () => {
        const either = union([string('A'), number(0)])
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
        expect(() => string()).toThrow(CodecError)
    })

    /** And the honest caller the type could not be tightened for is still honest. */
    it('still takes a spread of values the type cannot see as a tuple', () => {
        const values: string[] = ['A', 'B']
        const either = string(...values)
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
        expect(() => number(NaN)).toThrow(CodecError)
        expect(() => number(1e400)).toThrow(CodecError)
        expect(() => number(-1e400)).toThrow(CodecError)
    })

    /**
     * **Pins wording no law has, deliberately**, and these two are named for it: that the refusal
     * says *which* value is outside `D`, and says all of them rather than the first. The premise is
     * `ℓ ⊆ D` and the refusal above asserts it; what these add is the diagnostic, so they stay.
     */
    it('refuses one bad value among good ones, and names it', () => {
        expect(() => number(0, 1, NaN)).toThrow(/NaN is not a number/)
    })

    /** **Pins wording no law has, deliberately** — the same reason as the test above it. */
    it('names all of them when several are outside', () => {
        expect(() => number(NaN, 1e400)).toThrow(
            /NaN, Infinity are not numbers/,
        )
    })

    /** The magnitude range is DynamoDB's, not JavaScript's — `1e200` is a fine double. */
    it('refuses a magnitude past what an N holds', () => {
        expect(() => number(1e200)).toThrow(CodecError)
        expect(() => number(1e-200)).toThrow(CodecError)
    })

    /**
     * `5e-324` is the specification's own example of the precondition going unchecked — "the
     * implementation writes whatever `String` produces, so `5e-324` is written and the service
     * rejects it on arrival". Both terms that write an `N` from a double now refuse it here,
     * which is where it is still local.
     */
    it('refuses the denormal the specification named as the unchecked case', () => {
        expect(() => number(5e-324)).toThrow(CodecError)
        expect(accepts(number, 5e-324)).toBe(false)
        expect(() => number.unsafeEncode(5e-324)).toThrow(CodecError)
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
     * number(0, 1, 2).decode({ N: '' })      → 0
     * number(0, 16).decode({ N: '0x10' })    → 16
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
        const status = number(0, 1, 2)
        for (const text of ['', ' ', '\n', '0b11', '0o7', '1_0']) {
            // not admitted at all, which is the §1 claim — `Number` would have made a value of
            // each of these and membership would then have let some through
            expect(readsBack(status, { N: text })).toBe(false)
            expect(() => status.unsafeDecode({ N: text })).toThrow(CodecError)
        }
        expect(readsBack(number(0, 16), { N: '0x10' })).toBe(false)
        expect(() => number(0, 16).unsafeDecode({ N: '0x10' })).toThrow(
            CodecError,
        )
    })

    it('agrees with number on every one of them', () => {
        for (const text of [
            '',
            ' ',
            '0x10',
            '0b11',
            'Infinity',
            'NaN',
            'abc',
        ]) {
            expect(() => number.unsafeDecode({ N: text })).toThrow()
            expect(() => number(0, 1, 2).unsafeDecode({ N: text })).toThrow()
        }
    })

    /**
     * DynamoDB accepts `'1.0'`, `'01'`, `'+1'` and `'1e0'`, and returns `'1'` for each. A read of
     * such a numeral holds `1` and writes `'1'`, so the value read would not write back to the
     * attribute read. The store returns the stored form only, so the read refuses the other forms.
     */
    it('a numeric read refuses a numeral that the store would not return, so every read writes back', () => {
        const status = number(0, 1, 2)
        expect(status.unsafeDecode({ N: '1' })).toBe(1)
        expect(status.unsafeEncode(1)).toEqual({ N: '1' })
        for (const text of ['1.0', '01', '+1', '1e0']) {
            expect(readsBack(status, { N: text })).toBe(false)
            // one alternative carries the reason; more than one report that no option admits it
            expect(() => number(1).unsafeDecode({ N: text })).toThrow(
                "the store returns '1' for this numeral, so the value read would not write back",
            )
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
        // `9.9999999999999999999999999999999999999E+125`, in the form the store returns
        const past = `${'9'.repeat(38)}${'0'.repeat(88)}`
        expect(Number(past)).toBe(1e126)
        // refused by `ℓ` and not by a second gate: the rounded value is outside a set fixed at
        // construction, so membership is what declines it
        expect(readsBack(number(1e125), { N: `1${'0'.repeat(125)}` })).toBe(
            true,
        )
        expect(readsBack(number(1e125), { N: past })).toBe(false)
        expect(() => number(1e125).unsafeDecode({ N: past })).toThrow(
            CodecError,
        )
        expect(() => number.unsafeDecode({ N: past })).toThrow()
    })
})
