/**
 * A set is a capability of the base its members sit at — and `set(...)` is still the general one.
 *
 * `string.set()`, `number.set()`, `decimal.set()` and `binary.set()` are the four sets DynamoDB has,
 * spelled where the base is. `boolean` has no `.set`, because there is no `BOOLS`.
 *
 * **Both numeric forms are first-class.** `number.set()` is what a caller who means their platform's
 * numbers means; `decimal.set()` is the host-independent one. They write the same member — `NS` —
 * and hold different things, which is exactly why `formal/Calculus/Domain.lean:602` indexes a set by
 * a *base* rather than by a `Member`: `Member` cannot tell them apart and the index can. Neither is
 * a legacy path.
 *
 * ── what `.set()` cannot say, and why `set(...)` stays ──────────────────────────────────────────
 *
 * `.set(...)` takes **values**. `set(...)` takes a **codec**. That is not a stylistic difference: a
 * codec can be branded, and a list of values cannot brand anything. `set(amount)` where
 * `amount = refine(decimal, isAmount)` decodes to `ReadonlySet<Price>`; there is no arrangement of
 * `decimal.set(...)` that reaches `Price`, because the brand lives on the element codec and the new
 * spelling never sees one. So `set(...)` is **not deprecated** — deprecating it would silently widen
 * every branded set in every caller's schema to `ReadonlySet<string>`, which is a regression the
 * type checker would not report. `.set()` is sugar over `set(...)`, and the general form is the one
 * that keeps the brand.
 */
import { describe, expect, it } from 'vitest'
import type { BS, NS, SS } from './attribute'
import {
    binary,
    boolean,
    CodecError,
    decimal,
    held,
    legacy,
    number,
    object,
    refine,
    set,
    setBase,
    string,
    union,
    writes,
} from './codec'
import { checkRoundTrip } from './testing'

declare const brand: unique symbol
type Price = string & { [brand]: 'amount' }
const isAmount = (value: string): value is Price =>
    value.length > 0 && Number.isFinite(Number(value)) && Number(value) >= 0
const amount = refine(decimal, isAmount, {
    describe: 'a non-negative amount',
    arbitrary: (rng) =>
        (['0', '1', '2.5', '100'] as Price[])[Math.floor(rng() * 4)] as Price,
})

describe('a set at each base', () => {
    it('is the set that base stores', () => {
        expect(writes(string.set())).toBe('SS')
        expect(writes(number.set())).toBe('NS')
        expect(writes(decimal.set())).toBe('NS')
        expect(writes(binary.set())).toBe('BS')
    })

    it('is the same codec `set(...)` builds', () => {
        expect(string.set().def).toEqual(set(string).def)
        expect(number.set().def).toEqual(set(number).def)
        expect(decimal.set().def).toEqual(set(decimal).def)
        expect(binary.set().def).toEqual(set(binary).def)
    })

    it('encodes and decodes at the type the base holds', () => {
        const text: SS = string.set().unsafeEncode(new Set(['b', 'a']))
        expect(text).toEqual({ SS: ['a', 'b'] })
        const digits: NS = number.set().unsafeEncode(new Set([2, 1]))
        expect(digits).toEqual({ NS: ['1', '2'] })
        const exact: NS = decimal.set().unsafeEncode(new Set(['1', '2.5']))
        expect(exact).toEqual({ NS: ['1', '2.5'] })
        const bytes: BS = binary
            .set()
            .unsafeEncode(new Set([Uint8Array.from([1])]))
        expect(Object.keys(bytes)).toEqual(['BS'])
    })

    /**
     * The two numeric sets write one member and hold two different things, which is the whole
     * argument for indexing by base. A `NS` alone does not say which read it back.
     */
    it('distinguishes the two numeric sets, which the member cannot', () => {
        expect(writes(number.set())).toBe(writes(decimal.set()))
        expect(setBase(number)).toBe('number')
        expect(setBase(decimal)).toBe('decimal')

        const wide = '123456789012345678901234567890'
        expect([...decimal.set().unsafeDecode({ NS: [wide] })]).toEqual([wide])
        // the same attribute through the host, which is what `number.set()` is for and is lossy
        expect([...number.set().unsafeDecode({ NS: ['1'] })]).toEqual([1])
    })

    /** There is no `BOOLS`, so the capability is absent rather than throwing. */
    it('gives no set to the one base that has none', () => {
        expect('set' in boolean).toBe(false)
    })
})

describe('a set of a literal, spelled at the base', () => {
    it('checks each member against the values the base was given', () => {
        const tags = string.set('a', 'b', 'c')
        expect(writes(tags)).toBe('SS')
        expect(tags.unsafeEncode(new Set(['c', 'a']))).toEqual({
            SS: ['a', 'c'],
        })
        expect(() => tags.unsafeDecode({ SS: ['z'] })).toThrow(
            /at \[0\]: 'z' is not one of 'a', 'b', 'c'/,
        )
    })

    it('reaches the numeric set the old surface could not narrow losslessly', () => {
        const codes = decimal.set('1', '2', '10')
        const value = new Set(['10', '2'] as const)
        expect(codes.unsafeEncode(value)).toEqual({ NS: ['10', '2'] })
        expect(codes.unsafeDecode(codes.unsafeEncode(value))).toEqual(value)
        expect(() => codes.unsafeDecode({ NS: ['9'] })).toThrow(
            /'9' is not one of/,
        )
    })

    it('round-trips over generated values', () => {
        checkRoundTrip(
            object({
                tags: string.set('a', 'b'),
                codes: number.set(1, 2, 10),
            }).item,
            { count: 100, seed: 20260901 },
        )
    })
})

/**
 * **The branding verdict, pinned rather than asserted in prose.**
 *
 * The model recovers `set(refine(base, q))` exactly, by lifting the element predicate to a set-level
 * one — `setCodec_restrict`. In TypeScript that lift is not available *at the type*: a set-level
 * refinement of `ReadonlySet<string>` gives back `ReadonlySet<string>`, and the brand is gone. So
 * the only spelling that preserves it is the one that takes the element codec, and that spelling is
 * `set(...)`.
 *
 * This is what would have been lost had `set(...)` been deprecated in favour of `.set(...)`: not a
 * compile error, but a quietly wider type. `Price` would have become `string` and every place
 * downstream that required a checked amount would have accepted an unchecked one.
 */
describe('branding survives, and only through `set(...)`', () => {
    const Pet = object({ id: string, amounts: set(amount) }).item

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

    /**
     * And the base-named spelling of the same attribute is the *unbranded* one. Both are correct
     * codecs; they are not interchangeable, and the difference is invisible at runtime — which is
     * why it is worth a test rather than a comment.
     */
    it('is exactly what `decimal.set()` does not give', () => {
        const plain: ReadonlySet<string> = decimal
            .set()
            .unsafeDecode({ NS: ['1'] })
        expect([...plain]).toEqual(['1'])
        // @ts-expect-error `decimal.set()` holds strings; the brand is not recoverable from values
        const _widened: ReadonlySet<Price> = plain
    })

    it('reads the base through the refinement, which is what makes the lift sound', () => {
        expect(setBase(amount)).toBe('decimal')
        expect(writes(set(amount))).toBe('NS')
    })
})

/**
 * **What a set's element may be, tightened to match the model.**
 *
 * §3 `(set)`'s premise used to be `setMember μ = some μS`, read off an arbitrary element term, and
 * `setMember` is partial — so the constructor accepted elements the rule then refused.
 * `formal/Calculus/Term.lean:60` replaced the element term with a `SetBase` index, making the
 * refusal a type error, and states what that gives up: `set(held …)` and `set(legacy …)`.
 *
 * This library had the same hole and it was reachable. `writes` reads *through* an adapter — `held`
 * writes where its inner term does — so `set(held(string, …))` was accepted, and the adapter's two
 * functions then ran once per member of an attribute whose stored form records no adapter at all.
 * The refusal now lives beside the member check, which is where the other half of the premise
 * already was.
 */
describe('what a set cannot be built from', () => {
    it('still refuses an element that writes no single member', () => {
        expect(() => set(union([string, number]))).toThrow(
            /a set holds strings, numbers or binary/,
        )
    })

    it('refuses an adapter, which reads through to a member it does not store', () => {
        const asArray = held(string, {
            encode: (value: readonly string[]) => value.join(','),
            decode: (stored: string) => stored.split(','),
        })
        expect(writes(asArray)).toBe('S')
        expect(setBase(asArray)).toBeUndefined()
        expect(() => set(asArray)).toThrow(CodecError)
        expect(() => set(asArray)).toThrow(/must be one of the four bases/)
    })

    it('refuses a read widening, for the same reason', () => {
        const widened = legacy({ current: string, older: decimal })
        expect(setBase(widened)).toBeUndefined()
        expect(() => set(widened)).toThrow(/must be one of the four bases/)
    })

    /**
     * And the two the model keeps are kept: a `refine` and a literal are *restrictions* of a base,
     * so the set of one is the restriction of the base's set. That is `setCodec_restrict`, and it
     * is why {@link setBase} reads through exactly those two and nothing else.
     */
    it('accepts the two that are restrictions of a base', () => {
        expect(setBase(amount)).toBe('decimal')
        expect(setBase(string('a', 'b'))).toBe('string')
        expect(setBase(refine(amount, isAmount, { describe: 'twice' }))).toBe(
            'decimal',
        )
        // a literal at `boolean` is a fine literal and still has no set
        expect(setBase(boolean(true))).toBeUndefined()
    })
})
