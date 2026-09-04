/**
 * A set is a capability of the base its members sit at, and of everything that reduces to one.
 *
 * `string.set()`, `number.set()`, `decimal.set()` and `binary.set()` are the four sets DynamoDB
 * has, spelled where the base is. `boolean` has no `.set`, because there is no `BOOLS`.
 *
 * **Both numeric forms are first-class.** `number.set()` is what a caller who means their
 * platform's numbers means; `decimal.set()` is the host-independent one. They write the same member
 * — `NS` — and hold different things, which is exactly why `formal/Calculus/Domain.lean` indexes a
 * set by a *base* rather than by a `Member`: `Member` cannot tell them apart and the index can.
 * Neither is a legacy path.
 *
 * ── the free `set(...)` is gone, and the branding objection was answered rather than overruled ──
 *
 * This file used to argue that `set(...)` had to stay, because `.set(...)` takes **values** and a
 * list of values cannot brand anything: `set(amount)` with `amount = refine(decimal, isAmount)`
 * decodes to `ReadonlySet<Price>` and no arrangement of `decimal.set(...)` reaches `Price`.
 *
 * The premise was right and the conclusion was wrong. The brand rides on `amount`, so the
 * capability belongs on `amount` — `amount.set()`, which is `ReadonlySet<Price>` for exactly the
 * reason the old argument gave. {@link SetCapable} is the type and {@link setBase} is the runtime
 * reduction; a set of a refinement of a literal of a base is still a set of that base, which is
 * `setCodec_restrict`. So the general form did not need to be free-standing, and the free
 * `set(...)` is no longer exported: `.set()` is the whole surface, and the builder is internal.
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
/** Trivial predicates, used only to reach the refusals across a refinement. @see codec.set.spec */
const isText = (value: unknown): value is string => typeof value === 'string'
const isTexts = (value: unknown): value is readonly string[] =>
    Array.isArray(value)

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

    /**
     * One combinator, reached from four places. The definition records the *element codec*, and it
     * is the public base itself — not a copy of it — which is what makes two spellings of the same
     * set compare equal and a schema pin stable.
     *
     * **Pins a fact no law has, deliberately.** Identity of the recorded element is not something
     * §2 or §6 asks for — two codecs that behave alike satisfy every law here whether or not their
     * definitions are the same object. It is asserted because `toEqual` on `def` is what schema
     * comparison rests on, and a copy would pass every behavioural test and break that. It stays.
     */
    it('records the base itself as its element', () => {
        expect(string.set().def).toEqual({ kind: 'set', element: string })
        expect(number.set().def).toEqual({ kind: 'set', element: number })
        expect(decimal.set().def).toEqual({ kind: 'set', element: decimal })
        expect(binary.set().def).toEqual({ kind: 'set', element: binary })
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
        expect(() => tags.unsafeDecode({ SS: ['z'] })).toThrow(CodecError)
    })

    it('reaches the numeric set the old surface could not narrow losslessly', () => {
        const codes = decimal.set('1', '2', '10')
        const value = new Set(['10', '2'] as const)
        expect(codes.unsafeEncode(value)).toEqual({ NS: ['10', '2'] })
        expect(codes.unsafeDecode(codes.unsafeEncode(value))).toEqual(value)
        expect(() => codes.unsafeDecode({ NS: ['9'] })).toThrow(CodecError)
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
 * The model recovers a set of a refinement exactly, by lifting the element predicate to a
 * set-level one — `setCodec_restrict`. In TypeScript that lift is not available *at the type*: a
 * set-level refinement of `ReadonlySet<string>` gives back `ReadonlySet<string>`, and the brand is
 * gone. So the only spelling that preserves it is the one whose element is a *codec*.
 *
 * `amount.set()` is that spelling. What would have lost the brand is a surface where the only set
 * of a decimal was `decimal.set(...values)`: not a compile error, but a quietly wider type —
 * `Price` becoming `string`, and every place downstream that required a checked amount accepting an
 * unchecked one. Propagating the capability is what avoids that without a free function.
 */
describe('branding survives, and it survives through the capability', () => {
    const Pet = object({ id: string, amounts: amount.set() }).item

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
        ).toThrow(CodecError)
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
        expect(writes(amount.set())).toBe('NS')
    })

    /**
     * The capability propagates as far as {@link setBase} reduces, which is through any number of
     * refinements and through a literal — the two the model keeps under `setCodec_restrict`. So a
     * set whose members are checked twice, by the literal and by the predicate, is one `.set()`
     * call, where before it needed the free builder and a codec argument.
     */
    it('propagates through a refinement of a literal', () => {
        const first = refine(
            string('a', 'b'),
            (value): value is 'a' => value === 'a',
            { describe: 'the a tag' },
        )
        expect(setBase(first)).toBe('string')
        const tags = first.set()
        expect(writes(tags)).toBe('SS')
        expect(tags.unsafeEncode(new Set(['a']))).toEqual({ SS: ['a'] })
        // refused by the predicate, which the literal alone would have allowed
        expect(tags.decode({ SS: ['b'] })).toBeInstanceOf(CodecError)
        // and by the literal, which the predicate alone would not have seen
        expect(tags.decode({ SS: ['z'] })).toBeInstanceOf(CodecError)
    })
})

/**
 * **What a set's element may be, tightened to match the model.**
 *
 * §3 `(set)`'s premise used to be `setMember μ = some μS`, read off an arbitrary element term, and
 * `setMember` is partial — so the constructor accepted elements the rule then refused.
 * `formal/Calculus/Term.lean:60` replaced the element term with a `SetBase` index, making the
 * refusal a type error, and states what that gives up: a set of a `held` and of a `legacy`.
 *
 * This library had the same hole and it was reachable. `writes` reads *through* an adapter — `held`
 * writes where its inner term does — so a set of `held(string, …)` was accepted, and its two
 * functions then ran once per member of an attribute whose stored form records no adapter at all.
 * The refusal now lives beside the member check, which is where the other half of the premise
 * already was.
 */
describe('what a set cannot be built from', () => {
    it('still refuses an element that writes no single member', () => {
        const either = refine(
            union([string, number]),
            (value): value is string | number => value !== null,
        )
        // @ts-expect-error a union writes no single member, so the type declines it too
        expect(() => either.set()).toThrow(CodecError)
    })

    /**
     * **The two the type cannot catch.** `held` and `legacy` both write `S`, so `SetCapable`'s gate
     * — which sees the attribute and never the base — hands them a `.set()`. That is the gap the
     * runtime refusal exists to close, and the reason it must stay: closing it in the type needs a
     * codec type generic in its definition, measured at 481 of 968 signatures and rejected.
     */
    it('refuses an adapter, which reads through to a member it does not store', () => {
        const asArray = held(string, {
            encode: (value: readonly string[]) => value.join(','),
            decode: (stored: string) => stored.split(','),
        })
        expect(writes(asArray)).toBe('S')
        expect(setBase(asArray)).toBeUndefined()
        // no `@ts-expect-error`: `held` writes `S`, so this type-checks and throws
        const adapted = refine(asArray, isTexts)
        expect(() => adapted.set()).toThrow(CodecError)
        expect(() => adapted.set()).toThrow(CodecError)
    })

    it('refuses a read widening, for the same reason', () => {
        const widened = legacy({ current: string, older: decimal })
        expect(setBase(widened)).toBeUndefined()
        expect(() => refine(widened, isText).set()).toThrow(CodecError)
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
