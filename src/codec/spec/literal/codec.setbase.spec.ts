/**
 * A set is a capability of the base its members sit at, and of everything that reduces to one.
 *
 * `string.set()`, `number.set()`, `decimal.set()` and `binary.set()` are the four sets DynamoDB
 * has, spelled where the base is. `boolean` has no `.set`, because there is no `BOOLS`.
 *
 * **Both numeric forms are first-class.** `number.set()` is what a caller who means their
 * platform's numbers means; `decimal.set()` is the host-independent one. They write the same member,
 * `NS`, and hold different things: each is the set of its own adapter, and the adapter is what
 * tells them apart. Neither is a legacy encoding path.
 *
 * ── the free `set(...)` is gone, and the branding objection was answered rather than overruled ──
 *
 * This file used to argue that `set(...)` had to stay, because `.set(...)` takes **values** and a
 * list of values cannot brand anything: `set(amount)` with `amount = refine(decimal, isAmount)`
 * decodes to `ReadonlySet<Price>` and no arrangement of `decimal.set(...)` reaches `Price`.
 *
 * The premise was right and the conclusion was wrong. The brand rides on `amount`, so the
 * capability belongs on `amount` — `amount.set()`, which is `ReadonlySet<Price>` for exactly the
 * reason the old argument gave. {@link SetCapable} is the type and the element check of `.set()` is
 * the runtime one; a set of a refinement is the set of that refinement, with the predicate at the
 * element. So the general form did not need to be free-standing, and the free
 * `set(...)` is no longer exported: `.set()` is the whole surface, and the builder is internal.
 */
import { describe, expect, it } from 'vitest'
import type { BS, NS, SS } from '../../attribute'
import {
    array,
    binary,
    boolean,
    CodecError,
    decimal,
    held,
    number,
    object,
    refine,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import { checkRoundTrip } from '../../testing'

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
    /**
     * One combinator, reached from four places. The definition records the element's *term*, and
     * it is the public base's own term — not a copy of it — which is what makes two spellings of
     * the same set compare equal and a schema pin stable.
     *
     * **Pins a fact no law has, deliberately.** Identity of the recorded element is not something
     * §2 or §6 asks for — two codecs that behave alike satisfy every law here whether or not their
     * definitions are the same object. It is asserted because `toEqual` on `def` is what schema
     * comparison rests on, and a copy would pass every behavioural test and break that. It stays.
     *
     * **`toEqual` alone stopped pinning it when the element became a term, so `toBe` says it.**
     * The element used to be a codec, whose members are functions, and `toEqual` compares a
     * function by reference — so a copied element failed the shape assertion for free. A term is
     * plain data, and a copy of `{ kind: 'string' }` is `toEqual` to the original. The identity
     * claim is the one this test is for, so it is now asserted rather than obtained as a
     * side effect of comparing closures.
     */
    it('records the element term itself as the set element', () => {
        expect(string.set().def).toEqual({
            kind: 'set',
            elem: { kind: 'string' },
        })
        expect((string.set().def as { elem: unknown }).elem).toBe(string.def)
        expect(binary.set().def).toEqual({
            kind: 'set',
            elem: { kind: 'binary' },
        })
        // `number` and `decimal` are adapters over the one numeric base, so each set holds the
        // adapter as its element and the conversion rides there
        for (const [one, element] of [
            [number.set(), number],
            [decimal.set(), decimal],
        ] as const) {
            expect(one.def.kind).toBe('set')
            expect((one.def as { elem: unknown }).elem).toBe(element.def)
        }
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
 * The model spells a set of a refinement as the set of that refinement: the predicate sits at the
 * element. A set-level refinement would be the other spelling, and in TypeScript that lift is not available *at the type*: a
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

    /**
     * The capability propagates through any number of refinements and through a literal, because
     * each rides at the element. So a set whose members are checked twice, by the literal and by the predicate, is one `.set()`
     * call, where before it needed the free builder and a codec argument.
     */
    it('propagates through a refinement of a literal', () => {
        const first = refine(
            string('a', 'b'),
            (value): value is 'a' => value === 'a',
            { describe: 'the a tag' },
        )
        const tags = first.set()
        expect(tags.unsafeEncode(new Set(['a']))).toEqual({ SS: ['a'] })
        // refused by the predicate, which the literal alone would have allowed
        expect(tags.decode({ SS: ['b'] })).toBeInstanceOf(CodecError)
        // and by the literal, which the predicate alone would not have seen
        expect(tags.decode({ SS: ['z'] })).toBeInstanceOf(CodecError)
    })

    /**
     * The same rule on the write side, which the test above states only for the accepted value.
     *
     * A set over a restricted element runs the element's codec on every member, so both
     * restrictions have to run on every member and neither may be dropped. Only the read side was
     * asserted, and the two halves are one pair, so a spelling that keeps one and loses the other is
     * a codec that writes what it cannot read back.
     */
    it('encodes a set only where every member is in the literal and passes the predicate', () => {
        const first = refine(
            string('a', 'b'),
            (value): value is 'a' => value === 'a',
            { describe: 'the a tag' },
        )
        const tags = first.set()
        expect(tags.encode(new Set(['a'] as const))).toEqual({ SS: ['a'] })
        // in the literal, refused by the predicate
        expect(tags.encode(new Set(['b'] as never))).toBeInstanceOf(CodecError)
        // passes nothing: outside the literal, and outside the predicate with it
        expect(tags.encode(new Set(['z'] as never))).toBeInstanceOf(CodecError)
        // one bad member refuses the whole set, which is what `each` says
        expect(tags.encode(new Set(['a', 'b'] as never))).toBeInstanceOf(
            CodecError,
        )
    })
})

/**
 * **What a set's element may be: the DynamoDB set rule, and one host refusal.**
 *
 * A stored set holds elements of one member of `S`, `N` or `B`. That is the store universe's rule,
 * the model's `SetElem` obligation, and it is the whole of the element check: the lift of a lawful
 * element is lawful whatever the element is. The host adds one refusal, a `withLegacyRead`
 * element, because the model states no set of an older reader.
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
     * **An adapter is taken, and it used to be refused.** The refusal was guarding a real defect:
     * `held` writes where its inner term does, so the member said `S` and the conversion then ran
     * per member of an attribute storing no such thing.
     *
     * Mapping the conversion over the wire set is what fixes that, and it is the set-level
     * spelling the refusal said did not exist. It is needed either way now, because `decimal.set()`
     * is a set of an adapter.
     *
     * `withLegacyRead` is still refused and is still one the type cannot catch: it writes `S`, so
     * `SetCapable`'s gate — which sees the attribute and never the base — hands it a `.set()`.
     * Closing that in the type needs a codec type generic in its definition, measured at 481 of
     * 968 signatures and rejected, so the runtime refusal stays for it.
     */
    it('takes an adapter, mapping the conversion over the wire set', () => {
        const asArray = held(string, array(string), {
            encode: (value: readonly string[]) => value.join(','),
            decode: (stored: string) => stored.split(','),
        })
        const adapted = refine(asArray, isTexts)
        expect(
            adapted.set().unsafeEncode(new Set([['a', 'b'], ['c']])),
        ).toEqual({ SS: ['a,b', 'c'] })
        expect([...adapted.set().unsafeDecode({ SS: ['a,b', 'c'] })]).toEqual([
            ['a', 'b'],
            ['c'],
        ])
    })

    /**
     * **The DynamoDB set rule is the whole of the element check.** A stored set holds elements of
     * one member of `S`, `N` or `B`, so any element that writes one such member is taken: a union
     * of non-literal string options is one, and the set of it round-trips.
     */
    it('takes any element that writes one member of S, N or B, a union of string options included', () => {
        const short = refine(
            string,
            (value: string): value is string => value.length < 3,
            { describe: 'short' },
        )
        const shouting = refine(
            string,
            (value: string): value is string =>
                value.length >= 3 && value === value.toUpperCase(),
            { describe: 'long and upper case' },
        )
        const words = refine(union([short, shouting]), isText).set()
        const value = new Set(['ab', 'XYZ'])
        expect(words.unsafeEncode(value)).toEqual({ SS: ['XYZ', 'ab'] })
        expect(words.unsafeDecode(words.unsafeEncode(value))).toEqual(value)
    })

    it('refuses a read widening, because the model states no set of an older reader', () => {
        const widened = withLegacyRead({ current: string, older: decimal })
        expect(() => refine(widened, isText).set()).toThrow(CodecError)
    })
})
