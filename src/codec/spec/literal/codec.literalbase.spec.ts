/**
 * A literal is a capability of the primitive that names its base — not a constructor that guesses.
 *
 * `literal(...)` — now removed — inferred its carrier from the JS type of its arguments, and
 * `src/codec/codec.ts` said so in its own words: *"A literal is the one ground term whose member follows
 * from its **values** rather than from its name."* That was the single exception to how every other
 * term in this library works, and it is retired here. `string('A')`, `number(1)`, `decimal('1')`, `boolean(true)` and
 * `binary(bytes)` each name the ground term they narrow, so the base is data and not an inference.
 *
 * **What the guess could not reach, and this can.** Three things, and one of them is the reason:
 *
 * 1. `decimal('1')` — *stored as `N`, exactly this text*. The guess gave an `S` for `literal('1')`
 *    and went through the host's `number` for `literal(1)`, so a lossless numeric literal was not
 *    expressible at all. It
 *    is the counterexample that retires the rule outright: text that stores an `N`.
 * 2. `boolean(true)` — a literal at `BOOL`, which no spelling reached.
 * 3. `binary(bytes)` — a literal at `B`, compared by bytes rather than by reference.
 *
 * The term records the base (`Literal['base']`) rather than leaving `member` and
 * `carries` to recover it, because at `decimal` there is nothing to recover it *from*: the values are
 * strings and the member is `N`, and no reading of either says so.
 */
import { describe, expect, it } from 'vitest'
import type { B, BOOL, N, S } from '../../attribute'
import {
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    failed,
    number,
    object,
    string,
    union,
    valueKinds,
} from '../../codec'
import { readsBack } from '../../denote'
import { checkRoundTrip } from '../../testing'

describe('the base is named, not inferred', () => {
    it('writes each base into the member that base stores', () => {
        expect(string('A').unsafeEncode('A')).toEqual({ S: 'A' })
        expect(number(1).unsafeEncode(1)).toEqual({ N: '1' })
        expect(decimal('1').unsafeEncode('1')).toEqual({ N: '1' })
        expect(boolean(true).unsafeEncode(true)).toEqual({ BOOL: true })
        expect(
            binary(Uint8Array.from([1, 2])).unsafeEncode(
                Uint8Array.from([1, 2]),
            ),
        ).toEqual({ B: Uint8Array.from([1, 2]) })
    })

    it('types the attribute at each base', () => {
        const text: S = string('A').unsafeEncode('A')
        const digits: N = number(1).unsafeEncode(1)
        const exact: N = decimal('1').unsafeEncode('1')
        const flag: BOOL = boolean(true).unsafeEncode(true)
        const bytes: B = binary(Uint8Array.from([7])).unsafeEncode(
            Uint8Array.from([7]),
        )
        expect([text, digits, exact, flag, bytes]).toHaveLength(5)
    })

    /** The primitive is still the primitive: calling it is what narrows. */
    it('leaves the uncalled codec exactly what it was', () => {
        expect(string.unsafeEncode('anything')).toEqual({ S: 'anything' })
        expect(decimal.unsafeEncode('1.5')).toEqual({ N: '1.5' })
        expect(number.unsafeDecode({ N: '3' })).toBe(3)
    })
})

/**
 * `decimal('1')` is the point of the change, so its two halves are pinned separately.
 *
 * The held value is the **text**, not a number — that is the whole difference from `number(1)`,
 * which is the same attribute reached through a double. And the admissible set is checked against
 * the form DynamoDB *returns*, not merely the form it accepts: `decimal`'s read side is the identity
 * on the digits, so an alternative like `'1.50'` would be one this codec could write and could never
 * read back as the string it was given.
 */
describe('a decimal literal', () => {
    it('holds the text and stores the digits', () => {
        const one = decimal('1')
        const back: string = one.unsafeDecode({ N: '1' })
        expect(back).toBe('1')
        expect(typeof back).toBe('string')
    })

    it('is exact where a numeric literal is not', () => {
        const wide = '123456789012345678901234567890'
        expect(decimal(wide).unsafeDecode({ N: wide })).toBe(wide)
        // the same value through the host: a double cannot hold it, so `number` never had it to lose
        expect(String(Number(wide))).not.toBe(wide)
    })

    it('checks the admissible set in both directions', () => {
        const one = decimal('1', '2')
        // the law is that `'3'` is not admitted; the sentence saying so is not the law
        expect(readsBack(one, { N: '3' })).toBe(false)
        expect(readsBack(one, { N: '1' })).toBe(true)
        expect(() => one.unsafeDecode({ N: '3' })).toThrow(CodecError)
        // @ts-expect-error the held type is the alternatives, so this is refused before it runs
        expect(() => one.unsafeEncode('3')).toThrow(CodecError)
    })

    /**
     * The read gate is bare `decimal`'s, and it is not subsumed by membership: `'1.0'` is a numeral
     * the service accepts and never returns, and membership would have rejected it for the wrong
     * reason — or accepted it, had `'1.0'` been the alternative named.
     */
    it('reads through the same gate bare `decimal` does', () => {
        // refused by the *gate* and not by membership, which is the distinction the sentence
        // carried: `'1'` is the one alternative and is admitted, `'1.0'` names the same number
        // and is not, so what refuses it is §1's stored form rather than `ℓ`
        expect(readsBack(decimal('1'), { N: '1' })).toBe(true)
        expect(readsBack(decimal('1'), { N: '1.0' })).toBe(false)
        expect(readsBack(decimal('1'), { N: '0x1' })).toBe(false)
        expect(() => decimal('1').unsafeDecode({ N: '1.0' })).toThrow(
            CodecError,
        )
        expect(() => decimal('1').unsafeDecode({ N: '0x1' })).toThrow(
            CodecError,
        )
    })

    /** `ℓ ⊆ D`, at the narrower `D` this base has. */
    it('refuses an alternative the service would normalise away', () => {
        expect(() => decimal('1.50')).toThrow(CodecError)
        expect(() => decimal('007')).toThrow(CodecError)
        expect(() => decimal('1e5')).toThrow(CodecError)
        expect(() => decimal('1', 'x')).toThrow(CodecError)
    })

    it('round-trips', () => {
        checkRoundTrip(object({ price: decimal('1', '2.5', '100') }).item, {
            count: 100,
            seed: 20260901,
        })
    })
})

describe('the two bases that were unreachable', () => {
    it('holds a boolean literal, which the guessing form had no spelling for', () => {
        const yes = boolean(true)
        expect(valueKinds(yes.def)).toEqual(['boolean'])
        expect(yes.unsafeDecode({ BOOL: true })).toBe(true)
        expect(readsBack(yes, { BOOL: false })).toBe(false)
        expect(() => yes.unsafeDecode({ BOOL: false })).toThrow(CodecError)
    })

    /**
     * Binary compares **by bytes**. Reference equality would make the codec useless — the array a
     * schema names is never the array that came off the wire — and it would make `decode` answer
     * with a value the type says is one of `ℓ` and `===` says is not. So `decode` answers with the
     * member of `ℓ`, which is what keeps a decoded literal identical to the declared one.
     */
    it('compares a binary literal by its octets, and answers with the declared array', () => {
        const magic = Uint8Array.from([0x89, 0x50])
        const png = binary(magic)
        expect(png.unsafeDecode({ B: Uint8Array.from([0x89, 0x50]) })).toBe(
            magic,
        )
        expect(() =>
            png.unsafeDecode({ B: Uint8Array.from([0x89, 0x51]) }),
        ).toThrow(CodecError)
    })
})

describe('what each base refuses', () => {
    it('refuses no alternatives at all, naming the constructor that named none', () => {
        expect(() => string()).toThrow(CodecError)
        expect(() => number()).toThrow(CodecError)
        expect(() => decimal()).toThrow(CodecError)
        expect(() => boolean()).toThrow(CodecError)
        expect(() => binary()).toThrow(CodecError)
    })

    /**
     * Homogeneity is free in the model — `NEFinset k.Carrier` — and is not free here, because a
     * spread of a plain array (`string(...Object.values(Status))`) defeats any tuple-shaped
     * signature. So it is a construction-time refusal, at the base the caller named.
     */
    it('refuses a value that is not of the base it was handed to', () => {
        expect(() => string('A', 1 as unknown as string)).toThrow(CodecError)
        expect(() => number(1, 'A' as unknown as number)).toThrow(CodecError)
    })

    /** `ℓ ⊆ D` at `number`, which is where the old `literal` had the defect. */
    it('still refuses a numeric alternative outside what an N holds', () => {
        expect(() => number(Number.NaN)).toThrow(CodecError)
        expect(() => number(1e200)).toThrow(CodecError)
    })
})

/**
 * Two literals at different bases are a union that resolves, and the interesting pair is the one
 * the old surface could not build: `number(1)` and `decimal('1')` write the *same member* and take
 * different kinds of value, so `carries` separates them where `member` cannot.
 */
describe('bases as union options', () => {
    it('resolves a numeric literal against a decimal one by what each takes', () => {
        const either = union([number(1), decimal('2.5')])
        expect(either.unsafeEncode(1)).toEqual({ N: '1' })
        expect(either.unsafeEncode('2.5')).toEqual({ N: '2.5' })
    })

    it('reads a decimal tag, because a tag is carried as S or N', () => {
        const Rows = discriminatedUnion('v', [
            object({ v: decimal('1'), a: string }),
            object({ v: decimal('2'), b: string }),
        ])
        expect(
            Rows.item.unsafeDecode({ v: { N: '2' }, b: { S: 'x' } }),
        ).toEqual({ v: '2', b: 'x' })
    })

    /**
     * And the two bases that cannot be tags are refused at the declaration. `readTag` accepts `S`
     * or `N` and nothing else, so a literal at `BOOL` or `B` names no variant a lookup could reach
     * — which used to be discovered at decode time as "must be carried as 'S' or 'N'", one item at
     * a time, rather than when the union was built.
     */
    it('refuses a discriminator at a base no tag is carried in', () => {
        const options = [
            object({ v: boolean(true), a: string }),
            object({ v: boolean(false), b: string }),
        ] as const
        // the type refuses it too — `EveryOptionTagged` reads the discriminator's definition — so
        // the runtime refusal is what a cast one line away would otherwise walk straight past
        // @ts-expect-error a `BOOL` names no tag a lookup could find
        expect(() => discriminatedUnion('v', options)).toThrow(CodecError)
    })
})

/**
 * **`literal(...)` is gone, and what stands in its place is pinned here.**
 *
 * The deprecated constructor guessed its base from the JS type of its arguments and was, at the two
 * bases it could reach, behaviourally identical to the base-named forms — `literal('A','B').def`
 * deep-equalled `string('A','B').def`, which this file used to assert. It is removed rather than
 * left deprecated, because it was the library's one term whose member followed from its values, and
 * a surface that keeps a retired exception around keeps having to explain it.
 *
 * **Pins wording no law has, deliberately.** The two messages are the subject here — that a
 * caller who mixes bases is told which base and which value, rather than only that something was
 * refused. Every other refusal in this file now asserts `CodecError` and the behaviour; these two
 * stay as they are, because converting them would delete the claim.
 *
 * What is asserted now is the part a caller can still get wrong, and the two messages they meet.
 * The mixing message is the one thing the old constructor said better — it named the *mixing* —
 * and `string('A', 0)` names the base and the offending value instead, which is the more useful
 * half of it and is why nothing was kept to say the other.
 */
describe('what replaced the constructor that guessed', () => {
    it('refuses a value the base does not hold, and names it', () => {
        expect(() =>
            // @ts-expect-error `string(...)` admits strings, and 0 is not one
            string('A', 0),
        ).toThrow(/`string\(\.\.\.\)` admits string values, and 0 is not one/)
        expect(() =>
            // @ts-expect-error `number(...)` admits numbers, and 'A' is not one
            number(0, 'A'),
        ).toThrow(/`number\(\.\.\.\)` admits number values, and 'A' is not one/)
    })

    it('refuses to name nothing, at every base', () => {
        expect(() => string()).toThrow(CodecError)
        expect(() => number()).toThrow(CodecError)
        expect(() => decimal()).toThrow(CodecError)
        expect(() => boolean()).toThrow(CodecError)
        expect(() => binary()).toThrow(CodecError)
    })
})

describe("a literal's alternatives are a set", () => {
    /**
     * **Section 8 case (c): a refusal, a test that reaches it, and the reason.**
     *
     * The model's `ls` is a `NEFinset k.Carrier` and gets three guarantees from that type — the
     * base indexes the alternatives, `n ≥ 1`, and no two are equal. `term.ts`'s `Literal` buys the
     * first from a discriminated union over the base and the second from a tuple head.
     * **TypeScript cannot say the third**, so it is a refusal at construction.
     *
     * It is not tidiness. `NEFinset` is a set, so `literal(k, {'A','A'})` and `literal(k, {'A'})`
     * are one term in the model and would be two definitions here — and the second names a
     * cardinality the first does not. A repeat makes a two-value literal that admits one value,
     * and the constant would go unrecognised by everything that asks whether a literal decides.
     */
    it('refuses a repeated alternative, which the model has no way to hold', () => {
        expect(() => string('A', 'A')).toThrow(CodecError)
        expect(() => string('A', 'A')).toThrow(/positions 0 and 1/)
        // compared the way the base compares: bytes for `binary`, `===` otherwise
        expect(() =>
            binary(Uint8Array.from([1, 2]), Uint8Array.from([1, 2])),
        ).toThrow(CodecError)
        // and two that differ are fine, which is what makes the refusal about repetition
        expect(() => string('A', 'B')).not.toThrow()
        expect(() =>
            binary(Uint8Array.from([1]), Uint8Array.from([2])),
        ).not.toThrow()
    })

    /** A single alternative still decides, which is the cardinality the repeat would have hidden. */
    it('keeps a single alternative readable as the constant it is', () => {
        expect(string('ONLY').unsafeEncode('ONLY')).toEqual({ S: 'ONLY' })
    })

    /**
     * **A refusal reports a bad value; it does not throw on one.**
     *
     * The refusal path names the value it rejected, and naming a value runs the value's own
     * `toString`. `Object.create(null)` has none, so `String(value)` throws
     * `TypeError: Cannot convert object to primitive value` — and it threw from *inside* the
     * refusal, turning an expected failure into an exception at the one place whose job is to
     * describe a failure. Measured before the fix: a null-prototype value reached `string`,
     * `number`, `decimal`, `boolean`, `binary` and both literal forms, and all seven threw.
     *
     * A codec's input is typed, so such a value arrives past its type. Rule 14's line is that the
     * throw is caught where the caller's code runs and becomes a value in the code that follows.
     */
    it('refuses a value whose own rendering throws, rather than throwing with it', () => {
        const bare = Object.create(null) as never
        for (const codec of [
            string,
            number,
            decimal,
            boolean,
            binary,
            string('A'),
            number(1),
        ]) {
            expect(failed(codec.encode(bare))).toBe(true)
        }
        // and the message still names the shape, which is what it was rendering the value for
        const refused = string.encode(bare)
        expect(failed(refused) && (refused as CodecError).message).toMatch(
            /map/,
        )
    })
})
