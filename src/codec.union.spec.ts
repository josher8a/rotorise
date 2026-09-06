/**
 * Untagged unions: the shape `tagged` cannot express, because it has nothing to switch on.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from './attribute'
import type { AnyCodec, UnionCodec } from './codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    nullValue,
    number,
    object,
    opaque,
    optional,
    string,
    union,
} from './codec'
import { accepts } from './denote'
import { checkRoundTrip, roundTrip } from './testing'

type LineItem =
    | {
          readonly gift?: boolean
          readonly petId: string
          readonly sellerId: string
          readonly price: string
      }
    | { readonly petIds: readonly string[] }

const Leg = union([
    object({
        gift: optional(boolean),
        petId: string,
        sellerId: string,
        price: decimal,
    }),
    object({ petIds: array(string) }),
]).item

const single: LineItem = {
    petId: 'o1',
    sellerId: 'mm1',
    price: '10',
}
const many: LineItem = { petIds: ['o1', 'o2'] }

describe('untagged', () => {
    it('chooses the only variant that admits the attributes', () => {
        expect(Leg.unsafeEncode(single)).toEqual({
            petId: { S: 'o1' },
            sellerId: { S: 'mm1' },
            price: { N: '10' },
        })
        expect(Leg.unsafeEncode(many)).toEqual({
            petIds: { L: [{ S: 'o1' }, { S: 'o2' }] },
        })
    })

    it('decode ∘ encode = id, in both directions of the union', () => {
        expect(Leg.unsafeDecode(Leg.unsafeEncode(single))).toEqual(single)
        expect(Leg.unsafeDecode(Leg.unsafeEncode(many))).toEqual(many)
    })

    it('holds when an optional attribute is present', () => {
        const withFlag: LineItem = { ...single, gift: true }
        expect(Leg.unsafeDecode(Leg.unsafeEncode(withFlag))).toEqual(withFlag)
    })

    it('is order-independent: no declaration order is consulted', () => {
        const reversed = union([
            object({ petIds: array(string) }),
            object({
                gift: optional(boolean),
                petId: string,
                sellerId: string,
                price: decimal,
            }),
        ]).item
        expect(reversed.unsafeEncode(single)).toEqual(Leg.unsafeEncode(single))
        expect(reversed.unsafeDecode(reversed.unsafeEncode(many))).toEqual(many)
    })

    it('refuses an item no option admits', () => {
        // the two shapes the declaration names do resolve, and an item outside both does not —
        // which is admission deciding it, not a message
        expect(Leg.unsafeDecode(Leg.unsafeEncode(single))).toEqual(single)
        expect(Leg.unsafeDecode(Leg.unsafeEncode(many))).toEqual(many)
        expect(() => Leg.unsafeDecode({ somethingElse: { S: 'x' } })).toThrow(
            CodecError,
        )
        // a partial of the first variant is not that variant
        const { sellerId: _gone, ...partial } = Leg.unsafeEncode(single)
        expect(() => Leg.unsafeDecode(partial as AttributeMap)).toThrow(
            CodecError,
        )
    })

    it('rejects variants that cannot be told apart, at the declaration', () => {
        // `{ a }` is admitted by both, so nothing can tell them apart
        union(
            // @ts-expect-error the declaration itself is rejected
            [object({ a: string, b: optional(string) }), object({ a: string })],
        )
    })

    /**
     * **A one-sided check on a two-sided condition, and the union it let through.**
     *
     * The construction guard compared `carries` — value kinds — and nothing compared `writes`. So
     * `union([decimal, number])` was accepted: `decimal` takes a string, `number` takes a number,
     * no shared kind. Both store `'N'`.
     *
     * It built, it encoded, and it could never read back what it had written:
     *
     * ```
     * union([decimal, number]).encode('1.5')   → { N: '1.5' }
     * union([decimal, number]).decode({ N: '1.5' })
     *   → 'decimal and number both admit this attribute'
     * ```
     *
     * A row a union writes and no reader of that union can resolve is strictly worse than a
     * declaration that is refused, and this was invisible only because the *mirror* — the two
     * options swapped for two that share a value kind — is refused by the loop one line above.
     * That asymmetry is the whole tell: an ambiguity check on a pair has a write side and a read
     * side, and only one of them was written.
     *
     * **This rejects a union that built yesterday.** Deliberately, and there is no version of it
     * that keeps working: nothing about `{ N: '1.5' }` says whether it was written as a decimal or
     * as a host number.
     */
    it('rejects two options that store the same member, which no read can resolve', () => {
        // the behavioural claim is about which *declarations* stand: two options sharing a member
        // with neither checking what it reads is refused, and a pair separable by member is not
        expect(() => union([decimal, number])).toThrow(CodecError)
        expect(() => union([string, number])).not.toThrow()
        // and the mirror it was hiding behind, which was refused all along — twice over, since two
        // options reading back as the same type is also `ValidateOptions`. `union([decimal,
        // number])` passes *that* check too: they read back as `string` and `number`
        expect(() =>
            // @ts-expect-error both read back as a string, which the type refuses as well
            union([string, decimal]),
        ).toThrow(CodecError)
    })

    /**
     * The exemptions are the read side's too, and they are the ones the write side already had: an
     * object option is chosen by its names, and a literal knows which values are its own. So the two
     * numeric literals below share `'N'` and are still perfectly resolvable.
     */
    it('keeps the two exemptions the write side has', () => {
        const either = union([number(0, 1), decimal('2', '3')])
        expect(either.unsafeDecode({ N: '2' })).toBe('2')
        expect(either.unsafeDecode({ N: '1' })).toBe(1)
        // two object options both store `M`, and the names are what choose
        expect(() =>
            union([object({ a: string }), object({ b: string })]),
        ).not.toThrow()
    })

    it('still refuses ambiguity at runtime, as a backstop', () => {
        type Overlapping = { a: string; b?: string } | { a: string }
        // declared through a cast, as a caller bypassing the compile-time check would. The options
        // are still codecs — what is bypassed is `ValidateVariants`, which is the check being tested
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => UnionCodec<Overlapping, readonly AnyCodec[]>
        const Ambiguous = declare([
            object({ a: string, b: optional(string) }),
            object({ a: string }),
        ]).item

        // what makes it ambiguous is that *both* options admit the entity, and that is the
        // assertion the message was standing in for — (U) fails at this input
        expect(
            accepts(object({ a: string, b: optional(string) }), { a: '1' }),
        ).toBe(true)
        expect(accepts(object({ a: string }), { a: '1' })).toBe(true)
        expect(() => Ambiguous.unsafeEncode({ a: '1' })).toThrow(CodecError)
        // and the unambiguous case still works
        expect(Ambiguous.unsafeEncode({ a: '1', b: '2' })).toEqual({
            a: { S: '1' },
            b: { S: '2' },
        })
    })

    it('nests, like the discriminated form', () => {
        // the same declaration, read as one attribute rather than as a whole item
        const nested = union([
            object({ petId: string, sellerId: string, price: decimal }),
            object({ petIds: array(string) }),
        ])
        expect(nested.unsafeEncode(many)).toEqual({
            M: { petIds: { L: [{ S: 'o1' }, { S: 'o2' }] } },
        })
    })

    it('exposes a chosen variant as a plain item codec', () => {
        expect(Leg.variant(1).field('petIds').unsafeEncode(['x'])).toEqual({
            L: [{ S: 'x' }],
        })
    })

    it('round-trips through the shared helper', () => {
        expect(roundTrip(Leg as never, many)).toEqual(many)
    })
})

describe('the law, over generated values', () => {
    it('decode ∘ encode = id for Leg', () => {
        checkRoundTrip(Leg, { count: 300, seed: 20260826 })
    })
})

/**
 * The `NULL` point as an option.
 *
 * The gap this closed was found by asking whether `nullable(c)` could be written as
 * `union(c, nullValue)`. It could not, because the right-hand side was not a term: the value
 * language had `null` and the attribute domain had `NULL`, and no codec denoted either. So a schema
 * could say "this attribute is a string" or "this attribute is optional", and could not say "this
 * attribute is exactly `NULL`" — a tombstone, or a payload-free option of a union.
 *
 * The union resolves by member, which is why it needs no discrimination: `NULL` is a member no
 * other ground codec writes.
 */
describe('the NULL point', () => {
    it('writes and reads the one value it holds', () => {
        expect(nullValue.unsafeEncode(null)).toEqual({ NULL: true })
        expect(nullValue.unsafeDecode({ NULL: true })).toBeNull()
    })

    it('holds nothing else', () => {
        expect(() => nullValue.unsafeDecode({ S: 'x' })).toThrow(CodecError)
    })

    it('is a tombstone beside a real value, resolved by member alone', () => {
        const Deleted = union([string, nullValue])
        expect(Deleted.unsafeEncode('alive')).toEqual({ S: 'alive' })
        expect(Deleted.unsafeEncode(null)).toEqual({ NULL: true })
        expect(Deleted.unsafeDecode({ NULL: true })).toBeNull()
        expect(Deleted.unsafeDecode({ S: 'alive' })).toBe('alive')
    })

    it('round-trips as an option, over generated values', () => {
        const Pet = object({
            id: string,
            deletedAt: union([string, nullValue]),
        }).item
        checkRoundTrip(Pet, { count: 100, seed: 20260829 })
    })

    /** Distinct from `nullable`, which *adds* `null` to another codec's held set. */
    it('is not `nullable`, which holds its subject too', () => {
        expect(() => nullValue.unsafeEncode('x' as never)).toThrow(CodecError)
    })
})

describe('the declaration guard, where a term is what the guard reads', () => {
    /**
     * Two literal sets with disjoint alphabets are separable, and the declaration must stand.
     *
     * The model's warrant is `Exactness.lean`'s `SepJV` over
     * `refine (set string) (liftQ (inL string …))` at two disjoint alphabets: a set of a
     * restriction *is* a restriction of the set, which `setCodec_restrict` and
     * `setCodec_restrict_p` prove on both halves of the pair. So the pair separates, and refusing
     * it would refuse a union the model proves works.
     *
     * **Today it stands for the weaker reason**, and that is what this test is pinning against.
     * `Term.set` is indexed by a bare `SetBase`, so a set over a literal has no term at all, and
     * the guard answers on `undefined` — not certified rather than refused. The pass that respells
     * `.set()` over a restricted ground as `refine(set(b), liftQ q)` gives it a term, and then
     * `identifies` has to see the literal *through* the refinement or this test goes red. That is
     * the pin that pass must keep.
     */
    it('declares a union of two literal sets whose alphabets do not meet', () => {
        expect(() =>
            union([string.set('a', 'b'), string.set('c')]),
        ).not.toThrow()
        const either = union([string.set('a', 'b'), string.set('c')])
        expect(either.unsafeEncode(new Set(['a']) as never)).toEqual({
            SS: ['a'],
        })
    })

    /**
     * **An option no value can select is not an option.**
     *
     * `opaque` admits every value every other option admits, and §5's `select` acts only where
     * *exactly one* option does. So `union([opaque, X])` is not `opaque` with `X` beside it: it is
     * **undefined** wherever `X` admits, and `opaque` everywhere else. `X` is declared and can
     * never be chosen, which is §5's failure rather than a precedence question — there is no rank
     * that resolves it, because ranking would be choosing an option the model says is not chosen.
     *
     * The guard used to exempt an `opaque` option instead of comparing it, reading its occupancy
     * as `⊤`. §5 separates the two things a `⊤` covers, and `opaque` is the *everything* one: the
     * model states it as a closed form, so it is comparable and it meets every option. Refusing
     * these is JH's ruling, recorded in `ARCHITECTURE.md` §10, and it moved the corpus's refusal
     * set from 17 pairs to 32 with every new theorem holding.
     */
    it('refuses a union where one option can never be selected', () => {
        // @ts-expect-error `ValidateOptions` refuses this pair at the type level already, and has
        // since before this rule: `opaque` reads back as `unknown`, which absorbs `string`, so the
        // two "read back as the same type". This asserts the *runtime* half, which is what a
        // caller reaches past that type — a cast, or plain JavaScript.
        expect(() => union([opaque, string])).toThrow(CodecError)
        // the message names the option that swallows the other, because that is the one to remove,
        // and it names it as the caller wrote it rather than as the term spells it
        // @ts-expect-error the same type-level refusal
        expect(() => union([opaque, string])).toThrow(/opaque/)
        // both policies: `lossy` admits a number too, so it swallows strictly more
        // @ts-expect-error the same type-level refusal
        expect(() => union([opaque('lossy'), string])).toThrow(CodecError)
        // @ts-expect-error and the order of the options does not matter
        expect(() => union([string, opaque])).toThrow(CodecError)

        // and the refusal is about being unselectable, not about `opaque` being unusable
        expect(() => opaque.encode('a')).not.toThrow()
        expect(() => union([string, boolean])).not.toThrow()
    })
})
