/**
 * Untagged unions: the shape `tagged` cannot express, because it has nothing to switch on.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from '../../attribute'
import type { AnyCodec, UnionCodec } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    never,
    nullValue,
    number,
    object,
    opaque,
    optional,
    string,
    union,
} from '../../codec'
import { accepts } from '../../denote'
import { failed } from '../../result'
import { checkRoundTrip, roundTrip } from '../../testing'

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
        // `{ a }` is admitted by both, so nothing can tell them apart — and the two levels now
        // answer one rule, so the declaration is refused by the type and by the constructor
        expect(() =>
            union(
                // @ts-expect-error the declaration itself is rejected
                [
                    object({ a: string, b: optional(string) }),
                    object({ a: string }),
                ],
            ),
        ).toThrow(CodecError)
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

    it('refuses a caller who bypasses the compile-time check, at construction', () => {
        type Overlapping = { a: string; b?: string } | { a: string }
        // declared through a cast, as a caller bypassing the compile-time check would. The options
        // are still codecs — what is bypassed is `ValidateVariants`, which is the check being tested
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => UnionCodec<Overlapping, readonly AnyCodec[]>

        // what makes it ambiguous is that *both* options admit the entity — (U) fails at this input
        expect(
            accepts(object({ a: string, b: optional(string) }), { a: '1' }),
        ).toBe(true)
        expect(accepts(object({ a: string }), { a: '1' })).toBe(true)

        // the constructor answers the same structural question the type does, so the refusal
        // arrives at the declaration rather than on the first item that collides
        expect(() =>
            declare([
                object({ a: string, b: optional(string) }),
                object({ a: string }),
            ]),
        ).toThrow(CodecError)
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
     * The model's warrant is `Separation.lean`'s `SepJV` over
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
     * these is JH's ruling, landed in `ff75c6b`, and it moved the corpus's refusal
     * set from 17 pairs to 32 with every new theorem holding.
     */
    it('refuses a union where one option can never be selected', () => {
        // @ts-expect-error the type refuses this pair too, and now **for the right reason**: the
        // clause naming `opaque` fires ahead of the read-back one, so a caller is told to remove
        // the option rather than to add a discriminator that cannot help.
        // `Rotorise.attest.test.ts` pins the message. This asserts the *runtime* half, which is
        // what a caller reaches past the type — a cast, or plain JavaScript.
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

    /**
     * **The same rule, two widths narrower**, and it is the rule rather than a second exemption:
     * an option whose admitted values are all admitted by another can never be selected. `opaque`
     * is the widest instance, where "another" is every option. These two are the narrowest, where
     * one option is a *restriction of the thing it restricts*: a literal against its own base's
     * ground term, and a set of a literal against the plain set at that base.
     *
     * **The type level already refused both**, and with the discriminator advice, which is the
     * advice that cannot help. So what moves here is the runtime, which used to accept them
     * through the `identifies` exemption, and the message, which now names the option to remove.
     * A typed caller cannot have shipped one of these; what reaches the runtime is a cast, plain
     * JavaScript, or an erased path.
     *
     * JH ruled it, on the ground that it is `opaque`'s failure at a narrower width. The corpus's
     * refusal set moved from 32 to 36 and `Orth` declines all four, `not_orth_literal_string` on
     * purpose.
     */
    it('refuses an option that is a restriction of another option', () => {
        // @ts-expect-error the type refuses this pair too, and `Rotorise.attest.test.ts` pins the
        // message; this asserts the runtime half, which is what a cast reaches past
        expect(() => union([string, string('A')])).toThrow(CodecError)
        // @ts-expect-error the same refusal, and the order of the options does not matter
        expect(() => union([string('A'), string])).toThrow(CodecError)
        // the message names the narrower option first, because that is the one to remove
        // @ts-expect-error the same type-level refusal
        expect(() => union([string, string('A')])).toThrow(
            /admits only values that/,
        )
        // …and it says the thing a discriminator cannot be the answer to
        // @ts-expect-error the same type-level refusal
        expect(() => union([string, string('A')])).toThrow(
            /a discriminator does not fix this/,
        )
        // a set of a literal is a restriction of the plain set at its base, one spelling out
        // @ts-expect-error the same type-level refusal
        expect(() => union([string.set(), string.set('a', 'b')])).toThrow(
            CodecError,
        )

        // **and two restrictions of one base still declare**, which is the shape this is not
        // about: neither literal contains the other, and `Orth` certifies the pair since `OrthL`
        expect(() => union([string('A'), string('B')])).not.toThrow()
        expect(() => union([string('A'), number])).not.toThrow()
        expect(() =>
            union([string.set('a', 'b'), string.set('c')]),
        ).not.toThrow()
    })
})

/**
 * **An object option is admitted by its structure, not by its names alone.**
 *
 * Pass 7. Admission used to read the name set and stop, so two options declaring one name set were
 * ambiguous whatever their fields said, and a discriminator was the only way to tell them apart.
 * It now reads the name set *and* every literal field the value carries — the model's `keysOk` and
 * `literalsOk` — so a required literal with disjoint alternatives resolves the pair, at the
 * declaration and at the item.
 */
describe('an object option is admitted by its structure', () => {
    it('resolves two options with one name set whose required literals differ', () => {
        // no cast: the declaration itself now stands, which is half the rule
        const Kinded = union([
            object({ kind: string('a'), x: string }),
            object({ kind: string('b'), x: number }),
        ]).item

        expect(Kinded.unsafeEncode({ kind: 'a', x: '1' })).toEqual({
            kind: { S: 'a' },
            x: { S: '1' },
        })
        expect(Kinded.unsafeEncode({ kind: 'b', x: 1 })).toEqual({
            kind: { S: 'b' },
            x: { N: '1' },
        })
        // and both branches read back, which is the half `namesFit` alone could not reach: the
        // stored side asks each literal's own codec to decode the attribute it carries
        expect(
            Kinded.unsafeDecode({ kind: { S: 'a' }, x: { S: '1' } }),
        ).toEqual({ kind: 'a', x: '1' })
        expect(
            Kinded.unsafeDecode({ kind: { S: 'b' }, x: { N: '1' } }),
        ).toEqual({ kind: 'b', x: 1 })
    })

    it('still reports ambiguity where one name set carries no literal difference', () => {
        type Kinded =
            | { readonly kind: 'a'; readonly x: string }
            | { readonly kind: string; readonly x: string }
        /** Declared through a cast: the type refuses the pair for the same reason. */
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => UnionCodec<Kinded, readonly AnyCodec[]>

        // `string` admits `'a'`, so the two literals are not disjoint and no value chooses between
        // them — a literal field is not a discriminator merely by being a literal on one side
        expect(() =>
            declare([
                object({ kind: string('a'), x: string }),
                object({ kind: string, x: string }),
            ]),
        ).toThrow(CodecError)
    })

    it('reports the admitted option error when the structure fits one option and a value is wrong', () => {
        const Sum = union([
            object({ kind: string('a'), x: string }),
            object({ petIds: array(string) }),
        ]).item

        // the structure fits the first option and nothing else, so that option is the one chosen,
        // and what it says about its own field is what the caller is told
        expect(Sum.unsafeEncode({ kind: 'a', x: '1' })).toEqual({
            kind: { S: 'a' },
            x: { S: '1' },
        })
        expect(() => Sum.unsafeEncode({ kind: 'a', x: 1 } as never)).toThrow(
            CodecError,
        )
        expect(() =>
            Sum.unsafeEncode({ kind: 'a', x: 1 } as never),
        ).not.toThrow(/no option admits/)
    })

    it('admits no option where the literal itself is wrong, which is not that option error', () => {
        const Sum = union([
            object({ kind: string('a'), x: string }),
            object({ petIds: array(string) }),
        ]).item

        // `kind: 'b'` is outside the first option's literal, so the first option is not admitted
        // rather than admitted-and-failing — the difference structural admission makes
        expect(() => Sum.unsafeEncode({ kind: 'b', x: '1' } as never)).toThrow(
            /no option admits/,
        )
    })

    /**
     * **A union reads an object option as closed, and the option's term is what has to say so.**
     *
     * An undeclared name fails `namesFit` and so reaches no option's own `decode`: inside a union
     * a `drop` option already refuses what `drop` would skip. `Calculus.unionOk` asks every object
     * option for `refuse`, and until the builder wrote it the four object unions in the corpus
     * carried a `rest` that named the wrong policy and certified nothing.
     */
    it('states the closure a union reads its object options with', () => {
        const codec = union([object({ a: string }), object({ b: number })])
        const def = codec.def
        expect(
            def.kind === 'union' &&
                def.options.map(
                    (option) => option.kind === 'object' && option.body.rest,
                ),
        ).toEqual(['refuse', 'refuse'])
        // and what the union writes and reads is what it wrote and read before
        expect(codec.unsafeDecode(codec.unsafeEncode({ a: 'x' }))).toEqual({
            a: 'x',
        })
        expect(codec.unsafeDecode(codec.unsafeEncode({ b: 1 }))).toEqual({
            b: 1,
        })
    })

    /**
     * **The copy belongs to the union.** A codec is a value a caller keeps and passes to more than
     * one union, so the closure a union needs is written on that union's own option and nowhere
     * else. The same codec used alone still drops what it does not declare.
     */
    it('leaves the option codec the caller declared alone', () => {
        const option = object({ a: string })
        union([option, object({ b: number })])
        const def = option.def
        expect(def.kind === 'object' && def.body.rest).toBe('refuse')
    })
})

/**
 * **`never`: the term that admits no value.**
 *
 * `Term.never` on both sides. The model types it — `Typed.never` gives it `HNever`, which is
 * `False` — and denotes it as `Codec.empty`. A constructor rather than a `discriminatedUnion` over
 * no options: an empty option list is a term a caller can build by accident, and a rule reading it
 * as the bottom reads that accident as intent.
 */
describe('never', () => {
    it('admits no value, in either direction', () => {
        expect(failed(never.encode({} as never))).toBe(true)
        expect(failed(never.encode('x' as never))).toBe(true)
        expect(failed(never.encode(undefined as never))).toBe(true)
        expect(failed(never.decode({ S: 'x' }))).toBe(true)
        expect(failed(never.decode({ M: { a: { S: 'x' } } }))).toBe(true)
        expect(failed(never.decode({ NULL: true }))).toBe(true)
    })

    /** The refusal is a value in both directions, which is the rule every other codec follows. */
    it('reports a refusal as a value and never as a throw', () => {
        expect(() => never.encode({} as never)).not.toThrow()
        expect(() => never.encode(undefined as never)).not.toThrow()
        expect(() => never.decode({ S: 'x' })).not.toThrow()
    })

    /**
     * **`opaque`'s rule at the opposite width.** `opaque` admits every value, so every other
     * option is inside it. `never` admits none, so it is inside every other option, and §5's
     * `select` acts nowhere on it. The message is the same one, and it names the option to remove.
     */
    it('can never be an option of a union', () => {
        // @ts-expect-error the type refuses the pair; this asserts the runtime half
        expect(() => union([string, never])).toThrow(CodecError)
        // @ts-expect-error the order of the options does not matter
        expect(() => union([never, string])).toThrow(CodecError)
        // @ts-expect-error the same type-level refusal
        expect(() => union([string, never])).toThrow(/admits only values that/)
        // @ts-expect-error the same type-level refusal
        expect(() => union([string, never])).toThrow(
            /a discriminator does not fix this/,
        )
    })

    /**
     * **An object option is no exception**, and it is the one pair that made the order matter.
     *
     * `separable` exempts an object option, because a union admits an object by its names. That
     * exemption used to be asked before containment, so an object beside `never` was certified
     * separable and the refusal was never reached — the type refused the pair and the runtime
     * declared it. Containment is asked first now, and no other object pair changes answer: the
     * three {@link restricts} rows name a literal, a set of a literal and `never`.
     */
    it('can never be an option beside an object either', () => {
        // @ts-expect-error the type refuses the pair; this asserts the runtime half
        expect(() => union([object({ a: string }), never])).toThrow(CodecError)
        // @ts-expect-error the same type-level refusal
        expect(() => union([object({ a: string }), never])).toThrow(
            /admits only values that/,
        )
        // and the exemption itself still stands for a pair of objects, which names decide
        expect(() =>
            union([object({ a: string }), object({ b: string })]),
        ).not.toThrow()
    })

    /** `discriminatedUnion` over no options stays refused: an empty list is a mistake, not a term. */
    it('is the only name that reaches the term', () => {
        expect(() =>
            // @ts-expect-error the empty option list is refused by the type as well
            discriminatedUnion('kind', []),
        ).toThrow(CodecError)
    })
})
