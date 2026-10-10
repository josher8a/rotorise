/**
 * Untagged unions: the shape `tagged` cannot express, because it has nothing to switch on.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from '../../attribute'
import { DynamoNumber, MAX_DOCUMENT_NESTING } from '../../attribute'
import type { AnyCodec, UnionCodec } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    held,
    never,
    nullValue,
    number,
    object,
    opaque,
    optional,
    ref,
    refine,
    scope,
    string,
    union,
    withLegacyRead,
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

const LegCodec = union([
    object({
        gift: optional(boolean),
        petId: string,
        sellerId: string,
        price: decimal,
    }),
    object({ petIds: array(string) }),
])
const Leg = LegCodec.item

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

    it('declares variants that can hold the same attributes, and writes a shared value to one attribute whatever the order', () => {
        // `{ a }` is admitted by both, and both write it to one map, so the order is not observable
        const wide = object({ a: string, b: optional(string) })
        const narrow = object({ a: string })
        for (const options of [
            [wide, narrow],
            [narrow, wide],
        ] as const) {
            const either = union(options)
            expect(either.unsafeEncode({ a: '1' })).toEqual({
                M: { a: { S: '1' } },
            })
            expect(either.unsafeDecode({ M: { a: { S: '1' } } })).toEqual({
                a: '1',
            })
        }
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
        // and the mirror it was hiding behind, which was refused all along: `string` writes `'1'` as
        // an `S`, and `decimal` writes it as an `N`
        expect(() => union([string, decimal])).toThrow(CodecError)
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

    /**
     * The views of a union are the union of the views of its options, so an adapter below a union
     * is compared through its two sides like any other adapter.
     */
    it('accepts an object beside a union of objects that hold an adapter, where the views are apart', () => {
        const priced = union([
            object({ a: string, n: decimal }),
            object({ b: boolean, n: decimal }),
        ])
        const either = union([object({ a: string, n: boolean }), priced])
        for (const value of [
            { a: 'x', n: true },
            { a: 'x', n: '1.5' },
            { b: false, n: '2' },
        ])
            expect(either.unsafeDecode(either.unsafeEncode(value))).toEqual(
                value,
            )
        expect(either.unsafeEncode({ a: 'x', n: '1.5' })).toEqual({
            M: { a: { S: 'x' }, n: { N: '1.5' } },
        })
    })

    it('writes an attribute with the codec of the variant that the clause keeps', () => {
        const Holder = object({ leg: LegCodec }).item
        expect(
            Holder.at(
                (p) => p.leg.narrow({ petIds: array(string) }).petIds,
            ).unsafeEncode(['x']),
        ).toEqual({
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
     * The model's warrant is `Separation.lean`'s `sepJV_set_literals`: two sets of disjoint
     * literals share no set, because no stored set is empty. The meet states it: the two element
     * unions meet at the bottom, so the two sets do.
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
     * **A caller set that no stored family types still occupies a set slot.** The two options
     * below admit one caller value, `Set([true])`, and write the value to `SS` and to `NS`. The
     * model has no set of booleans, so the model drops the slot. The host holds the value, so the
     * occupancy keeps the slot, and the declaration refuses the pair.
     */
    it('refuses two sets that admit one caller set and write the set to two families', () => {
        const isTrue = (b: boolean): b is true => b === true
        const asText = held(string, boolean, {
            encode: (b) => (b ? 'y' : 'n'),
            decode: (s) => s === 'y',
        })
        const asNumber = held(dynamoNumber, boolean, {
            encode: (b) => DynamoNumber.from(b ? '1' : '0'),
            decode: (n) => String(n) === '1',
        })
        const x = refine(asText, isTrue).set()
        const y = refine(asNumber, isTrue).set()
        const one = new Set<true>([true])
        expect(x.unsafeEncode(one)).toEqual({ SS: ['y'] })
        expect(y.unsafeEncode(one)).toEqual({ NS: ['1'] })
        expect(() => union([x, y])).toThrow(CodecError)
        expect(() => union([y, x])).toThrow(CodecError)
    })

    it('dispatches a caller set that no stored family types to the set option', () => {
        const isTrue = (b: boolean): b is true => b === true
        const asText = held(string, boolean, {
            encode: (b) => (b ? 'y' : 'n'),
            decode: (s) => s === 'y',
        })
        const flags = union([refine(asText, isTrue).set(), string])
        expect(flags.unsafeEncode(new Set<true>([true]))).toEqual({ SS: ['y'] })
    })

    it('declares two sets and two lists whose element families do not meet', () => {
        expect(() => union([string.set(), dynamoNumber.set()])).not.toThrow()
        expect(() => union([array(string), array(dynamoNumber)])).not.toThrow()
    })

    /**
     * **`opaque` beside an option it contains is `opaque`.** `opaque` admits every value the other
     * option admits, and the two write each such value to one attribute, so the union writes what
     * `opaque` writes, whatever the order.
     */
    it('declares opaque beside a held-free option, and writes as opaque in either order', () => {
        for (const options of [
            [opaque, string],
            [string, opaque],
        ] as const) {
            const either = union(options)
            expect(either.unsafeEncode('a')).toEqual(opaque.unsafeEncode('a'))
            expect(either.unsafeEncode(true)).toEqual(opaque.unsafeEncode(true))
        }
        expect(() => union([opaque, dynamoNumber])).not.toThrow()
    })

    /**
     * **A `held` beside `opaque` is refused**, because the declaration cannot show that the
     * adapter writes a value where `opaque` writes it. `number` is an adapter over `dynamoNumber`,
     * and each numeric policy of `opaque` is a `held` over the canonical codec.
     */
    it('refuses an adapter beside opaque, and a numeric policy beside any option', () => {
        // declared through a cast, as a caller passing an erased list would
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => unknown
        const runtime = (options: readonly AnyCodec[]) => () => declare(options)
        for (const numeric of [number, number(1)]) {
            expect(runtime([opaque, numeric])).toThrow(
                /are not shown compatible/,
            )
        }
        for (const other of [string, string('a'), dynamoNumber]) {
            expect(runtime([opaque('refuse'), other])).toThrow(
                /are not shown compatible/,
            )
            expect(runtime([opaque('lossy'), other])).toThrow(
                /are not shown compatible/,
            )
        }
    })

    /**
     * **A closed body refuses a name it does not declare, on both sides.** The stand-in reads a
     * map without `a`, so the stand-in field alone keeps nothing apart. `priced` requires `b`,
     * and `standIn` is closed, so it neither writes nor reads a map that holds `b`. The two
     * options share no value and no attribute, and the certificate accepts the pair.
     */
    it('accepts an object with a stand-in field beside a closed object that requires another name', () => {
        const standIn = object({
            a: withLegacyRead({ current: string, whenMissing: 'stand-in' }),
        })
        const priced = object({ b: decimal })
        for (const either of [
            union([standIn, priced]),
            union([priced, standIn]),
        ]) {
            expect(either.unsafeEncode({ a: 'x' })).toEqual({
                M: { a: { S: 'x' } },
            })
            expect(either.unsafeEncode({ b: '1.5' })).toEqual({
                M: { b: { N: '1.5' } },
            })
            expect(either.unsafeDecode({ M: {} })).toEqual({ a: 'stand-in' })
            expect(either.unsafeDecode({ M: { b: { N: '1.5' } } })).toEqual({
                b: '1.5',
            })
        }
    })

    /**
     * **A restriction beside what it restricts is the wider option.** A literal inside its base,
     * and a set of a literal inside the plain set, add no value and take none away.
     */
    it('declares an option that is a restriction of another option, and writes as the wider one', () => {
        for (const options of [
            [string, string('A')],
            [string('A'), string],
        ] as const) {
            const either = union(options)
            expect(either.unsafeEncode('A')).toEqual({ S: 'A' })
            expect(either.unsafeEncode('B')).toEqual({ S: 'B' })
            expect(either.unsafeDecode({ S: 'A' })).toBe('A')
        }
        const sets = union([string.set(), string.set('a', 'b')])
        expect(sets.unsafeEncode(new Set(['a', 'z']) as never)).toEqual({
            SS: ['a', 'z'],
        })

        // and two restrictions of one base declare as before
        expect(() => union([string('A'), string('B')])).not.toThrow()
        expect(() => union([string('A'), number])).not.toThrow()
    })

    /**
     * **A refusal names each option as the caller declared it.** The caller removes an option by
     * its call, and two literal options at one form differ only in their literals.
     */
    it('names both declared options of a refused pair, literals included', () => {
        expect(() => union([decimal('1', '2'), string('1', '2')])).toThrow(
            "decimal('1', '2') and string('1', '2') are not shown compatible",
        )
    })
})

/**
 * **An object option is admitted by attempt, not by its names.**
 *
 * The union attempts each option in order. The first option whose codec encodes the value writes
 * the value, as the model's `Adm_union` and `AdmA_union` state. The names present select no option. Two
 * options with one name set resolve where no value is admitted by both, for example where a
 * required literal has disjoint alternatives. A value that no option encodes is refused, even
 * where its names fit one option.
 */
describe('an object option is admitted by attempt', () => {
    /**
     * **Two objects whose required slot meets at the bottom declare.** The two options declare
     * one name, and `string` meets `boolean` at `never`, so no value is admitted by both. The
     * value decides the option, and the names present decide nothing.
     */
    it('declares two objects that share a name and no value, and each value selects its own option', () => {
        /** Declared through a cast, which states the entity type. */
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => UnionCodec<{ readonly a: string | boolean }, readonly AnyCodec[]>
        const either = declare([object({ a: string }), object({ a: boolean })])
        const text = either.unsafeEncode({ a: 'x' })
        const flag = either.unsafeEncode({ a: true })
        expect(text).toEqual({ M: { a: { S: 'x' } } })
        expect(flag).toEqual({ M: { a: { BOOL: true } } })
        expect(either.unsafeDecode(text)).toEqual({ a: 'x' })
        expect(either.unsafeDecode(flag)).toEqual({ a: true })
    })

    /**
     * **A crossing pair declares, and the overlap is written once.** Two options cross where their
     * meet is neither `never` nor one of the two. A value in the overlap is admitted by both, and
     * both write it to one attribute, so no rule has to name an owner of the overlap.
     */
    it('declares two crossing options, and writes a value in the overlap once, whatever the order', () => {
        // both arrays hold `[]`, and `[]` is the whole overlap
        for (const options of [
            [array(string('A')), array(string('B'))],
            [array(string('B')), array(string('A'))],
        ] as const) {
            const either = union(options)
            expect(either.unsafeEncode([])).toEqual({ L: [] })
            expect(either.unsafeDecode({ L: [] })).toEqual([])
            expect(either.unsafeEncode(['A'])).toEqual({ L: [{ S: 'A' }] })
        }

        // JH's crossing pair, which overlaps at `{ a, b }`
        const first = object({ a: string }, [string, optional(dynamoNumber)])
        const second = object({ b: dynamoNumber }, [string, optional(string)])
        const both = { a: 's', b: DynamoNumber.from('1') }
        for (const options of [
            [first, second],
            [second, first],
        ] as const) {
            const either = (
                union as unknown as (
                    options: readonly AnyCodec[],
                ) => UnionCodec<Record<string, unknown>, readonly AnyCodec[]>
            )(options)
            const written = either.unsafeEncode(both)
            expect(written).toEqual({
                M: { a: { S: 's' }, b: { N: '1' } },
            })
            expect(either.unsafeDecode(written)).toEqual(both)
        }
    })

    /**
     * **A partition of two crossing objects declares, and each value selects its cell.**
     *
     * `{ a }` and `{ b }` with open blocks cross at `{ a, b }`. The partition writes the overlap as
     * its own option, and `optional(never)` excludes a name from the other two. `dynamoNumber` is
     * the numeric codec here, because `number` is a `held` adapter over it.
     */
    it('declares the partition of a crossing pair, and each value selects its cell on both sides', () => {
        const options = [
            object({ a: string, b: optional(never) }, [
                string,
                optional(dynamoNumber),
            ]),
            object({ b: dynamoNumber, a: optional(never) }, [
                string,
                optional(string),
            ]),
            object({ a: string, b: dynamoNumber }),
        ] as const
        /** Declared through a cast, which states the entity type. */
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => UnionCodec<Record<string, unknown>, readonly AnyCodec[]>
        const cells = declare(options)
        const one = DynamoNumber.from('1')
        const cases = [
            [{ a: 's' }, 0],
            [{ b: one }, 1],
            [{ a: 's', b: one }, 2],
        ] as const
        for (const [value, cell] of cases) {
            // exactly one option admits the value, and it is the expected cell
            expect(options.map((option) => accepts(option, value))).toEqual(
                options.map((_, at) => at === cell),
            )
            const written = cells.unsafeEncode(value as never)
            // exactly one option reads the attribute back, and it is the same cell
            expect(
                options.map((option) => !failed(option.decode(written))),
            ).toEqual(options.map((_, at) => at === cell))
            expect(cells.unsafeEncode(cells.unsafeDecode(written))).toEqual(
                written,
            )
        }
        // the one value the partition leaves out: `c` is an undeclared name at the overlap cell
        expect(() =>
            cells.unsafeEncode({
                a: 's',
                b: one,
                c: DynamoNumber.from('2'),
            } as never),
        ).toThrow(/no option admits/)
    })

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
        // and both branches read back: the stored side attempts each option's own decode, and the
        // literal of one option refuses the attribute that the other option wrote
        expect(
            Kinded.unsafeDecode({ kind: { S: 'a' }, x: { S: '1' } }),
        ).toEqual({ kind: 'a', x: '1' })
        expect(
            Kinded.unsafeDecode({ kind: { S: 'b' }, x: { N: '1' } }),
        ).toEqual({ kind: 'b', x: 1 })
    })

    it('declares an object option inside another, where a literal field sits inside its base', () => {
        // `string` admits `'a'`, so the first option sits inside the second, and the two write each
        // value of the first to one map
        const either = union([
            object({ kind: string('a'), x: string }),
            object({ kind: string, x: string }),
        ])
        expect(either.unsafeEncode({ kind: 'a', x: '1' })).toEqual({
            M: { kind: { S: 'a' }, x: { S: '1' } },
        })
        expect(either.unsafeEncode({ kind: 'b', x: '1' })).toEqual({
            M: { kind: { S: 'b' }, x: { S: '1' } },
        })
    })

    it('refuses a value that no option encodes, even where its names fit one option', () => {
        const Sum = union([
            object({ kind: string('a'), x: string }),
            object({ petIds: array(string) }),
        ]).item

        // the names fit the first option, and the names select nothing: the first option does not
        // encode `x: 1`, so no option admits the value
        expect(Sum.unsafeEncode({ kind: 'a', x: '1' })).toEqual({
            kind: { S: 'a' },
            x: { S: '1' },
        })
        expect(() => Sum.unsafeEncode({ kind: 'a', x: 1 } as never)).toThrow(
            /no option admits/,
        )
    })

    it('admits no option where the literal itself is wrong, which is not that option error', () => {
        const Sum = union([
            object({ kind: string('a'), x: string }),
            object({ petIds: array(string) }),
        ]).item

        // `kind: 'b'` is outside the first option's literal, so the first option does not admit
        // the value
        expect(() => Sum.unsafeEncode({ kind: 'b', x: '1' } as never)).toThrow(
            /no option admits/,
        )
    })

    /**
     * **A union reads an object option as closed, and the option's term is what has to say so.**
     *
     * An undeclared name fails the `decode` of each closed option.
     * The certificate `Calculus.certAll` asks no option for a closed body, so the term states the
     * closure that the union reads.
     */
    it('states the closure a union reads its object options with', () => {
        const codec = union([object({ a: string }), object({ b: number })])
        const def = codec.def
        expect(
            def.kind === 'union' &&
                def.options.map(
                    (option) => option.kind === 'object' && option.body.rest,
                ),
        ).toEqual([undefined, undefined])
        // and what the union writes and reads is what it wrote and read before
        expect(codec.unsafeDecode(codec.unsafeEncode({ a: 'x' }))).toEqual({
            a: 'x',
        })
        expect(codec.unsafeDecode(codec.unsafeEncode({ b: 1 }))).toEqual({
            b: 1,
        })
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
     * **`never` is the zero of `union`.** It admits no value, so it is compatible with every
     * option, and the union writes what the other option writes.
     */
    it('is the zero of a union: the union writes what the other option writes', () => {
        for (const options of [
            [string, never],
            [never, string],
        ] as const) {
            const either = union(options)
            expect(either.unsafeEncode('x')).toEqual({ S: 'x' })
            expect(either.unsafeDecode({ S: 'x' })).toBe('x')
        }
        const record = union([object({ a: string }), never])
        expect(record.unsafeEncode({ a: 'x' })).toEqual({
            M: { a: { S: 'x' } },
        })
    })

    /** `discriminatedUnion` over no options stays refused: an empty list is a mistake, not a term. */
    it('is the only name that reaches the term', () => {
        expect(() =>
            // @ts-expect-error the empty option list is refused by the type as well
            discriminatedUnion('kind', []),
        ).toThrow(CodecError)
    })
})

describe('the refusal of a union', () => {
    type Tree = readonly Tree[]
    const { Tree } = scope({ Tree: array(ref('Tree')) })

    /** `n` levels of list, the innermost one empty. */
    const nestTree = (n: number): Tree => {
        let v: Tree = []
        for (let i = 1; i < n; i++) v = [v]
        return v
    }

    /**
     * The kind of the value leaves one option, so the cause of the refusal is that option's. The
     * union keeps its own message and adds the reason, because "no option admits" alone hides the
     * bound that the write broke.
     */
    it('a union that refuses a value names the reason of the one option whose shape fits', () => {
        const Node = union([object({ a: optional(Tree) }), nullValue])
        const result = Node.encode({ a: nestTree(MAX_DOCUMENT_NESTING) })
        expect(result).toBeInstanceOf(CodecError)
        expect((result as CodecError).reason).toMatch(
            /^no option admits this value with attributes 'a'; options are .*nesting reaches 33 levels of list and map, and DynamoDB stores at most 32/,
        )
    })
})
