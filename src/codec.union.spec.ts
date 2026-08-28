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
    object,
    optional,
    string,
    union,
} from './codec'
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
        expect(() => Leg.unsafeDecode({ somethingElse: { S: 'x' } })).toThrow(
            /no option admits this item with attributes 'somethingElse'/,
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

        expect(() => Ambiguous.unsafeEncode({ a: '1' })).toThrow(
            /\{ a, b\? \} and \{ a \} both admit this entity with attributes 'a'; these options cannot be told apart/,
        )
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
