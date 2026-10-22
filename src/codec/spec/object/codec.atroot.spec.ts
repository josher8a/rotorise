/**
 * **`at` focuses any codec, and the item only anchors the location.** A path from a codec reaches
 * the codec that the longer path from an enclosing item reaches. The segments and the
 * preconditions are relative to the root, so the two differ by the prefix of the enclosing item.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { MAX_DOCUMENT_NESTING } from '../../attribute'
import {
    type AnyCodec,
    array,
    at,
    CodecError,
    discriminatedUnion,
    item as itemOf,
    list,
    narrow,
    number,
    object,
    opaque,
    optional,
    path,
    preconditions,
    type Segment,
    string,
    union,
} from '../../codec'
import { arbitraryOf, rngFrom, structuralEquals } from '../../testing'

const Leg = object({ id: string, deliveredAt: optional(string) })
const Pay = discriminatedUnion('tender', [
    object({ tender: string('CARD'), card: object({ last4: string }) }),
    object({ tender: string('CASH'), drawer: number }),
])
const Legs = array(Leg)
const Pair = list(Leg, Leg)
const Prices = object([string, optional(object({ amount: number }))])
const Shipment = object({ carrier: string, legs: Legs })
const Adoption = object({
    id: string,
    shipment: Shipment,
    pay: Pay,
    pair: Pair,
    prices: Prices,
})

type Located = AnyCodec

/** The encode and the decode of two codecs agree on each value of the pool, seeds 1 to 500. */
const sameOnPool = (left: Located, right: Located) => {
    for (let seed = 1; seed <= 500; seed++) {
        const value = arbitraryOf(right, rngFrom(seed), 3) as never
        const a = left.encode(value)
        const b = right.encode(value)
        expect(structuralEquals(a, b), `encode, seed ${seed}`).toBe(true)
        if (a instanceof Error) continue
        expect(
            structuralEquals(left.decode(a), right.decode(a)),
            `decode, seed ${seed}`,
        ).toBe(true)
    }
}

/** The preconditions with the prefix of an enclosing path taken off each segment list. */
const relative = (preconditions: unknown, prefix: number): unknown =>
    Array.isArray(preconditions)
        ? preconditions.map((one: { segments: unknown[] }) => ({
              ...one,
              segments: one.segments.slice(prefix),
          }))
        : preconditions

describe('K1: at from an object is at from its item', () => {
    it('gives the same codec, segments, preconditions and type at a name', () => {
        const fromObject = at(Adoption, ['shipment', 'carrier'])
        const fromItem = at(itemOf(Adoption), ['shipment', 'carrier'])
        expect(path(fromObject)).toEqual(['shipment', 'carrier'])
        expect(preconditions(fromObject)).toEqual(preconditions(fromItem))
        sameOnPool(fromObject, fromItem)
        expectTypeOf(fromObject.unsafeDecode).toEqualTypeOf(
            fromItem.unsafeDecode,
        )
        expectTypeOf(fromObject.unsafeEncode).toEqualTypeOf(
            fromItem.unsafeEncode,
        )
    })

    it('gives the same codec at a position of a list and through a narrow', () => {
        const fromObject = at(Adoption, ['shipment', 'legs', 1, 'deliveredAt'])
        const fromItem = at(itemOf(Adoption), [
            'shipment',
            'legs',
            1,
            'deliveredAt',
        ])
        expect(path(fromObject)).toEqual(['shipment', 'legs', 1, 'deliveredAt'])
        sameOnPool(fromObject, fromItem)
        expectTypeOf(fromObject.unsafeDecode).toEqualTypeOf(
            fromItem.unsafeDecode,
        )
        expectTypeOf(fromObject.unsafeEncode).toEqualTypeOf(
            fromItem.unsafeEncode,
        )
        const narrowedObject = at(
            narrow(at(Adoption, ['pay']), object({ tender: string('CARD') })),
            ['card'],
        )
        const narrowedItem = at(
            narrow(
                at(itemOf(Adoption), ['pay']),
                object({ tender: string('CARD') }),
            ),
            ['card'],
        )
        expect(path(narrowedObject)).toEqual(['pay', 'card'])
        expect(preconditions(narrowedObject)).toEqual(
            preconditions(narrowedItem),
        )
        sameOnPool(narrowedObject, narrowedItem)
        expectTypeOf(narrowedObject.unsafeDecode).toEqualTypeOf(
            narrowedItem.unsafeDecode,
        )
        expectTypeOf(narrowedObject.unsafeEncode).toEqualTypeOf(
            narrowedItem.unsafeEncode,
        )
    })

    it('gives the same codec at the field of an open entry', () => {
        const fromObject = at(Adoption, ['prices', 'eur', 'amount'])
        const fromItem = at(itemOf(Adoption), ['prices', 'eur', 'amount'])
        expect(path(fromObject)).toEqual(['prices', 'eur', 'amount'])
        sameOnPool(fromObject, fromItem)
        expectTypeOf(fromObject.unsafeDecode).toEqualTypeOf(
            fromItem.unsafeDecode,
        )
        expectTypeOf(fromObject.unsafeEncode).toEqualTypeOf(
            fromItem.unsafeEncode,
        )
    })
})

describe('K2: at from a union, a list, a tuple and a record reaches the codec of the longer path', () => {
    it('a union root', () => {
        const short = at(narrow(Pay, object({ tender: string('CARD') })), [
            'card',
            'last4',
        ])
        const long = at(
            narrow(
                at(itemOf(Adoption), ['pay']),
                object({ tender: string('CARD') }),
            ),
            ['card', 'last4'],
        )
        expect(path(short)).toEqual(['card', 'last4'])
        expect(preconditions(short)).toEqual(relative(preconditions(long), 1))
        sameOnPool(short, long)
        expectTypeOf(short.unsafeDecode).toEqualTypeOf(long.unsafeDecode)
        expectTypeOf(short.unsafeEncode).toEqualTypeOf(long.unsafeEncode)
    })

    it('a list root', () => {
        const short = at(Legs, [2, 'deliveredAt'])
        const long = at(itemOf(Adoption), [
            'shipment',
            'legs',
            2,
            'deliveredAt',
        ])
        expect(path(short)).toEqual([2, 'deliveredAt'])
        expect(preconditions(short)).toEqual(relative(preconditions(long), 2))
        sameOnPool(short, long)
        expectTypeOf(short.unsafeDecode).toEqualTypeOf(long.unsafeDecode)
        expectTypeOf(short.unsafeEncode).toEqualTypeOf(long.unsafeEncode)
    })

    it('a tuple root', () => {
        const short = at(Pair, [1, 'id'])
        const long = at(itemOf(Adoption), ['pair', 1, 'id'])
        expect(path(short)).toEqual([1, 'id'])
        expect(preconditions(short)).toEqual(relative(preconditions(long), 1))
        sameOnPool(short, long)
        expectTypeOf(short.unsafeDecode).toEqualTypeOf(long.unsafeDecode)
        expectTypeOf(short.unsafeEncode).toEqualTypeOf(long.unsafeEncode)
    })

    it('a record root', () => {
        const short = at(Prices, ['eur', 'amount'])
        const long = at(itemOf(Adoption), ['prices', 'eur', 'amount'])
        expect(path(short)).toEqual(['eur', 'amount'])
        expect(preconditions(short)).toEqual(relative(preconditions(long), 1))
        sameOnPool(short, long)
        expectTypeOf(short.unsafeDecode).toEqualTypeOf(long.unsafeDecode)
        expectTypeOf(short.unsafeEncode).toEqualTypeOf(long.unsafeEncode)
    })
})

describe('K3: at below a located object is at from the object codec', () => {
    it('reaches the same codec and type, and differs by the prefix only', () => {
        const below = at(at(itemOf(Adoption), ['shipment']), ['legs', 0, 'id'])
        const fromShipment = at(Shipment, ['legs', 0, 'id'])
        expect(path(below)).toBe('shipment.legs[0].id')
        expect(path(fromShipment)).toEqual(['legs', 0, 'id'])
        expect(preconditions(below)).toEqual(preconditions(fromShipment))
        sameOnPool(below, fromShipment)
        expectTypeOf(below.unsafeDecode).toEqualTypeOf(
            fromShipment.unsafeDecode,
        )
        expectTypeOf(below.unsafeEncode).toEqualTypeOf(
            fromShipment.unsafeEncode,
        )
    })
})

describe('the rulings at a root that is not an item', () => {
    it('gives a path relative to the root, because only an item writes the top-level attributes of a row', () => {
        // an expression helper takes the document path of a row, as a string
        const expressionPath = (documentPath: string) => documentPath
        // @ts-expect-error a relative path is no document path, so an expression refuses it
        expressionPath(path(at(Shipment, ['carrier'])))
        expressionPath(path(at(itemOf(Adoption), ['shipment', 'carrier'])))
        // the root kind survives composition: below an item stays absolute, below an object relative
        expectTypeOf(
            path(at(at(itemOf(Adoption), ['shipment']), ['carrier'])),
        ).toEqualTypeOf<string>()
        expectTypeOf(path(at(at(Shipment, ['legs']), [0]))).toEqualTypeOf<
            readonly Segment[]
        >()
        expect(path(at(Shipment, ['legs', 0, 'id']))).toEqual(['legs', 0, 'id'])
        expect(path(at(itemOf(Adoption), ['shipment', 'legs', 0, 'id']))).toBe(
            'shipment.legs[0].id',
        )
    })

    it('refuses level 32 from an object root, because the 32-level limit counts from the row', () => {
        const nestL = (n: number): unknown => {
            let v: unknown = 'leaf'
            for (let i = 0; i < n; i++) v = [v]
            return v
        }
        const Holder = object({ a: opaque })
        const deep = nestL(MAX_DOCUMENT_NESTING) as never
        expect(at(itemOf(Holder), ['a']).encode(deep)).not.toBeInstanceOf(
            CodecError,
        )
        expect(at(Holder, ['a']).encode(deep)).toBeInstanceOf(CodecError)
        // a union's whole-item reading writes a row too, though it offers no `encodePartial`
        const Either = union([Holder, object({ a: opaque, b: string })])
        expect(at(itemOf(Either), ['a']).encode(deep)).not.toBeInstanceOf(
            CodecError,
        )
    })
})

describe('the item of a union', () => {
    const Either = union([
        object({ a: object({ x: string }) }),
        object({ a: object({ x: string, y: number }) }),
    ])
    const Tagged = discriminatedUnion('k', [
        object({ k: string('p'), v: number }),
        object({ k: string('q'), w: string }),
    ])

    it('offers the segments of its options and gives a document path, because a union item writes a row', () => {
        const located = at(itemOf(Either), ['a', 'x'])
        expectTypeOf(path(located)).toEqualTypeOf<string>()
        expect(path(located)).toBe('a.x')
        // @ts-expect-error no option declares the segment, and the run time refuses the same segment
        expect(() => at(itemOf(Either), ['b'])).toThrow(CodecError)
    })

    it('refuses a segment that only some options declare, until a clause keeps those options', () => {
        // @ts-expect-error the option `q` declares no `v`, so no one codec stands at the path
        const some = at(itemOf(Tagged), ['v'])
        expect(some.encode(1 as never)).toBeInstanceOf(CodecError)
        const kept = at(
            narrow(at(itemOf(Tagged), []), object({ k: string('p') })),
            ['v'],
        )
        expect(path(kept)).toBe('v')
    })
})
