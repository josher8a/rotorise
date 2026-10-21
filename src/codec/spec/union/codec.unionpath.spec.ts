/**
 * Paths into a union.
 *
 * Without this, reaching a member-specific attribute needs a cast — `path().priceIn as Tender<'CASH'>`
 * — because `priceIn` is a union and `cardId` lives on one member of it. The cast narrows nothing
 * real: a path is a string, and the item is whatever it is. It works around a path type that only
 * offered the keys every member shares, and those are never the interesting ones — reaching a
 * member-specific attribute is the whole reason to write the path.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    at,
    discriminatedUnion,
    number,
    object,
    path,
    pathBuilder,
    refine,
    string,
} from '../../codec'

type Tender =
    | { tenderType: 'STORE_CREDIT'; tender: string }
    | { tenderType: 'CASH'; tender: string; cardId: string }

const AssetCodec = discriminatedUnion('tenderType', [
    object({ tenderType: string('STORE_CREDIT'), tender: string }),
    object({
        tenderType: string('CASH'),
        tender: string,
        cardId: string,
    }),
])

type Adoption = {
    adoptionId: string
    priceIn: Tender
    priceOut: Tender
    nested: { inner: Tender }
}

const Adoption = object({
    adoptionId: string,
    priceIn: AssetCodec,
    priceOut: AssetCodec,
    nested: object({ inner: AssetCodec }),
}).item

describe('a path into a union', () => {
    const p = path(Adoption)

    it('reaches a key every member shares', () => {
        expect(p.priceIn.tender.toString()).toBe('priceIn.tender')
        expect(p.priceIn.tenderType.toString()).toBe('priceIn.tenderType')
    })

    it('reaches a key only one member has, without a cast', () => {
        expect(p.priceIn.cardId.toString()).toBe('priceIn.cardId')
        expect(p.priceOut.cardId.toString()).toBe('priceOut.cardId')
    })

    it('reaches one nested inside another attribute', () => {
        expect(p.nested.inner.cardId.toString()).toBe('nested.inner.cardId')
    })

    it('still refuses a key no member has', () => {
        // @ts-expect-error neither variant states this
        const _nonsense = () => p.priceIn.notAnAttribute
        expect(typeof _nonsense).toBe('function')
    })
})

describe('a codec at a path into a union', () => {
    it('resolves the variant that has the attribute, under the clause that keeps that variant', () => {
        // only CASH declares cardId, so the clause keeps one candidate
        const cardId = at(
            Adoption,
            (q) => q.priceIn.narrow({ tenderType: string('CASH') }).cardId,
        )
        expect(path(cardId)).toBe('priceIn.cardId')
        expect(cardId.unsafeEncode('CASH')).toEqual({
            S: 'CASH',
        })
    })

    it('resolves a shared attribute the variants agree on', () => {
        const tender = at(Adoption, (q) => q.priceIn.tender)
        expect(tender.unsafeEncode('AKC')).toEqual({ S: 'AKC' })
    })

    it('resolves an attribute that each variant declares with its own call of one constructor, because the two declarations are one codec', () => {
        const Shipment = discriminatedUnion('kind', [
            object({ kind: string('PARCEL'), region: string('EU', 'US') }),
            object({ kind: string('PALLET'), region: string('EU', 'US') }),
        ])
        const Order = object({ shipment: Shipment }).item
        const region = at(Order, (q) => q.shipment.region)
        expect(region.unsafeEncode('EU')).toEqual({ S: 'EU' })
    })

    it('refuses an attribute that the variants refine with two different predicates, because two predicates are two codecs', () => {
        const short = (v: string): v is string => v.length < 8
        const upper = (v: string): v is string => v === v.toUpperCase()
        const Shipment = discriminatedUnion('kind', [
            object({
                kind: string('PARCEL'),
                label: refine(string, short, { describe: 'a label' }),
            }),
            object({
                kind: string('PALLET'),
                label: refine(string, upper, { describe: 'a label' }),
            }),
        ])
        const Order = object({ shipment: Shipment }).item
        const label = at(Order, (q) => q.shipment.label)
        expect(() => label.unsafeEncode('AB')).toThrow(
            /declared differently in different variants/,
        )
    })

    it('refuses at the type a path that a variant does not declare, as the walk refuses on use', () => {
        // @ts-expect-error a variant does not declare `cardId`, so the path refuses at the type as on use
        const cardId = at(Adoption, (q) => q.priceIn.cardId)
        const _wrong = () => cardId.unsafeEncode(1)
        expect(typeof _wrong).toBe('function')
    })
})

/**
 * Where merging is not enough, and picking a member is.
 *
 * Merging every member's keys is right where the members are objects: each key belongs to some
 * variant, and a path is well formed whether or not this item is that variant. It stops being enough
 * where members disagree about *kind*.
 */
describe('members that disagree about kind', () => {
    type Mixed =
        | { tag: 'FLAT'; data: string; both: readonly string[] }
        | { tag: 'DEEP'; data: { nested: number }; both: { k: string } }

    const p = pathBuilder<{ mixed: Mixed }>()

    it('cannot walk through a key that is an object in one member and a string in another', () => {
        // merging `string | { nested }` reaches neither
        // @ts-expect-error the merged node is a terminal
        const _unreachable = () => p.mixed.data.nested
        expect(typeof _unreachable).toBe('function')
    })

    it('reaches it once a member is picked', () => {
        expect(
            p.mixed.narrow({ tag: string('DEEP') }).data.nested.toString(),
        ).toBe('mixed.data.nested')
    })

    it('picks between a list and an object under one key', () => {
        expect(
            p.mixed
                .narrow({ tag: string('FLAT') })
                .both.at(0)
                .toString(),
        ).toBe('mixed.both[0]')
        expect(p.mixed.narrow({ tag: string('DEEP') }).both.k.toString()).toBe(
            'mixed.both.k',
        )
    })

    it('takes a clause on more than one key', () => {
        expect(
            p.mixed
                .narrow({
                    tag: string('DEEP'),
                    data: object({ nested: number }),
                })
                .data.nested.toString(),
        ).toBe('mixed.data.nested')
    })

    it('adds nothing to the path', () => {
        expect(p.mixed.narrow({ tag: string('FLAT') }).data.toString()).toBe(
            'mixed.data',
        )
        expect(p.mixed.data.toString()).toBe('mixed.data')
    })

    it('refuses a clause that separates every member', () => {
        // @ts-expect-error there is no such variant
        const _noSuchTag = () => p.mixed.narrow({ tag: string('MIDDLE') })
        expect(typeof _noSuchTag).toBe('function')
    })

    it('holds the narrowing while walking further', () => {
        const _stillFlat = () =>
            // @ts-expect-error FLAT's `data` is a string
            p.mixed.narrow({ tag: string('FLAT') }).data.nested
        expect(typeof _stillFlat).toBe('function')
    })

    it('is absent where there is nothing to pick', () => {
        const flat = { tag: string('FLAT') }
        // @ts-expect-error a single-member attribute has no `narrow`
        const _notAUnion = () => p.mixed.narrow(flat).data.narrow(flat)
        expect(typeof _notAUnion).toBe('function')
    })
})

/**
 * A union with no discriminant, which is why `narrow` takes a clause on any key rather than a tag.
 *
 * A `LineItem` of `{ gift?, petId, sellerId, price } | { petIds }` — a single pet or a bundle —
 * has nothing to switch on. Narrowing by discriminant cannot reach it; a clause on a key that one
 * member declares and the other does not can.
 */
describe('a union with nothing to switch on', () => {
    type LineItem =
        | {
              gift?: boolean
              petId: string
              sellerId: string
              price: string
          }
        | { petIds: readonly string[] }

    const p = pathBuilder<{ leg: LineItem }>()

    it('merges both members without narrowing', () => {
        expect(p.leg.petId.toString()).toBe('leg.petId')
        expect(p.leg.petIds.toString()).toBe('leg.petIds')
    })

    it('narrows by shape to reach a list member', () => {
        expect(
            p.leg
                .narrow({ petIds: array(string) })
                .petIds.at(1)
                .toString(),
        ).toBe('leg.petIds[1]')
    })

    it('narrows by shape to the other member', () => {
        expect(p.leg.narrow({ petId: string }).sellerId.toString()).toBe(
            'leg.sellerId',
        )
    })

    it('refuses a key neither member declares, at the call', () => {
        // @ts-expect-error neither member carries this
        const _neither = () => p.leg.narrow({ notAnAttribute: string })
        expect(typeof _neither).toBe('function')
    })
})
