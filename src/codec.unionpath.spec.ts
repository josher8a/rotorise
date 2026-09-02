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
import { discriminatedUnion, object, pathBuilder, string } from './codec'

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
    const p = Adoption.path()

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
    it('resolves the variant that has the attribute', () => {
        // only CASH declares cardId, so there is exactly one candidate
        const cardId = Adoption.at((q) => q.priceIn.cardId)
        expect(cardId.path()).toBe('priceIn.cardId')
        expect(cardId.unsafeEncode('CASH')).toEqual({
            S: 'CASH',
        })
    })

    it('resolves a shared attribute the variants agree on', () => {
        const tender = Adoption.at((q) => q.priceIn.tender)
        expect(tender.unsafeEncode('AKC')).toEqual({ S: 'AKC' })
    })

    it('types it by what lives there', () => {
        const cardId = Adoption.at((q) => q.priceIn.cardId)
        // @ts-expect-error cardId is a string
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
        expect(p.mixed.when<{ tag: 'DEEP' }>().data.nested.toString()).toBe(
            'mixed.data.nested',
        )
    })

    it('picks between a list and an object under one key', () => {
        expect(p.mixed.when<{ tag: 'FLAT' }>().both.at(0).toString()).toBe(
            'mixed.both[0]',
        )
        expect(p.mixed.when<{ tag: 'DEEP' }>().both.k.toString()).toBe(
            'mixed.both.k',
        )
    })

    it('takes the member type itself, not only a filter', () => {
        expect(
            p.mixed
                .when<Extract<Mixed, { tag: 'DEEP' }>>()
                .data.nested.toString(),
        ).toBe('mixed.data.nested')
    })

    it('adds nothing to the path — narrowing is about the type', () => {
        expect(p.mixed.when<{ tag: 'FLAT' }>().data.toString()).toBe(
            'mixed.data',
        )
        expect(p.mixed.data.toString()).toBe('mixed.data')
    })

    it('refuses a filter no member matches', () => {
        // @ts-expect-error there is no such variant
        const _noSuchTag = () => p.mixed.when<{ tag: 'MIDDLE' }>()
        expect(typeof _noSuchTag).toBe('function')
    })

    it('holds the narrowing while walking further', () => {
        // @ts-expect-error FLAT's `data` is a string
        const _stillFlat = () => p.mixed.when<{ tag: 'FLAT' }>().data.nested
        expect(typeof _stillFlat).toBe('function')
    })

    it('is absent where there is nothing to pick', () => {
        // @ts-expect-error a single-member attribute has no `when`
        const _notAUnion = () => p.mixed.when<{ tag: 'FLAT' }>().data.when<0>()
        expect(typeof _notAUnion).toBe('function')
    })
})

/**
 * A union with no discriminant, which is why `when` takes a type rather than a tag and a value.
 *
 * A `LineItem` of `{ gift?, petId, sellerId, price } | { petIds }` — a single pet or a bundle —
 * has nothing to switch on. Narrowing by discriminant cannot reach it; narrowing by shape can.
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
            p.leg.when<{ petIds: readonly string[] }>().petIds.at(1).toString(),
        ).toBe('leg.petIds[1]')
    })

    it('narrows by shape to the other member', () => {
        expect(p.leg.when<{ petId: string }>().sellerId.toString()).toBe(
            'leg.sellerId',
        )
    })

    it('refuses a shape neither member has, at the first use of the result', () => {
        // a filter of all-optional properties admits an extra key, so this cannot be caught at the
        // call — it resolves to `never` and the failure lands here instead
        // @ts-expect-error neither member carries this
        const _neither = () => p.leg.when<{ notAnAttribute: string }>().petId
        expect(typeof _neither).toBe('function')
    })
})
