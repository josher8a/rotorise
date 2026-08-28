/**
 * Nesting, stress-tested to the depth real entities reach.
 *
 * `Adoption.fulfilment` is a union discriminated on `type`, whose `legs` is a *tuple* of legs, each of
 * which carries `carrier` — itself a union discriminated on `carrierId` — and `priceIn` /
 * `priceOut`, which are unions discriminated on `chargeType` intersected with a `Tender` union
 * discriminated on `tenderType`. Four levels of union, three of them nested inside another.
 *
 * What does NOT fit is recorded at the bottom of this file.
 */
import { describe, expect, it } from 'vitest'
import {
    decimal,
    discriminatedUnion,
    literal,
    number,
    object,
    optional,
    string,
    tuple,
} from './codec'
import { checkEncodePaths, checkRoundTrip } from './testing'

// ── the entity ───────────────────────────────────────────────────────

type Tender =
    | { readonly tenderType: 'STORE_CREDIT'; readonly tender: string }
    | {
          readonly tenderType: 'CASH'
          readonly tender: string
          readonly cardId: string
          readonly cardDetailId?: string
      }

type Charge =
    | {
          readonly chargeType: 'FIXED'
          readonly value: string
          readonly tender: Tender
      }
    | {
          readonly chargeType: 'VARIABLE_OUT'
          readonly expected: string
          readonly minPrice: string
          readonly tolerancePercent: string
          readonly tender: Tender
      }

type CarrierData =
    | {
          readonly carrierId: 'ACME' | 'GLOBEX'
          readonly carrierRefId?: string
          readonly traits: {
              readonly type: 'scheduled'
              readonly duration: string
          }
      }
    | {
          readonly carrierId: 'PICKUP'
          readonly traits: {
              readonly type: 'walkin'
              readonly duration: string
          }
      }

type Leg = {
    readonly legType: string
    readonly fixedSide: 'IN' | 'OUT'
    readonly priceIn: Charge
    readonly priceOut: Charge
    readonly carrier?: CarrierData
    readonly pricing: {
        readonly localPriceRate: string
        readonly fee: string
    }
}

type Fulfilment =
    | { readonly type: 'SINGLE_LEG'; readonly legs: readonly [Leg] }
    | { readonly type: 'MULTI_LEG'; readonly legs: readonly [Leg, Leg] }

type Adoption = {
    readonly TAG: 'ADOPTION'
    readonly adoptionId: string
    readonly customerId: string
    readonly displayPrice: string
    readonly currentLegIndex: number
    readonly fulfilment: Fulfilment
}

// ── the codecs, composed bottom-up ───────────────────────────────────

const AssetCodec = discriminatedUnion('tenderType', [
    object({ tenderType: literal('STORE_CREDIT'), tender: string }),
    object({
        tenderType: literal('CASH'),
        tender: string,
        cardId: string,
        cardDetailId: optional(string),
    }),
])

// a union nested inside a union
const AmountCodec = discriminatedUnion('chargeType', [
    object({
        chargeType: literal('FIXED'),
        value: decimal,
        tender: AssetCodec,
    }),
    object({
        chargeType: literal('VARIABLE_OUT'),
        expected: decimal,
        minPrice: decimal,
        tolerancePercent: decimal,
        tender: AssetCodec,
    }),
])

const ProviderCodec = discriminatedUnion('carrierId', [
    object({
        carrierId: literal('ACME', 'GLOBEX'),
        carrierRefId: optional(string),
        traits: object({ type: literal('scheduled'), duration: string }),
    }),
    object(
        // one option, two tags: `literal('ACME', 'GLOBEX')` covers both stored values
        {
            carrierId: literal('PICKUP'),
            traits: object({ type: literal('walkin'), duration: string }),
        },
    ),
])

const StepCodec = object({
    legType: string,
    fixedSide: literal('IN', 'OUT'),
    priceIn: AmountCodec,
    priceOut: AmountCodec,
    carrier: optional(ProviderCodec),
    pricing: object({
        localPriceRate: decimal,
        fee: decimal,
    }),
})

// a union whose variants differ in tuple arity
const FulfilmentCodec = discriminatedUnion('type', [
    object({
        type: literal('SINGLE_LEG'),
        legs: tuple(StepCodec),
    }),
    object({
        type: literal('MULTI_LEG'),
        legs: tuple(StepCodec, StepCodec),
    }),
])

const AdoptionCodec = object({
    TAG: literal('ADOPTION'),
    adoptionId: string,
    customerId: string,
    displayPrice: decimal,
    currentLegIndex: number,
    fulfilment: FulfilmentCodec,
}).item

// ── fixtures ─────────────────────────────────────────────────────────

const cashIn: Charge = {
    chargeType: 'FIXED',
    value: '100',
    tender: {
        tenderType: 'CASH',
        tender: 'AKC',
        cardId: 'CASH',
        cardDetailId: 'pd1',
    },
}

const creditOut: Charge = {
    chargeType: 'VARIABLE_OUT',
    expected: '2.5',
    minPrice: '2.4',
    tolerancePercent: '0.01',
    tender: { tenderType: 'STORE_CREDIT', tender: 'STORE-CREDIT-01' },
}

const pickupLeg: Leg = {
    legType: 'CASH_TO_CREDIT',
    fixedSide: 'IN',
    priceIn: cashIn,
    priceOut: creditOut,
    carrier: {
        carrierId: 'PICKUP',
        traits: { type: 'walkin', duration: '30' },
    },
    pricing: { localPriceRate: '40', fee: '0.5' },
}

const acmeLeg: Leg = {
    legType: 'CREDIT_TO_CASH',
    fixedSide: 'OUT',
    priceIn: creditOut,
    priceOut: cashIn,
    carrier: {
        carrierId: 'ACME',
        carrierRefId: 'q1',
        traits: { type: 'scheduled', duration: '60' },
    },
    pricing: { localPriceRate: '41', fee: '0.6' },
}

const single: Adoption = {
    TAG: 'ADOPTION',
    adoptionId: 'q1',
    customerId: 'u1',
    displayPrice: '40',
    currentLegIndex: 0,
    fulfilment: { type: 'SINGLE_LEG', legs: [pickupLeg] },
}

const multi: Adoption = {
    ...single,
    fulfilment: { type: 'MULTI_LEG', legs: [pickupLeg, acmeLeg] },
}

describe('nested variant codecs', () => {
    it('round-trips an adoption four union levels deep', () => {
        expect(
            AdoptionCodec.unsafeDecode(AdoptionCodec.unsafeEncode(single)),
        ).toEqual(single)
        expect(
            AdoptionCodec.unsafeDecode(AdoptionCodec.unsafeEncode(multi)),
        ).toEqual(multi)
    })

    it('nests as M all the way down', () => {
        const item = AdoptionCodec.unsafeEncode(single)
        const leg = item.fulfilment?.M?.legs?.L?.[0]
        expect(leg?.M?.priceIn?.M?.chargeType).toEqual({ S: 'FIXED' })
        expect(leg?.M?.priceIn?.M?.tender?.M?.tenderType).toEqual({ S: 'CASH' })
        expect(leg?.M?.priceIn?.M?.tender?.M?.cardDetailId).toEqual({
            S: 'pd1',
        })
        expect(leg?.M?.carrier?.M?.traits?.M?.type).toEqual({ S: 'walkin' })
    })

    it('keeps each nested union on its own variant', () => {
        const item = AdoptionCodec.unsafeEncode(multi)
        const [first, second] = item.fulfilment?.M?.legs?.L ?? []
        // PICKUP has no carrierRefId; ACME does
        expect(first?.M?.carrier?.M).not.toHaveProperty('carrierRefId')
        expect(second?.M?.carrier?.M?.carrierRefId).toEqual({ S: 'q1' })
        // FIXED has `value`; VARIABLE_OUT has `minPrice`
        expect(first?.M?.priceIn?.M).toHaveProperty('value')
        expect(first?.M?.priceOut?.M).toHaveProperty('minPrice')
    })

    it('refuses a legs whose arity is wrong for its variant', () => {
        const item = AdoptionCodec.unsafeEncode(multi)
        const truncated = {
            ...item,
            fulfilment: {
                M: {
                    ...item.fulfilment?.M,
                    legs: { L: [item.fulfilment?.M?.legs?.L?.[0]] },
                },
            },
        }
        expect(() => AdoptionCodec.unsafeDecode(truncated as never)).toThrow(
            /expected a list of 2, found 1/,
        )
    })

    it('refuses a nested union whose discriminator names no variant', () => {
        const item = AdoptionCodec.unsafeEncode(single)
        const rogue = {
            ...item,
            fulfilment: {
                M: {
                    ...item.fulfilment?.M,
                    legs: {
                        L: [
                            {
                                M: {
                                    ...item.fulfilment?.M?.legs?.L?.[0]?.M,
                                    carrier: {
                                        M: { carrierId: { S: 'NOPE' } },
                                    },
                                },
                            },
                        ],
                    },
                },
            },
        }
        expect(() => AdoptionCodec.unsafeDecode(rogue as never)).toThrow(
            /'NOPE' is not a variant of 'carrierId'/,
        )
    })

    it('patches the top level without touching the nest', () => {
        expect(
            AdoptionCodec.unsafeEncodePartial({ currentLegIndex: 1 }),
        ).toEqual({
            currentLegIndex: { N: '1' },
        })
    })
})

describe('the law, over generated values', () => {
    it('decode ∘ encode = id for AdoptionCodec', () => {
        checkRoundTrip(AdoptionCodec, { count: 300, seed: 20260826 })
    })

    it('and the three encode paths agree, through every level of nesting', () => {
        checkEncodePaths(AdoptionCodec, { count: 200, seed: 20260826 })
    })
})

/**
 * ── What does NOT fit ──────────────────────────────────────────────────────────────────────────
 *
 * 1. A `LineItem` of `{ petId, sellerId, price } | { petIds }` is an **untagged** union, with no
 *    discriminator to switch on. `tagged` cannot express it.
 *    Either the type gains a tag, or the codec gains a way to discriminate on the *presence* of a
 *    witness attribute. Reduced away here rather than faked.
 *
 * 2. `VendorMeta` is open: `{ carrierId } & { [Key in string]?: string | number | boolean }`.
 *    Total coverage cannot say "and anything else", so an open record needs the `rest` policy the
 *    item codec does not have yet. This is a requirement for `Adoption`, not a nicety.
 *
 * 3. `Adoption<Status, IO, Side>` distributes over 8 statuses × 3 IOs × 2 sides. Declaring a spec per
 *    combination is not viable, and it is also not what the table holds: the row is one wider shape,
 *    and the precision lives in the domain type. The codec belongs against the *entry* type, not the
 *    full domain union — the same split `tableEntry` already makes.
 *
 * 4. `CarrierData` has one member spanning two tags (`'ACME' | 'GLOBEX'`). `VariantOf` reaches it,
 *    but the spec has to be written out once per tag. A grouping helper would remove the duplication.
 */
