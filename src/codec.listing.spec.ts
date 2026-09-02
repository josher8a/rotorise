/**
 * The proving case: a wide entity that a hand-written marshaller would need a `switch` for.
 *
 * Deliberately the most demanding item in these specs, because it is the honest test of the design.
 * If the codec cannot express `breed`'s conditionally-present `coat`, the twelve generated
 * `status_*` log attributes, index attributes whose *existence* is derived from other attributes,
 * or a field whose entity type is `string` but whose stored member is `N`, then the design is wrong
 * and this is where that shows.
 *
 * Every one of those is a shape real tables have; none of them is expressible by a marshaller that
 * looks at a value and guesses.
 */
import { describe, expect, it } from 'vitest'
import type { Attribute, AttributeMap } from './attribute'
import type { ItemCodec, OptionalCodec } from './codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    number,
    object,
    opaque,
    optional,
    record,
    string,
} from './codec'
import {
    arbitraryOf,
    checkDecodesAreWritable,
    checkEncodePaths,
    checkMembersStable,
    checkRoundTrip,
    checkStable,
    rngFrom,
    roundTrip,
} from './testing'

// ── the entity ───────────────────────────────────────────────────────

const ListingStatus = {
    DRAFT: 0,
    LISTED: 1,
    RESERVED: 2,
    SOLD: 3,
    DEPLETED: 4,
    WITHDRAWN: 5,
} as const
type ListingStatus = (typeof ListingStatus)[keyof typeof ListingStatus]
type ListingStatusName = keyof typeof ListingStatus
type ListingStatusLog =
    | `status_${ListingStatusName}_setAt`
    | `status_${ListingStatusName}_byStaffId`

const ListingType = { ADOPTION: 0, SALE: 1 } as const
type ListingType = (typeof ListingType)[keyof typeof ListingType]

type Breed = {
    readonly species: {
        readonly id: string
        readonly type: number
        readonly coat?: string
    }
    readonly registry: { readonly id: string; readonly type: number }
}

type SizeLimits = {
    readonly litterSize: string
    readonly maxLimit: string
    readonly minLimit: string
}

type Listing = {
    id: string
    ownerId: string
    storeId: string
    handle?: string
    displayName?: string
    channel?: string
    description: string
    createdAt: string
    status: ListingStatus
    statusReason?: string
    type: ListingType
    breed: Breed
    sizeLimits: SizeLimits
    /** `string` in the entity, `N` in the table — the field the original reads raw. */
    localPriceRate: string
    autoReply?: string
    basePrice: string
    acceptedTenders: ReadonlySet<string>
    tenderDetailIds: readonly string[]
    tenderDetails?: Readonly<Record<string, unknown>>
    tenderFilter?: unknown
    paused: boolean
    updatedAt?: string
    lastVisitAt?: string
    version?: string
    availableCount?: string
    visibility: 'PUBLIC' | 'PRIVATE'
    feeRate?: string
    feeAmount?: string
    holding: string
    feeBreakdown?: {
        readonly gross: string
        readonly amount: string
        readonly fee: string
        readonly rate: string
    }
    allowsAgentPickup: boolean
    vendorId: string
}

type ListingEntry = Listing & {
    filterIxBreed?: string
    filterIxIdle?: string
    pausedReason?: string
    status_reason?: string
} & { [k in ListingStatusLog]?: string }

// ── the codec ────────────────────────────────────────────────────────

const statusLog = Object.fromEntries(
    Object.keys(ListingStatus).flatMap((name) => [
        [`status_${name}_setAt`, optional(string)],
        [`status_${name}_byStaffId`, optional(string)],
    ]),
) as { [k in ListingStatusLog]: OptionalCodec<string, Attribute<'S'>> }

const Listing = object({
    id: string,
    ownerId: string,
    storeId: string,
    handle: optional(string),
    displayName: optional(string),
    channel: optional(string),
    description: string,
    createdAt: string,
    updatedAt: optional(string),
    autoReply: optional(string),
    basePrice: string,
    availableCount: optional(string),
    lastVisitAt: optional(string),
    version: optional(string),
    holding: string,
    vendorId: string,
    statusReason: optional(string),
    feeAmount: optional(string),
    feeRate: optional(string),
    filterIxIdle: optional(string),
    filterIxBreed: optional(string),
    pausedReason: optional(string),
    status_reason: optional(string),
    visibility: string('PUBLIC', 'PRIVATE'),

    // stored as `N`, and the original's `{ N: value.toString() }` — a numeric literal,
    // so the enum's members are checked on the way in *and* on the way out
    type: number(ListingType.ADOPTION, ListingType.SALE),
    status: number(
        ListingStatus.DRAFT,
        ListingStatus.LISTED,
        ListingStatus.RESERVED,
        ListingStatus.SOLD,
        ListingStatus.DEPLETED,
        ListingStatus.WITHDRAWN,
    ),
    // `string` in, `string` out, `N` in the table — no float ever touches it
    localPriceRate: decimal,

    paused: boolean,
    allowsAgentPickup: boolean,

    // a native set, not a list — the choice no generic marshaller can infer
    acceptedTenders: string.set(),
    tenderDetailIds: array(string),

    breed: object({
        species: object({
            id: string,
            type: number,
            coat: optional(string), // present only when the entity has it
        }),
        registry: object({ id: string, type: number }),
    }),
    sizeLimits: object({
        litterSize: string,
        maxLimit: string,
        minLimit: string,
    }),
    feeBreakdown: optional(
        object({
            gross: string,
            amount: string,
            fee: string,
            rate: string,
        }),
    ),

    // genuinely unknown shapes: the escape hatch, visible and local
    tenderDetails: optional(record(opaque)),
    tenderFilter: optional(opaque),

    ...statusLog,
}).item satisfies ItemCodec<ListingEntry>

// ── the invariants attributes hold between each other ────────────────

/**
 * These index attributes are *derived*: whether they exist at all is a function of status,
 * visibility and paused, which is the sparse-index pattern written out.
 */
const needsFilterIxBreed = (
    o: Pick<ListingEntry, 'status' | 'visibility' | 'paused'>,
) => o.status === ListingStatus.LISTED && o.visibility === 'PUBLIC' && !o.paused

const needsFilterIxIdle = (o: Pick<ListingEntry, 'status' | 'paused'>) =>
    !o.paused && o.status === ListingStatus.LISTED

/**
 * Restores those two invariants after independent per-attribute generation.
 *
 * Repairing beats filtering here: the invariants are satisfied by roughly half of all combinations,
 * so a filter would throw away half the search, and a narrower one would throw away nearly all of it.
 */
const refine = (listing: ListingEntry): ListingEntry => {
    const { filterIxBreed: _a, filterIxIdle: _b, ...rest } = listing
    return {
        ...rest,
        ...(needsFilterIxBreed(listing)
            ? {
                  filterIxBreed: `${listing.breed.registry.id}-${listing.breed.species.id}-${listing.type}`,
              }
            : {}),
        ...(needsFilterIxIdle(listing)
            ? { filterIxIdle: listing.updatedAt ?? listing.createdAt }
            : {}),
    }
}

// ── fixtures ─────────────────────────────────────────────────────────

const listing: ListingEntry = {
    id: 'o1',
    ownerId: 'u1',
    storeId: 'a1',
    handle: 'ana',
    displayName: undefined,
    channel: undefined,
    description: 'a friendly beagle',
    createdAt: '2026-01-01T00:00:00.000Z',
    status: ListingStatus.LISTED,
    type: ListingType.SALE,
    breed: {
        species: { id: 'DOG', type: 1, coat: 'SHORT' },
        registry: { id: 'AKC', type: 0 },
    },
    sizeLimits: { litterSize: '10', maxLimit: '5', minLimit: '1' },
    localPriceRate: '1.5',
    basePrice: '1',
    acceptedTenders: new Set(['CASH']),
    tenderDetailIds: ['d1', 'd2'],
    paused: false,
    visibility: 'PUBLIC',
    holding: 'STORE_V1',
    allowsAgentPickup: true,
    vendorId: 'DIRECT',
}

describe('a wide entity, encoded', () => {
    it('chooses the same member per field as the hand-written switch', () => {
        const item = Listing.unsafeEncode(listing)

        expect(item.id).toEqual({ S: 'o1' })
        expect(item.status).toEqual({ N: '1' })
        expect(item.type).toEqual({ N: '1' })
        expect(item.localPriceRate).toEqual({ N: '1.5' })
        expect(item.paused).toEqual({ BOOL: false })
        // a set, not a list
        expect(item.acceptedTenders).toEqual({ SS: ['CASH'] })
        // a list, not a set
        expect(item.tenderDetailIds).toEqual({
            L: [{ S: 'd1' }, { S: 'd2' }],
        })
        expect(item.sizeLimits).toEqual({
            M: {
                litterSize: { S: '10' },
                maxLimit: { S: '5' },
                minLimit: { S: '1' },
            },
        })
    })

    it("includes breed's coat only when the entity has it", () => {
        const withChain = Listing.unsafeEncode(listing).breed
        expect(withChain).toEqual({
            M: {
                species: {
                    M: {
                        id: { S: 'DOG' },
                        type: { N: '1' },
                        coat: { S: 'SHORT' },
                    },
                },
                registry: { M: { id: { S: 'AKC' }, type: { N: '0' } } },
            },
        })

        const { coat: _dropped, ...noChain } = listing.breed.species
        const without = Listing.unsafeEncode({
            ...listing,
            breed: { ...listing.breed, species: noChain },
        }).breed
        expect(without?.M?.species?.M).not.toHaveProperty('coat')
    })

    it('omits absent optionals rather than writing null', () => {
        const item = Listing.unsafeEncode(listing)
        expect(item).not.toHaveProperty('autoReply')
        expect(item).not.toHaveProperty('status_SOLD_setAt')
        expect(item).not.toHaveProperty('displayName')
    })

    it('encodes only what a patch carries, for UpdateItem', () => {
        const patch = Listing.unsafeEncodePartial({
            availableCount: '3',
            status: ListingStatus.SOLD,
            status_SOLD_setAt: '2026-02-02T00:00:00.000Z',
        })
        expect(Object.keys(patch).sort()).toEqual([
            'availableCount',
            'status',
            'status_SOLD_setAt',
        ])
        expect(patch.status).toEqual({ N: '3' })
    })

    it('hands back a single attribute for ExpressionAttributeValues', () => {
        expect(
            Listing.field('status').unsafeEncode(ListingStatus.DRAFT),
        ).toEqual({
            N: '0',
        })
        expect(Listing.field('ownerId').unsafeEncode('u1')).toEqual({ S: 'u1' })
    })
})

describe('the law', () => {
    it('decode ∘ encode = id, with no cast anywhere', () => {
        const back: ListingEntry = roundTrip(Listing, listing)
        expect(back).toEqual(listing)
    })

    it('holds for a fully-populated entity', () => {
        const full: ListingEntry = {
            ...listing,
            displayName: 'Ana Ruiz',
            channel: 'WALK_IN',
            statusReason: 'because',
            autoReply: 'hi',
            tenderDetails: { CASH: { drawer: '02' } },
            tenderFilter: ['a', 'b'],
            updatedAt: '2026-01-02T00:00:00.000Z',
            lastVisitAt: '2026-01-03T00:00:00.000Z',
            version: '2',
            availableCount: '4',
            feeRate: '0.01',
            feeAmount: '0.5',
            feeBreakdown: {
                gross: '10',
                amount: '9',
                fee: '1',
                rate: '0.1',
            },
            filterIxBreed: 'AKC-DOG-1',
            filterIxIdle: '2026-01-04T00:00:00.000Z',
            pausedReason: 'MANUAL',
            status_reason: 'ok',
            status_LISTED_setAt: '2026-01-01T00:00:00.000Z',
            status_LISTED_byStaffId: 'u9',
        }
        expect(roundTrip(Listing, full)).toEqual(full)
    })

    it('holds for every generated listing', () => {
        checkRoundTrip(Listing, { count: 300, seed: 20260826, refine })
    })

    /** (C), against attributes nobody would write — see `codec.laws.spec.ts`. */
    it('and everything it reads, it can write back', () => {
        checkDecodesAreWritable(Listing, {
            count: 60,
            seed: 20260829,
            refine,
        })
    })

    it('and the three encode paths agree with each other', () => {
        checkEncodePaths(Listing, { count: 200, seed: 20260826, refine })
    })

    it('and a read-modify-write leaves every attribute in its member', () => {
        // a reordered set is still worth pushing through; the denormalised `N` that used to sit
        // here is no longer a stored form the codec will read, which is the point of the test below
        const encoded = Listing.unsafeEncode(listing)
        checkMembersStable(Listing, [
            encoded,
            { ...encoded, acceptedTenders: { SS: ['b', 'a'] } },
        ])
    })

    it('generates listings that could actually exist', () => {
        // without `refine`, roughly half of them violate this
        const rng = rngFrom(20260826)
        for (let i = 0; i < 200; i++) {
            const listing = refine(
                arbitraryOf(Listing as never, rng, 4) as ListingEntry,
            )
            expect('filterIxBreed' in listing).toBe(needsFilterIxBreed(listing))
            expect('filterIxIdle' in listing).toBe(needsFilterIxIdle(listing))
        }
    })

    /**
     * This used to assert the opposite, and the comment beside it read "the codec cannot prevent
     * this; it is the service normalising `N`". It can, and the way it prevents it is by never
     * handing the service something to normalise: `'1.50'` is not a form DynamoDB gives back, so
     * `decimal` refuses to write it.
     *
     * The failure it used to pin was a round trip broken *across storage*, where neither the types
     * nor the in-memory law suite can see it — `encode` succeeded, `decode` succeeded, and the
     * value came back different. Refusing at the write is what moves that failure to where it is
     * still local, and `'1.5'` is the same price.
     */
    it('refuses a denormalised decimal, rather than losing the digits in storage', () => {
        const denormalised = { ...listing, localPriceRate: '1.50' }
        expect(() => Listing.unsafeEncode(denormalised)).toThrow(
            /not a numeral DynamoDB stores unchanged/,
        )

        // and the normalised price is the same money, written the way it comes back
        const normalised = { ...listing, localPriceRate: '1.5' }
        const encoded = Listing.unsafeEncode(normalised)
        expect(encoded.localPriceRate).toEqual({ N: '1.5' })
        expect(Listing.unsafeDecode(encoded as AttributeMap)).toEqual(
            normalised,
        )
        expect(() =>
            checkStable(Listing, [encoded as AttributeMap]),
        ).not.toThrow()
    })

    it('does NOT hold for set ordering — a set is unordered', () => {
        const many = { ...listing, acceptedTenders: new Set(['b', 'a']) }
        const asStored: AttributeMap = {
            ...Listing.unsafeEncode(many),
            acceptedTenders: { SS: ['a', 'b'] },
        }
        expect(Listing.unsafeDecode(asStored).acceptedTenders).toEqual(
            new Set(['a', 'b']),
        )

        // ...and again, re-reading what the table returned changes nothing
        expect(() => checkStable(Listing, [asStored])).not.toThrow()
    })
})

describe('what it refuses', () => {
    it('refuses an empty set rather than writing one DynamoDB rejects', () => {
        expect(() =>
            Listing.unsafeEncode({ ...listing, acceptedTenders: new Set() }),
        ).toThrow(CodecError)
    })

    it('refuses a required attribute the item does not carry', () => {
        const { ownerId: _missing, ...partial } = Listing.unsafeEncode(listing)
        expect(() => Listing.unsafeDecode(partial)).toThrow(
            /'ownerId' is required/,
        )
    })

    it('refuses an attribute carrying the wrong member', () => {
        expect(() =>
            Listing.unsafeDecode({
                ...Listing.unsafeEncode(listing),
                status: { S: '1' },
            }),
        ).toThrow(/expected attribute member 'N', found 'S'/)
    })

    it('drops attributes no schema mentions, which is why the inverse law fails', () => {
        const withLegacy = {
            ...Listing.unsafeEncode(listing),
            legacyFlag: { S: 'x' },
        }
        expect(Listing.unsafeDecode(withLegacy)).toEqual(listing)
    })
})
