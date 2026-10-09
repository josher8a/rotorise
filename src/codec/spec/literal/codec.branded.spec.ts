/**
 * Branded types.
 *
 * A domain that stores money as `N` and never lets it become a JS number, and identifies everything
 * with nominal brands, poses a codec one problem twice: `decimal` decodes to `string`, and a
 * `string` is not a `Price`, so the compiler refuses the spec. The brand has to be applied
 * somewhere, and the model already says where — a branded type of either kind ships a predicate.
 */
import { describe, expect, it } from 'vitest'
import {
    CodecError,
    decimal,
    discriminatedUnion,
    object,
    optional,
    refine,
    string,
} from '../../codec'
import {
    arbitraryOf,
    checkEncodePaths,
    checkMembersStable,
    checkRoundTrip,
    rngFrom,
} from '../../testing'

// ── the model, reproduced ────────────────────────────────────────────

declare const brand: unique symbol
type Brand<T, B> = T & { [brand]: B }

type Price = Brand<string, 'price'>
type SequenceValue = Brand<string, 'sequenceValue'>
type UserId = Brand<string, 'userId'>
type SpeciesId = Brand<string, 'speciesId'>
type ProfileId = Brand<string, 'profileId'>

const isPrice = (value: string): value is Price => {
    if (value.length === 0 || value.trim() !== value) return false
    const num = Number(value)
    return Number.isFinite(num) && num >= 0
}
const isSequenceValue = (value: string): value is SequenceValue => {
    if (value.length === 0 || value.trim() !== value) return false
    const num = Number(value)
    return Number.isInteger(num) && num >= 0
}
const isUserId = (value: string): value is UserId => value.length > 0
const isSpeciesId = (value: string): value is SpeciesId => value.length > 0
const isProfileId = (value: string): value is ProfileId => value.length > 0

type OwnerParty = {
    type: 'OWNER'
    userId: UserId
    profileId: ProfileId
    speciesId: SpeciesId
}
/**
 * Everything an owner has, but staff — so the discriminant is *replaced*, not intersected.
 *
 * `OwnerParty & { type: 'STAFF' }` reads as the intent and does not mean it: the two `type`s
 * intersect to `never`, so the variant has an uninhabitable discriminant and nothing can be that
 * variant. It went unnoticed while the variants were keyed by hand — the key said `STAFF` and was
 * believed — and surfaced the moment the tag had to be read off the spec instead.
 */
type StaffParty = Omit<OwnerParty, 'type'> & {
    type: 'STAFF'
    branchId: string
}
type AccountBalance = {
    balance: Price
    sequence: SequenceValue
    createdAt: string
    updatedAt: string
}
type Account = (OwnerParty & AccountBalance) | (StaffParty & AccountBalance)

// ── the codecs ───────────────────────────────────────────────────────

const some =
    <T>(values: readonly T[]) =>
    (rng: () => number) =>
        values[Math.floor(rng() * values.length)] as T

/**
 * Stored as `N`, read back as a branded string. Never a JS number, at any point.
 *
 * `decimal` generates negatives, which are not amounts, so the arbitrary is supplied rather than
 * left to filter — a predicate that rejects half of what it sees wastes the search.
 */
const amount = refine(decimal, isPrice, {
    describe: 'a non-negative amount',
    arbitrary: some(['0', '1', '0.5', '1000000', '0.00000001'] as Price[]),
})

const sequence = refine(decimal, isSequenceValue, {
    describe: 'a non-negative integer sequence',
    arbitrary: some(['0', '1', '42', '9007199254740993'] as SequenceValue[]),
})

// nominal brands: the predicate is all there is to them
const userId = refine(string, isUserId, { describe: 'a user id' })
const speciesId = refine(string, isSpeciesId, { describe: 'a currency id' })
const profileId = refine(string, isProfileId, {
    describe: 'a party id',
})

const balance = {
    balance: amount,
    sequence,
    createdAt: string,
    updatedAt: string,
}

const OwnerAccount = object({
    type: string('OWNER'),
    userId,
    profileId,
    speciesId,
    ...balance,
})

const StaffAccount = object({
    type: string('STAFF'),
    userId,
    profileId,
    speciesId,
    branchId: string,
    ...balance,
})

const AccountCodec = discriminatedUnion('type', [
    OwnerAccount,
    StaffAccount,
]).item

const HolderCodec = discriminatedUnion('type', [
    object({
        type: string('OWNER'),
        userId,
        profileId,
        speciesId,
    }),
    object({
        type: string('STAFF'),
        userId,
        profileId,
        speciesId,
        branchId: string,
    }),
])

const account: Account = {
    type: 'OWNER',
    userId: 'u1' as UserId,
    profileId: 's1' as ProfileId,
    speciesId: 'DOG' as SpeciesId,
    balance: '10.5' as Price,
    sequence: '3' as SequenceValue,
    createdAt: '2026-01-01T00:00:00.000Z',
    updatedAt: '2026-01-01T00:00:00.000Z',
}

describe('branded amounts', () => {
    it('stores as N and reads back branded, never as a number', () => {
        const item = AccountCodec.unsafeEncode(account)
        expect(item.balance).toEqual({ N: '10.5' })
        expect(item.sequence).toEqual({ N: '3' })

        const back = AccountCodec.unsafeDecode(item)
        // the brand survives at the type level — this line is the assertion
        const stillAnAmount: Price = back.balance
        expect(typeof stillAnAmount).toBe('string')
        expect(stillAnAmount).toBe('10.5')
    })

    it('carries a sequence wider than a float without rounding', () => {
        const wide = '9007199254740993' as SequenceValue
        const back = AccountCodec.unsafeDecode(
            AccountCodec.unsafeEncode({ ...account, sequence: wide }),
        )
        expect(back.sequence).toBe(wide)
        expect(String(Number(wide))).not.toBe(wide)
    })

    it('refuses a stored value the brand would not admit', () => {
        const item = {
            ...AccountCodec.unsafeEncode(account),
            balance: { N: '-1' },
        }
        expect(() => AccountCodec.unsafeDecode(item)).toThrow(CodecError)
        expect(() => AccountCodec.unsafeDecode(item)).toThrow(CodecError)
    })

    it('refuses a sequence that is not an integer', () => {
        const item = {
            ...AccountCodec.unsafeEncode(account),
            sequence: { N: '1.5' },
        }
        expect(() => AccountCodec.unsafeDecode(item)).toThrow(CodecError)
    })

    it('refuses an empty id, which the nominal brand still checks', () => {
        const item = {
            ...AccountCodec.unsafeEncode(account),
            userId: { S: '' },
        }
        expect(() => AccountCodec.unsafeDecode(item)).toThrow(CodecError)
    })
})

describe('the laws, over branded entities', () => {
    it('decode ∘ encode = id', () => {
        checkRoundTrip(AccountCodec, { count: 300, seed: 20260826 })
    })

    it('the encode paths agree, per variant', () => {
        checkEncodePaths(OwnerAccount.item, { seed: 1 })
        checkEncodePaths(StaffAccount.item, { seed: 2 })
    })

    it('a read-modify-write leaves the amounts as N', () => {
        checkMembersStable(AccountCodec, [AccountCodec.unsafeEncode(account)])
    })

    it('generation only ever produces values the brands admit', () => {
        const rng = rngFrom(20260826)
        for (let i = 0; i < 200; i++) {
            const generated = arbitraryOf(
                AccountCodec as never,
                rng,
                3,
            ) as Account
            expect(isPrice(generated.balance)).toBe(true)
            expect(isSequenceValue(generated.sequence)).toBe(true)
            expect(isUserId(generated.userId)).toBe(true)
        }
    })
})

describe('brands nested inside another entity', () => {
    // a fee and a visit's `from`/`to` carry a Party, which is itself a branded union
    const Fee = object({ owner: HolderCodec, amount })

    it('round-trips a fee holding a branded union', () => {
        const fee = {
            owner: {
                type: 'OWNER' as const,
                userId: 'u1' as UserId,
                profileId: 's1' as ProfileId,
                speciesId: 'DOG' as SpeciesId,
            },
            amount: '1.25' as Price,
        }
        expect(Fee.unsafeDecode(Fee.unsafeEncode(fee))).toEqual(fee)
        expect(Fee.unsafeEncode(fee).M?.amount).toEqual({ N: '1.25' })
    })

    it('an optional branded attribute stays optional', () => {
        const withFee = object({ fee: optional(Fee) }).item
        expect(withFee.unsafeEncode({})).toEqual({})
        expect(withFee.unsafeDecode({})).toEqual({})
    })
})
