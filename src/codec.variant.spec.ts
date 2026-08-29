/**
 * Unions of objects: an entity that needs a discriminator for its *keys* in `tableEntry` needs one
 * for its attributes too, and should spell it the same way in both places.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from './attribute'
import {
    CodecError,
    decimal,
    discriminatedUnion,
    literal,
    number,
    object,
    optional,
    string,
} from './codec'
import { checkEncodePaths, checkRoundTrip } from './testing'

type Account =
    | {
          type: 'OWNER'
          userId: string
          profileId: string
          balance: string
      }
    | {
          type: 'STAFF'
          userId: string
          profileId: string
          branchId: string
          weight: number
          note?: string
      }

const Account = discriminatedUnion('type', [
    object({
        type: literal('OWNER'),
        userId: string,
        profileId: string,
        balance: decimal,
    }),
    object({
        type: literal('STAFF'),
        userId: string,
        profileId: string,
        branchId: string,
        weight: number,
        note: optional(string),
    }),
]).item

const plain: Account = {
    type: 'OWNER',
    userId: 'u1',
    profileId: 's1',
    balance: '10.5',
}

const branch: Account = {
    type: 'STAFF',
    userId: 'u1',
    profileId: 's1',
    branchId: 'sh1',
    weight: 3,
}

describe('tagged', () => {
    it('encodes each variant with its own attributes', () => {
        expect(Account.unsafeEncode(plain)).toEqual({
            type: { S: 'OWNER' },
            userId: { S: 'u1' },
            profileId: { S: 's1' },
            balance: { N: '10.5' },
        })

        const encoded = Account.unsafeEncode(branch)
        expect(encoded.branchId).toEqual({ S: 'sh1' })
        expect(encoded.weight).toEqual({ N: '3' })
        // the other variant's field is not written
        expect(encoded).not.toHaveProperty('balance')
        expect(encoded).not.toHaveProperty('note')
    })

    it('decodes by the stored discriminator', () => {
        expect(Account.unsafeDecode(Account.unsafeEncode(plain))).toEqual(plain)
        expect(Account.unsafeDecode(Account.unsafeEncode(branch))).toEqual(
            branch,
        )
    })

    it('decode ∘ encode = id, per variant', () => {
        for (const value of [plain, branch] as const) {
            expect(Account.unsafeDecode(Account.unsafeEncode(value))).toEqual(
                value,
            )
        }
    })

    it('exposes one variant as a plain item codec', () => {
        expect(
            Account.variant('STAFF').field('weight').unsafeEncode(7),
        ).toEqual({
            N: '7',
        })
        expect(
            Account.variant('OWNER').field('balance').unsafeEncode('1.5'),
        ).toEqual({
            N: '1.5',
        })
    })

    it('patches through the variant the discriminator names', () => {
        const patch = Account.unsafeEncodePartial({
            type: 'STAFF',
            weight: 9,
        })
        expect(patch).toEqual({
            type: { S: 'STAFF' },
            weight: { N: '9' },
        })
    })

    it('refuses a patch attribute belonging to another variant', () => {
        expect(() =>
            Account.unsafeEncodePartial({
                type: 'OWNER',
                // `weight` is not an attribute of OWNER
                weight: 9,
            } as never),
        ).toThrow(/'weight' is not an attribute/)
    })

    it('refuses an item whose discriminator names no variant', () => {
        const rogue: AttributeMap = {
            ...Account.unsafeEncode(plain),
            type: { S: 'RETIRED_TIER' },
        }
        expect(() => Account.unsafeDecode(rogue)).toThrow(
            /is not a variant of 'type'/,
        )
    })

    it('refuses an item with no discriminator at all', () => {
        const { type: _gone, ...headless } = Account.unsafeEncode(plain)
        expect(() => Account.unsafeDecode(headless)).toThrow(
            /'type' chooses the variant/,
        )
    })

    it('refuses a discriminator carried as something other than S or N', () => {
        const wrong: AttributeMap = {
            ...Account.unsafeEncode(plain),
            type: { BOOL: true },
        }
        expect(() => Account.unsafeDecode(wrong)).toThrow(
            /must be carried as 'S' or 'N'/,
        )
    })

    it('still enforces required attributes inside a variant', () => {
        const { balance: _missing, ...partial } = Account.unsafeEncode(plain)
        expect(() => Account.unsafeDecode(partial)).toThrow(CodecError)
    })
})

describe('the law, over generated values', () => {
    it('decode ∘ encode = id for Account', () => {
        checkRoundTrip(Account, { count: 300, seed: 20260826 })
    })

    it('and the encode paths agree, per variant', () => {
        // a variant codec has no `field`, so each variant is checked as the item codec it is
        checkEncodePaths(Account.variant('OWNER'), { seed: 20260826 })
        checkEncodePaths(Account.variant('STAFF'), {
            seed: 20260826,
        })
    })
})
