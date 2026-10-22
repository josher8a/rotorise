/**
 * Unions of objects: an entity that needs a discriminator for its *keys* in `tableEntry` needs one
 * for its attributes too, and should spell it the same way in both places.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from '../../attribute'
import {
    at,
    CodecError,
    decimal,
    discriminatedUnion,
    item,
    narrow,
    number,
    object,
    optional,
    string,
} from '../../codec'
import { checkEncodePaths, checkRoundTrip } from '../../testing'

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

const Owner = object({
    type: string('OWNER'),
    userId: string,
    profileId: string,
    balance: decimal,
})

const Staff = object({
    type: string('STAFF'),
    userId: string,
    profileId: string,
    branchId: string,
    weight: number,
    note: optional(string),
})

const AccountCodec = discriminatedUnion('type', [Owner, Staff])
const Account = item(AccountCodec)

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

    it('writes an attribute with the codec of the variant that the clause keeps', () => {
        const Holder = item(object({ account: AccountCodec }))
        expect(
            at(
                narrow(
                    at(Holder, ['account']),
                    object({ type: string('STAFF') }),
                ),
                ['weight'],
            ).unsafeEncode(7),
        ).toEqual({
            N: '7',
        })
        expect(
            at(
                narrow(
                    at(Holder, ['account']),
                    object({ type: string('OWNER') }),
                ),
                ['balance'],
            ).unsafeEncode('1.5'),
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
        ).toThrow(CodecError)
    })

    it('refuses an item whose discriminator names no variant', () => {
        const rogue: AttributeMap = {
            ...Account.unsafeEncode(plain),
            type: { S: 'RETIRED_TIER' },
        }
        expect(() => Account.unsafeDecode(rogue)).toThrow(CodecError)
    })

    it('refuses an item with no discriminator at all', () => {
        const { type: _gone, ...headless } = Account.unsafeEncode(plain)
        expect(() => Account.unsafeDecode(headless)).toThrow(CodecError)
    })

    it('refuses a discriminator carried as something other than S or N', () => {
        const wrong: AttributeMap = {
            ...Account.unsafeEncode(plain),
            type: { BOOL: true },
        }
        expect(() => Account.unsafeDecode(wrong)).toThrow(CodecError)
    })

    it('still enforces required attributes inside a variant', () => {
        const { balance: _missing, ...partial } = Account.unsafeEncode(plain)
        expect(() => Account.unsafeDecode(partial)).toThrow(CodecError)
    })

    /**
     * **Every variant is an object, and this is the refusal that makes it so.**
     *
     * `taggedItemSem` reads each variant's term and takes its item pair, which exists only for an
     * `attributes` term. It is entitled to that because the declaration refuses anything else: an
     * option with no object `spec` has no attribute naming the discriminator, so there is no tag to
     * select on. The refusal was in the code and in no test, and a gate
     * with no test beside it reads as a gate nobody migrated.
     *
     * Asserted at the *declaration* rather than at a read, which is the whole point: a union built
     * from a bare codec cannot be used at all, rather than failing on the first item that reaches it.
     *
     * **Reached past a cast, deliberately.** `EveryOptionTagged` refuses both of these in the
     * *type*, landing on the option that is wrong, and that is the gate a caller meets. The cast is
     * how this test gets to the second one. Both are needed and neither is redundant: a cast defeats
     * the type and nothing defeats the throw, which is why `taggedItemSem` may take every variant's
     * item pair without asking again.
     */
    const past = <T>(options: T) => options as never

    it('refuses an option that is not an object codec, at the declaration', () => {
        const bare = past([
            object({ type: string('OWNER'), balance: decimal }),
            // a bare codec: no `spec`, so no attribute names the discriminator
            string,
        ])
        expect(() => discriminatedUnion('type', bare)).toThrow(CodecError)
        expect(() => discriminatedUnion('type', bare)).toThrow(
            /every option must be an object codec/,
        )
    })

    /**
     * The other half of the same guarantee: an object option that does not *name* the discriminator
     * with a literal is refused too, so a variant's term always carries the tag the lookup reads.
     */
    it('refuses an object option that does not name the discriminator with a literal', () => {
        const untagged = past([
            object({ type: string('OWNER'), balance: decimal }),
            // `type` is a plain string here, so it names no single variant
            object({ type: string, weight: number }),
        ])
        expect(() => discriminatedUnion('type', untagged)).toThrow(
            /must name 'type' with a literal/,
        )
    })
})

describe('the law, over generated values', () => {
    it('decode ∘ encode = id for Account', () => {
        checkRoundTrip(Account, { count: 300, seed: 20260826 })
    })

    it('and the encode paths agree, per variant', () => {
        // a tagged codec has no `field`, so each variant is checked through the object codec
        // that declares the variant
        checkEncodePaths(item(Owner), { seed: 20260826 })
        checkEncodePaths(item(Staff), {
            seed: 20260826,
        })
    })
})
