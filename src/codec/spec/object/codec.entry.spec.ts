/**
 * Codecs declared where the schema is.
 *
 * A typical repository file carries a handful of marshaller calls, a cast per read, and a
 * hand-written `getKeys` — every one of them `tableEntry` and a codec each doing half the job.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { decimal, optional, string } from '../../codec'
import {
    checkEncodePaths,
    checkMembersStable,
    checkRoundTrip,
} from '../../testing'

type Pet = {
    /** Every entity in this table carries a literal TAG discriminant. */
    TAG: 'PET'
    userId: string
    salt: string
    balance: string
    status: 'ACTIVE' | 'CLOSED'
    closedAt?: string
}

const Pet = tableEntry<Pet>()(
    { PK: ['userId'], SK: ['TAG', 'salt'] },
    {
        codec: {
            TAG: string('PET'),
            userId: string,
            salt: string,
            balance: decimal,
            status: string('ACTIVE', 'CLOSED'),
            closedAt: optional(string),
        },
    },
)

const pet: Pet = {
    TAG: 'PET',
    userId: 'u1',
    salt: 's1',
    balance: '10.5',
    status: 'ACTIVE',
}

describe('tableEntry with a codec', () => {
    it('computes the keys and encodes them without them being declared', () => {
        const item = Pet.unsafeToItem(pet)
        // key codecs are derived: a composite key is always a string
        expect(item.PK).toEqual({ S: 'USERID#u1' })
        expect(item.SK).toEqual({ S: 'TAG#PET#SALT#s1' })
        // and the entity's own attributes are encoded by the spec
        expect(item.balance).toEqual({ N: '10.5' })
        expect(item.status).toEqual({ S: 'ACTIVE' })
    })

    it('reads the entity back with no cast, and without the keys', () => {
        const back: Pet = Pet.unsafeFromItem(Pet.unsafeToItem(pet))
        expect(back).toEqual(pet)
        // fromEntry existed to *delete* the keys; fromItem never reads them
        expect(back).not.toHaveProperty('PK')
        expect(back).not.toHaveProperty('SK')
    })

    it('builds an encoded Key, replacing getKeys', () => {
        expect(
            Pet.keys(['PK', 'SK'], {
                userId: 'u1',
                TAG: 'PET',
                salt: 's1',
            }),
        ).toEqual({
            PK: { S: 'USERID#u1' },
            SK: { S: 'TAG#PET#SALT#s1' },
        })
    })

    it('encodes only what it is given', () => {
        expect(
            Pet.codec.unsafeEncodePartial({
                status: 'CLOSED',
                closedAt: 'now',
            }),
        ).toEqual({
            status: { S: 'CLOSED' },
            closedAt: { S: 'now' },
        })
    })

    it('still exposes the plain entry API', () => {
        expect(Pet.toEntry(pet).PK).toBe('USERID#u1')
        expect(Pet.key('PK', { userId: 'u9' })).toBe('USERID#u9')
    })

    it('omits the codec methods when no spec is given', () => {
        const plain = tableEntry<Pet>()({ PK: ['userId'], SK: ['salt'] })
        expect(plain).not.toHaveProperty('toItem')
        // @ts-expect-error toItem is not on the type either
        expect(plain.toItem).toBeUndefined()
    })

    /**
     * The shape this argument has always had, unchanged: a bare string is the separator.
     *
     * Adding the codec as a *second positional* would have cost this — every caller passing a
     * separator would have had to pass `undefined` before it — which is why it is a named slot.
     */
    it('keeps the separator working as a bare second argument', () => {
        const dashed = tableEntry<Pet>()({ PK: ['userId'], SK: ['salt'] }, '-')
        expect(dashed.toEntry(pet).PK).toBe('USERID-u1')
    })

    it('takes the separator alongside a codec, and beside one', () => {
        const dashed = tableEntry<Pet>()(
            { PK: ['userId'], SK: ['salt'] },
            { codec: Pet.codec, separator: '-' },
        )
        expect(dashed.toEntry(pet).PK).toBe('USERID-u1')
        expect(dashed.unsafeToItem(pet).PK).toEqual({ S: 'USERID-u1' })

        const sepOnly = tableEntry<Pet>()(
            { PK: ['userId'], SK: ['salt'] },
            { separator: '-' },
        )
        expect(sepOnly.toEntry(pet).PK).toBe('USERID-u1')
    })

    /**
     * Why the codec is a named slot and not a second positional union member.
     *
     * A parameter typed `Separator | CodecSpec` gives the two one inference site, and TypeScript
     * then infers a `CodecSpec` from the separator string — so `toItem` and `codec` appear on the
     * type while the implementation never built them, and calling one is a `TypeError` that
     * compiled. Nothing else in the suite notices: every test passes with that signature in place.
     * Two properties are two inference sites, and these are the assertions that say so.
     */
    it('does not invent a codec from the separator', () => {
        const dashed = tableEntry<Pet>()({ PK: ['userId'], SK: ['salt'] }, '-')
        expect(dashed).not.toHaveProperty('toItem')
        expect(dashed).not.toHaveProperty('codec')
        // @ts-expect-error a separator is not a codec, so there is nothing to encode an item with
        expect(dashed.toItem).toBeUndefined()
        // @ts-expect-error nor anything to read one with
        expect(dashed.codec).toBeUndefined()

        const sepOnly = tableEntry<Pet>()(
            { PK: ['userId'], SK: ['salt'] },
            { separator: '-' },
        )
        // @ts-expect-error naming the separator is still not giving a codec
        expect(sepOnly.toItem).toBeUndefined()
    })
})

describe('the law, over generated pets', () => {
    it('decode ∘ encode = id for the entity attributes', () => {
        // `Pet.codec` is the attribute half; keys are computed by the schema, not generated
        checkRoundTrip(Pet.codec, { count: 300, seed: 20260826 })
    })
    it('and the three encode paths agree', () => {
        checkEncodePaths(Pet.codec, { count: 200, seed: 20260826 })
    })

    it('and a read-modify-write preserves every member, keys included', () => {
        checkMembersStable(
            {
                unsafeEncode: Pet.unsafeToItem,
                unsafeDecode: Pet.unsafeFromItem,
            },
            [Pet.unsafeToItem(pet)],
        )
    })
})

describe('the separator of an entry with object options', () => {
    it('joins with the default at run time, and the type reads the separator as string', () => {
        // pins a known defect: object options widen the separator to string, so the type of a
        // composite key is wider than its value. A fix makes this assertion fail
        const Pets = tableEntry<{ petId: string }>()(
            { PK: ['petId'] },
            { codec: { petId: string } },
        )
        const entry = Pets.toEntry({ petId: 'p1' } as const)
        expect(entry.PK).toBe('PETID#p1')
        expectTypeOf(entry.PK).toEqualTypeOf<`PETID${string}p1`>()
    })
})
