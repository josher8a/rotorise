/**
 * A key update removes the key of a `null` arm.
 *
 * The key part of a row is a function from a key name to an optional string: a `null` arm gives no
 * key. A key update is that function at the keys that the change touches. A map of `SET` values
 * cannot remove an attribute, so the result has two parts, as the `SET` and `REMOVE` clauses of an
 * `UpdateExpression`. The key that `toEntry` writes for the merged item is in `set`. The key that
 * `toEntry` omits is in `remove`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Pet =
    | { petId: string; status: 'ADOPTED'; owner: string }
    | {
          petId: string
          status: 'AVAILABLE'
          species: 'CAT' | 'DOG'
          shelter: string
      }

const Pets = tableEntry<Pet>()({
    PK: ['petId'],
    GSI1PK: {
        discriminator: 'status',
        spec: { ADOPTED: null, AVAILABLE: ['shelter'] },
    },
    GSI2PK: {
        discriminator: 'status',
        spec: {
            ADOPTED: ['owner'],
            AVAILABLE: {
                discriminator: 'species',
                spec: { CAT: ['shelter'], DOG: null },
            },
        },
    },
    GSI3PK: ['petId'],
})

const adopted = { status: 'ADOPTED', owner: 'ann' } as const
const availableCat = {
    status: 'AVAILABLE',
    species: 'CAT',
    shelter: 's1',
} as const
const availableDog = {
    status: 'AVAILABLE',
    species: 'DOG',
    shelter: 's1',
} as const

describe('the change of a key that a `null` arm builds', () => {
    it('removes the key of a change into a `null` arm', () => {
        const update = Pets.keyUpdates(adopted)
        expect(update.remove).toEqual(['GSI1PK'])
        expect(update.set).toEqual({ GSI2PK: { S: 'OWNER#ann' } })
    })

    it('removes the key of a change into a `null` arm of a nested match', () => {
        const update = Pets.keyUpdates(availableDog)
        expect(update.remove).toEqual(['GSI2PK'])
        expect(update.set).toEqual({ GSI1PK: { S: 'SHELTER#s1' } })
    })

    it('sets the key of a change out of a `null` arm', () => {
        const update = Pets.keyUpdates(availableCat)
        expect(update.remove).toEqual([])
        expect(update.set).toEqual({
            GSI1PK: { S: 'SHELTER#s1' },
            GSI2PK: { S: 'SHELTER#s1' },
        })
    })

    it('leaves a key out of both parts when the change does not touch the key', () => {
        const update = Pets.keyUpdates(adopted)
        expect(update.set).not.toHaveProperty('GSI3PK')
        expect(update.remove).not.toContain('GSI3PK')
    })
})

/** The key part of the merged item, as `toEntry` writes it, against the two parts of the update. */
const expectAgreement = (
    update: { set: Record<string, unknown>; remove: readonly string[] },
    merged: Pet,
) => {
    const entry: Record<string, unknown> = Pets.toEntry(merged)
    for (const [name, value] of Object.entries(update.set)) {
        expect(value).toEqual({ S: entry[name] })
    }
    for (const name of update.remove) {
        expect(entry).not.toHaveProperty(name)
        expect(update.set).not.toHaveProperty(name)
    }
}

describe('the agreement of a key update with `toEntry`', () => {
    it('sets the key that toEntry writes, and removes the key that toEntry omits, for an adopted pet', () => {
        expectAgreement(Pets.keyUpdates(adopted), { petId: 'p1', ...adopted })
    })

    it('sets the key that toEntry writes, and removes the key that toEntry omits, for an available cat', () => {
        expectAgreement(Pets.keyUpdates(availableCat), {
            petId: 'p1',
            ...availableCat,
        })
    })

    it('sets the key that toEntry writes, and removes the key that toEntry omits, for an available dog', () => {
        expectAgreement(Pets.keyUpdates(availableDog), {
            petId: 'p1',
            ...availableDog,
        })
    })
})

type Nickname = { petId: string; nickname?: string | undefined }

const Nicknames = tableEntry<Nickname>()({
    PK: ['petId'],
    GSI1PK: 'nickname',
    GSI2PK: ['petId'],
})

describe('the change of a key that an attribute holds', () => {
    it('removes the key of a change that leaves the attribute undefined', () => {
        const update = Nicknames.keyUpdates({ nickname: undefined })
        expect(update).toEqual({ set: {}, remove: ['GSI1PK'] })
        const entry: Record<string, unknown> = Nicknames.toEntry({
            petId: 'p1',
            nickname: undefined,
        })
        expect(entry).not.toHaveProperty('GSI1PK')
    })
})

describe('the type of `remove`', () => {
    it('names the keys that an attribute holds, because the attribute can be absent', () => {
        const { remove } = Nicknames.keyUpdates({ nickname: 'rex' })
        expectTypeOf(remove).toEqualTypeOf<readonly 'GSI1PK'[]>()
    })

    it('names the keys whose spec reaches a `null` arm, and no other key', () => {
        const { remove } = Pets.keyUpdates(adopted)
        expectTypeOf(remove).toEqualTypeOf<readonly ('GSI1PK' | 'GSI2PK')[]>()
    })
})

describe('the type of an entry holds a key that builds no value as optional', () => {
    const rowOf = (pet: Pet) => Pets.toEntry(pet)
    const adoptedPet = { petId: 'p1', ...adopted } as const
    const dogPet = { petId: 'p1', ...availableDog } as const

    it('is absent from the row, so the type holds the key as optional for a member that can build it', () => {
        const read = (row: ReturnType<typeof rowOf>) => {
            // @ts-expect-error the row of an adopted pet holds no GSI1PK, so the key can be absent
            const text: string = row.GSI1PK
            return text
        }
        expect(typeof read).toBe('function')
        expect(rowOf(adoptedPet)).not.toHaveProperty('GSI1PK')
        expect(rowOf({ petId: 'p1', ...availableCat })).toHaveProperty(
            'GSI1PK',
            'SHELTER#s1',
        )
    })

    it('holds the key as optional with no value for a member that builds no value', () => {
        const row = Pets.toEntry(adoptedPet)
        expectTypeOf(row.GSI1PK).toEqualTypeOf<undefined>()
        expect(row).not.toHaveProperty('GSI1PK')
    })

    it('gives the key that a null arm builds the type undefined, as the row holds no such key', () => {
        const key = Pets.key('GSI1PK', adoptedPet)
        expectTypeOf(key).toEqualTypeOf<undefined>()
        expect(key).toBeUndefined()
    })

    it('holds a key that each member builds as required, beside the optional key', () => {
        const row = Pets.toEntry(dogPet)
        expectTypeOf(row.GSI3PK).toEqualTypeOf<'PETID#p1'>()
        expectTypeOf(row.GSI2PK).toEqualTypeOf<undefined>()
        expect(row).toHaveProperty('GSI3PK', 'PETID#p1')
        expect(row).not.toHaveProperty('GSI2PK')
    })
})
