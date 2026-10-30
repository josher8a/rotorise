/**
 * A key attribute is `S`, `N` or `B`, and the key of one attribute takes the member of that attribute.
 *
 * A key attribute of DynamoDB is `S`, `N` or `B`. A composite key joins its parts, so it is `S`. A
 * key of one attribute copies the value of that attribute, so a number is `N`, a `Uint8Array` is
 * `B`, and an `N` sort key
 * orders by number where an `S` key orders `10` before `9`. Every path that writes a row writes the
 * same member: `toItem`, `keys` and `keyUpdates`. `null` gives no key, as `undefined` does, in every
 * path. A key value that the store refuses is refused, and the refusal names the key and never the
 * value.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import type { Attribute } from '../../attribute'
import { binary, nullable, number, string } from '../../codec'

/** What a consumer writes: the narrowing of a result. */
const isError = (value: unknown): value is Error => value instanceof Error

type Pet =
    | { petId: string; status: 'ADOPTED'; owner: string | null; age: number }
    | { petId: string; status: 'AVAILABLE'; shelter: string; age: number }

const Pets = tableEntry<Pet>()({
    PK: ['petId'],
    GSI1SK: 'age',
    GSI2PK: {
        discriminator: 'status',
        spec: { ADOPTED: 'owner', AVAILABLE: ['shelter'] },
    },
})

type Litter = { litterId: string; born: number; name: string }

const Litters = tableEntry<Litter>()(
    { PK: ['litterId'], GSI1SK: 'born' },
    { codec: { litterId: string, born: number, name: string } },
)

describe('a key of one number attribute is N in every path that writes a row', () => {
    it('toItem writes N, and the composite key stays S', () => {
        const written = Litters.toItem({ litterId: 'l1', born: 9, name: 'a' })
        if (isError(written)) return expect.unreachable()
        expect(written.GSI1SK).toEqual({ N: '9' })
        expect(written.PK).toEqual({ S: 'LITTERID#l1' })
        expectTypeOf(written.GSI1SK).toEqualTypeOf<Attribute<'N'>>()
        expectTypeOf(written.PK).toEqualTypeOf<Attribute<'S'>>()
    })

    it('keyUpdates sets N, the member that toItem writes', () => {
        expect(Litters.keyUpdates({ born: 10 }).set).toEqual({
            GSI1SK: { N: '10' },
        })
    })

    it('keys writes N', () => {
        expect(Pets.keys(['GSI1SK'], { age: 3 })).toEqual({
            GSI1SK: { N: '3' },
        })
    })

    it('toEntry writes the number, which a marshaller writes as N', () => {
        expect(
            Pets.toEntry({
                petId: 'p1',
                status: 'AVAILABLE',
                shelter: 's1',
                age: 3,
            }).GSI1SK,
        ).toBe(3)
    })
})

describe('null gives no key in every path, as undefined does', () => {
    const adopted = {
        petId: 'p1',
        status: 'ADOPTED',
        owner: null,
        age: 3,
    } as const

    it('key gives no key for a null attribute arm', () => {
        expect(Pets.key('GSI2PK', adopted)).toBeUndefined()
    })

    it('toEntry omits the key of a null attribute arm', () => {
        expect(Pets.toEntry(adopted)).not.toHaveProperty('GSI2PK')
    })

    it('keyUpdates removes the key of a null attribute arm', () => {
        expect(Pets.keyUpdates({ status: 'ADOPTED', owner: null })).toEqual({
            set: {},
            remove: ['GSI2PK'],
        })
    })

    it('toItem omits the key of a null attribute arm', () => {
        type Owned = { petId: string; owner: string | null }
        const Owned = tableEntry<Owned>()(
            { PK: ['petId'], GSI1PK: 'owner' },
            { codec: { petId: string, owner: nullable(string) } },
        )
        const written = Owned.toItem({ petId: 'p1', owner: null })
        if (isError(written)) return expect.unreachable()
        expect(written).not.toHaveProperty('GSI1PK')
    })
})

describe('keys refuses a key that the attributes do not build', () => {
    it('refuses a key of a null attribute, and names the key', () => {
        expect(() => Pets.keys(['GSI2PK'], { status: 'ADOPTED' })).toThrow(
            "'GSI2PK' gives no key for these attributes",
        )
    })
})

describe('a key value that the store refuses is refused', () => {
    it('refuses a number that DynamoDB cannot store, and names the key and not the value', () => {
        const refusal = (() => {
            try {
                Pets.keys(['GSI1SK'], { age: Number.NaN })
            } catch (error) {
                return error
            }
        })()
        expect(refusal).toBeInstanceOf(RotoriseError)
        expect(String(refusal)).toContain("'GSI1SK'")
        expect(String(refusal)).not.toContain('NaN')
    })
})

type Tag = { tagId: Uint8Array; petId: string; nick: string }

const Tags = tableEntry<Tag>()(
    { PK: 'tagId', SK: 'nick' },
    { codec: { tagId: binary, petId: string, nick: string } },
)

describe('a key of one Uint8Array attribute is B in every path that writes a row', () => {
    const tagId = new Uint8Array([1, 2, 3])

    it('toItem writes B', () => {
        const written = Tags.toItem({ tagId, petId: 'p1', nick: 'Rex' })
        if (isError(written)) return expect.unreachable()
        expect(written.PK).toEqual({ B: tagId })
        expectTypeOf(written.PK).toEqualTypeOf<Attribute<'B'>>()
    })

    it('keys writes B', () => {
        expect(Tags.keys(['PK', 'SK'], { tagId, nick: 'Rex' })).toEqual({
            PK: { B: tagId },
            SK: { S: 'Rex' },
        })
    })

    it('a key with no codec writes B for a Uint8Array', () => {
        const Chips = tableEntry<{ chip: Uint8Array }>()({ GSI1PK: 'chip' })
        expect(Chips.keys(['GSI1PK'], { chip: tagId })).toEqual({
            GSI1PK: { B: tagId },
        })
    })
})

describe('DynamoDB refuses an empty key value, so the run time refuses it', () => {
    it('refuses an empty string key, and names the key and not the value', () => {
        expect(() => Tags.keys(['SK'], { nick: '' })).toThrow(
            "'SK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('refuses an empty Uint8Array key', () => {
        expect(() => Tags.keys(['PK'], { tagId: new Uint8Array() })).toThrow(
            "'PK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('keyUpdates refuses an empty key, where the update writes a key that DynamoDB refuses', () => {
        expect(() => Tags.keyUpdates({ nick: '' })).toThrow(
            "'SK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('toItem refuses an empty key, where the item has no key that DynamoDB stores', () => {
        expect(() =>
            Tags.toItem({ tagId: new Uint8Array([1]), petId: 'p1', nick: '' }),
        ).toThrow(RotoriseError)
    })
})
