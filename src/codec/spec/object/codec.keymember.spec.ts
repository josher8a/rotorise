/**
 * A key has one stored member, and every write of the key stores that member.
 *
 * The model gives one member to a key name. The host decides the member at construction from the
 * codec, so `toItem`, `keys` and `keyUpdates` write the key under one member, and a match whose arms
 * store the key as two members is refused where the entry is built.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    decimal,
    discriminatedUnion,
    item,
    number,
    object,
    string,
} from '../../codec'

const isError = (value: unknown): value is Error => value instanceof Error

type Listing = { price: 12.5 | 9; weight: string; petId: string }

const Listings = tableEntry<Listing>()(
    { PK: 'weight', SK: ['petId'] },
    {
        codec: item(
            discriminatedUnion('price', [
                object({ price: number(12.5), weight: decimal, petId: string }),
                object({ price: number(9), weight: decimal, petId: string }),
            ]),
        ),
    },
)

describe('a key has one stored member in every write', () => {
    it('stores an N key in toItem, keys and keyUpdates, where the item names no variant', () => {
        const written = Listings.toItem({
            price: 12.5,
            weight: '1.5',
            petId: 'p1',
        })
        if (isError(written)) return expect.unreachable()
        expect(written.PK).toEqual({ N: '1.5' })
        expect(Listings.keys(['PK'], { weight: '1.5' })).toEqual({
            PK: { N: '1.5' },
        })
        expect(Listings.keyUpdates({ weight: '1.5' }).set).toEqual({
            PK: { N: '1.5' },
        })
    })
})

describe('a match whose arms store the key as two members is refused', () => {
    type Pet = { kind: 'a' | 'b'; petId: string; age: number }
    const codec = item(
        discriminatedUnion('kind', [
            object({ kind: string('a'), petId: string, age: number }),
            object({ kind: string('b'), petId: string, age: number }),
        ]),
    )

    it('refuses at construction a list arm and a number arm', () => {
        expect(() =>
            tableEntry<Pet>()(
                {
                    PK: {
                        discriminator: 'kind',
                        // @ts-expect-error the type refuses a key that one arm stores as S and another as N
                        spec: { a: ['petId'], b: 'age' },
                    },
                },
                { codec },
            ),
        ).toThrow(/arms of a key give one member/)
    })

    it('refuses in the type a list arm and a number arm, where the entry has no codec', () => {
        tableEntry<Pet>()({
            PK: {
                discriminator: 'kind',
                // @ts-expect-error DynamoDB gives a key attribute one type, with a codec or without one
                spec: { a: ['petId'], b: 'age' },
            },
        })
    })
})
