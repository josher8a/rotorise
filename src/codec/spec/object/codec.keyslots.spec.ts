/**
 * An entry holds the slots of each key component as a fact of the schema, and holds the segments of
 * a changed name as a fact of the name. Neither fact may change an answer.
 *
 * A tagged codec states its own literal at the discriminator, and the item names the variant. So the
 * slots of that component are a fact of the item, and one entry prints two variants one after the
 * other. A refusal of a name stays a refusal on each call, and a name that follows it still lands.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    CodecError,
    discriminatedUnion,
    item,
    number,
    object,
    string,
} from '../../codec'

type Dog = { kind: 'dog'; petId: string; bark: string }
type Cat = { kind: 'cat'; petId: string; bark: number }
const Animals = tableEntry<Dog | Cat>()(
    { PK: ['petId'], SK: ['kind'] },
    {
        codec: item(
            discriminatedUnion('kind', [
                object({ kind: string('dog'), petId: string, bark: string }),
                object({ kind: string('cat'), petId: string, bark: number }),
            ]),
        ),
    },
)

type Pet = { petId: string; note: string; owner: { name: string } }
const makePets = () =>
    tableEntry<Pet>()(
        { PK: ['petId'], GSI1PK: ['owner.name'] },
        {
            codec: {
                petId: string,
                note: string,
                owner: object({ name: string }),
            },
        },
    )
const Pets = makePets()

describe('the slots of a key component', () => {
    it('follow the variant of each item, whatever the order of the calls', () => {
        const dog: Dog = { kind: 'dog', petId: 'p', bark: 'woof' }
        const cat: Cat = { kind: 'cat', petId: 'p', bark: 3 }
        expect(Animals.unsafeKey('SK', dog)).toBe('KIND#dog')
        expect(Animals.unsafeKey('SK', cat)).toBe('KIND#cat')
        expect(Animals.unsafeKey('SK', dog)).toBe('KIND#dog')
        expect(Animals.unsafeToEntry(dog).SK).toBe('KIND#dog')
        expect(Animals.unsafeToEntry(cat).SK).toBe('KIND#cat')
        expect(Animals.unsafeToEntry(dog).SK).toBe('KIND#dog')
        expect(Animals.unsafeToEntry(cat).SK).toBe('KIND#cat')
    })
})

describe('the segments of a changed name', () => {
    it('give each name the landing that a new entry gives, in the order that the calls come', () => {
        const owner = Pets.unsafeKeyUpdates({ 'owner.name': 'x' })
        const pet = Pets.unsafeKeyUpdates({ petId: 'q' })
        expect(owner).toEqual(
            makePets().unsafeKeyUpdates({ 'owner.name': 'x' }),
        )
        expect(pet).toEqual(makePets().unsafeKeyUpdates({ petId: 'q' }))
        expect(owner).not.toEqual(pet)
        expect(Pets.unsafeKeyUpdates({ 'owner.name': 'x' })).toEqual(owner)
    })

    it('refuse a name that is no path on each call, and a name after it still lands', () => {
        const first = Pets.keyUpdates({ 'owner.': 'x' } as never)
        const second = Pets.keyUpdates({ 'owner.': 'x' } as never)
        expect(first).toBeInstanceOf(CodecError)
        expect(second).toBeInstanceOf(CodecError)
        expect((second as CodecError).message).toBe(
            (first as CodecError).message,
        )
        expect(Pets.unsafeKeyUpdates({ 'owner.name': 'y' })).toEqual(
            makePets().unsafeKeyUpdates({ 'owner.name': 'y' }),
        )
    })
})
