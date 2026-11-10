/**
 * The type of a key prints the text that the run time prints.
 *
 * A component prints the stored text of its attribute. A field under `refine` prints through the
 * refinement, a field under the adapter of a caller prints the stored literal, a `DynamoNumber`
 * prints its digits, and a variant under a tag prints the stored text of the variant that the call
 * names.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { DynamoNumber } from '../../attribute'
import {
    discriminatedUnion,
    held,
    item,
    object,
    refine,
    string,
} from '../../codec'
import { dynamoNumber } from '../../prisms'
import { orThrow } from '../../result'
import type { StandardSchemaV1 } from '../../standard'

const bool: StandardSchemaV1<boolean> = {
    '~standard': {
        version: 1,
        vendor: 'test',
        validate: (v) =>
            typeof v === 'boolean'
                ? { value: v }
                : { issues: [{ message: 'no' }] },
    },
}
const Adopted = held(string('Y', 'N'), bool, {
    encode: (b: boolean) => (b ? 'Y' : 'N'),
    decode: (s: string) => s === 'Y',
})
const DogTag = held(string('D'), string('dog'), {
    encode: (_: 'dog') => 'D' as const,
    decode: (_: 'D') => 'dog' as const,
})
type Dog = { kind: 'dog'; petId: string; adopted: boolean }
type Cat = { kind: 'cat'; petId: string; adopted: boolean }
const codec = item(
    discriminatedUnion('kind', [
        object({ kind: DogTag, petId: string, adopted: Adopted }),
        object({ kind: string('cat'), petId: string, adopted: Adopted }),
    ]),
)

describe('a component under a refine prints the text of its field', () => {
    type Pet = { petId: string; name: string }
    const isPetId = (v: string): v is string => v.length > 0

    it('prints the string, where the refinement is over a string', () => {
        const Pets = tableEntry<Pet>()(
            { PK: ['petId'] },
            { codec: { petId: refine(string, isPetId), name: string } },
        )
        const key = Pets.key('PK', { petId: 'p1' })
        expect(key).toBe('PETID#p1')
        expectTypeOf(key).toEqualTypeOf<'PETID#p1'>()
        // `fromEntry` drops each key attribute, whatever its text
        expect(
            Pets.fromEntry({ petId: 'p1', name: 'a', PK: 'PETID#zz' }),
        ).toEqual({ petId: 'p1', name: 'a' })
    })

    it('prints the stored literal, where the refinement is over the adapter of a caller', () => {
        const Pets = tableEntry<{ petId: string; kind: 'dog' }>()(
            { PK: ['petId'], SK: ['kind'] },
            {
                codec: {
                    petId: string,
                    kind: refine(DogTag, (_: 'dog'): _ is 'dog' => true),
                },
            },
        )
        expect(Pets.key('SK', { kind: 'dog' })).toBe('KIND#D')
        expectTypeOf(Pets.key('SK', { kind: 'dog' })).toEqualTypeOf<'KIND#D'>()
    })
})

describe('a variant under a tag prints the stored text of the variant that the call names', () => {
    it('prints the literal of the cat and the stored literal of the dog, in a key of one attribute', () => {
        const Pets = tableEntry<Dog | Cat>()(
            { PK: ['petId'], SK: 'kind' },
            { codec },
        )
        const cat = Pets.key('SK', { kind: 'cat' })
        expect(cat).toBe('cat')
        expectTypeOf(cat).toEqualTypeOf<'cat'>()
        const dog = Pets.key('SK', { kind: 'dog' })
        expect(dog).toBe('D')
        expectTypeOf(dog).toEqualTypeOf<'D'>()
    })

    it('prints the stored literal of the dog in a composite key', () => {
        const Pets = tableEntry<Dog | Cat>()(
            { PK: ['petId'], SK: ['kind'] },
            { codec },
        )
        expect(Pets.key('SK', { kind: 'dog' })).toBe('KIND#D')
        expectTypeOf(Pets.key('SK', { kind: 'dog' })).toEqualTypeOf<'KIND#D'>()
        expectTypeOf(
            Pets.key('SK', { kind: 'cat' }),
        ).toEqualTypeOf<'KIND#cat'>()
    })

    it('stays the union of the variants where the call names an attribute that both variants declare', () => {
        const Adoption = tableEntry<Dog | Cat>()(
            { PK: ['petId'], SK: ['adopted'] },
            { codec },
        )
        expectTypeOf(Adoption.key('SK', { adopted: true })).toEqualTypeOf<
            'ADOPTED#Y' | 'ADOPTED#N'
        >()
        expect(Adoption.key('SK', { adopted: true })).toBe('ADOPTED#Y')
    })
})

describe('a DynamoNumber component prints its digits', () => {
    it('prints the digits that the run time prints, and the type is a text', () => {
        const Prices = tableEntry<{ id: string; price: DynamoNumber }>()(
            { PK: ['id'], SK: ['price'] },
            { codec: { id: string, price: dynamoNumber } },
        )
        const key = Prices.key('SK', {
            price: orThrow(DynamoNumber.from('1.5')),
        })
        expect(key).toBe('PRICE#1.5')
        expectTypeOf(key).toEqualTypeOf<`PRICE#${string}`>()
    })
})
