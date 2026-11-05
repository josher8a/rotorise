/**
 * An attribute named like a member of `Object.prototype` is data like any other name.
 *
 * The names of an object codec are the own keys of its body, and a value at a name is an own
 * property of the item or of the value. `in` and a plain index read the prototype chain, so each
 * of them answers true for `constructor`, `toString` and `valueOf` at a record that holds none.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    discriminatedUnion,
    item as itemOf,
    number,
    object,
    optional,
    string,
} from '../../codec'

const loose = (codec: unknown) =>
    itemOf(codec as never) as unknown as {
        encode: (value: unknown) => unknown
        decode: (item: unknown) => unknown
    }

const inherited = ['constructor', 'toString', 'valueOf'] as const

describe('an attribute named like a member of Object.prototype is data like any other name', () => {
    describe.each(inherited)('the name %s', (name) => {
        it('is written by the open entry of a pet', () => {
            const Pet = loose(object([string, optional(string)]))
            expect(Pet.encode({ [name]: 'Rex' })).toEqual({
                [name]: { S: 'Rex' },
            })
        })

        it('is refused on decode as an undeclared name of a closed pet', () => {
            const Pet = loose(object({ petId: string }))
            expect(
                Pet.decode({ petId: { S: '1' }, [name]: { S: '2' } }),
            ).toBeInstanceOf(Error)
        })

        it('is absent from a pet that declares it optional and holds none', () => {
            const Pet = loose(object({ [name]: optional(string) }))
            expect(Pet.encode({})).toEqual({})
            expect(Pet.decode({})).toEqual({})
        })

        it('is written and read when a pet declares it optional and holds one', () => {
            const Pet = loose(object({ [name]: optional(string) }))
            expect(Pet.encode({ [name]: 'Rex' })).toEqual({
                [name]: { S: 'Rex' },
            })
            expect(Pet.decode({ [name]: { S: 'Rex' } })).toEqual({
                [name]: 'Rex',
            })
        })
    })

    it('rewrites an index key built from valueOf when the change names valueOf', () => {
        const Pets = tableEntry<{ petId: string; valueOf: string }>()({
            PK: ['petId'],
            GSI1PK: ['valueOf'],
        } as never) as unknown as {
            keyUpdates: (change: Record<string, unknown>) => unknown
        }
        expect(Pets.keyUpdates({ valueOf: 'x' })).toEqual({
            set: { GSI1PK: { S: 'VALUEOF#x' } },
            remove: [],
        })
    })

    it('names no variant for an item that holds no tag, whatever the tag is called', () => {
        const Pet = discriminatedUnion('valueOf', [
            object({ valueOf: string('dog'), age: number }),
        ])
        expect(loose(Pet).decode({ age: { N: '3' } })).toBeInstanceOf(Error)
    })
})
