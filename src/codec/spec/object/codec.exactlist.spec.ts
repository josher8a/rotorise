/**
 * The type of an item and of a change compares the names of an element of a list.
 *
 * `toEntry` and `keyUpdates` refuse an extra name in an element of a list at run time, because the
 * codec refuses the element. The type states the same rule: an element of a list, of a readonly list,
 * of a tuple and of a list in a list holds the names of the shape, and no other. A list of a
 * primitive holds no name, so it stays accepted.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { array, CodecError, number, object, string } from '../../codec'

type Pet = {
    petId: string
    legs: readonly { readonly id: number }[]
    grid: readonly { readonly cell: readonly { readonly v: number }[] }[]
    tags: readonly string[]
}
const Coded = tableEntry<Pet>()(
    { PK: ['petId'] },
    {
        codec: {
            petId: string,
            legs: array(object({ id: number })),
            grid: array(object({ cell: array(object({ v: number })) })),
            tags: array(string),
        },
    },
)
const pet: Pet = {
    petId: 'p',
    legs: [{ id: 1 }],
    grid: [{ cell: [{ v: 1 }] }],
    tags: ['t'],
}

type Shapes = {
    petId: string
    ro: readonly { readonly id: number }[]
    pair: readonly [{ readonly id: number }, { readonly name: string }]
}
const Shaped = tableEntry<Shapes>()({ PK: ['petId'] })

const refusalOf = (given: unknown): CodecError => {
    expect(given).toBeInstanceOf(CodecError)
    return given as CodecError
}

describe('an extra name in an element of a list is refused at run time, as the type refuses it', () => {
    it('toEntry refuses an extra name in an element of a list, with the reason of the codec', () => {
        const refusal = refusalOf(
            Coded.toEntry({ ...pet, legs: [{ id: 1, ghost: 1 }] } as never),
        )
        expect(refusal.reason).toBe(
            "'ghost' is not an attribute this codec declares",
        )
        expect(refusal.message).toContain('legs[0]')
    })

    it('keyUpdates refuses an extra name in an element of a list, with the reason of the codec', () => {
        const refusal = refusalOf(
            Coded.keyUpdates({ legs: [{ id: 1, ghost: 1 }] } as never),
        )
        expect(refusal.reason).toBe(
            "'ghost' is not an attribute this codec declares",
        )
        expect(refusal.message).toContain('legs[0]')
    })

    it('refuses an extra name in an element of a list in a list, with the reason of the codec', () => {
        const refusal = refusalOf(
            Coded.keyUpdates({
                grid: [{ cell: [{ v: 1, ghost: 1 }] }],
            } as never),
        )
        expect(refusal.reason).toBe(
            "'ghost' is not an attribute this codec declares",
        )
    })

    it('accepts a list of a primitive, which holds no name to compare', () => {
        expect(Coded.unsafeToEntry({ ...pet, tags: ['a', 'b'] }).tags).toEqual([
            'a',
            'b',
        ])
        expect(Coded.unsafeKeyUpdates({ tags: ['a'] })).toEqual({
            set: {},
            remove: [],
        })
    })
})

describe('the type refuses an extra name in an element of a list', () => {
    it('refuses the name in a fresh literal, in a variable, in a list in a list, and in a readonly list', () => {
        const extra = { ...pet, legs: [{ id: 1, ghost: 1 }] }
        const refused = () => {
            Coded.toEntry({
                ...pet,
                // @ts-expect-error the element holds no name ghost
                legs: [{ id: 1, ghost: 1 }],
            })
            // @ts-expect-error the same name, read from a variable
            Coded.toEntry(extra)
            Coded.keyUpdates({
                // @ts-expect-error the element of the change holds no name ghost
                legs: [{ id: 1, ghost: 1 }],
            })
            Coded.keyUpdates({
                // @ts-expect-error the element of the list in the list holds no name ghost
                grid: [{ cell: [{ v: 1, ghost: 1 }] }],
            })
            Shaped.keyUpdates({
                // @ts-expect-error the element of a readonly list holds no name ghost
                ro: [{ id: 1, ghost: 1 }],
            })
        }
        expect(refused).toBeTypeOf('function')
    })

    it('refuses the name in an element of a tuple', () => {
        const refused = () => {
            Shaped.keyUpdates({
                pair: [
                    { id: 1 },
                    // @ts-expect-error the second element of the tuple holds no name ghost
                    { name: 'n', ghost: 1 },
                ],
            })
        }
        expect(refused).toBeTypeOf('function')
    })

    it('accepts a valid list, an empty list, a tuple, a list of a primitive and a list in a variable typed as the entity', () => {
        const typed: Pet['legs'] = [{ id: 1 }]
        const accepted = () => {
            Coded.toEntry(pet)
            Coded.toEntry({ ...pet, legs: [], grid: [], tags: [] })
            Coded.toEntry({ ...pet, legs: typed })
            Coded.keyUpdates({ legs: [{ id: 1 }], tags: ['a'] })
            Shaped.keyUpdates({ pair: [{ id: 1 }, { name: 'n' }] })
        }
        expect(accepted).toBeTypeOf('function')
    })
})
