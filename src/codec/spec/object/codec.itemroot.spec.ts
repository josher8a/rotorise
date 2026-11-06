/**
 * The root of an item is an item reading, in the type and at run time: it writes a row and reads a
 * row. A clause at the root keeps the options that it does not separate, and the reading of the kept
 * options refuses a row of a dropped option, as a clause below an object does.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AttributeMap, StoredItem } from '../../attribute'
import {
    at,
    CodecError,
    discriminatedUnion,
    item,
    narrow,
    number,
    object,
    string,
    union,
} from '../../codec'

const Pets = discriminatedUnion('kind', [
    object({ kind: string('dog'), bark: string }),
    object({ kind: string('cat'), lives: number }),
    object({ kind: string('fox'), cunning: number }),
])
const row = (
    entity: Parameters<ReturnType<typeof item<typeof Pets>>['unsafeEncode']>[0],
) => item(Pets).unsafeEncode(entity)

describe('the root of an item writes a row and reads a row', () => {
    const root = at(item(Pets), [])

    it('types the row that it writes, and the row that it reads', () => {
        expectTypeOf(root.unsafeEncode).returns.toEqualTypeOf<AttributeMap>()
        expectTypeOf(root.decode).parameter(0).toEqualTypeOf<StoredItem>()
    })

    it('writes the row of the item reading, and reads it back', () => {
        const written = root.unsafeEncode({ kind: 'dog', bark: 'w' })
        expect(written).toEqual({ kind: { S: 'dog' }, bark: { S: 'w' } })
        expect(root.unsafeDecode(written)).toEqual({ kind: 'dog', bark: 'w' })
    })
})

describe('a clause at the root refuses the row of an option that it dropped', () => {
    it('refuses a row of a dropped option, and names the tag that the clause keeps', () => {
        const dogs = narrow(at(item(Pets), []), object({ kind: string('dog') }))
        const read = dogs.decode(row({ kind: 'cat', lives: 9 }))
        expect(read).toBeInstanceOf(CodecError)
        expect(String(read)).toMatch(/is not one of 'dog'/)
        expect(dogs.unsafeDecode(row({ kind: 'dog', bark: 'w' }))).toEqual({
            kind: 'dog',
            bark: 'w',
        })
    })

    it('reads the rows of each option that it keeps, and refuses the others', () => {
        const pets = narrow(
            at(item(Pets), []),
            object({ kind: string('dog', 'cat') }),
        )
        expect(pets.unsafeDecode(row({ kind: 'cat', lives: 9 }))).toEqual({
            kind: 'cat',
            lives: 9,
        })
        expect(pets.decode(row({ kind: 'fox', cunning: 1 }))).toBeInstanceOf(
            CodecError,
        )
    })
})

describe('a clause at the root of an attribute codec refuses the value of an option that it dropped', () => {
    const Beasts = union([
        object({ kind: string('dog'), bark: string }),
        object({ kind: string('cat'), lives: number }),
        object({ kind: string('fox'), cunning: number }),
    ])
    const stored = (kind: 'dog' | 'cat' | 'fox') =>
        ({
            dog: { M: { kind: { S: 'dog' }, bark: { S: 'w' } } },
            cat: { M: { kind: { S: 'cat' }, lives: { N: '9' } } },
            fox: { M: { kind: { S: 'fox' }, cunning: { N: '1' } } },
        })[kind]

    it('refuses an option that the clause dropped, and reads the one that it kept', () => {
        const dogs = narrow(at(Beasts, []), object({ kind: string('dog') }))
        expect(dogs.decode(stored('cat'))).toBeInstanceOf(CodecError)
        expect(dogs.unsafeDecode(stored('dog'))).toEqual({
            kind: 'dog',
            bark: 'w',
        })
    })

    it('reads each option that it kept, and refuses the others', () => {
        const some = narrow(
            at(Beasts, []),
            object({ kind: string('dog', 'cat') }),
        )
        expect(some.unsafeDecode(stored('cat'))).toEqual({
            kind: 'cat',
            lives: 9,
        })
        expect(some.decode(stored('fox'))).toBeInstanceOf(CodecError)
    })
})
