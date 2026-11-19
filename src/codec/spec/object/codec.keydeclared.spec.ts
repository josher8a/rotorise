/**
 * A component of a key names an attribute that the codec declares.
 *
 * The run time gives an error value for each item of an entry whose key reads a name that the codec
 * declares no field of: the key cannot print the stored text. The construction refuses the schema
 * instead, with the refusal of a path that the codec cannot address. A codec with an open rest writes
 * any name, so it declares each name. An entry with no codec holds no fact about the names. The type
 * refuses the name too, so each call that reaches the refusal casts around the type. A name that can be
 * absent reaches a key through a record with a default, and a plain component refuses it.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'
import { discriminatedUnion, item, object, optional, string } from '../../codec'

type Pet = { id: string; note: string }
const codec = { id: string, note: string }
const refusal =
    'is a component of a key, and the codec declares no attribute of that name'

describe('a component of a key that the codec declares no attribute of is refused at construction', () => {
    it('refuses a name in a list of components, with the name and the reason', () => {
        expect(() =>
            tableEntry<Pet>()({ PK: ['id'], SK: ['ghost'] } as never, {
                codec,
            }),
        ).toThrow(RotoriseError)
        expect(() =>
            tableEntry<Pet>()({ PK: ['id'], SK: ['ghost'] } as never, {
                codec,
            }),
        ).toThrow(`'ghost' ${refusal}`)
    })

    it('refuses a key of one attribute that the codec does not declare', () => {
        expect(() =>
            tableEntry<Pet>()({ PK: ['id'], GSI1PK: 'ghost' } as never, {
                codec,
            }),
        ).toThrow(`'ghost' ${refusal}`)
    })

    it('refuses a component with a transform at a name that the codec does not declare', () => {
        expect(() =>
            tableEntry<Pet>()(
                {
                    PK: ['id'],
                    SK: [{ at: 'ghost', value: (v: string) => v }],
                } as never,
                { codec },
            ),
        ).toThrow(`'ghost' ${refusal}`)
    })
})

describe('a component of a key that the codec can write is accepted', () => {
    it('builds a key at a declared name, and gives the same entry as before', () => {
        const Declared = tableEntry<Pet>()(
            { PK: ['id'], SK: ['note'] },
            { codec },
        )
        expect(Declared.toEntry({ id: 'i', note: 'n' })).toMatchObject({
            PK: 'ID#i',
            SK: 'NOTE#n',
        })
    })

    it('builds a key at a name that only one variant of a tagged codec declares', () => {
        type Dog = { id: string; kind: 'dog'; bark: string }
        type Cat = { id: string; kind: 'cat'; lives: number }
        const Animals = tableEntry<Dog | Cat>()(
            { PK: ['id'], SK: ['bark'] } as never,
            {
                codec: item(
                    discriminatedUnion('kind', [
                        object({
                            kind: string('dog'),
                            id: string,
                            bark: string,
                        }),
                        object({ kind: string('cat'), id: string }),
                    ]),
                ),
            } as never,
        )
        expect(Animals).toBeDefined()
    })

    it('builds a key at any name where the codec holds an open rest', () => {
        const Open = tableEntry<Pet>()(
            { PK: ['id'], SK: ['extra'] } as never,
            {
                codec: item(object({ id: string }, [string, optional(string)])),
            } as never,
        )
        expect(Open).toBeDefined()
    })
})

describe('an entry with no codec holds no fact about the names', () => {
    it('builds the entry, and toEntry gives an error value for the item', () => {
        const Plain = tableEntry<Pet>()({ PK: ['id'], SK: ['ghost'] } as never)
        expect(Plain.toEntry({ id: 'i', note: 'n' })).toBeInstanceOf(CodecError)
    })
})

describe('a name that can be absent reaches a key through a record with a default', () => {
    type Opt = { id: string; note?: string }

    it('refuses the name as a plain component, and builds the default into the key', () => {
        const Plain = tableEntry<Opt>()({
            PK: ['id'],
            // @ts-expect-error the name can be absent, and a plain component has no value there
            SK: ['note'],
        })
        expect(Plain.toEntry({ id: 'i' })).toBeInstanceOf(CodecError)
        const Defaulted = tableEntry<Opt>()({
            PK: ['id'],
            SK: [{ at: 'note', default: 'NONE' }],
        })
        expect(Defaulted.toEntry({ id: 'i' })).toMatchObject({
            SK: 'NOTE#NONE',
        })
        expect(Defaulted.toEntry({ id: 'i', note: 'n' })).toMatchObject({
            SK: 'NOTE#n',
        })
    })
})
