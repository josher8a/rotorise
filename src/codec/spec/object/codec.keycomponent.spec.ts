/**
 * A component of a key is the stored text of its attribute.
 *
 * A key prints each component. An object has no text of its own, so two objects print one text and
 * two items share one key. An entry with no codec refuses an object component in the type and at run
 * time, at a name, at a path, and in each arm of a match. An entry with a codec prints the text or
 * the digits that the codec writes. The entry refuses a component that the codec writes as another
 * member, and an object at a path, in the type and at construction or at the key.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import { array, held, number, object, string } from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

type Walk = { id: string; n: number; at: Date; blob: Uint8Array }
type Owner = { id: string; owner: { name: string; born: Date } }
type Dog = { id: string; kind: 'dog'; bark: string }
type Cat = { id: string; kind: 'cat'; born: Date }

const day: StandardSchemaV1<Date> = {
    '~standard': {
        version: 1,
        vendor: 'test',
        validate: (v) =>
            v instanceof Date
                ? { value: v }
                : { issues: [{ message: 'not a Date' }] },
    },
}
const Born = held(string, day, {
    encode: (d: Date) => d.toISOString(),
    decode: (s: string) => new Date(s),
})

describe('a key component with no codec', () => {
    it('accepts text and a number, and refuses an object in the type and at run time', () => {
        const Plain = tableEntry<Walk>()({ PK: ['id'], SK: ['id', 'n'] })
        expect(Plain.keys(['SK'], { id: 'a', n: 1 } as Walk)).toEqual({
            SK: { S: 'ID#a#N#1' },
        })
        const Dated = tableEntry<Walk>()({
            PK: ['id'],
            // @ts-expect-error a Date has no text of its own
            SK: ['at'],
        })
        expect(() => Dated.keys(['SK'], { at: new Date(0) } as Walk)).toThrow(
            RotoriseError,
        )
        tableEntry<Walk>()({
            PK: ['id'],
            // @ts-expect-error bytes have no text of their own
            SK: ['blob'],
        })
    })

    it('refuses an object at a path, and accepts text at a path', () => {
        const Born_ = tableEntry<Owner>()({
            PK: ['id'],
            // @ts-expect-error a Date at a path has no text of its own
            SK: ['owner.born'],
        })
        expect(() =>
            Born_.key('SK', {
                owner: { name: 'a', born: new Date(0) },
            } as never),
        ).toThrow(/is an object/)
        const Named = tableEntry<Owner>()({ PK: ['id'], SK: ['owner.name'] })
        expect(Named.key('SK', { owner: { name: 'Rex' } })).toBe('NAME#Rex')
    })

    it('refuses an object in an arm of a match, and in an arm of the cases form', () => {
        tableEntry<Dog | Cat>()({
            PK: ['id'],
            SK: {
                discriminator: 'kind',
                spec: {
                    dog: ['bark'],
                    // @ts-expect-error a Date has no text of its own
                    cat: ['born'],
                },
            },
        })
        tableEntry<Dog | Cat>()({
            PK: ['id'],
            SK: {
                discriminator: 'kind',
                cases: [
                    [['dog'], ['bark']],
                    // @ts-expect-error a Date has no text of its own
                    [['cat'], ['born']],
                ],
            },
        })
    })
})

describe('a key component with a codec', () => {
    it('refuses at construction a component that the codec writes as another member', () => {
        expect(() =>
            tableEntry<{ id: string; tags: readonly string[] }>()(
                // @ts-expect-error the codec writes the list as L, and a component is S or N
                { PK: ['id'], SK: ['tags'] },
                { codec: { id: string, tags: array(string) } },
            ),
        ).toThrow(/as a component/)
    })

    it('accepts a component that the codec writes as S or N', () => {
        const Aged = tableEntry<{ id: string; age: number }>()(
            { PK: ['id'], SK: ['age'] },
            { codec: { id: string, age: number } },
        )
        expect(Aged.key('SK', { age: 3 })).toBe('AGE#3')
    })

    it('refuses an object at a path, where the codec prints the raw value', () => {
        tableEntry<Owner>()(
            // @ts-expect-error a Date at a path has no text of its own
            { PK: ['id'], SK: ['owner.born'] },
            {
                codec: {
                    id: string,
                    owner: object({ name: string, born: Born }),
                },
            },
        )
    })

    it('refuses a list in an arm of a match', () => {
        type Kennel = {
            id: string
            kind: 'big' | 'small'
            tags: readonly string[]
        }
        expect(() =>
            tableEntry<Kennel>()(
                {
                    PK: ['id'],
                    SK: {
                        discriminator: 'kind',
                        spec: {
                            big: ['id'],
                            // @ts-expect-error the codec writes the list as L
                            small: ['tags'],
                        },
                    },
                },
                {
                    codec: {
                        id: string,
                        kind: string('big', 'small'),
                        tags: array(string),
                    },
                },
            ),
        ).toThrow(/as a component/)
    })
})
