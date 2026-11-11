/**
 * A component of a key is the stored text of its attribute.
 *
 * A key prints each component. An object has no text of its own, so two objects print one text and
 * two items share one key. An entry with no codec refuses an object component in the type and at run
 * time, at a name, at a path, and in each arm of a match. An entry with a codec prints the text or
 * the digits that the codec writes, at a name and at a path. The entry refuses a component that the
 * codec writes as another member, at a name and at a path, in the type and at construction.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import {
    array,
    boolean,
    discriminatedUnion,
    held,
    item,
    number,
    object,
    optional,
    refine,
    string,
} from '../../codec'
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

    it('prints the stored text of a held value at a path, as it does at a name', () => {
        const Held = tableEntry<Owner>()(
            { PK: ['id'], SK: ['owner.born'] },
            {
                codec: {
                    id: string,
                    owner: object({ name: string, born: Born }),
                },
            },
        )
        const born = new Date(0)
        const key = Held.key('SK', { owner: { born } })
        expectTypeOf(key).toEqualTypeOf<`BORN#${string}`>()
        expect(key).toBe('BORN#1970-01-01T00:00:00.000Z')
        const row = Held.unsafeToItem({ id: 'p1', owner: { name: 'a', born } })
        expect(row.SK).toEqual({ S: 'BORN#1970-01-01T00:00:00.000Z' })
    })

    it('refuses a path that the codec cannot address, in the type and at construction, and names the path', () => {
        type Noted = { id: string; meta: { note: string } }
        const Meta = refine(
            object({ note: string }),
            (value: {
                readonly note: string
            }): value is { readonly note: string } => value.note !== '',
        )
        const codec = { id: string, meta: Meta }
        const refused =
            /'meta\.note' is a component of a key, and the codec cannot address that path/
        expect(() =>
            tableEntry<Noted>()(
                // @ts-expect-error a path cannot go into refine
                { PK: ['id'], SK: ['meta.note'] },
                { codec },
            ),
        ).toThrow(refused)
        expect(() =>
            tableEntry<Noted>()(
                // @ts-expect-error a key of one attribute at a path is a component too, and a path cannot go into refine
                { PK: ['id'], SK: 'meta.note' },
                { codec },
            ),
        ).toThrow(refused)
    })

    it('refuses a path that the codec cannot address in an arm of a match, and in an arm of the cases form', () => {
        type Row =
            | { id: string; kind: 'dog'; meta: { note: string } }
            | { id: string; kind: 'cat'; meta: { note: string } }
        const Meta = refine(
            object({ note: string }),
            (value: {
                readonly note: string
            }): value is { readonly note: string } => value.note !== '',
        )
        const codec = item(
            discriminatedUnion('kind', [
                object({ id: string, kind: string('dog'), meta: Meta }),
                object({ id: string, kind: string('cat'), meta: Meta }),
            ]),
        )
        expect(() =>
            tableEntry<Row>()(
                {
                    PK: ['id'],
                    SK: {
                        discriminator: 'kind',
                        spec: {
                            // @ts-expect-error a path cannot go into refine
                            dog: ['meta.note'],
                            cat: ['id'],
                        },
                    },
                },
                { codec },
            ),
        ).toThrow(/'meta\.note' is a component of a key/)
        expect(() =>
            tableEntry<Row>()(
                {
                    PK: ['id'],
                    SK: {
                        discriminator: 'kind',
                        cases: [
                            // @ts-expect-error a path cannot go into refine
                            [['dog'], ['meta.note']],
                            [['cat'], ['id']],
                        ],
                    },
                },
                { codec },
            ),
        ).toThrow(/'meta\.note' is a component of a key/)
    })

    it('refuses a path below an adapter of a caller, in the type and at construction', () => {
        const noteSchema: StandardSchemaV1<{ readonly note: string }> = {
            '~standard': {
                version: 1,
                vendor: 'test',
                validate: (v) => ({ value: v as { readonly note: string } }),
            },
        }
        const wholeNote = held(object({ note: string }), noteSchema, {
            encode: (v: { readonly note: string }) => v,
            decode: (v: { readonly note: string }) => v,
        })
        expect(() =>
            tableEntry<{ id: string; meta: { readonly note: string } }>()(
                // @ts-expect-error a path cannot go into an adapter
                { PK: ['id'], SK: ['meta.note'] },
                { codec: { id: string, meta: wholeNote } },
            ),
        ).toThrow(
            /'meta\.note' is a component of a key, and the codec cannot address that path.*a path cannot go into an adapter/,
        )
    })

    it('refuses an object at a path that the codec writes as a map', () => {
        type Chipped = { id: string; chip: { site: { zone: string } } }
        expect(() =>
            tableEntry<Chipped>()(
                // @ts-expect-error the codec writes the map `site`, and a component is S or N
                { PK: ['id'], SK: ['chip.site'] },
                {
                    codec: {
                        id: string,
                        chip: object({ site: object({ zone: string }) }),
                    },
                },
            ),
        ).toThrow(/as a component/)
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

describe('a name of a key that holds a dot and that the codec declares as an attribute', () => {
    type Kennel = {
        petId: string
        'owner.name'?: number
        owner: { name: string }
    }
    type Plain = { petId: string; 'owner.name': string }
    const codec = {
        petId: string,
        'owner.name': optional(number),
        owner: object({ name: string }),
    }
    // the type refuses an optional component with no default, so the schema is cast, as in the
    // tests of the optional components
    const Pets = tableEntry<Kennel>()(
        { PK: ['petId'], SK: ['petId', 'owner.name'] } as never,
        { codec },
    ) as unknown as {
        unsafeToItem: (item: Kennel) => Record<string, unknown>
        keyUpdates: (change: Kennel) => unknown
    }

    /**
     * **The item reads the whole name first, and the codec writes the slot that the item reads.** An
     * item that holds the attribute `'owner.name'` gives that attribute, and the path `owner` then
     * `name` is read only where the item holds no such name. The slot follows the value, in the
     * list of components, and in a change.
     */
    it('prints the attribute that the item holds under the whole name, not the object at the path', () => {
        const kennel: Kennel = {
            petId: 'p1',
            'owner.name': 7,
            owner: { name: 'bob' },
        }
        expect(Pets.unsafeToItem(kennel).SK).toEqual({
            S: 'PETID#p1#OWNER.NAME#7',
        })
        expect(Pets.keyUpdates({ ...kennel, petId: 'p2' })).toEqual({
            set: {
                PK: { S: 'PETID#p2' },
                SK: { S: 'PETID#p2#OWNER.NAME#7' },
            },
            remove: [],
        })
    })

    it('reads the path where the item holds no attribute of the whole name', () => {
        const kennel: Kennel = { petId: 'p1', owner: { name: 'bob' } }
        expect(Pets.unsafeToItem(kennel).SK).toEqual({
            S: 'PETID#p1#NAME#bob',
        })
        expect(Pets.keyUpdates({ ...kennel, petId: 'p2' })).toEqual({
            set: {
                PK: { S: 'PETID#p2' },
                SK: { S: 'PETID#p2#NAME#bob' },
            },
            remove: [],
        })
    })

    it('prints a name that the codec declares alone, with no object at the path', () => {
        const Alone = tableEntry<Plain>()(
            {
                PK: ['petId'],
                SK: ['petId', 'owner.name'],
                GSI1PK: 'owner.name',
            },
            { codec: { petId: string, 'owner.name': string } },
        )
        const written = Alone.unsafeToItem({ petId: 'p1', 'owner.name': 'ann' })
        expect(written.SK).toEqual({ S: 'PETID#p1#OWNER.NAME#ann' })
        expect(written.GSI1PK).toEqual({ S: 'ann' })
        expect(Alone.keyUpdates({ petId: 'p2', 'owner.name': 'bea' })).toEqual({
            set: {
                PK: { S: 'PETID#p2' },
                SK: { S: 'PETID#p2#OWNER.NAME#bea' },
                GSI1PK: { S: 'bea' },
            },
            remove: [],
        })
    })

    it('writes no key of one attribute for a pet that lacks an optional name that the codec declares alone', () => {
        const Alone = tableEntry<{ petId: string; 'owner.name'?: string }>()(
            { PK: ['petId'], GSI1PK: 'owner.name' },
            { codec: { petId: string, 'owner.name': optional(string) } },
        )
        expect(Alone.unsafeToItem({ petId: 'p1' }).GSI1PK).toBeUndefined()
    })

    it('refuses a component that the codec writes as BOOL under the whole name, where the path holds text', () => {
        expect(() =>
            tableEntry<{
                petId: string
                'owner.name': boolean
                owner: { name: string }
            }>()(
                {
                    PK: ['petId'],
                    // @ts-expect-error the codec writes the whole name as BOOL
                    SK: ['petId', 'owner.name'],
                },
                {
                    codec: {
                        petId: string,
                        'owner.name': boolean,
                        owner: object({ name: string }),
                    },
                },
            ),
        ).toThrow(/writes it as BOOL/)
    })

    it('refuses a key of one attribute whose two readings write two members, because a key attribute has one type', () => {
        expect(() =>
            tableEntry<Kennel>()(
                {
                    PK: ['petId'],
                    // @ts-expect-error the type refuses a key of one attribute with two members too
                    GSI1PK: 'owner.name',
                },
                { codec },
            ),
        ).toThrow(/stores 'owner.name' as N and 'owner.name' as S/)
    })
})
