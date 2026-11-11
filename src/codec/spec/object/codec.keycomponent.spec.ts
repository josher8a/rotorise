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
    binary,
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

    it('refuses a component that the codec writes as B at a path, where a key of one attribute takes B', () => {
        type Chipped = { id: string; tag: { chip: Uint8Array } }
        expect(() =>
            tableEntry<Chipped>()(
                {
                    PK: ['id'],
                    // @ts-expect-error a component is text or a number, and the codec writes B at the path
                    SK: ['tag.chip'],
                },
                { codec: { id: string, tag: object({ chip: binary }) } },
            ),
        ).toThrow(/writes it as B/)
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

/**
 * **A name with a `.` in a key is a path, always.** DynamoDB reads a `.` in a name of an expression as
 * a path separator. An item is a document, so a key reads the path at an item and never the attribute
 * whose own name holds a `.`. A change is a map from a written path to a value, so the given item of
 * an update reads the written name first, and then the walk into a written object.
 */
describe('a name of a key that holds a dot is a path', () => {
    type Kennel = {
        petId: string
        'owner.name': number
        owner: { name: string }
    }
    const kennel: Kennel = {
        petId: 'p1',
        'owner.name': 7,
        owner: { name: 'bob' },
    }
    const codecOf = {
        petId: string,
        'owner.name': number,
        owner: object({ name: string }),
    }

    it('prints the object at the path and not the attribute of the whole name, with a codec and with none', () => {
        const None = tableEntry<Kennel>()({
            PK: ['petId'],
            GSI1SK: ['owner.name'],
        })
        const Coded = tableEntry<Kennel>()(
            { PK: ['petId'], GSI1SK: ['owner.name'] },
            { codec: codecOf },
        )
        expect(None.toEntry(kennel).GSI1SK).toBe('NAME#bob')
        expect(Coded.unsafeToItem(kennel).GSI1SK).toEqual({ S: 'NAME#bob' })
    })

    it('rebuilds a key of a path for a change of the object, and for a write to the path', () => {
        const None = tableEntry<Kennel>()({
            PK: ['petId'],
            GSI1SK: ['owner.name'],
        })
        const Coded = tableEntry<Kennel>()(
            { PK: ['petId'], GSI1SK: ['owner.name'] },
            { codec: codecOf },
        )
        const bea = {
            set: { GSI1SK: { S: 'NAME#bea' } },
            remove: [],
        }
        expect(None.keyUpdates({ owner: { name: 'bea' } })).toEqual(bea)
        // a write to the path is a change of the key: the given item reads the written name first
        expect(None.keyUpdates({ 'owner.name': 8 })).toEqual({
            set: { GSI1SK: { S: 'NAME#8' } },
            remove: [],
        })
        expect(Coded.keyUpdates({ owner: { name: 'bea' } })).toEqual(bea)
        // the codec writes the path as text, so a number written to the path is refused
        expect(() => Coded.keyUpdates({ 'owner.name': 8 })).toThrow(
            /codec writes no text or number/,
        )
    })

    it('refuses a change of a path above the path that a key reads, because the change writes a part of what the key reads', () => {
        type Deep = {
            petId: string
            'owner.name': number
            owner: { name: { first: string } }
        }
        const Pets = tableEntry<Deep>()({
            PK: ['petId'],
            GSI1PK: ['owner.name.first'],
        })
        expect(() =>
            // the type reads a write to 'owner.name' as a hold of the path below it, and the run time reads no value there
            Pets.keyUpdates({ 'owner.name': 8 }),
        ).toThrow(/cannot be rebuilt/)
    })

    it('gives the transform of a component the value at the path, and types its parameter as the type at the path', () => {
        type Optional = {
            petId: string
            'owner.name'?: number
            owner: { name: string }
        }
        const Pets = tableEntry<Optional>()({
            PK: ['petId'],
            SK: [['owner.name', (name: string) => name.toUpperCase(), '']],
        })
        expect(Pets.toEntry({ petId: 'p1', owner: { name: 'bob' } }).SK).toBe(
            'NAME#BOB',
        )
        tableEntry<Optional>()({
            PK: ['petId'],
            // @ts-expect-error the parameter is the string at the path, and not the number of the attribute
            SK: [['owner.name', (name: number) => name + 1, 0]],
        })
    })

    it('prints the object at the path where the attribute of the whole name is absent or undefined', () => {
        type Undefinable = {
            petId: string
            'owner.name'?: number | undefined
            owner: { name: string }
        }
        const Pets = tableEntry<Undefinable>()({
            PK: ['petId'],
            SK: ['owner.name'],
        })
        expect(Pets.toEntry({ petId: 'p1', owner: { name: 'bob' } }).SK).toBe(
            'NAME#bob',
        )
        expect(
            Pets.toEntry({
                petId: 'p1',
                'owner.name': undefined,
                owner: { name: 'bob' },
            }).SK,
        ).toBe('NAME#bob')
    })

    it('refuses a path below a refinement, in the type and at construction, for a name that the codec also declares whole', () => {
        const Owner = refine(
            object({ name: string }),
            (o: { readonly name: string }): o is { readonly name: string } =>
                o.name !== '',
        )
        expect(() =>
            tableEntry<{
                petId: string
                'owner.name'?: string
                owner: { name: string }
            }>()(
                {
                    PK: ['petId'],
                    // @ts-expect-error the path enters a refinement, and the attribute of the whole name is no reading
                    GSI1PK: 'owner.name',
                },
                {
                    codec: {
                        petId: string,
                        'owner.name': optional(string),
                        owner: Owner,
                    },
                },
            ),
        ).toThrow(/cannot address that path/)
    })

    const Open = item(
        object({ petId: string, owner: object({ name: string }) }, [
            string,
            optional(string),
        ]),
    )
    type OpenPet = ReturnType<typeof Open.unsafeDecode>
    type OpenKeys = { petId: string; owner: { name: string } }

    it('reads the path over an open codec, where the rest holds no attribute of the whole name', () => {
        const Pets = tableEntry<OpenPet, never, OpenKeys>()(
            { PK: ['petId'], GSI1PK: 'owner.name' },
            { codec: Open },
        )
        expect(
            Pets.unsafeToItem({ petId: 'p1', owner: { name: 'bob' } }).GSI1PK,
        ).toEqual({ S: 'bob' })
    })

    it('prints the object at the path on each route, for a pet that holds the name of the path in the rest', () => {
        const Pets = tableEntry<OpenPet, never, OpenKeys>()(
            { PK: ['petId'], GSI1SK: ['owner.name'] },
            { codec: Open },
        )
        const pet: OpenPet = {
            petId: 'p1',
            'owner.name': 'ann',
            owner: { name: 'bob' },
        }
        expect(Pets.unsafeToItem(pet).GSI1SK).toEqual({ S: 'NAME#bob' })
        expect(Pets.toEntry(pet).GSI1SK).toBe('NAME#bob')
        expect(Pets.keys(['GSI1SK'], pet)).toEqual({
            GSI1SK: { S: 'NAME#bob' },
        })
        expect(Pets.keyUpdates({ owner: { name: 'bea' } })).toEqual({
            set: { GSI1SK: { S: 'NAME#bea' } },
            remove: [],
        })
        // a write to the path is a change of the key, and the rest of the open codec holds no reading
        expect(Pets.keyUpdates({ 'owner.name': 'cat' })).toEqual({
            set: { GSI1SK: { S: 'NAME#cat' } },
            remove: [],
        })
    })

    it('refuses a write to a path below a key that reads the name above, because the change lacks the value that the key reads', () => {
        type Housed = { petId: string; owner: string; 'owner.name': number }
        const None = tableEntry<Housed>()({
            PK: ['petId'],
            GSI1SK: ['owner'],
        })
        const Coded = tableEntry<Housed>()(
            { PK: ['petId'], GSI1SK: ['owner'] },
            { codec: { petId: string, owner: string, 'owner.name': number } },
        )
        // @ts-expect-error the change writes below 'owner', and the change lacks 'owner'
        expect(() => None.keyUpdates({ 'owner.name': 8 })).toThrow(
            /cannot be rebuilt/,
        )
        // @ts-expect-error the change writes below 'owner', and the change lacks 'owner'
        expect(() => Coded.keyUpdates({ 'owner.name': 8 })).toThrow(
            /cannot be rebuilt/,
        )
    })

    it('refuses an entity whose attribute holds the dot, in the type and at construction, and gives the reason', () => {
        type Flat = { petId: string; 'owner.name': string }
        // an entry with no codec holds no declaration at run time, so the type is the one refusal
        tableEntry<Flat>()({
            PK: ['petId'],
            // @ts-expect-error a `.` in a key name is a path separator, as in DynamoDB
            GSI1SK: ['owner.name'],
        })
        expect(() =>
            tableEntry<Flat>()(
                {
                    PK: ['petId'],
                    // @ts-expect-error a `.` in a key name is a path separator, as in DynamoDB
                    GSI1SK: ['owner.name'],
                },
                { codec: { petId: string, 'owner.name': string } },
            ),
        ).toThrow(/a `\.` in a key name is a path separator, as in DynamoDB/)
    })

    it('reads a component through the first name when the codec decides an attribute of a dotted name', () => {
        type Decided = {
            petId: string
            'owner.name': 'x'
            owner: { name: string }
        }
        const Pets = tableEntry<Decided>()(
            { PK: ['petId'], GSI1SK: ['owner.name'] },
            {
                codec: {
                    petId: string,
                    'owner.name': string('x'),
                    owner: object({ name: string }),
                },
            },
        )
        expect(
            Pets.unsafeToItem({
                petId: 'p1',
                'owner.name': 'x',
                owner: { name: 'bob' },
            }).GSI1SK,
        ).toEqual({ S: 'NAME#bob' })
        expect(Pets.keyUpdates({ owner: { name: 'bea' } })).toEqual({
            set: { GSI1SK: { S: 'NAME#bea' } },
            remove: [],
        })
    })

    it('refuses a component that the codec writes as BOOL at the path', () => {
        expect(() =>
            tableEntry<{ petId: string; owner: { flag: boolean } }>()(
                {
                    PK: ['petId'],
                    // @ts-expect-error the codec writes the path as BOOL
                    SK: ['petId', 'owner.flag'],
                },
                {
                    codec: {
                        petId: string,
                        owner: object({ flag: boolean }),
                    },
                },
            ),
        ).toThrow(/writes it as BOOL/)
    })
    it('types the key of toEntry at the path, for a key of one attribute and for a list', () => {
        const Pets = tableEntry<Kennel>()({
            PK: ['petId'],
            GSI1PK: 'owner.name',
            GSI1SK: ['owner.name'],
        })
        const entry = Pets.toEntry(kennel)
        expectTypeOf(entry.GSI1PK).toEqualTypeOf<string>()
        expectTypeOf(entry.GSI1SK).toEqualTypeOf<`NAME#${string}`>()
        expect(entry.GSI1PK).toBe('bob')
    })

    it('reads the object at the path in the parameter of key, and refuses the attribute of the whole name', () => {
        const Pets = tableEntry<Kennel>()({
            PK: ['petId'],
            GSI1PK: 'owner.name',
            GSI1SK: ['owner.name'],
        })
        expect(Pets.key('GSI1PK', { owner: { name: 'bob' } })).toBe('bob')
        expect(Pets.key('GSI1SK', { owner: { name: 'bob' } })).toBe('NAME#bob')
        // @ts-expect-error a key of one attribute at 'owner.name' reads the path, and the run time reads no value at the whole name
        const one = Pets.key('GSI1PK', { 'owner.name': 7 })
        expect(one).toBeUndefined()
        // @ts-expect-error a list that holds 'owner.name' reads the path, and the run time finds no value at the path
        const list = () => Pets.key('GSI1SK', { 'owner.name': 7 })
        expect(list).toThrow(/Attribute owner\.name not found/)
        // the attribute of the whole name is no input of the key: the type states nothing of its value, and the run time does not read it
        expect(
            Pets.key('GSI1SK', {
                owner: { name: 'bob' },
                'owner.name': 'any text',
            }),
        ).toBe('NAME#bob')
    })

    it('gives the type and the text at the path to a call of key whose attributes hold both names, for a literal object and for a value of the entity type', () => {
        const Pets = tableEntry<Kennel>()({
            PK: ['petId'],
            GSI1PK: 'owner.name',
            GSI1SK: ['owner.name'],
        })
        const both = {
            petId: 'p1',
            'owner.name': 7,
            owner: { name: 'bob' },
        } as const
        expectTypeOf(Pets.key('GSI1PK', both)).toEqualTypeOf<'bob'>()
        expect(Pets.key('GSI1PK', both)).toBe('bob')
        expectTypeOf(Pets.key('GSI1PK', kennel)).toEqualTypeOf<string>()
        expect(Pets.key('GSI1PK', kennel)).toBe('bob')
        expectTypeOf(Pets.key('GSI1SK', both)).toEqualTypeOf<'NAME#bob'>()
        expect(Pets.key('GSI1SK', kennel)).toBe('NAME#bob')
    })

    it('gives the type and the text at the path to the arm of a match that is one name with a `.`, where the attributes hold both names', () => {
        type Owned =
            | {
                  petId: string
                  'owner.name': number
                  owner: { kind: 'P'; name: string }
              }
            | {
                  petId: string
                  'owner.name': number
                  owner: { kind: 'Q'; id: string }
              }
        const Pets = tableEntry<Owned>()({
            PK: ['petId'],
            GSI1PK: {
                discriminator: 'owner.kind',
                spec: { P: 'owner.name', Q: 'petId' },
            },
        })
        const both = {
            petId: 'p1',
            'owner.name': 7,
            owner: { kind: 'P', name: 'bob' },
        } as const
        expectTypeOf(Pets.key('GSI1PK', both)).toEqualTypeOf<'bob'>()
        expect(Pets.key('GSI1PK', both)).toBe('bob')
    })
})
