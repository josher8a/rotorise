/**
 * A key reads its attribute through the variant that the stored tag selects, and through the codec
 * at the path.
 *
 * A tag under the adapter of a caller is stored as a literal that is not the decoded value, so the
 * variant of an item is the one that the stored literal names. A component of a key prints the text
 * that the row holds at that variant. A key on the discriminator writes the stored literal, and each
 * variant states its own. A key of one attribute at a path is the attribute that the codec writes at
 * the path, as a key of one top-level attribute is. The type refuses that key where it stands
 * alone, so the specs reach it through an entry that the type does not check.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import {
    binary,
    discriminatedUnion,
    held,
    item,
    number,
    object,
    optional,
    ref,
    scope,
    string,
} from '../../codec'
import { native } from '../../native'
import type { StandardSchemaV1 } from '../../standard'

type Route = {
    readonly unsafeToItem: (entity: never) => Record<string, unknown>
    readonly keys: (
        names: readonly string[],
        attributes: never,
    ) => Record<string, unknown>
    readonly key: (name: string, attributes: never) => unknown
    readonly keyUpdates: (changed: never) => {
        readonly set: Record<string, unknown>
    }
    readonly toEntry: (entity: never) => Record<string, unknown>
}
/** An entry over a schema and a codec, which the type of a held tag need not admit. */
const route = (schema: unknown, codec?: unknown): Route =>
    tableEntry<Record<string, unknown>>()(
        schema as never,
        (codec === undefined ? undefined : { codec }) as never,
    ) as unknown as Route

const schemaOf = <T>(
    guard: (value: unknown) => value is T,
): StandardSchemaV1<T> => ({
    '~standard': {
        version: 1,
        vendor: 'handwritten',
        validate: (value) =>
            guard(value) ? { value } : { issues: [{ message: 'no' }] },
    },
})
const dateSchema = schemaOf((v): v is Date => v instanceof Date)
const numberSchema = schemaOf((v): v is number => typeof v === 'number')

const isoAt = held(string, dateSchema, {
    encode: (day: Date) => day.toISOString(),
    decode: (text: string) => new Date(text),
})
const hex = held(string, numberSchema, {
    encode: (n: number) => n.toString(16),
    decode: (text: string) => Number.parseInt(text, 16),
})
const Dog = held(string('D'), string('dog'), {
    encode: (_: 'dog') => 'D' as const,
    decode: (_: 'D') => 'dog' as const,
})

const unionOf = (dog: unknown) =>
    item(
        discriminatedUnion('kind', [
            object({ kind: dog as never, petId: string, chip: hex, at: isoAt }),
            object({
                kind: string('cat'),
                petId: string,
                chip: hex,
                at: isoAt,
            }),
        ] as never),
    )
const { Pets: refUnion } = scope({
    Pets: discriminatedUnion('kind', [
        object({ kind: ref('DogTag'), petId: string, chip: hex, at: isoAt }),
        object({ kind: string('cat'), petId: string, chip: hex, at: isoAt }),
    ] as never),
    DogTag: Dog,
} as never) as { Pets: never }

const dog = { kind: 'dog', petId: 'p1', chip: 255, at: new Date(0) }
const cat = { kind: 'cat', petId: 'p1', chip: 255, at: new Date(0) }
const iso = '1970-01-01T00:00:00.000Z'

describe.each([
    ['a held tag', () => unionOf(Dog)],
    ['a ref to a held tag', () => item(refUnion)],
])('a key of a variant under %s is the key that the row holds', (_, codec) => {
    it('writes the attribute of the variant on each route, where the key is one attribute', () => {
        const Visits = route({ PK: ['petId'], GSI1SK: 'at' }, codec())
        const row = Visits.unsafeToItem(dog as never)
        expect(row.GSI1SK).toEqual({ S: iso })
        expect(Visits.keys(['GSI1SK'], dog as never)).toEqual({
            GSI1SK: { S: iso },
        })
        expect(Visits.key('GSI1SK', dog as never)).toBe(iso)
        expect(Visits.toEntry(dog as never).GSI1SK).toBe(iso)
        expect(Visits.keyUpdates(dog as never).set.GSI1SK).toEqual({ S: iso })
    })

    it('prints the stored text of each component, as the row holds it', () => {
        const Chips = route({ PK: ['petId'], SK: ['kind', 'chip'] }, codec())
        expect(Chips.unsafeToItem(dog as never).SK).toEqual({
            S: 'KIND#D#CHIP#ff',
        })
        expect(Chips.unsafeToItem(cat as never).SK).toEqual({
            S: 'KIND#cat#CHIP#ff',
        })
        expect(Chips.keys(['SK'], dog as never)).toEqual({
            SK: { S: 'KIND#D#CHIP#ff' },
        })
        expect(Chips.key('SK', dog as never)).toBe('KIND#D#CHIP#ff')
        expect(Chips.toEntry(dog as never).SK).toBe('KIND#D#CHIP#ff')
    })

    it('writes the stored literal of the variant, where the key is the discriminator', () => {
        const Kinds = route({ PK: ['petId'], GSI1PK: 'kind' }, codec())
        expect(Kinds.unsafeToItem(dog as never).GSI1PK).toEqual({ S: 'D' })
        expect(Kinds.keys(['GSI1PK'], dog as never)).toEqual({
            GSI1PK: { S: 'D' },
        })
        expect(Kinds.keys(['GSI1PK'], cat as never)).toEqual({
            GSI1PK: { S: 'cat' },
        })
    })
})

describe('a key of a variant that holds its field in a rest, under a held tag', () => {
    it('prints the stored text that the rest writes', () => {
        const Chips = route(
            { PK: ['petId'], SK: ['kind', 'chip'] },
            item(
                discriminatedUnion('kind', [
                    object({ kind: Dog, petId: string }, [
                        string,
                        optional(hex),
                    ]),
                    object({ kind: string('cat'), petId: string }, [
                        string,
                        optional(hex),
                    ]),
                ] as never),
            ),
        )
        expect(
            Chips.unsafeToItem({ kind: 'dog', petId: 'p1', chip: 255 } as never)
                .SK,
        ).toEqual({
            S: 'KIND#D#CHIP#ff',
        })
        expect(Chips.keys(['SK'], { kind: 'dog', chip: 255 } as never)).toEqual(
            {
                SK: { S: 'KIND#D#CHIP#ff' },
            },
        )
    })
})

describe('a key on the discriminator of a tagged entry', () => {
    it('is built, and writes the literal of each variant', () => {
        const Kinds = route(
            { PK: ['petId'], GSI1PK: 'kind' },
            item(
                discriminatedUnion('kind', [
                    object({ kind: string('DOG'), petId: string }),
                    object({ kind: string('CAT'), petId: string }),
                ]),
            ),
        )
        expect(Kinds.keys(['GSI1PK'], { kind: 'DOG' } as never)).toEqual({
            GSI1PK: { S: 'DOG' },
        })
        expect(
            Kinds.unsafeToItem({ kind: 'CAT', petId: 'p1' } as never).GSI1PK,
        ).toEqual({ S: 'CAT' })
    })
})

describe('a key of one attribute at a path is the attribute that the codec writes at the path', () => {
    const entity = (v: unknown) => ({ litterId: 'l1', body: { v } })
    const entryOf = (v: unknown) =>
        route(
            { PK: ['litterId'], GSI1SK: 'body.v' },
            { litterId: string, body: object({ v: v as never }) },
        )

    it('is N for a number, on each route, as the entry with no codec writes it', () => {
        const Numbers = entryOf(number)
        expect(Numbers.unsafeToItem(entity(90) as never).GSI1SK).toEqual({
            N: '90',
        })
        expect(Numbers.keys(['GSI1SK'], entity(90) as never)).toEqual({
            GSI1SK: { N: '90' },
        })
        expect(Numbers.key('GSI1SK', entity(90) as never)).toBe(90)
        expect(
            native.encode(Numbers.toEntry(entity(90) as never).GSI1SK as never),
        ).toEqual({ N: '90' })
        expect(Numbers.keyUpdates(entity(90) as never).set.GSI1SK).toEqual({
            N: '90',
        })
    })

    it('is S for a string, and S for a number that a caller writes as a string', () => {
        const Names = entryOf(string)
        expect(Names.keys(['GSI1SK'], entity('abc') as never)).toEqual({
            GSI1SK: { S: 'abc' },
        })
        const Chips = entryOf(hex)
        expect(Chips.unsafeToItem(entity(255) as never).GSI1SK).toEqual({
            S: 'ff',
        })
        expect(Chips.keys(['GSI1SK'], entity(255) as never)).toEqual({
            GSI1SK: { S: 'ff' },
        })
        expect(Chips.key('GSI1SK', entity(255) as never)).toBe('ff')
    })

    it('is B for a binary, on each route', () => {
        const Chips = entryOf(binary)
        const bytes = new Uint8Array([1, 2])
        expect(Chips.unsafeToItem(entity(bytes) as never).GSI1SK).toEqual({
            B: bytes,
        })
        expect(Chips.keys(['GSI1SK'], entity(bytes) as never)).toEqual({
            GSI1SK: { B: bytes },
        })
        expect(Chips.toEntry(entity(bytes) as never).GSI1SK).toBe(bytes)
    })

    it('is the member of the value, where the entry has no codec', () => {
        const Bare = route({ PK: ['litterId'], GSI1SK: 'body.v' })
        expect(Bare.keys(['GSI1SK'], entity(90) as never)).toEqual({
            GSI1SK: { N: '90' },
        })
        expect(
            native.encode(Bare.toEntry(entity(90) as never).GSI1SK as never),
        ).toEqual({ N: '90' })
    })
})

describe('a path that variants declare differently refuses on use with the reason of the path', () => {
    it('names the path and the reason of at, and not a missing text', () => {
        const Notes = route(
            { PK: ['petId'], SK: ['meta.note'] },
            item(
                discriminatedUnion('kind', [
                    object({
                        kind: string('DOG'),
                        petId: string,
                        meta: object({ note: string }),
                    }),
                    object({
                        kind: string('CAT'),
                        petId: string,
                        meta: object({ note: isoAt }),
                    }),
                ]),
            ),
        )
        const dogNote = { kind: 'DOG', meta: { note: 'a' } } as never
        expect(() => Notes.keys(['SK'], dogNote)).toThrow(RotoriseError)
        expect(() => Notes.keys(['SK'], dogNote)).toThrow(
            /declared differently in different variants/,
        )
        expect(() => Notes.keys(['SK'], dogNote)).toThrow(
            /^'meta\.note' is a component of a key, and the codec cannot address that path/,
        )
    })
})
