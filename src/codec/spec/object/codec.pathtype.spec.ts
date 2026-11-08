/**
 * The type of a key at a path reads the codec along the path, as `at` does at run time.
 *
 * The member that the codec writes at a path decides the member of a key of one attribute. A path
 * goes below an object field, and below no field that `refine`, `legacy` or `held` wraps, whatever
 * the adapter stores. A key of one attribute holds the value or no key, so a path whose value can
 * be absent gives a sparse key.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import type { Attribute } from '../../attribute'
import { DynamoNumber } from '../../attribute'
import {
    boolean,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    held,
    object,
    optional,
    refine,
    string,
} from '../../codec'
import { orThrow } from '../../result'
import type { StandardSchemaV1 } from '../../standard'

const schemaOf = <T>(
    admits: (value: unknown) => boolean,
): StandardSchemaV1<T> => ({
    '~standard': {
        version: 1,
        vendor: 'test',
        validate: (v) =>
            admits(v) ? { value: v as T } : { issues: [{ message: 'no' }] },
    },
})
const isoAt = held(
    string,
    schemaOf<Date>((v) => v instanceof Date),
    {
        encode: (d: Date) => d.toISOString(),
        decode: (s: string) => new Date(s),
    },
)
const Hexed = held(
    string,
    schemaOf<number>(() => true),
    {
        encode: (n: number) => n.toString(16),
        decode: (s: string) => Number.parseInt(s, 16),
    },
)

describe('the member of a key of one attribute at a path is the member that the codec writes there', () => {
    it('admits a held Date at a path, which the codec writes as S', () => {
        const Visits = tableEntry<{ id: string; meta: { at: Date } }>()(
            { PK: ['id'], SK: 'meta.at' },
            { codec: { id: string, meta: object({ at: isoAt }) } },
        )
        expect(Visits.key('SK', { meta: { at: new Date(0) } })).toBe(
            '1970-01-01T00:00:00.000Z',
        )
    })

    it('types the row member S where an adapter writes text for a number', () => {
        const Weighed = tableEntry<{ id: string; meta: { grams: number } }>()(
            { PK: ['id'], SK: 'meta.grams' },
            { codec: { id: string, meta: object({ grams: Hexed }) } },
        )
        const row = Weighed.unsafeToItem({ id: 'a', meta: { grams: 255 } })
        expect(row.SK).toEqual({ S: 'ff' })
        expectTypeOf(row.SK).toEqualTypeOf<Attribute<'S'>>()
    })

    it('types the row member N where decimal writes N for a string', () => {
        const Priced = tableEntry<{ id: string; body: { price: string } }>()(
            { PK: ['id'], SK: 'body.price' },
            { codec: { id: string, body: object({ price: decimal }) } },
        )
        const row = Priced.unsafeToItem({ id: 'a', body: { price: '1.5' } })
        expect(row.SK).toEqual({ N: '1.5' })
        expectTypeOf(row.SK).toEqualTypeOf<Attribute<'N'>>()
    })
})

describe('a path below a field that a wrapper blocks is refused, whatever the wrapper stores', () => {
    type Note =
        | { readonly kind: 'a'; readonly note: string }
        | { readonly kind: 'b'; readonly note: string }
    const Meta = discriminatedUnion('kind', [
        object({ kind: string('a'), note: string }),
        object({ kind: string('b'), note: string }),
    ])

    it('refuses a path below a refine over a union of objects', () => {
        const Checked = refine(Meta, (v: Note): v is Note => v.note !== '')
        expect(() =>
            tableEntry<{ id: string; meta: Note }>()(
                // @ts-expect-error a path cannot go into refine
                { PK: ['id'], SK: ['meta.note'] },
                { codec: { id: string, meta: Checked } },
            ),
        ).toThrow(/cannot address/)
    })

    it('refuses a path below an adapter that stores text', () => {
        const noteText = held(
            string,
            schemaOf<{ readonly note: string }>(() => true),
            {
                encode: (v: { readonly note: string }) => JSON.stringify(v),
                decode: (s: string) =>
                    JSON.parse(s) as { readonly note: string },
            },
        )
        expect(() =>
            tableEntry<{ id: string; meta: { readonly note: string } }>()(
                // @ts-expect-error a path cannot go into an adapter
                { PK: ['id'], SK: ['meta.note'] },
                { codec: { id: string, meta: noteText } },
            ),
        ).toThrow(/cannot address/)
    })

    it('refuses a boolean component at a path, which the codec writes as BOOL', () => {
        expect(() =>
            tableEntry<{ id: string; meta: { flag: boolean } }>()(
                // @ts-expect-error a component is text or a number
                { PK: ['id'], SK: ['meta.flag'] },
                { codec: { id: string, meta: object({ flag: boolean }) } },
            ),
        ).toThrow(/A component is text or a number/)
    })
})

describe('a key of one attribute reads the codec under a presence mark and a DynamoNumber as the value', () => {
    it('types an optional caller adapter as its stored text, alone', () => {
        const Visits = tableEntry<{ petId: string; at?: Date }>()(
            { PK: ['petId'], GSI2SK: 'at' },
            { codec: { petId: string, at: optional(isoAt) } },
        )
        const at = new Date(0)
        expect(Visits.key('GSI2SK', { at })).toBe('1970-01-01T00:00:00.000Z')
        expectTypeOf(Visits.key('GSI2SK', { at })).toEqualTypeOf<string>()
    })

    it('holds the DynamoNumber in a key of one attribute, as the run time does', () => {
        const Prices = tableEntry<{ id: string; price: DynamoNumber }>()(
            { PK: ['id'], SK: 'price' },
            { codec: { id: string, price: dynamoNumber } },
        )
        const price = orThrow(DynamoNumber.from('1.5'))
        const key = Prices.key('SK', { price })
        expect(key).toBe(price)
        expectTypeOf(key).toEqualTypeOf<typeof price>()
    })
})

describe('a key of one attribute at a path can be sparse, as at the top level', () => {
    it('admits a path whose value can be absent, and writes no key for an item without it', () => {
        const Notes = tableEntry<{ id: string; meta?: { note: string } }>()({
            PK: ['id'],
            GSI1SK: 'meta.note',
        })
        expect(Notes.key('GSI1SK', { meta: { note: 'x' } })).toBe('x')
        expect(Notes.toEntry({ id: 'a' })).not.toHaveProperty('GSI1SK')
        // the top-level form is admitted too
        expect(
            tableEntry<{ id: string; note?: string }>()({
                PK: ['id'],
                GSI1SK: 'note',
            }),
        ).toBeTypeOf('object')
    })
})
