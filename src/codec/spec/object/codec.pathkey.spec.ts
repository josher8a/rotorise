/**
 * A key of one attribute at a path prints the value at the path, as a component of a list does.
 *
 * The key model is parametric in the name of an attribute, so a name can be a path. The key part
 * holds the value at the member of the name. An entry with no codec prints the value. An entry
 * with a codec prints the text or the number that the codec writes at the path. The type refuses
 * a path that the codec cannot address: a path cannot go into `refine`, `legacy` or `held`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { held, number, object, refine, string } from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

type Noted = { id: string; meta: { note: string; grams: number } }
const hex: StandardSchemaV1<number> = {
    '~standard': {
        version: 1,
        vendor: 'test',
        validate: (v) => ({ value: v as number }),
    },
}
const Hexed = held(string, hex, {
    encode: (n: number) => n.toString(16),
    decode: (s: string) => Number.parseInt(s, 16),
})
const meta = object({ note: string, grams: number })

describe('a key of one attribute at a path', () => {
    it('prints the value at the path, in an entry with no codec', () => {
        const Notes = tableEntry<Noted>()({ PK: ['id'], SK: 'meta.note' })
        const key = Notes.key('SK', { meta: { note: 'x' } })
        expect(key).toBe('x')
        expectTypeOf(key).toEqualTypeOf<'x'>()
        const entry = Notes.toEntry({
            id: 'a',
            meta: { note: 'x', grams: 1 },
        })
        expect(entry.SK).toBe('x')
        expectTypeOf(entry.SK).toEqualTypeOf<'x'>()
    })

    it('holds the number that the codec writes at the path, and writes it as an N in the row', () => {
        const Notes = tableEntry<Noted>()(
            { PK: ['id'], SK: 'meta.grams' },
            { codec: { id: string, meta } },
        )
        const key = Notes.key('SK', { meta: { grams: 90 } })
        expect(key).toBe(90)
        expectTypeOf(key).toEqualTypeOf<90>()
        // the row member is the one that the codec writes at the path
        expect(Notes.keys(['SK'], { meta: { note: 'n', grams: 90 } })).toEqual({
            SK: { N: '90' },
        })
    })

    it('prints the stored text under the adapter of a caller at the path', () => {
        type Weighed = { id: string; meta: { grams: number } }
        const Notes = tableEntry<Weighed>()(
            { PK: ['id'], SK: 'meta.grams' },
            { codec: { id: string, meta: object({ grams: Hexed }) } },
        )
        const key = Notes.key('SK', { meta: { grams: 255 } })
        expect(key).toBe('ff')
        expectTypeOf(key).toEqualTypeOf<string>()
    })

    it('refuses a path that the entity does not hold, in the type', () => {
        tableEntry<Noted>()(
            // @ts-expect-error the entity has no 'meta.nope'
            { PK: ['id'], SK: 'meta.nope' },
        )
    })

    it('refuses a path into a refine, in the type and at construction', () => {
        const Meta = refine(
            meta,
            (v: {
                readonly note: string
                readonly grams: number
            }): v is { readonly note: string; readonly grams: number } =>
                v.note !== '',
        )
        expect(() =>
            tableEntry<Noted>()(
                // @ts-expect-error a path cannot go into refine
                { PK: ['id'], SK: 'meta.note' },
                { codec: { id: string, meta: Meta } },
            ),
        ).toThrow(/cannot address/)
    })
})
