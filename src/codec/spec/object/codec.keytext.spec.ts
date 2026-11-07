/**
 * A component of a key is the stored text of its attribute, in the type and at run time.
 *
 * A caller's adapter over an attribute writes the caller's value as another text. The key prints
 * that text, so the type of the key names the stored literal where the inner term pins one, and
 * `string` where the inner term pins none. A field with no adapter of a caller prints its value.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { discriminatedUnion, held, item, object, string } from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

const schema = <T>(is: (v: unknown) => v is T): StandardSchemaV1<T> => ({
    '~standard': {
        version: 1,
        vendor: 'test',
        validate: (v) =>
            is(v) ? { value: v } : { issues: [{ message: 'no' }] },
    },
})
const Adopted = held(
    string('Y', 'N'),
    schema((v): v is boolean => typeof v === 'boolean'),
    {
        encode: (b: boolean) => (b ? 'Y' : 'N'),
        decode: (s: string) => s === 'Y',
    },
)
const Born = held(
    string,
    schema((v): v is Date => v instanceof Date),
    {
        encode: (d: Date) => d.toISOString(),
        decode: (s: string) => new Date(s),
    },
)

type Pet = { petId: string; adopted: boolean }
const Pets = tableEntry<Pet>()(
    { PK: ['petId'], SK: ['adopted'] },
    { codec: { petId: string, adopted: Adopted } },
)

describe('the type of a key component under an adapter of a caller', () => {
    it('names the stored literal on every route, as the run time prints it', () => {
        const key = Pets.key('SK', { adopted: true })
        expectTypeOf(key).toEqualTypeOf<'ADOPTED#Y' | 'ADOPTED#N'>()
        expect(key).toBe('ADOPTED#Y')
        const entry = Pets.toEntry({ petId: 'p1', adopted: false })
        expectTypeOf(entry.SK).toEqualTypeOf<'ADOPTED#Y' | 'ADOPTED#N'>()
        expect(entry.SK).toBe('ADOPTED#N')
        expectTypeOf(Pets.infer.SK).toEqualTypeOf<'ADOPTED#Y' | 'ADOPTED#N'>()
        expectTypeOf(Pets.path().adopted.toString()).toBeString()
    })

    it('prints a plain field as its value, beside the adapter', () => {
        expectTypeOf(
            Pets.key('PK', { petId: 'p1' }),
        ).toEqualTypeOf<'PETID#p1'>()
    })

    it('names string where the inner term pins no literal', () => {
        const Visits = tableEntry<{ petId: string; at: Date }>()(
            { PK: ['petId'], SK: ['at'] },
            { codec: { petId: string, at: Born } },
        )
        const key = Visits.key('SK', { at: new Date(0) })
        expectTypeOf(key).toEqualTypeOf<`AT#${string}`>()
        expect(key).toBe('AT#1970-01-01T00:00:00.000Z')
    })

    it('names the stored literal for the variants of a union', () => {
        type Dog = { kind: 'dog'; petId: string; adopted: boolean }
        type Cat = { kind: 'cat'; petId: string; adopted: boolean }
        const Both = tableEntry<Dog | Cat>()(
            { PK: ['petId'], SK: ['adopted'] },
            {
                codec: item(
                    discriminatedUnion('kind', [
                        object({
                            kind: string('dog'),
                            petId: string,
                            adopted: Adopted,
                        }),
                        object({
                            kind: string('cat'),
                            petId: string,
                            adopted: Adopted,
                        }),
                    ]),
                ),
            },
        )
        expectTypeOf(Both.key('SK', { adopted: true })).toEqualTypeOf<
            'ADOPTED#Y' | 'ADOPTED#N'
        >()
    })

    it('leaves the entry with no codec as it was', () => {
        const Plain = tableEntry<Pet>()({ PK: ['petId'], SK: ['adopted'] })
        expectTypeOf(
            Plain.key('SK', { adopted: true }),
        ).toEqualTypeOf<'ADOPTED#true'>()
    })
})
