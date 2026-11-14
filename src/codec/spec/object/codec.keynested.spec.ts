/**
 * A key of one attribute below a second match states the stored text, as below one match.
 *
 * A key of one attribute is the stored value of the attribute. Under a tagged codec the stored text
 * of `adopted` is `Y` or `N`, and the entity holds a boolean. The type of `key` read the stored
 * text where the key is the arm of one match, and read the type of the entity where the key is the
 * arm of a match inside the arm of a match. The type of `toEntry` read the stored text at each
 * depth. The recursion on a nested arm goes through `OptimizedBuiltKey`: a read of the stored text
 * in `ProcessKey` makes `ProcessKey` circular. Without a codec the stored value is the value of the
 * entity, so the type of the key at each depth is the type of the attribute.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { discriminatedUnion, held, item, object, string } from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

const flag: StandardSchemaV1<boolean> = {
    '~standard': {
        version: 1,
        vendor: 'test',
        validate: (v) =>
            typeof v === 'boolean'
                ? { value: v }
                : { issues: [{ message: 'no' }] },
    },
}
const Adopted = held(string('Y', 'N'), flag, {
    encode: (b: boolean) => (b ? 'Y' : 'N'),
    decode: (s: string) => s === 'Y',
})
type Cat = {
    petId: string
    species: 'CAT'
    status: 'IN' | 'OUT'
    adopted: boolean
}
type Dog = { petId: string; species: 'DOG'; status: 'IN'; adopted: boolean }
const Tagged = item(
    discriminatedUnion('species', [
        object({
            petId: string,
            species: string('CAT'),
            status: string('IN', 'OUT'),
            adopted: Adopted,
        }),
        object({
            petId: string,
            species: string('DOG'),
            status: string('IN'),
            adopted: Adopted,
        }),
    ]),
)
const housed: Cat = { petId: 'p1', species: 'CAT', status: 'IN', adopted: true }

describe('a key of one attribute states the stored text at each depth of a match', () => {
    it('is the stored text below one match', () => {
        const OneLevel = tableEntry<Cat | Dog>()(
            {
                PK: ['petId'],
                SK: {
                    discriminator: 'species',
                    spec: { CAT: 'adopted', DOG: null },
                },
            },
            { codec: Tagged },
        )
        const key = OneLevel.key('SK', housed)
        expectTypeOf(key).toEqualTypeOf<'N' | 'Y'>()
        expect(key).toBe('Y')
    })

    it('is the stored text below a second match, and key and toEntry state one type', () => {
        const TwoLevels = tableEntry<Cat | Dog>()(
            {
                PK: ['petId'],
                SK: {
                    discriminator: 'species',
                    spec: {
                        CAT: {
                            discriminator: 'status',
                            spec: { IN: 'adopted', OUT: null },
                        },
                        DOG: null,
                    },
                },
            },
            { codec: Tagged },
        )
        const key = TwoLevels.key('SK', housed)
        const stored = TwoLevels.toEntry(housed).SK
        expectTypeOf(key).toEqualTypeOf<'N' | 'Y' | undefined>()
        expectTypeOf(stored).toEqualTypeOf<typeof key>()
        expect(key).toBe('Y')
        expect(stored).toBe('Y')
    })

    it('is the value of the entity at each depth where the entry has no codec', () => {
        type Weighed =
            | {
                  petId: string
                  species: 'CAT'
                  status: 'IN' | 'OUT'
                  weight: number
              }
            | { petId: string; species: 'DOG'; status: 'IN'; weight: number }
        const Plain = tableEntry<Weighed>()({
            PK: ['petId'],
            SK: {
                discriminator: 'species',
                spec: {
                    CAT: {
                        discriminator: 'status',
                        spec: { IN: 'weight', OUT: null },
                    },
                    DOG: null,
                },
            },
        })
        const weighed: Weighed = {
            petId: 'p1',
            species: 'CAT',
            status: 'IN',
            weight: 5,
        }
        const key = Plain.key('SK', weighed)
        expectTypeOf(key).toEqualTypeOf<number | undefined>()
        expect(key).toBe(5)
    })
})
