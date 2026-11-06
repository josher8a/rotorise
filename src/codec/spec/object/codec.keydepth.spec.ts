/**
 * A depth keeps that many components of a key, so it is a non-negative integer.
 *
 * A depth that is no non-negative integer keeps no whole number of components, and the key it
 * names does not exist. A depth of 0 keeps none, and the model prints the empty prefix. The type
 * accepts a literal non-negative integer, because the type of the key follows the count. The run
 * time refuses the rest, for a caller without the type. A depth above the count keeps the whole key.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'

type Pet = { shelterId: string; petId: string }

const Pets = tableEntry<Pet>()({ SK: ['shelterId', 'petId'] })

describe('a depth is a non-negative integer', () => {
    it('keeps that many components', () => {
        expect(
            Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 1 }),
        ).toBe('SHELTERID#s')
        expectTypeOf(
            Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 1 }),
        ).toEqualTypeOf<'SHELTERID#s'>()
    })

    it('keeps the whole key where the depth is above the count', () => {
        expect(
            Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 9 }),
        ).toBe('SHELTERID#s#PETID#p')
    })

    it('keeps no component at a depth of 0, and the key is the empty prefix, with or without the boundary', () => {
        const attributes = { shelterId: 's', petId: 'p' }
        expect(Pets.key('SK', attributes, { depth: 0 })).toBe('')
        expect(
            Pets.key('SK', attributes, { depth: 0, enforceBoundary: true }),
        ).toBe('')
    })

    it.each([-1, 1.5, Number.NaN])(
        'refuses the depth %s at run time, and the error names the key',
        (depth) => {
            // a caller without the type: the cast through `unknown` stands for it, because the
            // generic signature is too deep to compare with this one
            const untyped = Pets.key as unknown as (
                name: string,
                attributes: object,
                config: object,
            ) => unknown
            expect(() =>
                untyped('SK', { shelterId: 's', petId: 'p' }, { depth }),
            ).toThrow(
                new RotoriseError('Key SK: depth is a non-negative integer'),
            )
        },
    )

    it('refuses in the type a depth that is a number, a negative and a fraction', () => {
        const depth: number = 1
        const refused = () => {
            // @ts-expect-error a number does not say how many components the key keeps
            void Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth })
            // @ts-expect-error a negative depth keeps no component
            void Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: -1 })
            // @ts-expect-error a fraction keeps no whole number of components
            void Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 1.5 })
        }
        expect(typeof refused).toBe('function')
    })
})
