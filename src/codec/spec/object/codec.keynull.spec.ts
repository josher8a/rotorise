/**
 * A transform of a key component can give no value, and the key prints the empty string there.
 *
 * `Array.join` prints `null` and `undefined` as the empty string, and the builder joins the
 * segments. The type of the key prints the same text, so a caller that matches on the type of a key
 * reads the key that the run time builds.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Pet = { petId: string; collar: string }

describe('a key component that a transform leaves empty', () => {
    it('prints the empty string for a null result, at the type and at run time', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            GSI1PK: [
                'petId',
                [
                    'collar',
                    (collar: string) =>
                        collar === 'NONE' ? null : ('red' as const),
                ],
            ],
        })
        const key = Pets.key('GSI1PK', { petId: 'p1', collar: 'NONE' })
        expectTypeOf(key).toEqualTypeOf<
            'PETID#p1#COLLAR#' | 'PETID#p1#COLLAR#red'
        >()
        expect(key).toBe('PETID#p1#COLLAR#')
    })

    it('prints the empty string for an undefined result, at the type and at run time', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            GSI1PK: [
                'petId',
                [
                    'collar',
                    (collar: string) =>
                        collar === 'NONE' ? undefined : ('red' as const),
                ],
            ],
        })
        const key = Pets.key('GSI1PK', { petId: 'p1', collar: 'NONE' })
        expectTypeOf(key).toEqualTypeOf<
            'PETID#p1#COLLAR#' | 'PETID#p1#COLLAR#red'
        >()
        expect(key).toBe('PETID#p1#COLLAR#')
    })
})
