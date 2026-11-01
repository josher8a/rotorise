/**
 * The fit walk stops at a cycle, and the stop is a fit.
 *
 * A recursive entry reaches itself through a `ref`. The order is the greatest fixed point of its
 * rules, so a pair that the walk entered again is below. A walk that decides `'u'` at the cut keeps
 * the entry in the exclusion, and a walk with no stop does not end. Each test below excludes the
 * entry by itself, so the result type holds the other member alone.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { Decoded } from '../../codec'
import {
    array,
    exclude,
    extract,
    object,
    optional,
    ref,
    scope,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'

const stray = object({ kind: string('stray') })
const strayStored = { M: { kind: { S: 'stray' } } }

describe('the fit of a recursive entry at the entry itself', () => {
    it('removes in the exclusion a pet whose friends are pets, as the run time removes it', () => {
        const { Pet } = scope({
            Pet: object({
                kind: string('pet'),
                friends: array(ref('Pet')),
            }),
        })
        const rest = exclude(union([Pet, stray]), Pet)
        const kept = extract(union([Pet, stray]), Pet)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof stray>
        >()
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof Pet>
        >()
        expect(rest.decode(strayStored)).toEqual({ kind: 'stray' })
        expect(
            failed(
                rest.decode({
                    M: { kind: { S: 'pet' }, friends: { L: [] } },
                }),
            ),
        ).toBe(true)
    })

    it('removes in the exclusion an owner whose pets name the owner back, through two entries', () => {
        const { Owner, Pet } = scope({
            Owner: object({
                kind: string('owner'),
                pets: array(ref('Pet')),
            }),
            Pet: object({
                kind: string('pet'),
                owner: optional(ref('Owner')),
            }),
        })
        const rest = exclude(union([Owner, Pet, stray]), Owner)
        const kept = extract(union([Owner, Pet, stray]), Owner)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof Pet> | Decoded<typeof stray>
        >()
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof Owner>
        >()
        expect(rest.decode(strayStored)).toEqual({ kind: 'stray' })
        expect(rest.decode({ M: { kind: { S: 'pet' } } })).toEqual({
            kind: 'pet',
        })
        expect(
            failed(
                rest.decode({
                    M: { kind: { S: 'owner' }, pets: { L: [] } },
                }),
            ),
        ).toBe(true)
    })
})
