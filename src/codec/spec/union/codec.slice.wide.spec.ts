/**
 * A literal that is not one value pins nothing that the type can decide, so the slice keeps the
 * member in the extraction and in the exclusion.
 *
 * `string(kind)` where `kind: 'DOG' | 'CAT'` is one value at run time, and the type names two. The
 * constructor keeps the argument as it is. The slice cannot say which value the pattern pins, and
 * a result type that names one value drops a member that the run time keeps. The fit of such a
 * pattern is undecided, so each result type is wider than the value and never narrower. A union,
 * a template literal, a whole base and a spread that is no tuple are the four kinds. Each test
 * assigns a value that the run time keeps to the decoded type.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { Decoded } from '../../codec'
import {
    boolean,
    exclude,
    extract,
    meet,
    number,
    object,
    string,
    union,
} from '../../codec'

const dog = object({ kind: string('DOG') })
const cat = object({ kind: string('CAT') })
const pets = union([dog, cat])
const either = 'DOG' as 'DOG' | 'CAT'
const startsWithD = 'DUCK' as `D${string}`
const spread = ['DOG'] as string[]

const dogStored = { M: { kind: { S: 'DOG' } } }
const catStored = { M: { kind: { S: 'CAT' } } }

describe('a literal pattern that is not one value pins nothing that the type can decide', () => {
    it('keeps the member in the exclusion at a union of literals', () => {
        const rest = exclude(pets, object({ kind: string(either) }))
        expectTypeOf<Decoded<typeof cat>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(rest.decode(catStored)).toEqual({ kind: 'CAT' })
    })

    it('keeps the member in the exclusion at a template literal', () => {
        const rest = exclude(pets, object({ kind: string(startsWithD) }))
        expectTypeOf<Decoded<typeof dog>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(rest.decode(dogStored)).toEqual({ kind: 'DOG' })
    })

    it('keeps the member in the exclusion at a spread that is no tuple', () => {
        const rest = exclude(pets, object({ kind: string(...spread) }))
        expectTypeOf<Decoded<typeof cat>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(rest.decode(catStored)).toEqual({ kind: 'CAT' })
    })

    it('keeps the member in the exclusion at a union of numbers', () => {
        const one = object({ legs: number(4) })
        const two = object({ legs: number(2) })
        const legs = 4 as 4 | 2
        const rest = exclude(union([one, two]), object({ legs: number(legs) }))
        expectTypeOf<Decoded<typeof two>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(rest.decode({ M: { legs: { N: '2' } } })).toEqual({ legs: 2 })
    })

    it('keeps the member in the exclusion at a boolean', () => {
        const yes = object({ vaccinated: boolean(true) })
        const no = object({ vaccinated: boolean(false) })
        const flag = true as boolean
        const rest = exclude(
            union([yes, no]),
            object({ vaccinated: boolean(flag) }),
        )
        expectTypeOf<Decoded<typeof no>>().toMatchTypeOf<Decoded<typeof rest>>()
        expect(rest.decode({ M: { vaccinated: { BOOL: false } } })).toEqual({
            vaccinated: false,
        })
    })

    it('keeps the member in the extraction, as the run time keeps it', () => {
        const kept = extract(pets, object({ kind: string(either) }))
        expectTypeOf<Decoded<typeof dog>>().toMatchTypeOf<
            Decoded<typeof kept>
        >()
        expect(kept.decode(dogStored)).toEqual({ kind: 'DOG' })
    })

    it('keeps in the extraction a member whose literal is not one value', () => {
        const wideDog = object({ kind: string(either) })
        const kept = extract(
            union([wideDog, cat]),
            object({ kind: string('DOG') }),
        )
        expectTypeOf<Decoded<typeof wideDog>>().toMatchTypeOf<
            Decoded<typeof kept>
        >()
        expect(kept.decode(dogStored)).toEqual({ kind: 'DOG' })
    })

    it('reads a literal that is one value exactly', () => {
        const rest = exclude(pets, object({ kind: string('DOG') }))
        const kept = extract(pets, object({ kind: string('DOG') }))
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof cat>
        >()
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof dog>
        >()
    })

    it('reads a boolean literal that is one value exactly', () => {
        const yes = object({ vaccinated: boolean(true) })
        const no = object({ vaccinated: boolean(false) })
        const rest = exclude(
            union([yes, no]),
            object({ vaccinated: boolean(true) }),
        )
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<Decoded<typeof no>>()
    })

    it('meets a wide literal at the value that the other side pins', () => {
        const left = meet(string(either), string('DOG'))
        const right = meet(string('DOG'), string(either))
        expectTypeOf<'DOG'>().toMatchTypeOf<Decoded<typeof left>>()
        expectTypeOf<'DOG'>().toMatchTypeOf<Decoded<typeof right>>()
        expect(left.decode({ S: 'DOG' })).toBe('DOG')
        expect(right.decode({ S: 'DOG' })).toBe('DOG')
    })
})
