/**
 * A check that runs no case is no green run.
 *
 * Each generated check reads a count. A count is a positive integer. Zero, a negative count and
 * `NaN` run no case, and a fraction is no whole number of cases, so the check refuses the count
 * and says why.
 */
import { describe, expect, it } from 'vitest'
import { item, number, object, string } from '../../codec'
import {
    checkAgainst,
    checkDecodesAreWritable,
    checkEncodePaths,
    checkEquivalent,
    checkIso,
    checkRoundTrip,
} from '../../testing'

const Pet = item(object({ petId: string, age: number }))
const Named = string
const reference = { marshall: () => ({}) }
const identity = {
    encode: (value: unknown) => value,
    decode: (held: unknown) => held,
}

const checks = {
    checkRoundTrip: (count: number) => checkRoundTrip(Pet, { count }),
    checkDecodesAreWritable: (count: number) =>
        checkDecodesAreWritable(Pet, { count }),
    checkEncodePaths: (count: number) =>
        checkEncodePaths(Pet as never, { count } as never),
    checkEquivalent: (count: number) =>
        checkEquivalent(Pet as never, Pet as never, { count }),
    checkIso: (count: number) =>
        checkIso(Named, identity as never, { count } as never),
    checkAgainst: (count: number) =>
        checkAgainst(Pet, reference as never, { count }),
} as const

describe('a check with a count that is no whole number of one or more cases', () => {
    const refused =
        /is not a whole number of one or more cases; give a count of one or more whole cases/
    for (const [name, run] of Object.entries(checks)) {
        for (const [what, count] of [
            ['zero', 0],
            ['a negative count', -1],
            ['NaN', Number.NaN],
        ] as const)
            it(`${name} refuses ${what}, because it would test nothing`, () => {
                expect(() => run(count)).toThrow(refused)
            })
        for (const [what, count] of [
            ['a fraction below one', 0.5],
            ['a fraction above one', 1.5],
        ] as const)
            it(`${name} refuses ${what}, because a count is a whole number of cases`, () => {
                expect(() => run(count)).toThrow(refused)
            })
    }

    it('names the count that it refused', () => {
        expect(() => checkRoundTrip(Pet, { count: 0 })).toThrow(
            /^a count of 0 is not a whole number/,
        )
        expect(() => checkRoundTrip(Pet, { count: Number.NaN })).toThrow(
            /^a count of NaN is not a whole number/,
        )
    })
})
