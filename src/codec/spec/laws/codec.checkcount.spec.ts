/**
 * A check that runs no case is no green run.
 *
 * Each generated check reads a count. A count is a positive integer: zero, a negative count, `NaN`
 * and a fraction run no whole case, so the check refuses the count and says why.
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

describe('a check with a count that runs no whole case', () => {
    for (const [name, run] of Object.entries(checks)) {
        for (const [what, count] of [
            ['zero', 0],
            ['a negative count', -1],
            ['NaN', Number.NaN],
            ['a fraction', 0.5],
        ] as const)
            it(`${name} refuses ${what}, because it would test nothing`, () => {
                expect(() => run(count)).toThrow(
                    /runs no case, so the check has nothing to test; give a count of one or more whole cases/,
                )
            })
    }

    it('names the count that it refused', () => {
        expect(() => checkRoundTrip(Pet, { count: 0 })).toThrow(
            /^a count of 0 runs no case/,
        )
        expect(() => checkRoundTrip(Pet, { count: Number.NaN })).toThrow(
            /^a count of NaN runs no case/,
        )
    })
})
