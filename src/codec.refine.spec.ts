/**
 * Generating values for a refined codec, and saying when that goes badly.
 *
 * `refine` takes a predicate, which is what a brand *is*. Generation is a different concern: it only
 * matters when a property run happens, so demanding an example beside every predicate would tax
 * every declaration for something most of them never reach. The fallback filters the inner codec's
 * values instead — and reports when that thins a run enough to matter.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, decimal, object, refine, string } from './codec'
import { checkRoundTrip, rngFrom } from './testing'

declare const brand: unique symbol
type Brand<T, B> = T & { [brand]: B }
type SequenceValue = Brand<string, 'sequence'>
type Uuid = Brand<string, 'uuid'>

const isSequence = (v: string): v is SequenceValue =>
    Number.isInteger(Number(v)) && Number(v) >= 0
const isUuid = (v: string): v is Uuid => /^[0-9a-f]{8}-/.test(v)

describe('a predicate the inner codec rarely satisfies', () => {
    it('reports the rate rather than thinning the run in silence', () => {
        const thin: [string, number][] = []
        const sequence = refine(decimal, isSequence, {
            describe: 'a sequence',
            onThinSearch: (what, rate) => thin.push([what, rate]),
        })
        const Entity = object({ sequence }).item

        checkRoundTrip(Entity, { count: 100, seed: 1 })

        expect(thin).toHaveLength(1)
        const [what, rate] = thin[0] as [string, number]
        expect(what).toBe('a sequence')
        // `decimal` yields fractions and negatives, so under half survive
        expect(rate).toBeLessThan(0.5)
    })

    it('says it once, not once per generated value', () => {
        const thin: string[] = []
        const sequence = refine(decimal, isSequence, {
            describe: 'a sequence',
            onThinSearch: (what) => thin.push(what),
        })
        checkRoundTrip(object({ sequence }).item, {
            count: 300,
            seed: 2,
        })
        expect(thin).toEqual(['a sequence'])
    })

    it('says nothing when the search is healthy', () => {
        const thin: string[] = []
        const anything = refine(
            string,
            (_v): _v is Brand<string, 'any'> => true,
            {
                describe: 'anything',
                onThinSearch: (what) => thin.push(what),
            },
        )
        checkRoundTrip(object({ v: anything }).item, {
            count: 200,
            seed: 3,
        })
        expect(thin).toEqual([])
    })

    it('says nothing when a generator was given, because nothing is filtered', () => {
        const thin: string[] = []
        const pick = (rng: () => number) =>
            (['0', '1', '42'] as SequenceValue[])[
                Math.floor(rng() * 3)
            ] as SequenceValue
        const sequence = refine(decimal, isSequence, {
            describe: 'a sequence',
            arbitrary: pick,
            onThinSearch: (what) => thin.push(what),
        })
        checkRoundTrip(object({ sequence }).item, {
            count: 200,
            seed: 4,
        })
        expect(thin).toEqual([])
    })
})

describe('a predicate the inner codec never satisfies', () => {
    it('still fails, because there is nothing to thin', () => {
        const uuid = refine(string, isUuid, { describe: 'a uuid' })
        expect(() =>
            checkRoundTrip(object({ id: uuid }).item, {
                count: 10,
            }),
        ).toThrow(CodecError)
    })
})

describe('the fallback is only reached from a generator', () => {
    it('never runs while encoding or decoding', () => {
        const thin: string[] = []
        const sequence = refine(decimal, isSequence, {
            describe: 'a sequence',
            onThinSearch: (what) => thin.push(what),
        })
        const Entity = object({ sequence }).item

        const value = { sequence: '7' as SequenceValue }
        for (let i = 0; i < 500; i++) {
            Entity.unsafeDecode(Entity.unsafeEncode(value))
        }
        expect(thin).toEqual([])
        expect(rngFrom(1)()).toBeGreaterThanOrEqual(0)
    })
})
