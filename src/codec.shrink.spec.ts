/**
 * Shrinking: reducing a counterexample to the part that actually fails.
 *
 * A generated `Listing` has forty attributes. Without this, a failure prints all forty and leaves you
 * to find the one that matters.
 */
import { describe, expect, it } from 'vitest'
import type { Attribute, AttributeValue } from './attribute'
import { type AttributeCodec, custom, object, optional, string } from './codec'
import { checkRoundTrip } from './testing'

/** Round-trips only strings of three characters or fewer. */
const truncating: AttributeCodec<string, Attribute<'S'>> = custom({
    encode: (value: string) => ({ S: value }) as Attribute<'S'>,
    decode: (attribute) => ((attribute as { S: string }).S ?? '').slice(0, 3),
    arbitrary: (rng) => 'abcdefgh'.slice(0, 1 + Math.floor(rng() * 8)),
    shrink: (value) =>
        value === ''
            ? []
            : [
                  '',
                  value.slice(0, Math.floor(value.length / 2)),
                  value.slice(0, -1),
              ].filter((x) => x !== value),
})

/** Same, but empty throws — a *different* failure mode that shrinking must not drift into. */
const truncatingButEmptyThrows: AttributeCodec<string, Attribute<'S'>> = custom<
    string,
    Attribute<'S'>
>({
    encode: truncating.encode,
    arbitrary: truncating.arbitrary,
    shrink: truncating.shrink,
    decode: (attribute: AttributeValue) => {
        const carried = (attribute as { S: string }).S ?? ''
        // deliberately *thrown*, not returned: a bug in a caller's own codec is not a decoding
        // failure, and this pins that shrinking does not drift into a different failure mode
        if (carried === '') throw new Error('a different bug entirely')
        return carried.slice(0, 3)
    },
})

const messageOf = (run: () => void) => {
    try {
        run()
    } catch (error) {
        return String((error as Error).message)
    }
    throw new Error('expected a counterexample, found none')
}

describe('shrinking', () => {
    it('reduces every attribute that is not the cause', () => {
        const Broken = object({
            a: string,
            b: string,
            c: optional(truncating),
        }).item

        const message = messageOf(() =>
            checkRoundTrip(Broken, { count: 200, seed: 1 }),
        )

        // the irrelevant attributes are gone or emptied...
        expect(message).toMatch(/"a":""/)
        expect(message).toMatch(/"b":""/)
        // ...and what remains is the shortest string that still fails: four characters
        const minimal = message.match(/"c":"([^"]*)"/)?.[1]
        expect(minimal).toHaveLength(4)
        expect(message).toMatch(/shrunk in \d+ steps? from/)
    })

    it('keeps the failing attribute rather than dropping it', () => {
        // `c` is optional, so dropping it would "fix" the failure — shrinking must not take that
        const Broken = object({
            a: string,
            c: optional(truncating),
        }).item
        const message = messageOf(() =>
            checkRoundTrip(Broken, { count: 200, seed: 2 }),
        )
        expect(message).toMatch(/"c":/)
    })

    it('will not trade the failure it found for a different one', () => {
        const Broken = object({
            c: truncatingButEmptyThrows,
        }).item

        const message = messageOf(() =>
            checkRoundTrip(Broken, { count: 200, seed: 3 }),
        )

        // `''` is the smallest candidate and it throws — a different bug, so it is refused
        expect(message).toMatch(/!== x/)
        expect(message).not.toMatch(/a different bug entirely/)
        expect(message).not.toMatch(/"c":""/)
    })

    it('reports the seed, so a counterexample reproduces', () => {
        const Broken = object({ c: truncating }).item
        expect(messageOf(() => checkRoundTrip(Broken, { seed: 4242 }))).toMatch(
            /with seed 4242/,
        )
    })

    it('says nothing about shrinking when the first case is already minimal', () => {
        const Broken = object({
            c: { ...truncating, shrink: undefined },
        }).item
        expect(
            messageOf(() => checkRoundTrip(Broken, { seed: 5 })),
        ).not.toMatch(/shrunk in/)
    })
})
