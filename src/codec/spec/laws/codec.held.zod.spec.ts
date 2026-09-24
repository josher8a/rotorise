/**
 * A held side written in zod.
 *
 * The held side of a `held` can be a schema of another library, through the Standard Schema
 * interface. zod ships the same construction as `z.codec(input, output, { decode, encode })`, so
 * the two agree value by value: the output schema answers before `encode` runs, and again on what
 * `decode` returns.
 */
import { describe, expect, it } from 'vitest'
import { z } from 'zod'
import { boolean, CodecError, failed, held, string, union } from '../../codec'

const inputs: readonly unknown[] = [
    new Date(0),
    '2020-01-01',
    42,
    new Date('not a date'),
]

describe('a zod schema as the held side', () => {
    it('refuses a string typed as a Date before encode runs', () => {
        let calls = 0
        const at = held(string, z.date(), {
            encode: (d) => {
                calls += 1
                return d.toISOString()
            },
            decode: (s) => new Date(s),
        })
        const written = at.encode('2020-01-01' as never)
        expect(failed(written)).toBe(true)
        expect((written as CodecError).reason).toMatch(
            /the held side of this `held`, a zod schema, refuses the value before `encode` runs/,
        )
        expect(calls).toBe(0)
    })

    it('refuses what decode returns when the zod schema refuses it', () => {
        const at = held(string, z.date(), {
            encode: (d) => d.toISOString(),
            decode: (s) => new Date(s),
        })
        const read = at.decode({ S: 'not a date' })
        expect(failed(read)).toBe(true)
        expect((read as CodecError).reason).toMatch(
            /refuses the value that `decode` returned/,
        )
    })

    it('accepts and refuses the same values that z.codec accepts and refuses', () => {
        const ours = held(string, z.date(), {
            encode: (d) => d.toISOString(),
            decode: (s) => new Date(s),
        })
        const theirs = z.codec(z.string(), z.date(), {
            decode: (s) => new Date(s),
            encode: (d) => d.toISOString(),
        })
        for (const value of inputs) {
            const written = ours.encode(value as Date)
            const encoded = theirs.safeEncode(value as Date)
            expect(failed(written)).toBe(!encoded.success)
            if (encoded.success) expect(written).toEqual({ S: encoded.data })
        }
    })

    it('needs a discriminator beside another option, because the library does not rule a zod side', () => {
        const at = held(string, z.date(), {
            encode: (d) => d.toISOString(),
            decode: (s) => new Date(s),
        })
        expect(() => union([at, boolean])).toThrow(
            /held and boolean are not shown compatible/,
        )
    })
})
