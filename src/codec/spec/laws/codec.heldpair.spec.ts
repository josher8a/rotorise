/**
 * The pair of a `held` writes the held value through the adapter to the stored form, and reads the
 * stored form back through the adapter. The constructor and the bare term share one pair.
 */
import { describe, expect, it } from 'vitest'
import { codecOfTerm } from '../../allKinds'
import type { AnyCodec } from '../../codec'
import { held, string } from '../../codec'
import { termOf } from '../../denote'

describe('the pair of a held codec', () => {
    const upper = held(string, string, {
        encode: (s: string) => s.toUpperCase(),
        decode: (s: string) => s.toLowerCase(),
    })
    const rebuilt = codecOfTerm({ ...termOf(upper) }) as AnyCodec

    for (const [name, codec] of [
        ['constructor', upper as AnyCodec],
        ['bare term', rebuilt],
    ] as const) {
        it(`${name}: encodes the held value to the stored form`, () => {
            expect(codec.encode('ab' as never)).toEqual({ S: 'AB' })
        })
        it(`${name}: decodes the stored form back to the held value`, () => {
            expect(codec.decode({ S: 'AB' } as never)).toBe('ab')
        })
    }
})
