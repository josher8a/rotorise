/**
 * The held type of a foreign schema is its input.
 *
 * `validate` of a Standard Schema takes an input. A schema that transforms has an output type that
 * `validate` refuses, so the held value of a `held` over such a schema is the input type, and the
 * pair round-trips on it. A value of the output type is outside the held side and is refused by
 * name, as a base codec refuses a value past its type.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { z } from 'zod'
import { CodecError } from '../../../Rotorise'
import { type Decoded, held, string } from '../../codec'

describe('a held side over a schema that transforms', () => {
    const Trimmed = z.string().transform((text) => text.trim())
    const clean = held(string, Trimmed, {
        encode: (text) => text,
        decode: (text) => text,
    })

    it('has the input of the schema as its held type', () => {
        expectTypeOf<Decoded<typeof clean>>().toEqualTypeOf<string>()
    })

    it('round-trips a value of the input type', () => {
        expect(clean.decode({ S: ' rex ' })).toBe(' rex ')
        expect(clean.encode(' rex ')).toEqual({ S: ' rex ' })
    })

    it('refuses a value of the output type, because validate takes an input', () => {
        const lengthOf = held(
            string,
            z.string().transform((s) => s.length),
            {
                encode: (text) => text,
                // @ts-expect-error a number is the output of the schema, not its input
                decode: (text) => text.length,
            },
        )
        expect(lengthOf.decode({ S: 'abc' })).toBeInstanceOf(CodecError)
    })
})
