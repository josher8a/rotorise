/**
 * A union of no option admits no value, as `never` does, so there is nothing to generate.
 *
 * `union([])` is a constructor call that the type accepts. The generator refuses it with a
 * CodecError, as it refuses `never`, and does not read an option that the union lacks.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, never, union } from '../../codec'
import { arbitraryOf, rngFrom } from '../../testing'

describe('a union of no option', () => {
    it('is refused by the generator with the CodecError of `never`, and no other error', () => {
        const draw = (codec: Parameters<typeof arbitraryOf>[0]) => {
            try {
                return arbitraryOf(codec, rngFrom(1), 3)
            } catch (error) {
                return error
            }
        }
        const refused = draw(never)
        expect(refused).toBeInstanceOf(CodecError)
        const empty = draw(union([]))
        expect(empty).toBeInstanceOf(CodecError)
        expect((empty as CodecError).message).toBe(
            (refused as CodecError).message,
        )
    })
})
