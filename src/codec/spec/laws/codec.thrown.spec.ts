/**
 * A check that a codec fails names what the codec threw, and a value that is no `Error` names its
 * own text. `error.message` of a thrown string is `undefined`, which hides the failure.
 */
import { describe, expect, it } from 'vitest'
import { item, object, string } from '../../codec'
import type { Checkable } from '../../testing'
import { checkDecodesAreWritable } from '../../testing'

const codec = item(object({ a: string }))

/**
 * A subject that writes as the codec writes until it has read an item, and then throws `thrown`. The
 * read accepts each mutated item, so the check writes the read value again.
 */
const throwingAfterRead = (thrown: unknown): Checkable<{ a: string }> => {
    let read = false
    return {
        def: codec.def,
        unsafeDecode: (item) => {
            read = true
            return { a: String(item) }
        },
        unsafeEncode: (value) => {
            if (!read) return codec.unsafeEncode(value)
            throw thrown
        },
    }
}

describe('a check that cannot write names the thrown value', () => {
    it('a thrown string is named in the failure of the second write', () => {
        expect(() =>
            checkDecodesAreWritable(throwingAfterRead('boom'), { count: 1 }),
        ).toThrow(/encoding it again said: "boom"/)
    })

    it('a thrown object is named in the failure of the second write', () => {
        expect(() =>
            checkDecodesAreWritable(throwingAfterRead({ code: 7 }), {
                count: 1,
            }),
        ).toThrow(/encoding it again said: \{"code":7\}/)
    })

    it('a thrown cyclic object is named by its own text, and the printer does not throw', () => {
        const cyclic: Record<string, unknown> = {}
        cyclic.self = cyclic
        expect(() =>
            checkDecodesAreWritable(throwingAfterRead(cyclic), { count: 1 }),
        ).toThrow(/encoding it again said: \[object Object\]/)
    })

    it('a thrown cyclic object with no prototype is named, though String and the printer both throw on it', () => {
        const bare: Record<string, unknown> = Object.create(null)
        bare.self = bare
        expect(() => String(bare)).toThrow(TypeError)
        expect(() => JSON.stringify(bare)).toThrow(TypeError)
        expect(() =>
            checkDecodesAreWritable(throwingAfterRead(bare), { count: 1 }),
        ).toThrow(/encoding it again said: \[object Object\]/)
    })

    it('a thrown BigInt is named by its own text, and the printer does not throw', () => {
        expect(() =>
            checkDecodesAreWritable(throwingAfterRead(10n), { count: 1 }),
        ).toThrow(/encoding it again said: 10$/m)
    })

    it('a thrown Error is named by its message', () => {
        expect(() =>
            checkDecodesAreWritable(throwingAfterRead(new Error('bang')), {
                count: 1,
            }),
        ).toThrow(/encoding it again said: bang/)
    })
})
