/**
 * The pin: the codec equals the model, and an optional key cannot slip past it.
 *
 * `satisfies AttributeCodec<T>` asks for assignability both ways. An object without `k?` is
 * assignable to an object with it, and back, so a codec that drops or adds an optional key still
 * satisfies. The pin also compares the key paths with their optional marks. Each case below is a
 * compile-time check: a refused pair carries a `@ts-expect-error`, and `tsc` fails where the pin
 * accepts it.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeCodec } from '../../codec'
import { array, object, optional, string, union } from '../../codec'
import { pin } from '../../pin'

describe('the pin accepts a codec that has the key paths of the model', () => {
    it('accepts the same keys', () => {
        const codec = object({ a: string })
        expect(pin<{ readonly a: string }>()(codec)).toBe(codec)
    })
    it('accepts an intersection against its flat object', () => {
        const codec = object({ a: string, b: string })
        expect(pin<{ a: string } & { b: string }>()(codec)).toBe(codec)
    })
    it('accepts a split union against its compact form', () => {
        const codec = object({
            s: union([string('A'), string('B')]),
            x: string,
        })
        type Split = { s: 'A'; x: string } | { s: 'B'; x: string }
        expect(pin<Split>()(codec)).toBe(codec)
    })
    it('accepts the same optional mark two levels down', () => {
        const codec = object({
            o: object({ a: string, b: optional(string) }),
        })
        expect(pin<{ o: { a: string } & { b?: string } }>()(codec)).toBe(codec)
    })
    it('accepts the keys of the elements of a list', () => {
        const codec = object({ rows: array(object({ id: string })) })
        expect(pin<{ rows: readonly { id: string }[] }>()(codec)).toBe(codec)
    })
})

describe('the pin refuses a codec that differs from the model in a key path', () => {
    it('refuses an optional key that the codec drops, which satisfies accepts', () => {
        type Model = { a: string; q?: string }
        const codec = object({ a: string })
        codec satisfies AttributeCodec<Model>
        // @ts-expect-error the model has the path '.q?' and the codec has not
        pin<Model>()(codec)
        expect(codec).toBeDefined()
    })
    it('refuses an optional key that the codec adds, which satisfies accepts', () => {
        type Model = { a: string }
        const codec = object({ a: string, q: optional(string) })
        codec satisfies AttributeCodec<Model>
        // @ts-expect-error the codec has the path '.q?' and the model has not
        pin<Model>()(codec)
        expect(codec).toBeDefined()
    })
    it('refuses a key dropped two levels down', () => {
        type Model = { o: { a: string; n?: number } }
        const codec = object({ o: object({ a: string }) })
        codec satisfies AttributeCodec<Model>
        // @ts-expect-error the model has the path '.o.n?' and the codec has not
        pin<Model>()(codec)
        expect(codec).toBeDefined()
    })
    it('refuses a required key against an optional key', () => {
        // @ts-expect-error '.a' and '.a?' are different paths
        pin<{ a?: string }>()(object({ a: string }))
    })
    it('refuses a decoded type that is not assignable both ways', () => {
        // @ts-expect-error the literal 'A' is not the model string
        pin<{ a: string }>()(object({ a: string('A') }))
    })
})
