/**
 * A declared attribute named `__proto__` is an own attribute.
 *
 * `JSON.parse` and a spec literal hold `__proto__` as an own data property. A plain assignment of
 * that name runs the setter of `Object.prototype`, so each builder of a declared name writes the
 * name as an own key.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    exclude,
    item,
    meet,
    object,
    optional,
    scope,
    string,
} from '../../codec'

describe('an object that declares an attribute named __proto__', () => {
    const spec = JSON.parse('{"__proto__":{}}') as Record<string, unknown>
    Object.defineProperty(spec, '__proto__', {
        value: string,
        enumerable: true,
        configurable: true,
        writable: true,
    })

    it('builds, and reads the attribute back as an own key', () => {
        const build = () => item(object(spec as never))
        expect(build).not.toThrow()
        const row = JSON.parse('{"__proto__":{"S":"Rex"}}')
        const read = build().decode(row)
        expect(Object.hasOwn(read as object, '__proto__')).toBe(true)
        expect(Object.getOwnPropertyDescriptor(read, '__proto__')?.value).toBe(
            'Rex',
        )
    })

    it('writes the attribute back as an own key', () => {
        const written = item(object(spec as never)).unsafeEncode(
            JSON.parse('{"__proto__":"Rex"}') as never,
        )
        expect(Object.hasOwn(written, '__proto__')).toBe(true)
    })

    it('builds where the field may be absent', () => {
        const absent = JSON.parse('{"__proto__":{}}') as Record<string, unknown>
        Object.defineProperty(absent, '__proto__', {
            value: optional(string),
            enumerable: true,
            configurable: true,
            writable: true,
        })
        expect(() => item(object(absent as never))).not.toThrow()
    })
})

describe('a scope that names an entry __proto__', () => {
    it('keeps the entry as an own entry', () => {
        const entries = JSON.parse('{"__proto__":{}}') as Record<
            string,
            unknown
        >
        Object.defineProperty(entries, '__proto__', {
            value: string,
            enumerable: true,
            configurable: true,
            writable: true,
        })
        const built = scope(entries as never) as unknown as object
        expect(Object.hasOwn(built, '__proto__')).toBe(true)
    })
})

/**
 * Each builder that writes a declared name writes an own key, so a name `__proto__` survives a meet,
 * a slice and a partial write. A plain assignment of the name sets the prototype of the record, and
 * the record then lacks the field.
 */
describe('a pattern or a meet over an attribute named __proto__', () => {
    const named = (value: unknown) => {
        const spec = JSON.parse('{"__proto__":{}}') as Record<string, unknown>
        Object.defineProperty(spec, '__proto__', {
            value,
            enumerable: true,
            configurable: true,
            writable: true,
        })
        return spec
    }
    type Decoder = { unsafeDecode: (row: unknown) => unknown }
    const own = (value: unknown) => Object.hasOwn(value as object, '__proto__')
    const pet = () =>
        object({
            kind: string('dog', 'cat'),
            ...named(string('a', 'b')),
        } as never)
    const row = (text: string) => JSON.parse(text)

    it('keeps the name as an own key in a partial write', () => {
        const written = (
            item(object(named(string) as never)) as unknown as {
                encodePartial: (patch: unknown) => unknown
            }
        ).encodePartial(row('{"__proto__":"a"}'))
        expect(own(written)).toBe(true)
    })

    it('keeps the name as an own key in the meet of two objects that differ', () => {
        const met = meet(
            object({ kind: string('dog', 'cat'), ...named(string) } as never),
            object({ ...named(string) } as never),
        ) as unknown as Decoder
        expect(
            own(
                met.unsafeDecode(
                    row('{"M":{"kind":{"S":"dog"},"__proto__":{"S":"a"}}}'),
                ),
            ),
        ).toBe(true)
    })

    it('keeps the name as an own key in the opening of an exclude pattern', () => {
        const pattern = () => object({ ...named(string('a')) } as never)
        const excluded = exclude(
            pet() as never,
            pattern() as never,
        ) as unknown as Decoder
        expect(
            own(
                excluded.unsafeDecode(
                    row('{"M":{"kind":{"S":"dog"},"__proto__":{"S":"b"}}}'),
                ),
            ),
        ).toBe(true)
    })
})

describe('a key named __proto__', () => {
    const Pets = tableEntry<{ petId: string }>()({
        PK: ['petId'],
        ['__proto__']: ['petId'],
    } as never) as unknown as {
        keyUpdates: (changed: object) => { set: Record<string, unknown> }
        keys: (names: string[], given: object) => Record<string, unknown>
    }

    it('is an own attribute of the update that keyUpdates writes', () => {
        const { set } = Pets.keyUpdates({ petId: 'p2' })
        expect(Object.hasOwn(set, '__proto__')).toBe(true)
    })

    it('is an own attribute of the keys that keys writes', () => {
        const out = Pets.keys(['__proto__'], { petId: 'p2' })
        expect(Object.hasOwn(out, '__proto__')).toBe(true)
    })
})
