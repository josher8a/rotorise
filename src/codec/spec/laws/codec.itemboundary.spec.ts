/**
 * An item is a plain object of attributes, and an attribute name is a name.
 *
 * The whole-item write asks the record test that the whole-item read asks, so a class instance, an
 * array and `null` are refusals on both sides, as the `M` row refuses them. A record that a read or
 * a write builds holds each name as an own property, `__proto__` included, as `JSON.parse` and
 * `Object.fromEntries` hold it.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, failed } from '../../../Rotorise'
import {
    discriminatedUnion,
    item,
    number,
    object,
    opaque,
    optional,
    string,
} from '../../codec'

class PetRow {
    name = 'Rex'
    species = 'dog' as const
}

describe('a whole-item write', () => {
    const Pet = object({ name: string, species: string('cat', 'dog') })
    const Tagged = discriminatedUnion('kind', [
        object({ kind: string('dog'), bark: string }),
        object({ kind: string('cat'), lives: number }),
    ])

    it('refuses a value that is no plain object, as the attribute write refuses it', () => {
        expect(Pet.encode(new PetRow())).toBeInstanceOf(CodecError)
        for (const Whole of [item(Pet), item(Tagged)]) {
            for (const bad of [new PetRow(), ['x'], null, undefined]) {
                expect(Whole.encode(bad as never)).toBeInstanceOf(CodecError)
                expect(Whole.encodePartial(bad as never)).toBeInstanceOf(
                    CodecError,
                )
            }
        }
    })

    it('still writes a plain object', () => {
        expect(item(Pet).encode({ name: 'Rex', species: 'dog' })).toEqual({
            name: { S: 'Rex' },
            species: { S: 'dog' },
        })
        expect(item(Tagged).encode({ kind: 'dog', bark: 'w' })).toEqual({
            kind: { S: 'dog' },
            bark: { S: 'w' },
        })
    })
})

describe('an attribute named __proto__', () => {
    const Open = object({}, [string, optional(string)])

    it('is read as an own attribute, not dropped', () => {
        const read = opaque.decode(JSON.parse('{"M":{"__proto__":{"S":"x"}}}'))
        expect(failed(read)).toBe(false)
        expect(Object.hasOwn(read as object, '__proto__')).toBe(true)
        const open = Open.decode(JSON.parse('{"M":{"__proto__":{"S":"x"}}}'))
        expect(Object.hasOwn(open as object, '__proto__')).toBe(true)
        const whole = item(object({ a: string }, [string, optional(string)]))
        const row = whole.decode(
            JSON.parse('{"a":{"S":"x"},"__proto__":{"S":"y"}}'),
        )
        expect(Object.keys(row as object).sort()).toEqual(['__proto__', 'a'])
    })

    it('is written as an own attribute, not dropped', () => {
        const written = Open.encode(JSON.parse('{"__proto__":"x"}')) as {
            M: object
        }
        expect(Object.hasOwn(written.M, '__proto__')).toBe(true)
        const whole = item(object({ a: string }, [string, optional(string)]))
        const row = whole.encode(JSON.parse('{"a":"x","__proto__":"y"}'))
        expect(Object.keys(row as object).sort()).toEqual(['__proto__', 'a'])
    })

    it('reads back what it wrote', () => {
        const value = JSON.parse('{"__proto__":"x"}')
        const written = Open.encode(value)
        expect(failed(written)).toBe(false)
        expect(Open.decode(written as never)).toEqual(value)
    })
})
