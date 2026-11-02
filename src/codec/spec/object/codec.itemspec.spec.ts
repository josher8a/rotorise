/**
 * The spec of an item codec holds the codecs that the caller wrote, because the type of the spec
 * says so. A member of the spec offers what the codec at that member offers.
 */
import { describe, expect, it } from 'vitest'
import { item, object, string } from '../../codec'

describe('the spec of an item codec', () => {
    it('holds the codec that the caller wrote at each member', () => {
        const pet = object({ name: string })
        const spec = item(pet).spec
        expect(spec.name).toBe(string)
        expect(spec.name.set).toBeTypeOf('function')
        expect(spec.name('REX').def).toEqual(string('REX').def)
    })

    it('is a member of an object that spreads it', () => {
        const pet = object({ name: string })
        const adopted = object({ ...item(pet).spec, owner: string })
        expect(Object.keys(adopted.spec)).toEqual(['name', 'owner'])
    })
})
