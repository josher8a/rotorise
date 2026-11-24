/**
 * An attribute carries its value under the member that the caller names, and under no other member.
 *
 * Each member has its own result: a value written as `N` is never read as `S`. A name that is no
 * member is a broken call, and the call throws with the name, so the error shows the broken caller.
 */
import { describe, expect, it } from 'vitest'
import { type AttributeName, carrying } from '../../attribute'

const bytes = new Uint8Array([1])
const values: { readonly [K in AttributeName]: unknown } = {
    S: 's',
    N: '1',
    B: bytes,
    SS: ['a'],
    NS: ['1'],
    BS: [bytes],
    M: { a: { S: 'x' } },
    L: [{ S: 'x' }],
    BOOL: true,
    NULL: true,
}

describe('an attribute carries its value under the named member only', () => {
    for (const name of Object.keys(values) as AttributeName[]) {
        it(`writes ${name} as one property named ${name}`, () => {
            const written = carrying(name, values[name] as never)
            expect(Object.keys(written)).toEqual([name])
            expect(written).toEqual({ [name]: values[name] })
        })
    }

    it('throws, naming the member, for a name that is no member', () => {
        expect(() => carrying('X' as never, 'x' as never)).toThrow(
            /'X' is no member of an attribute/,
        )
    })
})
