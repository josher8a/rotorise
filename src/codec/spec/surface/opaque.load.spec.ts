/**
 * A module that builds a codec at load registers the capabilities of a term first.
 *
 * `opaque.ts` builds `canonicalOpaque` when it loads, and `codecOfTerm` refuses until `prisms.ts`
 * has registered the capabilities of a term. The import of `opaque` below is the first import of
 * the library in this file, so `opaque.ts` is the first module of the library that loads. The test
 * fails at load if `opaque.ts` does not pull `prisms.ts` in itself.
 */
import { describe, expect, it } from 'vitest'
import { opaque } from '../../opaque'

describe('opaque.ts loads alone, because it loads prisms.ts', () => {
    it('reads a stored string back as the string', () => {
        expect(opaque.decode({ S: 'x' })).toBe('x')
    })
})
