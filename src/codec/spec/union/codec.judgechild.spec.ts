/**
 * A term has no codec where the judgment refuses an option of a union, or the element of a set.
 *
 * A slice, a meet or an opening builds a term whose children no former built, so no declaration
 * judged those children. The `union` row and the `set` row of `denote` are where the judgment of
 * such a child runs. A row that read the codec of the child without the judgment gave a codec to a
 * term that the judgment refuses.
 */
import { describe, expect, it } from 'vitest'
import { codecOfTerm } from '../../capabilities'
import type { Term } from '../../term'

const adapted = (): Term => ({
    kind: 'held',
    inner: { kind: 'string' },
    outer: { kind: 'string' },
    f: (value: never) => value,
    g: (held: never) => held,
})

// two adapters on one union: the declaration cannot show that the options are compatible
const incompatible = (): Term => ({
    kind: 'union',
    options: [adapted(), adapted()],
})

describe('a term has no codec where the judgment refuses a child that no former built', () => {
    it('refuses an option of a union that breaks the compatibility rule', () => {
        const outer: Term = { kind: 'union', options: [incompatible()] }
        expect(() => codecOfTerm(outer)).toThrow(/not shown compatible/)
    })

    it('refuses the element of a set that breaks the compatibility rule', () => {
        const set: Term = { kind: 'set', elem: incompatible() }
        expect(() => codecOfTerm(set)).toThrow(/not shown compatible/)
    })
})
