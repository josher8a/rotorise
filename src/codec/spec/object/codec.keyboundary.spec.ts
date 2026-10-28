/**
 * The boundary of a derived key.
 *
 * A key is the segments of its components, joined by the separator. A component prints one or two
 * segments: a name and a value, a tag and a value, or a value alone, where a transform gives an
 * object with no tag. `enforceBoundary` appends one empty segment, so a trailing separator, where
 * the print stops before the last component. A prefix match on a partial key then selects the items
 * that agree on the components, and no item whose component only begins with the same characters.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Row = { a: string; b: string }

const tagless = (x: string) => ({ value: x })
const tagged = (x: string) => ({ tag: 'T', value: x })

describe('a key with enforceBoundary', () => {
    const Mixed = tableEntry<Row>()({
        K: [['a', tagless], 'b'],
        L: [['a', tagless]],
        M: [['a', tagged], 'b'],
        N: ['a', 'b'],
    })
    const row = { a: '1', b: '2' }

    it('has no trailing separator on a full key with a tagless transform', () => {
        expect(Mixed.key('K', row, { enforceBoundary: true })).toBe('1#B#2')
        expect(Mixed.key('L', { a: '1' }, { enforceBoundary: true })).toBe('1')
    })

    it('has a trailing separator on a partial key with a tagless transform', () => {
        expect(
            Mixed.key(
                'K',
                { a: '1' },
                { allowPartial: true, enforceBoundary: true },
            ),
        ).toBe('1#')
        expect(Mixed.key('K', row, { depth: 1, enforceBoundary: true })).toBe(
            '1#',
        )
    })

    it('leaves the key of a spec with no tagless transform as it was', () => {
        expect(Mixed.key('M', row, { enforceBoundary: true })).toBe('T#1#B#2')
        expect(Mixed.key('N', row, { enforceBoundary: true })).toBe('A#1#B#2')
        expect(Mixed.key('N', row, { depth: 1, enforceBoundary: true })).toBe(
            'A#1#',
        )
    })

    it('adds nothing where the option is absent', () => {
        expect(Mixed.key('K', row)).toBe('1#B#2')
        expect(Mixed.key('K', row, { depth: 1 })).toBe('1')
    })
    it('reads the same option in the type of the key', () => {
        const as = { a: '1', b: '2' } as const
        const full: 'A#1#B#2' = Mixed.key('N', as, { enforceBoundary: true })
        const cut: 'A#1#' = Mixed.key('N', as, {
            depth: 1,
            enforceBoundary: true,
        })
        const plain: 'A#1' = Mixed.key('N', as, { depth: 1 })
        const partial: 'A#1#' | 'A#1#B#2' = Mixed.key('N', as, {
            allowPartial: true,
            enforceBoundary: true,
        })
        // a key that stops before the last component ends with the separator, and a full key does not
        // @ts-expect-error the key stops before the last component, so the separator ends it
        const wrong: 'A#1' = Mixed.key('N', as, {
            depth: 1,
            enforceBoundary: true,
        })
        expect([full, cut, plain, partial, typeof wrong]).toEqual([
            'A#1#B#2',
            'A#1#',
            'A#1',
            'A#1#B#2',
            'string',
        ])
    })
})
