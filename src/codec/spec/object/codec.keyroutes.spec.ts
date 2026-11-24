/**
 * Each route that reads a component agrees on the name of the component, whatever the form.
 *
 * A component is a name, a number, or a record that holds the name or the number at `at`, with or
 * without a transform. The label that `key` prints, the components that `keyComponents` gives, and
 * the key that `keyUpdates` writes for a write to the name are three readers of the one form. A
 * reader that reads a form another way names another attribute.
 */
import { describe, expect, it } from 'vitest'
import { keyComponents, tableEntry } from '../../../Rotorise'

type Rows = { 0: string; petId: string }
const row: Rows = { 0: 'zero', petId: 'p1' }

const agree = (
    spec: readonly unknown[],
    name: string,
    label: string,
    key: () => string,
    update: () => unknown,
) => {
    expect(key()).toBe(`${label}#${row[name as keyof Rows]}`)
    expect([...keyComponents(spec)]).toEqual([name])
    expect(update()).toEqual({
        set: { SK: { S: `${label}#new` } },
        remove: [],
    })
}

describe('the routes of a component agree on its name, in each form of the component', () => {
    it('is a name', () => {
        const E = tableEntry<Rows>()({ SK: ['petId'] })
        agree(
            ['petId'],
            'petId',
            'PETID',
            () => E.unsafeKey('SK', row),
            () => E.keyUpdates({ petId: 'new' }),
        )
    })

    it('is a number', () => {
        const E = tableEntry<Rows>()({ SK: [0] })
        agree(
            [0],
            '0',
            '0',
            () => E.unsafeKey('SK', row),
            () => E.keyUpdates({ 0: 'new' }),
        )
    })

    it('is a record with a name', () => {
        const E = tableEntry<Rows>()({ SK: [{ at: 'petId' }] })
        agree(
            [{ at: 'petId' }],
            'petId',
            'PETID',
            () => E.unsafeKey('SK', row),
            () => E.keyUpdates({ petId: 'new' }),
        )
    })

    it('is a record with a number', () => {
        const E = tableEntry<Rows>()({ SK: [{ at: 0 }] })
        agree(
            [{ at: 0 }],
            '0',
            '0',
            () => E.unsafeKey('SK', row),
            () => E.keyUpdates({ 0: 'new' }),
        )
    })

    it('is a record with a transform', () => {
        const E = tableEntry<Rows>()({
            SK: [{ at: 'petId', value: (value: string) => value }],
        })
        agree(
            [{ at: 'petId', value: (value: string) => value }],
            'petId',
            'PETID',
            () => E.unsafeKey('SK', row),
            () => E.keyUpdates({ petId: 'new' }),
        )
    })

    it('is a number that stands alone as the spec that keyComponents reads', () => {
        // the type of a key spec refuses a bare number, and the export reads an unknown spec
        expect([...keyComponents(0)]).toEqual(['0'])
    })
})
