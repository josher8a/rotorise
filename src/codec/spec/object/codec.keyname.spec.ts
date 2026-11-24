/**
 * The type of a key prints the tag of a component whose name is a number, as the run time prints it.
 *
 * A component of a key is a name of the entity. The run time prints the name as the tag, so the
 * name `0` gives the tag `0`. The type read a name that is a string only, and the print of a name
 * that is a number had no label. The type of the key and of the entry now hold the label, and a
 * text with another label is refused.
 *
 * A write to the attribute changes the key, as for a name that is a string. `keyUpdates` read a
 * name that is a string only, so the patch of a write to `0` left the stored key stale.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Rows = { 0: string; petId: string }
const row: Rows = { 0: 'zero', petId: 'p1' }

describe('a component whose name is a number prints the number as its tag', () => {
    it('is the tag of a list of one component, in key and in toEntry', () => {
        const Plain = tableEntry<Rows>()({ PK: ['petId'], SK: [0] })
        const key = Plain.unsafeKey('SK', row)
        expectTypeOf(key).toEqualTypeOf<`0#${string}`>()
        expect(key).toBe('0#zero')
        // @ts-expect-error the tag is 0
        const other: typeof key = '~0#zero'
        expect(other).toBe('~0#zero')
        const entry = Plain.unsafeToEntry(row).SK
        expectTypeOf(entry).toEqualTypeOf<`0#${string}`>()
        expect(entry).toBe('0#zero')
    })

    it('is the tag of the first component of a composite key, before the name of a string component', () => {
        const Composite = tableEntry<Rows>()({ PK: [0, 'petId'] })
        const key = Composite.unsafeKey('PK', row)
        expectTypeOf(key).toEqualTypeOf<`0#${string}#PETID#${string}`>()
        expect(key).toBe('0#zero#PETID#p1')
        // @ts-expect-error the tag is 0
        const other: typeof key = '~0#zero#PETID#p1'
        expect(other).toBe('~0#zero#PETID#p1')
    })

    it('is joined with the separator of the entry', () => {
        const Barred = tableEntry<Rows>()(
            { PK: ['petId'], SK: [0] },
            { separator: '|' },
        )
        const key = Barred.unsafeKey('SK', row)
        expectTypeOf(key).toEqualTypeOf<`0|${string}`>()
        expect(key).toBe('0|zero')
        // @ts-expect-error the tag is 0
        const other: typeof key = '~0|zero'
        expect(other).toBe('~0|zero')
    })

    it('is the tag of a component with a transform', () => {
        const Transformed = tableEntry<Rows>()({
            PK: ['petId'],
            SK: [{ at: 0, value: (value: string) => value }],
        })
        const key = Transformed.unsafeKey('SK', row)
        expectTypeOf(key).toEqualTypeOf<`0#${string}`>()
        expect(key).toBe('0#zero')
        // @ts-expect-error the tag is 0
        const other: typeof key = '~0#zero'
        expect(other).toBe('~0#zero')
    })

    it('re-keys the key when an update writes the component', () => {
        const Plain = tableEntry<Rows>()({ PK: ['petId'], SK: [0] })
        expect(Plain.keyUpdates({ 0: 'one' })).toEqual({
            set: { SK: { S: '0#one' } },
            remove: [],
        })
        expect(Plain.keyUpdates({ 0: 'one', petId: 'p1' })).toEqual({
            set: { PK: { S: 'PETID#p1' }, SK: { S: '0#one' } },
            remove: [],
        })
    })
})
