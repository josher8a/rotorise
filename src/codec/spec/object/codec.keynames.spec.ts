/**
 * `keys(names, item)` reads each component of the named keys from `item`. The second argument is
 * the item, and the type requires it where the first argument is a list of names. A call past the
 * type with no item is a broken call, as an unknown name is: it throws a `RotoriseError` that names
 * the missing item, and it does not return a refusal about an attribute that the caller never lost.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import { failed } from '../../result'

type Entry = { petId: string }
const table = tableEntry<Entry>()(
    { PK: ['petId'] },
    { key: { partition: 'PK' } },
)
const past = table as unknown as Record<
    'keys' | 'unsafeKeys',
    (...args: unknown[]) => unknown
>
const noItem = /gives no item.*The second argument is the item/

describe('keys of names with no item, called past the type', () => {
    it('throws a RotoriseError that names the missing item', () => {
        expect(() => past.keys(['PK'])).toThrow(RotoriseError)
        expect(() => past.keys(['PK'])).toThrow(noItem)
    })

    it('throws the same error where the call is unsafe', () => {
        expect(() => past.unsafeKeys(['PK'])).toThrow(RotoriseError)
        expect(() => past.unsafeKeys(['PK'])).toThrow(noItem)
    })

    it('reads each component from an item that is given', () => {
        const given = past.keys(['PK'], { petId: 'p1' })
        expect(failed(given as never)).toBe(false)
        expect(given).toEqual({ PK: { S: 'PETID#p1' } })
    })
})
