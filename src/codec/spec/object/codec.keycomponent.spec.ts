/**
 * A component of a key is the stored text of its attribute.
 *
 * A key prints each component. An object has no text of its own, so two objects print one text and
 * two items share one key. An entry with no codec refuses an object component in the type and at run
 * time. An entry with a codec prints the text or the digits that the codec writes, and refuses at
 * construction a component that the codec writes as another member.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import { array, string } from '../../codec'

type Walk = { id: string; n: number; at: Date; blob: Uint8Array }

describe('a key component with no codec', () => {
    it('accepts text and a number, and refuses an object in the type and at run time', () => {
        const Plain = tableEntry<Walk>()({ PK: ['id'], SK: ['id', 'n'] })
        expect(Plain.keys(['SK'], { id: 'a', n: 1 } as Walk)).toEqual({
            SK: { S: 'ID#a#N#1' },
        })
        const Dated = tableEntry<Walk>()({
            PK: ['id'],
            // @ts-expect-error a Date has no text of its own
            SK: ['at'],
        })
        expect(() => Dated.keys(['SK'], { at: new Date(0) } as Walk)).toThrow(
            RotoriseError,
        )
        tableEntry<Walk>()({
            PK: ['id'],
            // @ts-expect-error bytes have no text of their own
            SK: ['blob'],
        })
    })
})

describe('a key component with a codec', () => {
    it('refuses at construction a component that the codec writes as another member', () => {
        expect(() =>
            tableEntry<{ id: string; tags: string[] }>()(
                { PK: ['id'], SK: ['tags'] },
                // @ts-expect-error the type refuses the list as a component too
                { codec: { id: string, tags: array(string) } },
            ),
        ).toThrow(/as a component/)
    })
})
