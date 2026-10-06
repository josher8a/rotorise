/**
 * A numeric read admits the form the store returns, and no other form.
 *
 * DynamoDB accepts `'1.0'`, `'01'` and `'1e0'`, and returns `'1'` for each. The carrier normalises,
 * so a read of `'1.0'` would hold `1` and write `'1'`: the value read would not write back to the
 * attribute read. The store returns no such numeral, so each numeric read refuses the numeral.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import {
    type AnyCodec,
    decimal,
    dynamoNumber,
    number,
    opaque,
} from '../../codec'
import { native } from '../../native'
import { failed } from '../../result'

const refused = ['1.0', '01', '1e0']
const stored = ['1', '1.5']

const reason = (text: string): string =>
    `'${text}' is not in the form the store returns: the store returns '1' for this numeral, so the value read would not write back`

/** Each reader of an `N`, as one codec, with the stored numerals that the codec holds. */
const readers: readonly (readonly [string, AnyCodec, readonly string[]])[] = [
    ['decimal', decimal, stored],
    ['dynamoNumber', dynamoNumber, stored],
    ['number', number, stored],
    // one alternative, because more than one report that no option admits the numeral
    ['a numeric literal', number(1), ['1']],
    ['opaque', opaque, stored],
    ['native', native as AnyCodec, stored],
]

describe('a numeric read refuses a numeral that the store would not return, so every read writes back', () => {
    for (const [name, codec, holds] of readers) {
        it(`at ${name}`, () => {
            for (const text of refused) {
                const read = codec.decode({ N: text })
                expect(failed(read) && read.message).toBe(reason(text))
            }
            for (const text of holds) {
                const read = codec.unsafeDecode({ N: text })
                expect(codec.unsafeEncode(read as never)).toEqual({ N: text })
            }
        })
    }

    it('at a numeric literal of more than one alternative', () => {
        const literal = number(1, 1.5)
        for (const text of refused) {
            expect(failed(literal.decode({ N: text }))).toBe(true)
        }
        for (const text of stored) {
            const read = literal.unsafeDecode({ N: text })
            expect(literal.unsafeEncode(read)).toEqual({ N: text })
        }
    })

    const sets: readonly (readonly [string, AnyCodec])[] = [
        ['number.set()', number.set()],
        ['decimal.set()', decimal.set()],
        ['opaque', opaque],
        ['native', native as AnyCodec],
    ]
    for (const [name, codec] of sets) {
        it(`at an NS, read by ${name}`, () => {
            for (const text of refused) {
                const attribute: AttributeValue = { NS: ['2', text] }
                const read = codec.decode(attribute)
                expect(failed(read) && read.message).toContain(reason(text))
            }
            const attribute: AttributeValue = { NS: stored }
            const read = codec.unsafeDecode(attribute)
            expect(codec.unsafeEncode(read as never)).toEqual(attribute)
        })
    }
})
