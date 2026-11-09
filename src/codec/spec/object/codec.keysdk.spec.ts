/**
 * The key that `toEntry` holds is the key that the AWS SDK writes.
 *
 * `toEntry` builds the item that a consumer hands to `marshall` of `@aws-sdk/util-dynamodb`. At an
 * `N` key the SDK writes a `number` within the safe integer range and a `bigint` of any size, and it
 * refuses a `number` outside the range. DynamoDB normalises a number on write, so the key is held as
 * a `number` where the number equals the numeral that `toItem` writes, whatever the spelling: `1e-7`
 * and `0.0000001` are one number. A numeral that is an integer outside the range is held as a
 * `bigint`. A numeral that is no integer, and that no `number` holds, has no form that the SDK
 * writes, so `toEntry` refuses it and points to `toItem`.
 */
import { marshall, unmarshall } from '@aws-sdk/util-dynamodb'
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import type { AttributeMap, AttributeValue } from '../../attribute'
import { decimal, number, string } from '../../codec'

const Measures = tableEntry<{ id: string; value: number }>()(
    { PK: ['id'], SK: 'value' },
    { codec: { id: string, value: number } },
)
const Weights = tableEntry<{ id: string; weight: string }>()(
    { PK: ['id'], SK: 'weight' },
    { codec: { id: string, weight: decimal } },
)

/** The attribute that the SDK writes for the key alone: the entity holds its own number, past the range. */
const marshalled = (key: unknown): AttributeValue =>
    marshall({ SK: key }).SK as AttributeValue

const written = (row: unknown): AttributeMap => {
    if (row instanceof Error) throw row
    return row as AttributeMap
}

describe('toEntry holds a key of N as the SDK writes it, and the SDK reads it back', () => {
    it('holds a number that equals the numeral as a number, whatever its spelling', () => {
        const entry = Measures.toEntry({ id: 'm1', value: 1e-7 })
        expect(entry.SK).toBe(1e-7)
        expect(written(Measures.toItem({ id: 'm1', value: 1e-7 })).SK).toEqual({
            N: '0.0000001',
        })
        // the SDK writes the spelling of the number, and DynamoDB reads both as one number
        expect(marshalled(entry.SK)).toEqual({ N: '1e-7' })
        expect(unmarshall({ SK: marshalled(entry.SK) } as never).SK).toBe(1e-7)
    })

    it('holds an integer outside the safe range as a bigint, which the SDK writes in full', () => {
        const past = 2 ** 53 + 2
        const entry = Measures.toEntry({ id: 'm1', value: past })
        expect(entry.SK).toBe(9007199254740994n)
        expect(marshalled(entry.SK)).toEqual({ N: '9007199254740994' })
        expect(written(Measures.toItem({ id: 'm1', value: past })).SK).toEqual({
            N: '9007199254740994',
        })
        expect(unmarshall({ SK: marshalled(entry.SK) } as never).SK).toBe(
            9007199254740994n,
        )
        const big = Measures.toEntry({ id: 'm1', value: 1e21 })
        expect(big.SK).toBe(10n ** 21n)
        expect(marshalled(big.SK)).toEqual({ N: '1000000000000000000000' })
    })

    it('holds a number within the safe range as a number', () => {
        const entry = Measures.toEntry({ id: 'm1', value: 3 })
        expect(entry.SK).toBe(3)
        expect(marshalled(entry.SK)).toEqual({ N: '3' })
    })

    it('refuses a numeral that the SDK cannot write, and points to toItem', () => {
        const numeral = '12345678901234567890.123'
        const row = written(Weights.toItem({ id: 'w1', weight: numeral }))
        expect(row.SK).toEqual({ N: numeral })
        expect(() => Weights.toEntry({ id: 'w1', weight: numeral })).toThrow(
            RotoriseError,
        )
        expect(() => Weights.toEntry({ id: 'w1', weight: numeral })).toThrow(
            /Read the key from toItem/,
        )
    })
})
