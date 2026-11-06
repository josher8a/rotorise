/**
 * A read refuses an attribute whose payload is no value of its member.
 *
 * An attribute comes from outside the program. `{ S: 5 }` names the member `S` and holds a number,
 * and a read that checks the name of the member only hands the number back as a pet name. Each
 * member has one type of payload, and one check in `expect` holds it for every reader.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import {
    type AnyCodec,
    array,
    binary,
    boolean,
    dynamoNumber,
    nullValue,
    number,
    object,
    opaque,
    string,
} from '../../codec'
import { native } from '../../native'
import { failed } from '../../result'

/** Each member with a payload of another type, and the codec that reads the member. */
const wrong: readonly (readonly [string, AttributeValue, AnyCodec])[] = [
    ['S', { S: 5 } as never, string],
    ['N', { N: 5 } as never, dynamoNumber],
    ['N', { N: 5 } as never, number],
    ['B', { B: 'bytes' } as never, binary],
    ['BOOL', { BOOL: 'true' } as never, boolean],
    ['NULL', { NULL: false } as never, nullValue],
    ['L', { L: 'abc' } as never, array(string)],
    ['M', { M: ['a'] } as never, object({ petName: string })],
    ['SS', { SS: 'ab' } as never, string.set()],
]

describe('a read refuses a payload of the wrong type, for every member', () => {
    it.each(wrong)(
        'at %s, through a codec of the member',
        (_, stored, codec) => {
            expect(failed(codec.decode(stored as never))).toBe(true)
        },
    )

    it.each(wrong)(
        'at %s, through opaque and native, which read every member',
        (_, stored) => {
            expect(failed(opaque.decode(stored as never))).toBe(true)
            expect(failed((native as AnyCodec).decode(stored as never))).toBe(
                true,
            )
        },
    )

    it('names the member and the payload, and no stored value', () => {
        const refused = string.decode({ S: 5 } as never)
        expect(failed(refused)).toBe(true)
        expect(String(refused)).toMatch(/'S' holds number/)
    })

    it('reads the payload that the member holds', () => {
        expect(string.decode({ S: 'Rex' })).toBe('Rex')
        expect(
            object({ petName: string }).decode({
                M: { petName: { S: 'Rex' } },
            }),
        ).toEqual({
            petName: 'Rex',
        })
    })
})
