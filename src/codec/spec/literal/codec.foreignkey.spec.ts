/**
 * An attribute is read by the members that DynamoDB has, and a key that no member names is no member.
 *
 * `memberOf` answers one of the ten member names or `undefined`, and the answer does not depend on the
 * key order of the attribute. So each codec gives one verdict for one attribute: a foreign key before
 * the member decides nothing in one codec and everything in another.
 */
import { describe, expect, it } from 'vitest'
import { memberOf } from '../../attribute'
import { array, nullable, number, string, union } from '../../codec'

describe('an attribute that carries a key that no member names', () => {
    it('memberOf answers a member name or undefined, and never the foreign key', () => {
        expect(memberOf({ foo: 1, S: 'x' } as never)).toBe('S')
        expect(memberOf({ S: 'x', foo: 1 } as never)).toBe('S')
        expect(memberOf({ foo: 1 } as never)).toBeUndefined()
    })

    it('string, array, nullable and union give one verdict, whatever the position of the foreign key', () => {
        const first = { foo: 1, S: 'x' } as never
        const last = { S: 'x', foo: 1 } as never
        const verdicts = (attribute: never) => [
            string.decode(attribute),
            nullable(string).decode(attribute),
            union([string, number]).decode(attribute),
        ]
        expect(verdicts(first)).toEqual(verdicts(last))
        const list = { L: [{ S: 'x' }], foo: 1 } as never
        const listFirst = { foo: 1, L: [{ S: 'x' }] } as never
        expect(array(string).decode(list)).toEqual(
            array(string).decode(listFirst),
        )
    })
})
