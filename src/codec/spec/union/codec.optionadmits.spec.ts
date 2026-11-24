/**
 * An option admits a value exactly where its codec writes the value.
 *
 * A union asks each option whether the option writes the value, and the write of the first option
 * that admits it. The option of a literal of base `string` or `boolean` decides the question by
 * `===`, so the union builds no refusal for each option that does not hold the value. Every other
 * option asks its codec. The two routes give one answer, so the table holds a row for each kind of
 * option that `optionOfTerm` builds. A new literal base needs one row.
 */
import { describe, expect, it } from 'vitest'
import { DynamoNumber } from '../../attribute'
import {
    array,
    boolean,
    nullValue,
    number,
    object,
    string,
    termOf,
} from '../../codec'
import { optionOfTerm } from '../../denote'
import { failed } from '../../result'

const kinds = {
    'a literal of base string': string('A'),
    'a literal of base string, empty': string(''),
    'a literal of base boolean, true': boolean(true),
    'a literal of base boolean, false': boolean(false),
    'a literal of base number': number(1),
    'the base string': string,
    'the base number': number,
    null: nullValue,
    'an object': object({ a: string }),
    'a list': array(string),
}

const values: Record<string, unknown> = {
    A: 'A',
    B: 'B',
    'the empty string': '',
    'a lower case letter': 'a',
    'a numeral string': '1',
    'a number': 1,
    zero: 0,
    'a numeral': DynamoNumber.from('1'),
    true: true,
    false: false,
    null: null,
    undefined: undefined,
    'an empty object': {},
    'an object with a': { a: 'x' },
    'an empty list': [],
    'a list of strings': ['x'],
    bytes: new Uint8Array(1),
}

const writes = (encode: (value: never) => unknown, value: unknown): boolean => {
    try {
        return !failed(encode(value as never) as never)
    } catch {
        return false
    }
}

describe('an option admits a value exactly where its codec writes the value', () => {
    for (const [kind, codec] of Object.entries(kinds)) {
        it(`holds for ${kind}`, () => {
            const option = optionOfTerm(termOf(codec as never))
            for (const [what, value] of Object.entries(values)) {
                expect(option.admits(value), `${kind} and ${what}`).toBe(
                    writes(option.codec.encode as never, value),
                )
            }
        })
    }

    it('admits a literal of base string at its own value only', () => {
        const option = optionOfTerm(termOf(string('A')))
        expect(option.admits('A')).toBe(true)
        expect(option.admits('B')).toBe(false)
    })
})
