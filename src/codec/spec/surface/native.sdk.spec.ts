/**
 * `native` follows `convertToAttr` of `@aws-sdk/util-dynamodb`, branch for branch.
 *
 * Each test names the function of the SDK that states the rule, read from the source of the
 * installed version. A port that drifts from a branch writes a row that the SDK would not write.
 */
import { describe, expect, it } from 'vitest'
import { CodecError } from '../../codec'
import { native } from '../../native'

describe('convertToMapAttrFromIterable keeps the entries that convertToMapAttrFromEnumerableProps keeps', () => {
    it('drops a function value of a Map, as it drops one of an object', () => {
        const entries = new Map<string, unknown>([
            ['name', 'Rex'],
            ['bark', () => 1],
        ])
        expect(native.encode(entries)).toEqual({ M: { name: { S: 'Rex' } } })
        expect(native.encode({ name: 'Rex', bark: () => 1 })).toEqual({
            M: { name: { S: 'Rex' } },
        })
    })

    it('drops an undefined value of a Map where removeUndefinedValues is set, and refuses it otherwise', () => {
        const entries = new Map([['nickname', undefined]])
        expect(native({ removeUndefinedValues: true }).encode(entries)).toEqual(
            { M: {} },
        )
        expect(native.encode(entries)).toBeInstanceOf(CodecError)
    })
})

describe('convertToAttr reads a boxed primitive by constructor.name', () => {
    it('writes a boxed String as S, a boxed Number as N and a boxed Boolean as BOOL', () => {
        expect(native.encode(new String('PET'))).toEqual({ S: 'PET' })
        expect(native.encode(new Number(5))).toEqual({ N: '5' })
        expect(native.encode(new Boolean(true))).toEqual({ BOOL: true })
    })

    it('writes the boxed primitive as its primitive, whatever convertClassInstanceToMap says', () => {
        expect(
            native({ convertClassInstanceToMap: true }).encode(
                new String('PET'),
            ),
        ).toEqual({ S: 'PET' })
    })
})

describe('convertToAttr tries convertClassInstanceToMap last', () => {
    it('writes a binary view as B where convertClassInstanceToMap is set', () => {
        expect(
            native({ convertClassInstanceToMap: true }).encode(
                new Uint8Array([1, 2]),
            ),
        ).toEqual({ B: new Uint8Array([1, 2]) })
    })
})
