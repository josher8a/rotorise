/**
 * The options, as they show in the types — and the two that cannot.
 *
 * Each case asserts the type with `attest` and the runtime with an encode, because a shape that
 * described one configuration while the marshaller ran another is the failure worth preventing here:
 * a team would diff against it and migrate on the answer.
 */
import { attest } from '@ark/attest'
import * as sdk from '@aws-sdk/util-dynamodb'
import { describe, expect, it } from 'vitest'
import type { B, BOOL, L, M, N, NULL, S, SS } from './attribute'
import { failed } from './codec'
import { native } from './native'
import type { ErrorMessage } from './utils'

const encoded = (value: unknown, options: native.Options = {}) => {
    const out = native(options).encode(value)
    return failed(out) ? `refused` : out
}

describe('convertEmptyValues shows in the type', () => {
    it('makes a string possibly NULL, because a type cannot see it is empty', () => {
        attest<[native.Encode<string>], [S]>()
        attest<
            [native.Encode<string, { convertEmptyValues: true }>],
            [S | NULL]
        >()

        expect(encoded('')).toEqual({ S: '' })
        expect(encoded('', { convertEmptyValues: true })).toEqual({
            NULL: true,
        })
        expect(encoded('a', { convertEmptyValues: true })).toEqual({ S: 'a' })
    })

    it('is exact where the type is a literal', () => {
        // an empty literal can only be NULL...
        attest<[native.Encode<'', { convertEmptyValues: true }>], [NULL]>()
        // ...and a non-empty one can only be S
        attest<[native.Encode<'PET', { convertEmptyValues: true }>], [S]>()
    })

    it('reaches sets and binary, whose emptiness a type also cannot see', () => {
        attest<[native.Encode<ReadonlySet<string>>], [SS]>()
        attest<
            [native.Encode<ReadonlySet<string>, { convertEmptyValues: true }>],
            [SS | NULL]
        >()
        attest<
            [native.Encode<Uint8Array, { convertEmptyValues: true }>],
            [B | NULL]
        >()

        expect(
            encoded(new Set<string>(), { convertEmptyValues: true }),
        ).toEqual({
            NULL: true,
        })
    })

    it('reaches inside an item', () => {
        type Row = { id: string; n: number }
        attest<[native.ItemEncode<Row>], [{ id: S; n: N }]>()
        attest<
            [native.ItemEncode<Row, { convertEmptyValues: true }>],
            [{ id: S | NULL; n: N }]
        >()
    })
})

describe('removeUndefinedValues shows in the type, inside a list', () => {
    it('refuses a list holding undefined, and drops it once set', () => {
        attest<
            [native.Encode<readonly (string | undefined)[]>],
            [
                ErrorMessage<'[native] a list holds `undefined`, which is refused unless `removeUndefinedValues` is set'>,
            ]
        >()
        attest<
            [
                native.Encode<
                    readonly (string | undefined)[],
                    { removeUndefinedValues: true }
                >,
            ],
            [L<S>]
        >()

        expect(encoded(['a', undefined])).toBe('refused')
        expect(
            encoded(['a', undefined], { removeUndefinedValues: true }),
        ).toEqual({ L: [{ S: 'a' }] })
    })

    it('leaves a list with no undefined alone either way', () => {
        attest<[native.Encode<readonly string[]>], [L<S>]>()
        expect(encoded(['a'])).toEqual({ L: [{ S: 'a' }] })
    })
})

/**
 * The two with no representable effect, and why — so nobody looks for them.
 *
 * These are not omissions to be closed later. `allowImpreciseNumbers` decides whether a number is
 * *refused*, not which member it reaches, so there is no shape for it to change. And a prototype is
 * not visible to a type, so a class instance cannot be told from a plain object.
 */
describe('the two options a type cannot reflect', () => {
    it('allowImpreciseNumbers changes whether it succeeds, not the member', () => {
        attest<[native.Encode<number>], [N]>()
        const wide = 12345678901234567890
        expect(encoded(wide)).toBe('refused')
        expect(encoded(wide, { allowImpreciseNumbers: true })).toEqual({
            N: '12345678901234567000',
        })
    })

    it('convertClassInstanceToMap turns on something a type cannot see', () => {
        class Thing {
            constructor(readonly id: string) {}
        }
        // described as a map whatever the option says, because the prototype is invisible
        attest<[native.Encode<Thing>], [import('./attribute').M<{ id: S }>]>()
        expect(encoded(new Thing('t'))).toBe('refused')
        expect(
            encoded(new Thing('t'), { convertClassInstanceToMap: true }),
        ).toEqual({ M: { id: { S: 't' } } })
    })

    it('and a boolean is a boolean regardless', () => {
        attest<[native.Encode<boolean>], [BOOL]>()
        expect(encoded(true)).toEqual({ BOOL: true })
    })
})

/**
 * The option that is a type rather than an option: the top-level container.
 *
 * `convertTopLevelContainer` belongs to `marshall`, not to `convertToAttr`, and this port is a codec
 * — `encode` produces one attribute, which is what an attribute codec is. So there is no option to
 * pass; there are two types, and choosing between them *is* the choice. Asserted against the SDK
 * itself, both readings, so the mapping cannot quietly stop being true.
 *
 * The same pairing runs the other way: {@link native.Decode} reads a wrapped attribute where
 * {@link native.ItemDecode} reads a bare map, which is `unmarshall`'s `convertWithoutMapWrapper`.
 */
describe('the top-level container is the choice between two types', () => {
    type Row = { a: number }
    const row: Row = { a: 1 }

    it('native.encode matches convertToAttr, which always wraps', () => {
        const ours = native.encode(row)
        expect(ours).toEqual(sdk.convertToAttr(row))
        expect(ours).toEqual({ M: { a: { N: '1' } } })
        // and that wrapped reading is `Encode`
        attest<[native.Encode<Row>], [M<{ a: N }>]>()
    })

    it('marshall unwraps by default, which is ItemEncode', () => {
        expect(sdk.marshall(row)).toEqual({ a: { N: '1' } })
        attest<[native.ItemEncode<Row>], [{ a: N }]>()
    })

    it('and marshall with the option set is Encode again', () => {
        expect(sdk.marshall(row, { convertTopLevelContainer: true })).toEqual(
            native.encode(row),
        )
    })
})
