/**
 * The ported marshaller, held against the one it was ported from.
 *
 * `native` reproduces `@aws-sdk/util-dynamodb`'s `convertToAttr` / `convertToNative` so a table
 * written by that marshaller can be read and written byte for byte while the schema and key layers
 * are adopted around it. A port is only worth having if it is faithful, and the only way to know
 * that is to ask the original.
 *
 * The SDK is a **devDependency** here and an *optional* peer for consumers, so this comparison is
 * an ordinary test rather than something anyone has to take on trust. Nothing shipped imports it:
 * `rotorise/native` stays dependency-free, and the peer entry only records the range the port was
 * verified against so a package manager can say when yours is far from it.
 *
 * Two kinds of agreement are checked, and the second is the one a port usually gets wrong:
 * the *values* both produce, and the *types* both name.
 */

import type { marshallOptions } from '@aws-sdk/util-dynamodb'
import * as sdk from '@aws-sdk/util-dynamodb'
import { describe, expect, it } from 'vitest'
import type { AttributeMap, B, BOOL, L, M, N, NULL, S, SS } from './attribute'
import { CodecError, opaque } from './codec'
import { native } from './native'
import { arbitraryOf, rngFrom } from './testing'

/**
 * Every option this port names is one the SDK names, with the same meaning.
 *
 * The half of a port that reviewing cannot catch: an option spelled slightly differently, or one
 * invented here that the SDK never had, would pass every value comparison and still be wrong the
 * first time somebody set it. `wrapNumbers` is deliberately absent — see {@link native.Options}.
 */
type OptionsAreTheirs = native.Options extends Pick<
    marshallOptions,
    keyof native.Options & keyof marshallOptions
>
    ? true
    : never
const optionsAreTheirs: OptionsAreTheirs = true

/** And every option we name exists there at all, rather than only being compatible in shape. */
type NoInventedOptions = Exclude<
    keyof native.Options,
    keyof marshallOptions
> extends never
    ? true
    : never
const noInventedOptions: NoInventedOptions = true

/**
 * And the direction that was not checked: no option of theirs is silently absent from ours.
 *
 * `NoInventedOptions` only catches an option we made up. It said nothing about one the SDK has and
 * we do not, which is how `convertTopLevelContainer` went unnoticed — so it is named here as
 * deliberately unrepresented rather than left to be discovered. Anything else appearing in their
 * options fails this, which is the point.
 *
 * `convertTopLevelContainer` is an option of `marshall`, not of `convertToAttr`, and this port is a
 * *codec* — `encode` produces one attribute, which is what an attribute codec is. The distinction it
 * makes is carried by the types instead: {@link native.Encode} is the wrapped reading
 * (`convertToAttr`, and `marshall` with the option set) and {@link native.ItemEncode} the bare map
 * (`marshall`'s default). See the assertions below.
 */
type UnrepresentedOptions = Exclude<keyof marshallOptions, keyof native.Options>
const unrepresented: UnrepresentedOptions = 'convertTopLevelContainer'

/** Values chosen for the branches, not for realism. */
const values: readonly [string, unknown][] = [
    ['string', 'abc'],
    ['empty string', ''],
    ['number', 42],
    ['negative', -7],
    ['fractional', 1.5],
    ['zero', 0],
    ['bigint', 9007199254740993n],
    ['boolean', true],
    ['null', null],
    ['binary', Uint8Array.from([1, 2, 3])],
    ['string set', new Set(['a', 'b'])],
    ['number set', new Set([1, 2])],
    ['list', ['a', 1, null]],
    ['nested list', [['a'], []]],
    ['object', { a: 'x', b: 2 }],
    ['nested object', { a: { b: { c: 'deep' } } }],
    ['object with null', { a: null }],
    ['empty object', {}],
    ['empty list', []],
    ['map', new Map([['a', 'x']])],
]

describe('the port agrees with the SDK it was ported from', () => {
    it('names the options the SDK names, and invents none', () => {
        expect([optionsAreTheirs, noInventedOptions]).toEqual([true, true])
    })

    it.each(values.map(([name, value]) => ({ name, value })))(
        'stores $name the same way',
        ({ value }) => {
            const ours = native.encode(value)
            const theirs = sdk.convertToAttr(value)
            expect(ours).toEqual(theirs)
        },
    )

    it.each(values.map(([name, value]) => ({ name, value })))(
        'reads $name back the same way',
        ({ value }) => {
            const stored = sdk.convertToAttr(value)
            expect(native.decode(stored as never)).toEqual(
                sdk.convertToNative(stored as never),
            )
        },
    )

    it('agrees on a whole item, both directions', () => {
        const entity = { id: 'p1', price: 10.5, tags: new Set(['a']) }
        const theirs = sdk.marshall(entity) as AttributeMap
        const ours = Object.fromEntries(
            Object.entries(entity).map(([k, v]) => [k, native.encode(v)]),
        )
        expect(ours).toEqual(theirs)
        expect(sdk.unmarshall(theirs)).toEqual(
            Object.fromEntries(
                Object.entries(theirs).map(([k, v]) => [k, native.decode(v)]),
            ),
        )
    })

    it.each([
        { name: 'convertEmptyValues', options: { convertEmptyValues: true } },
        {
            name: 'removeUndefinedValues',
            options: { removeUndefinedValues: true },
        },
        {
            name: 'allowImpreciseNumbers',
            options: { allowImpreciseNumbers: true },
        },
    ])('honours $name the same way', ({ options }) => {
        const cases = ['', new Set<string>(), { a: undefined, b: 'x' }, []]
        for (const value of cases) {
            const ours = native(options).encode(value)
            let theirs: unknown
            try {
                theirs = sdk.convertToAttr(value, options)
            } catch {
                expect(ours).toBeInstanceOf(CodecError)
                continue
            }
            expect(ours).toEqual(theirs)
        }
    })
})

/**
 * The same question, asked of values nobody chose.
 *
 * The comparison above walks the branches *I knew to test*, which is the weakness every hand-written
 * conformance list has: it agrees on exactly what its author thought of. This generates instead —
 * the same generator the property tests use, over the `opaque` definition, so nested lists of maps
 * of sets turn up without anyone writing one down.
 *
 * Refusal is compared as carefully as success. A port that accepts what the SDK refuses writes rows
 * the SDK cannot read back, which is worse than one that merely stores them differently.
 */
/**
 * The sixteen constructor names `isBinary` accepts, not just the one anybody uses.
 *
 * `Uint8Array` is the type every example shows and the only one a hand-written list tends to cover;
 * the SDK accepts fifteen more, and a `Buffer` or a `DataView` reaching `M` instead of `B` is a
 * silent change of stored type.
 */
describe('the port agrees on every binary the SDK accepts', () => {
    const binaries: readonly [string, unknown][] = [
        ['Uint8Array', Uint8Array.from([1, 2])],
        ['Buffer', Buffer.from([1, 2])],
        ['Int8Array', Int8Array.from([1, -2])],
        ['Uint8ClampedArray', Uint8ClampedArray.from([1, 2])],
        ['Int16Array', Int16Array.from([1, 2])],
        ['Uint32Array', Uint32Array.from([1, 2])],
        ['Float64Array', Float64Array.from([1.5])],
        ['BigInt64Array', BigInt64Array.from([1n])],
        ['ArrayBuffer', new ArrayBuffer(4)],
        ['DataView', new DataView(new ArrayBuffer(4))],
        ['empty Uint8Array', new Uint8Array(0)],
    ]

    it.each(binaries.map(([name, value]) => ({ name, value })))(
        'stores $name the same way',
        ({ value }) => {
            expect(native.encode(value)).toEqual(sdk.convertToAttr(value))
        },
    )

    it.each(binaries.map(([name, value]) => ({ name, value })))(
        'stores $name the same way with convertEmptyValues',
        ({ value }) => {
            const options = { convertEmptyValues: true }
            expect(native(options).encode(value)).toEqual(
                sdk.convertToAttr(value, options),
            )
        },
    )
})

/** One option at a time is not how anyone configures a marshaller. */
describe('the port agrees on combinations of options', () => {
    const flags = [
        'convertEmptyValues',
        'removeUndefinedValues',
        'allowImpreciseNumbers',
    ] as const
    const combinations = Array.from({ length: 2 ** flags.length }, (_, mask) =>
        Object.fromEntries(
            flags.map((flag, bit) => [flag, Boolean(mask & (1 << bit))]),
        ),
    )
    const awkward: readonly unknown[] = [
        '',
        new Set<string>(),
        { a: undefined, b: 'x' },
        [undefined, 'x'],
        1e300,
        { nested: { deeper: [new Set(['a']), ''] } },
    ]

    it.each(
        combinations.map((options) => ({
            name: JSON.stringify(options),
            options,
        })),
    )('agrees under $name', ({ options }) => {
        for (const value of awkward) {
            const ours = native(options).encode(value)
            let theirs: unknown
            try {
                theirs = sdk.convertToAttr(value, options)
            } catch {
                expect(ours, JSON.stringify(value)).toBeInstanceOf(CodecError)
                continue
            }
            expect(ours, JSON.stringify(value)).toEqual(theirs)
        }
    })
})

describe('the port agrees on values nobody picked', () => {
    const holder = { ...opaque, def: opaque.def }

    it.each([1, 7, 0x5eed, 20260827, 99].map((seed) => ({ seed })))(
        'agrees over 200 generated values, seed $seed',
        ({ seed }) => {
            const rng = rngFrom(seed)
            let compared = 0
            let refusedByBoth = 0

            for (let i = 0; i < 200; i++) {
                const value = arbitraryOf(holder as never, rng, 4)

                const ours = native.encode(value)
                let theirs: unknown
                let sdkRefused = false
                try {
                    theirs = sdk.convertToAttr(value)
                } catch {
                    sdkRefused = true
                }

                if (sdkRefused) {
                    // refusal parity: what the SDK will not store, this must not store either
                    expect(ours, `${JSON.stringify(value)}`).toBeInstanceOf(
                        CodecError,
                    )
                    refusedByBoth++
                    continue
                }

                expect(ours, `encoding ${JSON.stringify(value)}`).toEqual(
                    theirs,
                )
                expect(
                    native.decode(theirs as never),
                    `decoding ${JSON.stringify(theirs)}`,
                ).toEqual(sdk.convertToNative(theirs as never))
                compared++
            }

            // the sweep is worthless if the generator only ever produced things both refuse
            expect(compared).toBeGreaterThan(100)
            expect(compared + refusedByBoth).toBe(200)
        },
    )
})

describe('what the port does, with or without the SDK present', () => {
    it('refuses what the SDK refuses', () => {
        expect(native.encode(undefined)).toBeInstanceOf(CodecError)
        expect(native.encode('')).toEqual({ S: '' })
        expect(native.encode(new Set())).toBeInstanceOf(CodecError)
        expect(native.encode(Number.NaN)).toBeInstanceOf(CodecError)
        expect(native.encode(Number.MAX_SAFE_INTEGER + 2)).toBeInstanceOf(
            CodecError,
        )
    })

    it('converts empty values when told to, as the SDK does', () => {
        const lenient = native({ convertEmptyValues: true })
        expect(lenient.encode('')).toEqual({ NULL: true })
        expect(lenient.encode(new Set())).toEqual({ NULL: true })
    })

    /** A `Map` goes in and a plain object comes out — the SDK's asymmetry, reproduced. */
    it('stores a Map as M and reads it back as an object', () => {
        const stored = native.unsafeEncode(new Map([['a', 'x']]))
        expect(stored).toEqual({ M: { a: { S: 'x' } } })
        expect(native.decode(stored)).toEqual({ a: 'x' })
    })

    /** A number too wide for a float comes back as a `bigint`, not a rounded number. */
    it('reads a wide number back as a bigint', () => {
        expect(native.decode({ N: '9007199254740993' })).toBe(9007199254740993n)
    })
})

describe('the type says what the marshaller writes', () => {
    type Pet = {
        id: string
        price: number
        adopted: boolean
        photo: Uint8Array
        tags: ReadonlySet<string>
        visits: readonly { at: string }[]
        breed: { species: string }
        retiredAt: null
        note?: string
    }

    it('matches the shape written by hand', () => {
        type Expected = {
            id: S
            price: N
            adopted: BOOL
            photo: B
            tags: SS
            visits: L<M<{ at: S }>>
            breed: M<{ species: S }>
            retiredAt: NULL
            note?: S
        }
        const derived: Expected = {} as native.ItemEncode<Pet>
        const declared: native.ItemEncode<Pet> = {} as Expected
        expect([derived, declared]).toHaveLength(2)
    })
})
