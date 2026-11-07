/**
 * The ported marshaller, held against the one it was ported from.
 *
 * `native` reproduces `@aws-sdk/util-dynamodb`'s `convertToAttr` / `convertToNative` so a table
 * written by that marshaller can be read and written as the same stored data while the schema and key layers
 * are adopted around it. A port is only worth having if it is faithful, and the only way to know
 * that is to ask the original.
 *
 * The SDK is a **devDependency** here and an *optional* peer for consumers, so this comparison is
 * an ordinary test rather than something anyone has to take on trust. Nothing shipped imports it:
 * `rotorise/native` stays dependency-free, and the peer entry only records the range the port was
 * verified against so a package manager can say when yours is far from it.
 *
 * Two kinds of agreement are checked, and the second is the one a port usually gets wrong:
 * the *values* both produce, and the *types* both name. Then the one **disagreement**, which is
 * where the port stops being faithful on purpose: the SDK does not check that an `N` carries a
 * numeral, in either direction, and this does.
 */

import { File } from 'node:buffer'
import type { marshallOptions } from '@aws-sdk/util-dynamodb'
import * as sdk from '@aws-sdk/util-dynamodb'
import { describe, expect, expectTypeOf, it } from 'vitest'
import type {
    AttributeMap,
    B,
    BOOL,
    L,
    M,
    N,
    NS,
    NULL,
    S,
    SS,
} from '../../attribute'
import { DynamoNumber } from '../../attribute'
import {
    CodecError,
    fits,
    item,
    object,
    opaque,
    orThrow,
    termOf,
} from '../../codec'
import { native } from '../../native'
import { arbitraryOf, rngFrom } from '../../testing'

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
void unrepresented

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
        const theirs = sdk.marshall(entity)
        const ours = Object.fromEntries(
            Object.entries(entity).map(([k, v]) => [k, native.encode(v)]),
        )
        expect(ours).toEqual(theirs)
        expect(sdk.unmarshall(theirs)).toEqual(
            Object.fromEntries(
                // the SDK's wire type, read by this library's decoder
                Object.entries(theirs as AttributeMap).map(([k, v]) => [
                    k,
                    native.decode(v),
                ]),
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
 * the same arbitrary the property tests use, over the `opaque` definition, so nested lists of maps
 * of sets turn up without anyone writing one down.
 *
 * Refusal is compared as carefully as success. A port that accepts what the SDK refuses writes rows
 * the SDK cannot read back, which is worse than one that merely stores them differently.
 * @anchored
 */
/**
 * The sixteen constructor names `isBinaryValue` accepts, not just the one anybody uses.
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
        // the SDK tests `data.length`, which these two lack, so an empty one is a `B` and no `NULL`
        ['empty ArrayBuffer', new ArrayBuffer(0)],
        ['empty DataView', new DataView(new ArrayBuffer(0))],
    ]

    /**
     * The SDK writes the view itself, and the store holds bytes. The port writes the `Uint8Array`
     * over the same bytes, which is what the store returns, so a read-modify-write keeps the type.
     */
    const bytesOf = (view: unknown): Uint8Array =>
        ArrayBuffer.isView(view)
            ? new Uint8Array(view.buffer, view.byteOffset, view.byteLength)
            : new Uint8Array(view as ArrayBuffer)
    const asBytes = (attribute: unknown): unknown => {
        const stored = (attribute as { B?: unknown }).B
        return stored === undefined ? attribute : { B: bytesOf(stored) }
    }

    it.each(binaries.map(([name, value]) => ({ name, value })))(
        'writes $name as the bytes the store returns',
        ({ value }) => {
            expect(asBytes(native.encode(value))).toEqual(
                asBytes(sdk.convertToAttr(value)),
            )
        },
    )

    it.each(binaries.map(([name, value]) => ({ name, value })))(
        'writes $name as the bytes the store returns with convertEmptyValues',
        ({ value }) => {
            const options = { convertEmptyValues: true }
            expect(asBytes(native(options).encode(value))).toEqual(
                asBytes(sdk.convertToAttr(value, options)),
            )
        },
    )

    it('native writes a typed array as the bytes the store returns', () => {
        const written = native.encode(Int16Array.from([1, 2]))
        expect(written).toEqual({ B: Uint8Array.from([1, 0, 2, 0]) })
        expect((written as { B: unknown }).B).toBeInstanceOf(Uint8Array)
    })
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
        // imprecise, so `allowImpreciseNumbers` decides it — and *inside* the numerals, so the
        // gate below does not. `1e300` was here, which conflated the two checks; it now has its
        // own describe, because that is a disagreement rather than an agreement
        1e30,
        { nested: { deeper: [new Set(['a']), ''] } },
    ]

    /**
     * The SDK writes `1e30` as `1e+30`, and the store returns `1000000000000000000000000000000`.
     * The port writes the second, so each side is compared in the form the store returns.
     */
    const stored = (attribute: unknown): unknown => {
        if (typeof attribute !== 'object' || attribute === null)
            return attribute
        const one = attribute as Record<string, unknown>
        if (typeof one.N === 'string') {
            return { N: orThrow(DynamoNumber.from(one.N)).digits }
        }
        if (Array.isArray(one.L)) return { L: one.L.map(stored) }
        if (typeof one.M === 'object' && one.M !== null) {
            return {
                M: Object.fromEntries(
                    Object.entries(one.M).map(([key, held]) => [
                        key,
                        stored(held),
                    ]),
                ),
            }
        }
        return attribute
    }

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
            expect(stored(ours), JSON.stringify(value)).toEqual(stored(theirs))
        }
    })
})

/**
 * The one place the port deliberately disagrees — and it is the store it agrees with instead.
 *
 * `Carries('N')` is the numerals: 38 significant digits, magnitude `1e-130 … 9.9…e125`. The SDK
 * checks a finite double on the way in and *nothing* on the way out, so `convertToAttr` marshals
 * numbers DynamoDB refuses and `convertToNative` reads back strings DynamoDB never stored. A port
 * faithful there would be the one codec in this package that writes outside `𝔸`, so both halves
 * gate on the same predicate every other term touching an `N` uses.
 *
 * Each case asserts *both* sides: that the SDK really does the thing (so the divergence is a fact
 * about the SDK and not about a test) and that this refuses it.
 */
describe('the port refuses four things the SDK does not', () => {
    const permissive = { allowImpreciseNumbers: true }

    it.each([
        { name: 'too large', value: 1e300 },
        { name: 'denormal', value: 5e-324 },
        // a `bigint` is the case that turns up in real data rather than in a bound: it is exactly
        // how a caller carries more digits than a double holds, and the safe-range check that
        // catches the two above does not look at it at all
        {
            name: '41 significant digits',
            value: 12345678901234567890123456789012345678901n,
        },
    ])('will not write $name, where the SDK will', ({ value }) => {
        expect(sdk.convertToAttr(value, permissive)).toHaveProperty('N')
        expect(native(permissive).encode(value)).toBeInstanceOf(CodecError)
    })

    it.each([
        { name: 'empty', digits: '', reads: 0 },
        { name: 'hexadecimal', digits: '0x10', reads: 16 },
        { name: 'not a number at all', digits: 'abc', reads: Number.NaN },
        {
            name: 'out of range',
            digits: '1e400',
            reads: Number.POSITIVE_INFINITY,
        },
    ])(
        'will not read $name, where the SDK reads it as $reads',
        ({ digits, reads }) => {
            expect(sdk.convertToNative({ N: digits } as never)).toEqual(reads)
            expect(native.decode({ N: digits } as never)).toBeInstanceOf(
                CodecError,
            )
        },
    )

    it.each(['SS', 'NS', 'BS'] as const)(
        'will not read an empty %s, where the SDK returns an empty Set',
        (member) => {
            const stored = { [member]: [] } as never
            expect(sdk.convertToNative(stored)).toEqual(new Set())
            expect(native.decode(stored)).toBeInstanceOf(CodecError)
        },
    )

    /**
     * A refusal reaches a log line, so a refusal that holds the attribute writes the stored data
     * into the log. The SDK names the key of an attribute with no member, and the port names
     * neither the key nor the value.
     */
    it('names no stored value when it refuses an attribute with no member', () => {
        const stored = { petName: 'Rex' } as never
        expect(() => sdk.convertToNative(stored)).toThrow(
            'Unsupported type passed: petName',
        )
        const refused = native.decode(stored)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).toBe(
            'an AttributeValue carrying no member',
        )
    })

    it('will not read an NS holding a non-numeral', () => {
        const stored = { NS: ['1', 'abc'] } as never
        expect(sdk.convertToNative(stored)).toEqual(new Set([1, Number.NaN]))
        expect(native.decode(stored)).toBeInstanceOf(CodecError)
    })

    /**
     * And the way back. A team migrating a table that already holds these rows needs the SDK's
     * reading until they are repaired, which is what {@link native.Deviations} is for — so the
     * divergence is a default, not a wall.
     */
    it('reaches the numerals of the store through deviations, and no non-numeral', () => {
        const sdkLike = native(permissive, {
            writeNumber: (value) => ({ N: value.toString() }),
            readNumber: (digits) => Number(digits),
        })
        expect(sdkLike.encode(1.5)).toEqual(sdk.convertToAttr(1.5, permissive))
        expect(sdkLike.decode({ N: '1.5' })).toBe(1.5)
        // the canonical opaque is under the pair, and it holds numerals only, in both directions
        expect(sdkLike.encode(5e-324)).toBeInstanceOf(CodecError)
        expect(sdkLike.decode({ N: '' } as never)).toBeInstanceOf(CodecError)
    })
})

describe('the port agrees on values nobody picked', () => {
    const holder = { ...opaque, def: opaque.def }

    /**
     * The SDK writes the class it names, `NumberValue`, where the port writes a `DynamoNumber`.
     * The SDK side of the comparison reads the same digits through its own class.
     */
    const asSdk = (value: unknown): unknown => {
        if (value instanceof DynamoNumber) {
            return sdk.NumberValueImpl.from(value.digits)
        }
        if (Array.isArray(value)) return value.map(asSdk)
        if (value instanceof Set) return new Set([...value].map(asSdk))
        if (value instanceof Map) {
            return new Map([...value].map(([key, held]) => [key, asSdk(held)]))
        }
        if (typeof value === 'object' && value !== null) {
            const proto: unknown = Object.getPrototypeOf(value)
            if (proto === Object.prototype || proto === null) {
                return Object.fromEntries(
                    Object.entries(value).map(([key, held]) => [
                        key,
                        asSdk(held),
                    ]),
                )
            }
        }
        return value
    }

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
                    theirs = sdk.convertToAttr(asSdk(value))
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

            // the sweep is worthless if the arbitrary only ever produced things both refuse
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

/**
 * The text of a refusal is a contract: a caller reads it, and the SDK's text is the one the
 * caller already knows. Compared on `reason`, which is the text without the path of the port.
 *
 * One sentence differs by design. The SDK ends a safe-range refusal with "Use NumberValue from
 * @aws-sdk/lib-dynamodb." That advice is false here, because the port does not write that class.
 * The port writes a `DynamoNumber`, and the tail names it, so the advice is true.
 */
describe('the port refuses what the SDK refuses, with the text of the SDK', () => {
    const sdkTail = 'Use NumberValue from @aws-sdk/lib-dynamodb.'
    const portTail = 'Use DynamoNumber from rotorise.'
    class Pet {
        name = 'Rex'
    }

    const pool: readonly { name: string; value: unknown }[] = [
        { name: 'NaN', value: Number.NaN },
        { name: 'Infinity', value: Number.POSITIVE_INFINITY },
        { name: '-Infinity', value: Number.NEGATIVE_INFINITY },
        { name: '2 ** 60', value: 2 ** 60 },
        { name: '-(2 ** 60)', value: -(2 ** 60) },
        { name: 'undefined', value: undefined },
        { name: 'a list holding undefined', value: [1, undefined] },
        { name: 'an object holding undefined', value: { a: undefined } },
        { name: 'a Set holding undefined', value: new Set(['a', undefined]) },
        { name: 'a Map holding undefined', value: new Map([['a', undefined]]) },
        { name: 'an empty Set', value: new Set() },
        { name: 'a class instance', value: new Pet() },
        {
            name: 'a class that has no name',
            value: new (
                [
                    class {
                        petName = 'Rex'
                    },
                ][0] as new () => object
            )(),
        },
        // the SDK prints the digits of a bigint, where a float would print its nearest binary64
        {
            name: 'a number set holding an unsafe bigint',
            value: new Set([1, 2n ** 60n]),
        },
        {
            name: 'a number set holding a bigint below the safe range',
            value: new Set([1, -(2n ** 60n)]),
        },
        // `constructor` is a string, so the SDK finds no `!data.constructor` and refuses the value
        {
            name: 'an object whose constructor is a string',
            value: { constructor: 'Acme Kennels' },
        },
        { name: 'NaN inside a list', value: [[Number.NaN]] },
        {
            name: 'undefined inside an object',
            value: { a: [{ b: undefined }] },
        },
        { name: 'a Set of unsafe numbers', value: new Set([2 ** 60]) },
    ]

    const sdkReason = (value: unknown): string => {
        try {
            sdk.convertToAttr(value)
        } catch (thrown) {
            return (thrown as Error).message
        }
        throw new Error(
            'the SDK accepted a value that the pool says it refuses',
        )
    }

    it.each(pool)('refuses $name, and says what the SDK says', ({ value }) => {
        const refused = native.encode(value)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).toBe(
            sdkReason(value).replace(sdkTail, portTail),
        )
    })

    /** The canonical write owns the rule of a stored set, so its text is the text of the refusal. */
    it('refuses a Set of booleans with the text of the canonical write', () => {
        const refused = native.encode(new Set([true]))
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).toMatch(/each holds one kind/)
    })

    it('names DynamoNumber in the tail of a safe-range refusal', () => {
        const refused = native.encode(2 ** 60)
        expect((refused as CodecError).reason).toMatch(
            /Number\.MAX_SAFE_INTEGER\. Use DynamoNumber from rotorise\.$/,
        )
    })

    it('writes N with the exact digits of a DynamoNumber, as the SDK does for a NumberValue', () => {
        const digits = '12345678901234567890'
        expect(native.encode(DynamoNumber.from(digits))).toEqual({ N: digits })
        expect(sdk.NumberValueImpl.from(digits).toAttributeValue()).toEqual({
            N: digits,
        })
    })

    it('writes NS from a Set of DynamoNumber, as the SDK does for a Set of NumberValue', () => {
        const digits = ['12345678901234567890', '1.5']
        // the store holds a set without an order, and the canonical write sorts the members
        expect(
            native.encode(new Set(digits.map((d) => DynamoNumber.from(d)))),
        ).toEqual({ NS: [...digits].sort() })
        expect(
            sdk.convertToAttr(
                new Set(digits.map((d) => sdk.NumberValueImpl.from(d))),
            ),
        ).toEqual({ NS: digits })
    })

    it('types a DynamoNumber as N, and a set of them as NS, as the write does', () => {
        expectTypeOf<native.Encode<DynamoNumber>>().toEqualTypeOf<N>()
        expectTypeOf<
            native.Encode<ReadonlySet<DynamoNumber>>
        >().toEqualTypeOf<NS>()
        expectTypeOf<
            native.ItemEncode<{ price: DynamoNumber }>
        >().toEqualTypeOf<native.ItemEncode<{ price: number }>>()
    })
})

describe('a writeNumber deviation sees each number that the codec writes', () => {
    const refusing = native(
        {},
        { writeNumber: () => new CodecError('no numbers here') },
    )
    const one = orThrow(DynamoNumber.from('1'))

    it('refuses every set that holds a number, whatever its first member is', () => {
        for (const set of [
            new Set([1, 2]),
            new Set([1n, 2n]),
            new Set([1n, 2]),
            new Set([2, 1n]),
            new Set([one, 2]),
        ])
            expect(refusing.encode(set)).toBeInstanceOf(CodecError)
    })

    it('hands each number member of a set to the writer one time, and no DynamoNumber', () => {
        const seen: (number | bigint)[] = []
        const recording = native(
            {},
            {
                writeNumber: (value) => {
                    seen.push(value)
                    return { N: value.toString() }
                },
            },
        )
        expect(recording.encode(new Set([1n, 2, 3n]))).toEqual({
            NS: ['1', '2', '3'],
        })
        expect(seen).toEqual([1n, 2, 3n])
        seen.length = 0
        expect(recording.encode(new Set([one, 2]))).toEqual({
            NS: ['1', '2'],
        })
        expect(seen).toEqual([2])
    })

    it('keeps the numeral refusal of a NaN that is not the first member of a bigint-first set', () => {
        const refused = native.encode(new Set([1n, Number.NaN]))
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).toMatch(
            /^NaN is not a number DynamoDB stores/,
        )
    })
})

describe('native in a container', () => {
    const pet = item(object({ x: native }))

    it('native in a container writes and reads as native alone', () => {
        expect(native.encode(1e20)).toBeInstanceOf(CodecError)
        expect(pet.encode({ x: 1e20 })).toBeInstanceOf(CodecError)
        expect(object({ x: native }).encode({ x: 1e20 })).toBeInstanceOf(
            CodecError,
        )
        expect(pet.decode({ x: { N: '9007199254740993' } })).toEqual({
            x: 9007199254740993n,
        })
    })

    it('reads as a marshaller and not as opaque lossy, and two configurations are two adapters', () => {
        expect(fits(termOf(native), termOf(opaque('lossy')))).toBe(false)
        expect(fits(termOf(native), termOf(native))).toBe(true)
        expect(
            fits(termOf(native), termOf(native({ convertEmptyValues: true }))),
        ).toBe(false)
    })
})

describe('what native refuses and reads back', () => {
    it('native refuses a set the store cannot hold', () => {
        expect(native.encode(new Set(['a', 1]))).toBeInstanceOf(CodecError)
        expect(native.encode(new Set([1, 1n]))).toBeInstanceOf(CodecError)
    })

    it('native reads back what it writes', () => {
        const written = native.encode(1e-7)
        expect(written).toEqual({ N: '0.0000001' })
        expect(native.decode(written as never)).toBe(1e-7)
    })
})

describe('a Blob and a File', () => {
    /**
     * The SDK lists both as binary and writes a `B` that holds the object. A synchronous write
     * cannot read their bytes, so the port refuses, and the type has no attribute for them.
     */
    it('are refused by name, where the SDK writes a B that holds the object', () => {
        expect(sdk.convertToAttr(new Blob(['a']))).toEqual({
            B: expect.any(Blob),
        })
        for (const bytes of [new Blob(['a']), new File(['a'], 'a.txt')]) {
            const refused = native.encode(bytes)
            expect(refused).toBeInstanceOf(CodecError)
            expect((refused as CodecError).reason).toMatch(/behind a promise/)
        }
    })

    it('have no attribute in the type', () => {
        expectTypeOf<native.Encode<Blob>>().toBeNever()
        expectTypeOf<native.Encode<File>>().toBeNever()
        expectTypeOf<native.Encode<Uint8Array>>().toEqualTypeOf<B>()
    })

    it('are not the name of an object that only has a method named arrayBuffer, which is a map', () => {
        type Doc = { title: string; arrayBuffer: () => Promise<ArrayBuffer> }
        expectTypeOf<native.Encode<Doc>>().toEqualTypeOf<M<{ title: S }>>()
        const doc: Doc = {
            title: 'a',
            arrayBuffer: async () => new ArrayBuffer(0),
        }
        expect(native.encode(doc)).toEqual({ M: { title: { S: 'a' } } })
    })

    it('are not the name of a value that only claims a binary constructor', () => {
        const claimed = { constructor: { name: 'Uint8Array' } }
        const refused = native.encode(claimed)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).not.toMatch(/promise/)
        expect((refused as CodecError).reason).toMatch(/is no binary value/)
    })
})

describe('an attribute named __proto__', () => {
    /**
     * DynamoDB stores the name. The SDK assigns each key into a plain object, so its write drops
     * the attribute and its read sets a prototype from the stored data. The port keeps the
     * attribute on both halves.
     */
    it('is written, where the SDK drops it with no refusal', () => {
        const pet = JSON.parse('{"petId":"p1","__proto__":{"name":"Rex"}}')
        expect(sdk.convertToAttr(pet)).toEqual({ M: { petId: { S: 'p1' } } })
        const written = native.encode(pet) as { M: Record<string, unknown> }
        expect(Object.keys(written.M).sort()).toEqual(['__proto__', 'petId'])
        expect(Object.hasOwn(written.M, '__proto__')).toBe(true)
    })

    it('is read as an attribute, and writes back as it was stored', () => {
        const stored = JSON.parse(
            '{"M":{"__proto__":{"M":{"isAdmin":{"BOOL":true}}}}}',
        )
        const read = native.decode(stored) as Record<string, unknown>
        expect(Object.keys(read)).toEqual(['__proto__'])
        expect(read.isAdmin).toBeUndefined()
        expect(native.encode(read)).toEqual(stored)
    })
})

describe('a Set that repeats a stored member', () => {
    /**
     * Two objects with one numeral are two members of a Set. The SDK writes both, and DynamoDB
     * refuses the set. The port refuses it, as it refuses a document past the nesting bound.
     */
    it('is refused, where the SDK writes a set that DynamoDB refuses', () => {
        expect(
            sdk.convertToAttr(
                new Set([
                    sdk.NumberValueImpl.from('1'),
                    sdk.NumberValueImpl.from('1.0'),
                ]),
            ),
        ).toEqual({ NS: ['1', '1.0'] })
        const refused = native.encode(
            new Set([DynamoNumber.from('1'), DynamoNumber.from('1.0')]),
        )
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).toMatch(
            /holds one number two times/,
        )
    })

    it('is refused as a Binary Set (BS) too, where the SDK writes both members', () => {
        const twice = new Set([Uint8Array.of(1), Uint8Array.of(1)])
        expect(sdk.convertToAttr(twice)).toEqual({
            BS: [Uint8Array.of(1), Uint8Array.of(1)],
        })
        const refused = native.encode(twice)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).reason).toMatch(
            /holds one byte sequence two times/,
        )
    })

    it('reads no stored set with a member of another type, and refuses without a throw', () => {
        for (const stored of [{ SS: ['a', 1] }, { NS: [1] }, { BS: ['a'] }]) {
            const read = native.decode(stored as never)
            expect(read).toBeInstanceOf(CodecError)
            expect((read as CodecError).reason).toMatch(
                /^member \d+ of this [SNB]S is not/,
            )
        }
    })

    it('reads no stored set that repeats a member, which DynamoDB never returns', () => {
        for (const stored of [
            { SS: ['a', 'a'] },
            { NS: ['1', '1'] },
            { BS: [Uint8Array.of(1), Uint8Array.of(1)] },
        ]) {
            const read = native.decode(stored)
            expect(read).toBeInstanceOf(CodecError)
            expect((read as CodecError).reason).toMatch(
                /^DynamoDB holds no [SNB]S that repeats a member/,
            )
        }
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

describe('a set takes the writer of its first member, as the SDK does', () => {
    const outcome = (written: () => unknown) => {
        try {
            return written()
        } catch {
            return 'refused'
        }
    }
    const sets: readonly { name: string; value: ReadonlySet<unknown> }[] = [
        {
            name: 'a bigint, then an unsafe number',
            value: new Set([1n, 2 ** 60]),
        },
        {
            name: 'a number, then an unsafe bigint',
            value: new Set([1, 2n ** 60n]),
        },
        { name: 'a bigint, then a number', value: new Set([1n, 2]) },
        { name: 'a number, then a bigint', value: new Set([1, 2n]) },
    ]

    it.each(
        [{}, { allowImpreciseNumbers: true }].flatMap((options) =>
            sets.map(({ name, value }) => ({ name, value, options })),
        ),
    )(
        'writes or refuses $name as the SDK does, with $options',
        ({ value, options }) => {
            const ours = native(options).encode(value)
            expect(ours instanceof CodecError ? 'refused' : ours).toEqual(
                outcome(() => sdk.convertToAttr(value, options)),
            )
        },
    )
})

/**
 * **The port writes what the SDK writes, or both refuse**, over a generated pool.
 *
 * The pool draws the forms that the SDK reads: safe and unsafe numbers, `NaN` and the infinities,
 * bigints, strings, booleans, `null`, `undefined`, the typed arrays, `Buffer`, `ArrayBuffer` and
 * `DataView`, a class, an anonymous class and an object whose `constructor` is a string, sets of
 * one family, of two families and empty, arrays, plain objects, null-prototype objects and `Map`, at
 * depth 3. It draws no `Blob`, no `File` and no depth above 3. Each of the 16 sets of the four options
 * that the port reproduces draws 500 values from one seed.
 *
 * The rows are compared after the normalisations that the port states: a set is sorted, a typed
 * array is its bytes, and a numeral is its normal digits. A value that the port writes and the SDK
 * refuses, a row that differs, and a refusal of both with a text that no exception names, are
 * failures. Four exceptions are stated by name, and each is counted:
 *
 * - **set family**: the port refuses a set of two families or of a kind that no stored set holds,
 *   where the SDK writes the members as the first member does (the doc of `native`).
 * - **numeral gate**: the port refuses a number that DynamoDB refuses (`5e-324`, `1e300` with
 *   `allowImpreciseNumbers`), where the SDK writes it (the doc of `nativeNumber`).
 * - **set of booleans text**: both refuse a set of a kind that no stored set holds, with the text
 *   of the canonical write on one side and the text of the SDK on the other.
 * - **first fault**: a value holds two faults and the two read them in another order, because the
 *   port refuses a number as it meets it and a set when it writes it.
 */
describe('the port writes what the SDK writes, or both refuse', () => {
    class Pet {
        name = 'Rex'
    }
    const Anonymous = [
        class {
            petName = 'Rex'
        },
    ][0] as new () => object
    const number_ = (digits: string): DynamoNumber =>
        orThrow(DynamoNumber.from(digits))
    const leaves: readonly (() => unknown)[] = [
        () => 1,
        () => -7,
        () => 1.5,
        () => 0.1,
        () => 2 ** 53,
        () => 2 ** 60,
        () => -(2 ** 60),
        () => 1e300,
        () => 5e-324,
        () => Number.NaN,
        () => Number.POSITIVE_INFINITY,
        () => Number.NEGATIVE_INFINITY,
        () => 1n,
        () => 2n ** 60n,
        () => '',
        () => 'abc',
        () => true,
        () => false,
        () => null,
        () => undefined,
        () => new Uint8Array(0),
        () => new Uint8Array([1, 2]),
        () => Buffer.from([1]),
        () => Buffer.alloc(0),
        () => new ArrayBuffer(0),
        () => new ArrayBuffer(2),
        () => new DataView(new ArrayBuffer(0)),
        () => new DataView(new ArrayBuffer(2)),
        () => Int16Array.from([1, 2]),
        () => new Int16Array(0),
        () => number_('1.5'),
        () => number_('12345678901234567890'),
        () => new Pet(),
        () => new Anonymous(),
        () => ({ constructor: 'Acme' }),
    ]
    const sets: readonly (() => unknown)[] = [
        () => new Set(['a', 'b']),
        () => new Set([1, 2]),
        () => new Set([1n, 2n]),
        () => new Set([new Uint8Array([1]), new Uint8Array([2])]),
        () => new Set([1, 'a']),
        () => new Set(['a', 1]),
        () => new Set([1n, 2 ** 60]),
        () => new Set([1, 2n ** 60n]),
        () => new Set([1n, 2]),
        () => new Set([1, 2n]),
        () => new Set(),
        () => new Set(['a', undefined]),
        () => new Set([2 ** 60]),
        () => new Set([number_('1.5'), number_('2')]),
        () => new Set([true]),
        () => new Set(['a', new Uint8Array([1])]),
        () => new Set([number_('1'), 2 ** 60]),
        () => new Set([1, number_('12345678901234567890')]),
        () => new Set([number_('1'), Number.NaN]),
        () => new Set([number_('1'), 'a']),
        () => new Set([1, new Number(2)]),
        () => new Set([new Number(1), 2]),
        () => new Set([1n, new Number(2)]),
        () => new Set(['a', new String('b')]),
        () => new Set([new String('a'), 'b']),
        () => new Set([1, 1n]),
        () => new Set([new Uint8Array([1]), new Uint8Array([1])]),
    ]
    /** The family of a member of a set, as the SDK writes it. */
    const familyOf = (member: unknown): string => {
        const named = (member as { constructor?: { name?: string } })
            ?.constructor?.name
        if (
            member instanceof DynamoNumber ||
            typeof member === 'number' ||
            typeof member === 'bigint' ||
            named === 'Number'
        )
            return 'N'
        if (typeof member === 'string' || named === 'String') return 'S'
        if (ArrayBuffer.isView(member) || member instanceof ArrayBuffer)
            return 'B'
        return 'other'
    }
    /** Whether a set at any depth of a value holds members of two families. */
    const hasMixedSet = (value: unknown): boolean => {
        if (value instanceof Set) {
            return (
                new Set([...value].map(familyOf)).size > 1 ||
                [...value].some(hasMixedSet)
            )
        }
        if (Array.isArray(value)) return value.some(hasMixedSet)
        if (value instanceof Map) return [...value.values()].some(hasMixedSet)
        if (typeof value === 'object' && value !== null) {
            return Object.values(value).some(hasMixedSet)
        }
        return false
    }
    type Rng = ReturnType<typeof rngFrom>
    const pick = <T>(rng: Rng, from: readonly T[]): T =>
        from[Math.floor(rng() * from.length)] as T
    const drawn = (rng: Rng, depth: number): unknown => {
        const kind = rng()
        if (depth <= 0 || kind < 0.5) return pick(rng, leaves)()
        if (kind < 0.65) return pick(rng, sets)()
        if (kind < 0.8) {
            return Array.from({ length: Math.floor(rng() * 4) }, () =>
                drawn(rng, depth - 1),
            )
        }
        if (kind < 0.9) {
            return Object.fromEntries(
                ['a', 'b', 'c']
                    .slice(0, Math.floor(rng() * 4))
                    .map((name) => [name, drawn(rng, depth - 1)]),
            )
        }
        if (kind < 0.95) {
            const bare = Object.create(null) as Record<string, unknown>
            for (const name of ['a', 'b'].slice(0, Math.floor(rng() * 3))) {
                bare[name] = drawn(rng, depth - 1)
            }
            return bare
        }
        return new Map([['a', drawn(rng, depth - 1)]])
    }

    /** The SDK reads `NumberValue` where the port reads a `DynamoNumber`. */
    const forSdk = (value: unknown): unknown => {
        if (value instanceof DynamoNumber) {
            return sdk.NumberValueImpl.from(value.digits)
        }
        if (Array.isArray(value)) return value.map(forSdk)
        if (value instanceof Set) return new Set([...value].map(forSdk))
        if (value instanceof Map) {
            return new Map([...value].map(([key, held]) => [key, forSdk(held)]))
        }
        if (typeof value === 'object' && value !== null) {
            const proto: unknown = Object.getPrototypeOf(value)
            if (proto === Object.prototype || proto === null) {
                return Object.fromEntries(
                    Object.entries(value).map(([key, held]) => [
                        key,
                        forSdk(held),
                    ]),
                )
            }
        }
        return value
    }
    const bytesOf = (value: unknown): string => {
        const view = ArrayBuffer.isView(value)
            ? new Uint8Array(value.buffer, value.byteOffset, value.byteLength)
            : value instanceof ArrayBuffer
              ? new Uint8Array(value)
              : (value as Uint8Array)
        return [...view].join(',')
    }
    const digitsOf = (numeral: unknown): unknown => {
        if (typeof numeral !== 'string') return numeral
        const read = DynamoNumber.from(numeral)
        return read instanceof DynamoNumber ? read.digits : numeral
    }
    /** A row as the port states it: a set sorted, bytes as bytes, a numeral as its normal digits. */
    const normal = (row: unknown): unknown => {
        if (row === null || typeof row !== 'object') return row
        const attribute = row as Record<string, unknown>
        if (attribute.B !== undefined) return { B: bytesOf(attribute.B) }
        if (attribute.N !== undefined) return { N: digitsOf(attribute.N) }
        if (Array.isArray(attribute.SS)) return { SS: [...attribute.SS].sort() }
        if (Array.isArray(attribute.NS)) {
            return { NS: attribute.NS.map(digitsOf).sort() }
        }
        if (Array.isArray(attribute.BS)) {
            return { BS: attribute.BS.map(bytesOf).sort() }
        }
        if (Array.isArray(attribute.L)) return { L: attribute.L.map(normal) }
        if (typeof attribute.M === 'object' && attribute.M !== null) {
            return {
                M: Object.fromEntries(
                    Object.entries(attribute.M).map(([key, held]) => [
                        key,
                        normal(held),
                    ]),
                ),
            }
        }
        return attribute
    }

    it('holds over 16 option sets, with each exception counted', () => {
        const flags = [
            'removeUndefinedValues',
            'convertEmptyValues',
            'convertClassInstanceToMap',
            'allowImpreciseNumbers',
        ] as const
        const optionSets = Array.from({ length: 16 }, (_, bits) =>
            Object.fromEntries(
                flags.map((flag, at) => [flag, Boolean(bits & (1 << at))]),
            ),
        )
        const sdkTail = ' Use NumberValue from @aws-sdk/lib-dynamodb.'
        const portTail = ' Use DynamoNumber from rotorise.'
        const setText =
            'Only Number Set (NS), Binary Set (BS) or String Set (SS) are allowed.'
        const rng = rngFrom(20261107)
        const count = {
            agree: 0,
            bothRefuseSameText: 0,
            setFamily: 0,
            repeatedMember: 0,
            numeralGate: 0,
            setOfBooleansText: 0,
            firstFault: 0,
        }
        const failures: string[] = []
        for (const options of optionSets) {
            const port = native(options)
            for (let at = 0; at < 500; at++) {
                const value = drawn(rng, 3)
                const ours = port.encode(value)
                let theirs: unknown
                let sdkText: string | undefined
                try {
                    theirs = sdk.convertToAttr(forSdk(value), options)
                } catch (thrown) {
                    sdkText = (thrown as Error).message
                }
                const refused = ours instanceof CodecError
                const shown = `${Object.prototype.toString.call(value)} at ${at} ${JSON.stringify(options)}`
                if (refused && sdkText !== undefined) {
                    if (ours.reason === sdkText.replace(sdkTail, portTail)) {
                        count.bothRefuseSameText++
                    } else if (
                        ours.reason.startsWith('a set writes') &&
                        sdkText === setText
                    ) {
                        count.setOfBooleansText++
                    } else if (
                        sdkText === setText ||
                        /is not a number DynamoDB stores/.test(ours.reason)
                    ) {
                        count.firstFault++
                    } else {
                        failures.push(
                            `${shown}: two texts: ${ours.reason} | ${sdkText}`,
                        )
                    }
                } else if (refused) {
                    if (
                        ours.reason.startsWith('a set writes') &&
                        hasMixedSet(value)
                    )
                        count.setFamily++
                    else if (/ two times, as two /.test(ours.reason))
                        count.repeatedMember++
                    else if (
                        /is not a number DynamoDB stores/.test(ours.reason)
                    ) {
                        count.numeralGate++
                    } else
                        failures.push(
                            `${shown}: only the port refuses: ${ours.reason}`,
                        )
                } else if (sdkText !== undefined) {
                    failures.push(`${shown}: only the SDK refuses: ${sdkText}`)
                } else if (
                    JSON.stringify(normal(ours)) ===
                    JSON.stringify(normal(theirs))
                ) {
                    count.agree++
                } else {
                    failures.push(`${shown}: two rows`)
                }
            }
        }
        expect(failures).toEqual([])
        const decided = Object.values(count).reduce((sum, n) => sum + n, 0)
        expect(decided).toBe(8000)
        expect(count.agree).toBeGreaterThan(decided / 2)
        expect(count).toEqual({
            agree: 5416,
            bothRefuseSameText: 1638,
            setFamily: 239,
            repeatedMember: 121,
            numeralGate: 358,
            setOfBooleansText: 194,
            firstFault: 34,
        })
    })
})
