/**
 * **A union is the join of its options, so the option order is not observable.**
 *
 * The first option that admits a value writes it, and the first option that reads an attribute
 * reads it. Where the options are compatible, every option that admits a value writes it to one
 * attribute, and every option that reads an attribute reads it to one value. So each permutation
 * of the options gives one codec. These tests put each public operation of a union to each
 * permutation, over values in each option, in the overlap, and outside both.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import { DynamoNumber } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    CodecError,
    decimal,
    dynamoNumber,
    held,
    lazy,
    number,
    object,
    refine,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import { failed } from '../../result'

type Erased = {
    readonly encode: (value: unknown) => unknown
    readonly decode: (attribute: AttributeValue) => unknown
    readonly item: {
        readonly encode: (value: unknown) => unknown
        readonly decode: (item: unknown) => unknown
    }
    readonly extract: (clause: Readonly<Record<string, unknown>>) => Erased
    readonly exclude: (clause: Readonly<Record<string, unknown>>) => Erased
}

// declared through a cast, because the options come as an erased list of permutations
const declare = union as unknown as (options: readonly AnyCodec[]) => Erased

/** A result, with a failure read as the fact that it failed: the message names the options. */
const answer = (result: unknown) => (failed(result) ? 'failed' : result)

const permutations = <T>(xs: readonly T[]): readonly (readonly T[])[] =>
    xs.length <= 1
        ? [xs]
        : xs.flatMap((x, at) =>
              permutations([...xs.slice(0, at), ...xs.slice(at + 1)]).map(
                  (rest) => [x, ...rest],
              ),
          )

/** Each permutation gives the answer the first permutation gives, value by value. */
const sameUnderEveryOrder = (
    options: readonly AnyCodec[],
    run: (codec: Erased) => readonly unknown[],
) => {
    const [first, ...rest] = permutations(options).map((order) =>
        run(declare(order)).map(answer),
    )
    for (const other of rest) expect(other).toEqual(first)
    return first
}

describe('a union of compatible options gives one answer whatever the option order', () => {
    it('writes and reads a crossing pair of restrictions of one base the same way in each order', () => {
        const values = ['A', 'B', 'C', 'D', 1]
        const attributes: AttributeValue[] = [
            { S: 'A' },
            { S: 'B' },
            { S: 'C' },
            { S: 'D' },
            { N: '1' },
        ]
        const answers = sameUnderEveryOrder(
            [string('A', 'B'), string('B', 'C')],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        // the overlap is written once, and what the union writes it reads back
        expect(answers?.slice(0, 4)).toEqual([
            { S: 'A' },
            { S: 'B' },
            { S: 'C' },
            'failed',
        ])
    })

    it('writes and reads a nested pair as the wider option, in each order', () => {
        const values = ['A', 'B']
        const attributes: AttributeValue[] = [
            { S: 'A' },
            { S: 'B' },
            { N: '1' },
        ]
        const answers = sameUnderEveryOrder([string('A'), string], (codec) => [
            ...values.map((v) => codec.encode(v)),
            ...attributes.map((a) => codec.decode(a)),
        ])
        expect(answers?.slice(0, 2)).toEqual([{ S: 'A' }, { S: 'B' }])
    })

    // `dynamoNumber` and not `number`: `number` is an adapter over it, and the declaration cannot
    // show an adapter compatible with a held-free option that admits one of its values
    it('writes the empty list of two lists of other elements once, in each order', () => {
        const one = DynamoNumber.from('1')
        const values = [[], ['a'], [one], ['a', one]]
        const attributes: AttributeValue[] = [
            { L: [] },
            { L: [{ S: 'a' }] },
            { L: [{ N: '1' }] },
        ]
        const answers = sameUnderEveryOrder(
            [array(string), array(dynamoNumber)],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers?.[0]).toEqual({ L: [] })
    })

    it('writes, reads and slices a crossing pair of objects the same way in each order', () => {
        const first = object({ kind: string('x', 'y'), a: string })
        const second = object({ kind: string('y', 'z'), a: string })
        const values = [
            { kind: 'x', a: '1' },
            { kind: 'y', a: '1' },
            { kind: 'z', a: '1' },
            { kind: 'w', a: '1' },
        ]
        const items = [
            { kind: { S: 'x' }, a: { S: '1' } },
            { kind: { S: 'y' }, a: { S: '1' } },
            { kind: { S: 'z' }, a: { S: '1' } },
        ]
        const answers = sameUnderEveryOrder([first, second], (codec) => [
            ...values.map((v) => codec.encode(v)),
            ...items.map((i) => codec.decode({ M: i })),
            ...values.map((v) => codec.item.encode(v)),
            ...items.map((i) => codec.item.decode(i)),
            ...values.map((v) =>
                codec.extract({ kind: string('y') }).encode(v),
            ),
            ...values.map((v) =>
                codec.exclude({ kind: string('x') }).encode(v),
            ),
        ])
        expect(answers?.[1]).toEqual({
            M: { kind: { S: 'y' }, a: { S: '1' } },
        })
    })

    // `lazy` is transparent: a thunk of a held-free term is held-free, as the model's `HF` reads
    it('writes and reads a held-free option beside a thunk of a held-free option the same way in each order', () => {
        const values = ['A', 'B']
        const attributes: AttributeValue[] = [
            { S: 'A' },
            { S: 'B' },
            { N: '1' },
        ]
        const answers = sameUnderEveryOrder(
            [string('A'), lazy(() => string)],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers?.slice(0, 2)).toEqual([{ S: 'A' }, { S: 'B' }])
    })
})

describe('a union of two restrictions of one adapter is the adapter, whatever the option order', () => {
    // one adapter is the common bound (Lawson, Lemma 4.8): the wider option reads each attribute
    // that the narrower reads, to the same value
    it('writes and reads a decimal beside a literal decimal the same way in each order', () => {
        const values = ['1', '2.5', '3']
        const attributes: AttributeValue[] = [
            { N: '1' },
            { N: '2.5' },
            { N: '3' },
            { S: '1' },
        ]
        const answers = sameUnderEveryOrder(
            [decimal('1', '2.5'), decimal],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers?.slice(0, 3)).toEqual([
            { N: '1' },
            { N: '2.5' },
            { N: '3' },
        ])
    })

    // the held side of `decimal('1', '2.5')` is the texts it writes, so its view meets the other
    // option's literals at the bottom (Lawson: orthogonality reads the views exactly)
    it('writes and reads a literal decimal beside other string literals the same way in each order', () => {
        const values = ['1', '2.5', 'A', 'B', 'C']
        const attributes: AttributeValue[] = [
            { N: '1' },
            { N: '2.5' },
            { S: 'A' },
            { S: 'B' },
            { S: '1' },
        ]
        const answers = sameUnderEveryOrder(
            [decimal('1', '2.5'), string('A', 'B')],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers?.slice(0, 4)).toEqual([
            { N: '1' },
            { N: '2.5' },
            { S: 'A' },
            { S: 'B' },
        ])
    })

    // plain `decimal` holds every numeral text, and no data states that set, so the view is `string`
    it('refuses a decimal beside string literals, whose view shows no separation', () => {
        expect(() =>
            union([
                decimal,
                string('A', 'B'),
            ] as unknown as readonly AnyCodec[]),
        ).toThrow(/not shown compatible/)
    })

    it('keeps what a literal decimal writes: its own numerals, and no other', () => {
        const only = decimal('1', '2.5') as unknown as Erased
        expect(only.encode('1')).toEqual({ N: '1' })
        expect(failed(only.encode('3'))).toBe(true)
        expect(failed(only.encode('1.0'))).toBe(true)
        expect(only.decode({ N: '2.5' })).toBe('2.5')
        expect(failed(only.decode({ N: '3' }))).toBe(true)
    })

    it('refuses two adapters with distinct functions, which show no common bound', () => {
        const up = held(string, string, {
            encode: (s: string) => s.toUpperCase(),
            decode: (s: string) => s.toLowerCase(),
        })
        const same = held(string, string, {
            encode: (s: string) => s.toUpperCase(),
            decode: (s: string) => s.toLowerCase(),
        })
        expect(() =>
            union([up, same] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
    })
})

describe('a union refuses a thunk it must read and cannot, because the model has no recursive term', () => {
    it('refuses a union whose thunk names the union itself, and ends', () => {
        const declare = () => {
            const self: AnyCodec = union([
                string,
                lazy(() => self as never),
            ] as unknown as readonly AnyCodec[])
            return self
        }
        expect(declare).toThrow(CodecError)
    })

    // a thunk below a list names the union being declared, so the walk meets the thunk again
    it('ends beside a union that recurses below a list, and refuses where the options overlap', () => {
        const json: AnyCodec = union([
            string,
            array(lazy(() => json as never)),
        ] as unknown as readonly AnyCodec[]) as unknown as AnyCodec
        expect(() =>
            union([dynamoNumber, json] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
        expect(() =>
            union([array(string), json] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
    })

    it('accepts recursion below an object, where the union reads no thunk', () => {
        const tree: AnyCodec = object({
            v: string,
            kids: array(lazy(() => tree as never)),
        }) as unknown as AnyCodec
        expect(() =>
            union([string, tree] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
    })
})

describe("an accepted union's options never write one value, or read one attribute, two ways", () => {
    const one = DynamoNumber.from('1')
    const nonEmpty = refine(string, (s: string): s is string => s.length > 0)
    // an older reader that migrates `N` to text: a read side the declaration cannot see
    const legacy = withLegacyRead({
        current: string,
        older: {
            decode: (attribute: AttributeValue) =>
                'N' in attribute ? attribute.N : new CodecError('not an N'),
        },
    } as never)
    const flip = held(string, string, {
        encode: (s: string) => s.toUpperCase(),
        decode: (s: string) => s.toLowerCase(),
    })
    const options: readonly (readonly [string, AnyCodec])[] = [
        ['string', string],
        ["string('1', '2.5')", string('1', '2.5')],
        ["string('A', 'B')", string('A', 'B')],
        ['nonEmpty', nonEmpty],
        ['decimal', decimal],
        ["decimal('1', '2.5')", decimal('1', '2.5')],
        ["decimal('2', '3')", decimal('2', '3')],
        ['dynamoNumber', dynamoNumber],
        ['number', number],
        ['number(1)', number(1)],
        ['flip', flip],
        ['decimal.set()', decimal.set()],
        ['array(string)', array(string)],
        ['legacy', legacy],
    ] as unknown as readonly (readonly [string, AnyCodec])[]
    const values: readonly unknown[] = [
        '1',
        '2.5',
        '3',
        'A',
        'a',
        '',
        1,
        2.5,
        one,
        ['1'],
        new Set(['1']),
    ]
    const attributes: readonly AttributeValue[] = [
        { S: '1' },
        { S: '2.5' },
        { S: 'A' },
        { S: 'a' },
        { N: '1' },
        { N: '2.5' },
        { N: '3' },
    ]
    type Pair = {
        readonly encode: (value: unknown) => unknown
        readonly decode: (attribute: AttributeValue) => unknown
    }
    const ok = (result: unknown) => !failed(result)
    const sameAnswer = (a: unknown, b: unknown) =>
        JSON.stringify(a, (_, v) =>
            v instanceof DynamoNumber ? `N:${v}` : v,
        ) ===
        JSON.stringify(b, (_, v) => (v instanceof DynamoNumber ? `N:${v}` : v))

    it('finds no value written two ways and no attribute read two ways, over every accepted pair', () => {
        const disagreements: string[] = []
        for (const [at, [an, a]] of options.entries()) {
            for (const [bn, b] of options.slice(at + 1)) {
                try {
                    union([a, b] as unknown as readonly AnyCodec[])
                } catch {
                    continue
                }
                const [x, y] = [a, b] as unknown as readonly [Pair, Pair]
                for (const v of values) {
                    const wx = x.encode(v)
                    const wy = y.encode(v)
                    if (ok(wx) && ok(wy) && !sameAnswer(wx, wy))
                        disagreements.push(`${an} | ${bn} write ${String(v)}`)
                }
                for (const attribute of attributes) {
                    const rx = x.decode(attribute)
                    const ry = y.decode(attribute)
                    if (ok(rx) && ok(ry) && !sameAnswer(rx, ry))
                        disagreements.push(
                            `${an} | ${bn} read ${JSON.stringify(attribute)}`,
                        )
                    // a value one option reads, the other writes back at the same attribute
                    for (const [r, w] of [
                        [rx, y],
                        [ry, x],
                    ] as const) {
                        if (!ok(r)) continue
                        const back = w.encode(r)
                        if (ok(back) && !sameAnswer(back, attribute))
                            disagreements.push(
                                `${an} | ${bn} cross ${JSON.stringify(attribute)}`,
                            )
                    }
                }
            }
        }
        expect(disagreements).toEqual([])
    })

    it('writes a set of decimals only from a Set', () => {
        const numerals = decimal.set() as unknown as Pair
        expect(failed(numerals.encode('1'))).toBe(true)
        expect(failed(numerals.encode(['1']))).toBe(true)
        expect(numerals.encode(new Set(['1']))).toEqual({ NS: ['1'] })
    })

    it('refuses a value outside the base of a refinement, and runs no predicate on it', () => {
        const nonEmptyText = refine(
            string,
            (s: string): s is string => s.length > 0,
        ) as unknown as Pair
        expect(failed(nonEmptyText.encode(null))).toBe(true)
        expect(nonEmptyText.encode('a')).toEqual({ S: 'a' })
    })

    it('refuses an older reader beside an option that reads the attribute it migrates', () => {
        expect(() =>
            union([legacy, dynamoNumber] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
        expect(() =>
            union([dynamoNumber, legacy] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
    })

    it('refuses a literal string beside a literal decimal of the same texts', () => {
        expect(() =>
            union([
                string('1', '2.5'),
                decimal('1', '2.5'),
            ] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
    })

    it('refuses a literal decimal beside a refinement of string that admits its texts', () => {
        expect(() =>
            union([
                decimal('1', '2.5'),
                nonEmpty,
            ] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
    })
})
