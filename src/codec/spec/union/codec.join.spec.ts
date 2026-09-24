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
    dynamoNumber,
    lazy,
    object,
    string,
    union,
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
