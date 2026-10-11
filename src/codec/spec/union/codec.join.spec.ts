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
import { DynamoNumber, isNumeral } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    held,
    list,
    mdunion,
    nullable,
    number,
    object,
    optional,
    product,
    ref,
    refine,
    scope,
    spread,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import { failed } from '../../result'
import { RecursionRefused } from '../../term'

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

    // a ref to a held-free term is held-free: the model reads the term that the ref names
    it('writes and reads a held-free option beside a ref to a held-free option the same way in each order', () => {
        const values = ['A', 'B']
        const attributes: AttributeValue[] = [
            { S: 'A' },
            { S: 'B' },
            { N: '1' },
        ]
        const answers = sameUnderEveryOrder(
            [string('A'), scope({ At: ref('S'), S: string }).At],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers?.slice(0, 2)).toEqual([{ S: 'A' }, { S: 'B' }])
    })

    /**
     * **A closure refinement meets at the bottom where its inner term does.** A closure refinement
     * of `string` writes `S` from text, and a list of decimals writes `L` from an array. No value
     * and no attribute reaches both, so `string` meets the list at the bottom, and the union is
     * certified.
     */
    it('declares a closure refinement of string beside a list of decimals, and gives one answer in each order', () => {
        // `refine` wants a type predicate, and `isNumeral` returns a `boolean`
        const numeral = refine(
            string,
            isNumeral as (value: string) => value is string,
        )
        const values = ['1.5', 'x', ['1.5'], [], 1.5]
        const attributes: AttributeValue[] = [
            { S: '1.5' },
            { S: 'x' },
            { L: [{ N: '1.5' }] },
            { L: [] },
            { N: '1.5' },
        ]
        const answers = sameUnderEveryOrder(
            [numeral, array(decimal)] as unknown as readonly AnyCodec[],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers).toEqual([
            { S: '1.5' },
            'failed',
            { L: [{ N: '1.5' }] },
            { L: [] },
            'failed',
            '1.5',
            'failed',
            ['1.5'],
            [],
            'failed',
        ])
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

    // one adapter, and each side of `decimal('1')` is below one option of a held-free union of
    // literals, so the wider option is the common bound
    it('writes and reads a literal decimal beside a wider literal decimal the same way in each order', () => {
        const values = ['1', '2.5', '3']
        const attributes: AttributeValue[] = [
            { N: '1' },
            { N: '2.5' },
            { N: '3' },
            { S: '1' },
        ]
        const answers = sameUnderEveryOrder(
            [decimal('1'), decimal('1', '2.5')],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers).toEqual([
            { N: '1' },
            { N: '2.5' },
            'failed',
            '1',
            '2.5',
            'failed',
            'failed',
        ])
    })

    // the two options share `2.5` under one adapter, and their stored sides agree, so both write
    // `2.5` to one attribute and read that attribute to one value
    it('writes and reads two overlapping literal decimals the same way in each order', () => {
        const values = ['1', '2.5', '3']
        const attributes: AttributeValue[] = [
            { N: '1' },
            { N: '2.5' },
            { N: '3' },
        ]
        const answers = sameUnderEveryOrder(
            [decimal('1', '2.5'), decimal('2.5', '3')],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers).toEqual([
            { N: '1' },
            { N: '2.5' },
            { N: '3' },
            '1',
            '2.5',
            '3',
        ])
    })

    // the held row reads the one adapter, and the stored sides of the two decimals agree beside
    // the other option, so a literal decimal beside a union that holds a wider decimal declares
    it('declares a literal decimal beside a union whose wider option holds the same adapter', () => {
        expect(() =>
            union([
                decimal('1'),
                union([decimal('1', '2.5'), string('A')]),
            ] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
    })

    // the business rule of the held row: two options under one adapter whose stored sides agree
    // are compatible, whatever else the union holds
    it('accepts a decimal beside a union of a decimal and a boolean, and answers the same in each order', () => {
        const values = ['1.5', true]
        const attributes: AttributeValue[] = [{ N: '1.5' }, { BOOL: true }]
        const answers = sameUnderEveryOrder(
            [decimal, union([decimal, boolean(true)])],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        expect(answers).toEqual([{ N: '1.5' }, { BOOL: true }, '1.5', true])
    })

    // two caller adapters over one stored side are two tags: `swap` reads the stored `X` as `x`,
    // and `id` reads it as `X`, so one attribute reads to two values
    it('refuses two caller adapters over one stored side, which read one attribute two ways', () => {
        const swapX = (s: string) => (s === 'x' ? 'X' : s === 'X' ? 'x' : s)
        const swap = held(string, string, { encode: swapX, decode: swapX })
        const id = held(string, string, {
            encode: (s: string) => s,
            decode: (s: string) => s,
        })
        expect(() =>
            union([swap, id] as unknown as readonly AnyCodec[]),
        ).toThrow(/not shown compatible/)
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

describe('a union refuses a thunk it must read at its own input, because the model guards each binder', () => {
    it('refuses a union whose ref names the union itself, and ends', () => {
        const declare = () => scope({ Self: union([string, ref('Self')]) })
        expect(declare).toThrow(CodecError)
    })

    /**
     * **A `ref` that names a later entry is read with the entry bound.** The union waits for the
     * scope, and the scope binds every name before the union reads its options. So the option reads
     * the later entry, a list, and the union is accepted.
     */
    it('accepts a ref that names a later entry, because the scope binds the entry before the union reads it', () => {
        const declare = () =>
            scope({
                Early: union([string, ref('Later')]),
                Later: array(boolean),
            })
        expect(declare).not.toThrow()
    })

    /**
     * **A part that reads no variable is decided as a closed term, under a binder too.** The
     * recursive option holds two literals of `decimal` beside an object that recurses, and its
     * binder holds an adapter. The literals read no variable, so the test of the views applies to
     * them as it does at the top, and the union with `decimal` is accepted.
     */
    it('accepts a recursive option beside decimal, where the part that reads no variable is closed', () => {
        const declare = () => {
            const { Self } = scope({
                Self: union([
                    decimal('1', '2.5'),
                    object({ m: optional(ref('Self')) }),
                ]),
            })
            return union([Self, decimal])
        }
        expect(declare).not.toThrow()
    })

    // a ref below a list names the union being declared, so the walk meets the ref again. Two
    // held-free options sit below `opaque` wherever they overlap, and an adapter that writes a text
    // to another attribute does not
    it('ends beside a union that recurses below a list, and refuses where an adapter overlaps it', () => {
        const { json } = scope({ json: union([string, array(ref('json'))]) })
        expect(() =>
            union([dynamoNumber, json] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
        expect(() =>
            union([array(string), json] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
        expect(() =>
            union([decimal, json] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
    })

    /**
     * **An adapter on the path of a recursion is refused at the scope that closes the cycle.** The
     * model's guard refuses a `held` between a binder and its variable, because the conversion can
     * make the input deeper, so the stages need not agree. A list on the path bounds nothing then.
     * At the declaration of the `held`, the `ref` below the `held` is a free variable, so the
     * `held` builds an open fragment, and the scope runs the guard with the name bound.
     */
    it('refuses a held between a recursive ref and the codec it names at the scope that binds the ref', () => {
        const same = { encode: (v: unknown) => v, decode: (v: unknown) => v }
        const inUnion = () =>
            scope({
                Self: union([
                    string,
                    array(held(ref('Self'), ref('Self'), same)),
                ]),
            })
        expect(inUnion).toThrow(
            /\[scope\] 'Self' reaches a recursion with an adapter/,
        )
        const inObject = () =>
            scope({
                Kids: object({
                    kids: array(held(ref('Kids'), ref('Kids'), same)),
                }),
            })
        expect(inObject).toThrow(
            /\[scope\] 'Kids' reaches a recursion with an adapter/,
        )
    })

    /**
     * **An older reader on the path of a recursion is refused as an adapter is, at the scope that
     * binds the ref.** The read writes the older reader's answer through the inner term, and the
     * answer has any depth, so a container on the path bounds nothing.
     */
    it('refuses a withLegacyRead between a recursive ref and the codec it names at the scope that binds the ref', () => {
        const declare = () =>
            scope({
                Kids: object({
                    kids: array(
                        withLegacyRead({
                            current: ref('Kids'),
                            older: { decode: () => ({ kids: [] }) as never },
                        }),
                    ),
                }),
            })
        expect(declare).toThrow(
            /\[scope\] 'Kids' reaches a recursion with an adapter/,
        )
    })

    it('accepts a recursion below a list or an object with no adapter on its path', () => {
        const { json, tree } = scope({
            json: union([string, array(ref('json'))]),
            tree: object({ v: string, kids: array(ref('tree')) }),
        })
        expect(() =>
            union([number, json] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
        expect(() =>
            union([number, tree] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
    })

    it('accepts recursion below an object, where the union reads no thunk', () => {
        const { tree } = scope({
            tree: object({ v: string, kids: array(ref('tree')) }),
        })
        expect(() =>
            union([string, tree] as unknown as readonly AnyCodec[]),
        ).not.toThrow()
    })

    /**
     * **A scope names the cause of a refusal that a union option reaches.** The `held` sits on the
     * cycle through an object, so the scope names the adapter and not a recursion with no
     * container.
     */
    it('a scope names the adapter when a union option reaches an adapter on the cycle', () => {
        const same = { encode: (v: unknown) => v, decode: (v: unknown) => v }
        const declare = () =>
            scope({
                Self: union([
                    held(
                        object({ a: ref('Self') }) as never,
                        string as never,
                        same as never,
                    ) as unknown as AnyCodec,
                    string,
                ]),
            })
        expect(declare).toThrow(
            /^\[scope\] 'Self' reaches a recursion with an adapter/,
        )
    })

    /**
     * **An adapter over a free `ref` builds an open fragment, and an adapter on a recursive path is
     * refused at the scope.** A cycle passes through a `ref`, and the former of each `held` and each
     * `withLegacyRead` runs before the scope binds the name. So the former reads the `ref` as a
     * free variable, which holds no recursion yet. The scope binds the name, and the guard refuses
     * the cycle there with the term of the entry.
     */
    it('builds an adapter over a free ref as an open fragment, and refuses an adapter on a recursive path at the scope', () => {
        const same = { encode: (v: unknown) => v, decode: (v: unknown) => v }
        const older = { decode: () => 'o' as never }
        const unbound = ref('Unbound')
        const h = (c: unknown) =>
            held(
                c as never,
                string as never,
                same as never,
            ) as unknown as AnyCodec
        const leg = (c: unknown) =>
            withLegacyRead({
                current: c as never,
                older,
            }) as unknown as AnyCodec
        const u = (xs: readonly unknown[]) =>
            union(xs as readonly AnyCodec[]) as unknown as AnyCodec
        const routes: readonly (readonly [string, () => unknown])[] = [
            ['a held over a free ref', () => u([h(unbound), string])],
            [
                'a withLegacyRead over a free ref',
                () => u([leg(unbound), string]),
            ],
            [
                'a held under an object',
                () => u([object({ a: h(unbound) }), string]),
            ],
            [
                'a held over an object',
                () => u([h(object({ a: unbound })), string]),
            ],
            ['a held over an array', () => u([h(array(unbound)), string])],
            [
                'a ref to a held over an object of the ref',
                () => scope({ L: h(object({ a: ref('L') })) }),
            ],
            [
                'a ref to a withLegacyRead over an array of the ref',
                () => scope({ L: leg(array(ref('L'))) }),
            ],
            [
                'an object above a ref to a held that closes the cycle',
                () =>
                    scope({
                        H: h(array(ref('X'))),
                        X: object({ h: ref('H') }),
                    }),
            ],
            [
                'two refs, the second to a held over the first',
                () => scope({ A: ref('B'), B: h(object({ a: ref('A') })) }),
            ],
            ['a nested union', () => u([u([h(unbound), string]), string])],
            [
                'a ref to a nested union',
                () => scope({ L: u([h(object({ a: ref('L') })), string]) }),
            ],
            [
                'a union inside its own entry',
                () => scope({ L: u([h(ref('L')), string]) }),
            ],

            [
                'a list spread over a held',
                () => u([list(spread(h(unbound) as never)), string]),
            ],
            [
                'an object rest over a held',
                () =>
                    u([
                        (object as (...x: unknown[]) => unknown)({}, [
                            string,
                            optional(h(unbound) as never),
                        ]),
                        string,
                    ]),
            ],
            [
                'a product with a held field',
                () =>
                    u([
                        (product as (...x: unknown[]) => unknown)(
                            object({ a: h(unbound) }),
                            object({ b: string }),
                        ),
                        string,
                    ]),
            ],
            [
                'a discriminatedUnion member with a held',
                () =>
                    u([
                        (discriminatedUnion as (...x: unknown[]) => unknown)(
                            'k',
                            [
                                object({ k: string('a'), x: h(unbound) }),
                                object({ k: string('b') }),
                            ],
                        ),
                        string,
                    ]),
            ],
            [
                'an mdunion member with a withLegacyRead',
                () =>
                    u([
                        (mdunion as (...x: unknown[]) => unknown)(
                            ['k'],
                            [
                                object({ k: string('a'), x: leg(unbound) }),
                                object({ k: string('b') }),
                            ],
                        ),
                        string,
                    ]),
            ],
            [
                'a held whose outer is a free ref',
                () =>
                    u([
                        held(string as never, unbound as never, same as never),
                        string,
                    ]),
            ],
            [
                'a held in an entry that its object names',
                () => scope({ T: h(ref('Y')), Y: object({ t: ref('T') }) }),
            ],
            [
                'a ref used once before the scope',
                () => {
                    const L = h(object({ a: ref('L') }))
                    L.encode('x' as never)
                    return scope({ L })
                },
            ],
            [
                'a nullable over a ref to a held',
                () =>
                    scope({
                        L: nullable(ref('H')),
                        H: h(object({ a: ref('L') })),
                    }),
            ],
        ]
        const refusedAt = (make: () => unknown): string => {
            try {
                make()
                return 'open fragment'
            } catch (thrown) {
                if (thrown instanceof RecursionRefused)
                    return thrown.use === 3 ? 'scope' : 'scope, no container'
                return String(thrown)
            }
        }
        // each route that a scope closes is a cycle, and each other route reads a free ref
        const closedByScope = new Set([
            'a ref to a held over an object of the ref',
            'a ref to a withLegacyRead over an array of the ref',
            'an object above a ref to a held that closes the cycle',
            'two refs, the second to a held over the first',
            'a ref to a nested union',
            'a union inside its own entry',
            'a held in an entry that its object names',
            'a ref used once before the scope',
            'a nullable over a ref to a held',
        ])
        expect(routes.map(([name, make]) => [name, refusedAt(make)])).toEqual(
            routes.map(([name]) => [
                name,
                closedByScope.has(name) ? 'scope' : 'open fragment',
            ]),
        )
    })
})

/**
 * **The views of an option read through its thunk, as the model's views read through a binder.**
 * The caller view of a recursive option is the recursion of the caller view of its body, and the
 * stored view is the same on the stored side. Two options whose caller views meet at the bottom
 * and whose stored views meet at the bottom are orthogonal, and an adapter below the recursion
 * does not change that.
 */
describe('a union reads the views of a recursive option through its thunk', () => {
    it('accepts a recursive option with an adapter below the recursion, where the views of the two options part', () => {
        const { json } = scope({
            json: union([decimal('1', '2.5'), array(ref('json'))]),
        })
        const values = ['A', '1', ['2.5', ['1']]]
        const attributes: AttributeValue[] = [
            { S: 'A' },
            { N: '1' },
            { L: [{ N: '2.5' }, { L: [{ N: '1' }] }] },
        ]
        const answers = sameUnderEveryOrder(
            [string('A', 'B'), json],
            (codec) => [
                ...values.map((v) => codec.encode(v)),
                ...attributes.map((a) => codec.decode(a)),
            ],
        )
        // each value has one writer, and what the union writes it reads back
        expect(answers).toEqual([...attributes, ...values])
    })

    it('refuses the same recursive option beside an option whose caller view meets its caller view', () => {
        const { json } = scope({
            json: union([decimal('1', '2.5'), array(ref('json'))]),
        })
        // the text '1' is a value of both options, written as `S` by one and as `N` by the other
        expect(() =>
            union([string('1', 'B'), json] as unknown as readonly AnyCodec[]),
        ).toThrow(CodecError)
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
        ["decimal('1')", decimal('1')],
        ["decimal('1', '2.5')", decimal('1', '2.5')],
        ["decimal('2', '3')", decimal('2', '3')],
        ['dynamoNumber', dynamoNumber],
        ['number', number],
        ['number(1)', number(1)],
        ['flip', flip],
        ['decimal.set()', decimal.set()],
        ['array(string)', array(string)],
        ['legacy', legacy],
        // a closure, and a list of adapters beside it that its inner term meets at the bottom
        ['numeral', refine(string, isNumeral as (s: string) => s is string)],
        ['array(decimal)', array(decimal)],
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
        ['A'],
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
        { L: [{ N: '1' }] },
        { L: [{ S: 'A' }] },
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

describe("extract and exclude partition a union's values and keep its answers", () => {
    type Pair = {
        readonly encode: (value: unknown) => unknown
        readonly decode: (attribute: AttributeValue) => unknown
    }
    type Sliceable = Pair & {
        readonly extract: (clause: Readonly<Record<string, unknown>>) => Pair
        readonly exclude: (clause: Readonly<Record<string, unknown>>) => Pair
    }
    const rows = union([
        object({ k: string('A', 'B'), a: string }),
        object({ k: string('C'), b: decimal }),
        object({ k: string('D', 'E'), c: boolean }),
    ] as unknown as readonly AnyCodec[]) as unknown as Sliceable
    const clauses = [
        { k: string('A') },
        { k: string('C') },
        { k: string('B', 'D') },
        { k: string('A', 'B') },
        { k: string('C', 'D', 'E') },
        { k: string('A', 'B', 'C', 'D', 'E') },
    ]
    const values: readonly unknown[] = [
        { k: 'A', a: 'x' },
        { k: 'B', a: 'y' },
        { k: 'C', b: '1.5' },
        { k: 'D', c: true },
        { k: 'E', c: false },
        { k: 'A', b: '1' },
        { k: 'Z', a: 'x' },
        'not an object',
    ]
    const sameAnswer = (a: unknown, b: unknown) =>
        JSON.stringify(a) === JSON.stringify(b)
    const ok = (result: unknown) => !failed(result)

    // the control: a slice is not empty, so the partition below is not vacuous. A slice keeps
    // whole options, as TypeScript's `Extract` does: `k: string('A')` covers no option, because
    // the first option also takes 'B'
    it('keeps a value its clause names, and drops it from the rest', () => {
        const clause = { k: string('A', 'B') }
        expect(ok(rows.extract(clause).encode({ k: 'A', a: 'x' }))).toBe(true)
        expect(ok(rows.exclude(clause).encode({ k: 'A', a: 'x' }))).toBe(false)
        expect(ok(rows.exclude(clause).encode({ k: 'C', b: '1.5' }))).toBe(true)
    })

    it("writes each value of the union through exactly one slice, with the union's answer", () => {
        const disagreements: string[] = []
        for (const clause of clauses) {
            const kept = rows.extract(clause)
            const rest = rows.exclude(clause)
            for (const v of values) {
                const whole = rows.encode(v)
                const [x, y] = [kept.encode(v), rest.encode(v)]
                const at = `${JSON.stringify(clause.k.def)} ${JSON.stringify(v)}`
                if (!ok(whole)) {
                    if (ok(x) || ok(y)) disagreements.push(`slice writes ${at}`)
                    continue
                }
                if (ok(x) === ok(y)) disagreements.push(`not a partition ${at}`)
                const answer = ok(x) ? x : y
                if (!sameAnswer(answer, whole))
                    disagreements.push(`answer ${at}`)
            }
        }
        expect(disagreements).toEqual([])
    })

    it("reads each attribute of the union through exactly one slice, with the union's answer", () => {
        const attributes = values
            .map((v) => rows.encode(v))
            .filter(ok) as AttributeValue[]
        const disagreements: string[] = []
        for (const clause of clauses) {
            const kept = rows.extract(clause)
            const rest = rows.exclude(clause)
            for (const attribute of attributes) {
                const whole = rows.decode(attribute)
                const [x, y] = [kept.decode(attribute), rest.decode(attribute)]
                const at = `${JSON.stringify(clause.k.def)} ${JSON.stringify(attribute)}`
                if (ok(x) === ok(y)) disagreements.push(`not a partition ${at}`)
                const answer = ok(x) ? x : y
                if (!sameAnswer(answer, whole))
                    disagreements.push(`answer ${at}`)
            }
        }
        expect(disagreements).toEqual([])
    })
})

/**
 * **A union over an open fragment defers its decision to the scope.** A `ref` that no scope binds
 * names a codec with no meaning yet, so the union holds no compatibility verdict and no guard
 * verdict. The construction accepts, each use refuses by name, and the scope that binds the name
 * decides. The pair has the shape of the pool's open fragments: a stand-in over a slot that reads
 * the free `ref`.
 */
describe('a union over an open fragment defers its decision to the scope, so no caller observes a compatibility or guard verdict on an open term', () => {
    const build = object as unknown as (spec: unknown) => AnyCodec
    const fragment = (inner: AnyCodec, standIn: unknown) =>
        build({
            a: number,
            b: withLegacyRead({
                current: build({
                    a: optional(build({ a: inner, b: number }) as never),
                }) as never,
                whenMissing: standIn as never,
            }),
        })
    const free = /reads 'undeclared' through a `ref` that no scope binds/
    const open = () => ref('undeclared') as unknown as AnyCodec

    it('refuses the closed pair at compatibility, so the open pair has a verdict to defer', () => {
        expect(() =>
            union([fragment(string, {}), fragment(string, {})]),
        ).toThrow(/are not shown compatible/)
    })

    it('accepts the open pair at construction, and refuses each use by the free name', () => {
        const u = union([fragment(open(), {}), fragment(open(), {})])
        expect(String(u.encode({ a: 1, b: {} } as never))).toMatch(free)
        expect(String(u.decode({ M: {} } as never))).toMatch(free)
    })

    it('accepts an option that reads the free ref at its own input, and the scope that binds the name refuses it at the guard', () => {
        const u = union([open(), string])
        expect(String(u.encode('x' as never))).toMatch(free)
        expect(() =>
            scope({ undeclared: union([ref('undeclared'), string]) }),
        ).toThrow(CodecError)
    })
})
