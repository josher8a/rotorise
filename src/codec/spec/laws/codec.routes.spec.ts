/**
 * A codec of a constructor and the codec of its term agree.
 *
 * A term is the object, and a codec is its projection. A constructor builds the codec from the
 * codecs of its parts, and a bare term takes the all-kinds route, which builds the same codec
 * from the term alone. The two routes are two ways to one meaning, so each value that the
 * arbitrary of `testing.ts` draws for the codec of a constructor is written and read to the same
 * result by the codec of the copied term, and the item reading agrees where the codec has one.
 * The copy is a new object, so the cache of the identity of a term gives no answer.
 */
import * as sdk from '@aws-sdk/util-dynamodb'
import { describe, expect, it } from 'vitest'
import { codecOfTerm } from '../../allKinds'
import type { AttributeMap } from '../../attribute'
import { DynamoNumber } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    encodeAny,
    fill,
    held,
    item,
    legacy,
    list,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    orThrow,
    refine,
    set,
    spread,
    string,
    undefinable,
    union,
} from '../../codec'
import { termOf } from '../../denote'
import { native } from '../../native'
import { dynamoNumber } from '../../prisms'
import type { Rng, Term } from '../../term'
import type { Checkable, Reference } from '../../testing'
import {
    arbitraryOf,
    checkAgainst,
    firstDifference,
    rngFrom,
    structuralEquals,
} from '../../testing'

/** A deep copy of a term, which keeps each `ref` and each function by identity. */
const copyOf = (t: unknown, seen = new Map<object, unknown>()): unknown => {
    if (typeof t !== 'object' || t === null) return t
    if (Object.getPrototypeOf(t) !== Object.prototype && !Array.isArray(t))
        return t
    if ((t as Term).kind === 'ref') return t
    const known = seen.get(t)
    if (known) return known
    const out: Record<string, unknown> = Array.isArray(t)
        ? ([] as unknown as Record<string, unknown>)
        : {}
    seen.set(t, out)
    for (const [k, v] of Object.entries(t)) out[k] = copyOf(v, seen)
    return out
}

/**
 * A named codec of the pool, and the values that the intended meaning admits. A list of entries holds
 * each name, so a name that two entries share is visible. The intended values come from the reading
 * of the constructor and not from the term of the codec, so a wrong term cannot hide behind them.
 */
type Entry = readonly [
    name: string,
    codec: AnyCodec,
    ...intended: readonly unknown[],
]

const A = object({ kind: string('A'), a: string })
const B = object({ kind: string('B'), b: number })

const numOne = orThrow(DynamoNumber.from('1'))
const twoAndAHalf = orThrow(DynamoNumber.from('2.5'))
const seven = orThrow(DynamoNumber.from('7'))
const bytes = [Uint8Array.of(1), Uint8Array.of(2, 3)] as const

/**
 * The literal codecs. A literal of one value and a choice among literals of one base build their
 * pair in the constructor, and the all-kinds route builds the same term through the general union.
 * The two statements of one meaning must agree on each value and on the text of each refusal.
 */
const literals: readonly Entry[] = [
    ['one', string('A'), 'A'],
    ['choice', string('A', 'B'), 'A', 'B'],
    ['flags', boolean(true, false), true, false],
    ['oneBinary', binary(bytes[0]), bytes[0]],
    ['binaries', binary(...bytes), ...bytes],
    ['oneNumber', dynamoNumber(numOne)],
    ['numbers', dynamoNumber(numOne, twoAndAHalf)],
    ['floats', number(1, 2), 1, 2],
    ['decimals', decimal('1', '2.5')],
    [
        'inObject',
        object({ kind: string('A', 'B'), n: number(1, 2) }),
        { kind: 'A', n: 1 },
        { kind: 'B', n: 2 },
    ],
    ['inArray', array(string('A', 'B')), ['A', 'B'], []],
]

const constructed: readonly Entry[] = [
    ...literals,
    ['string', string, 'x', ''],
    ['number', number, 1.5, 0],
    ['decimal', decimal],
    ['boolean', boolean, true, false],
    ['binary', binary, bytes[1]],
    ['literal', string('x', 'y'), 'x', 'y'],
    ['list', array(string), ['a', 'b'], []],
    ['strings', set(string), new Set(['a', 'b'])],
    ['tuple', list(string, number), ['a', 1]],
    [
        'tail',
        list(string, spread(number), boolean),
        ['a', 1, 2, true],
        ['a', true],
    ],
    [
        'middle',
        list(string, spread(number), boolean, binary),
        ['a', 1, 2, true, bytes[0]],
        ['a', true, bytes[0]],
    ],
    [
        'listOfLiterals',
        list(string('A', 'B'), spread(string('C'))),
        ['A', 'C', 'C'],
        ['B'],
    ],
    ['setOfLiterals', set(string('A', 'B')), new Set(['A', 'B'])],
    ['setOfBinary', set(binary), new Set(bytes)],
    ['ofObjects', array(A), [{ kind: 'A', a: 'x' }]],
    [
        'open',
        object({ a: string }, [string, optional(number)]),
        { a: 'x' },
        { a: 'x', k: 1 },
    ],
    [
        'marks',
        object({
            a: undefinable(string),
            b: optional(boolean),
            c: fill(number, 1),
        }),
        { a: undefined, b: true, c: 2 },
        { a: 'x', c: 1 },
    ],
    [
        'deep',
        object({
            inner: object({ list: array(string('A', 'B')), tags: set(string) }),
        }),
        { inner: { list: ['A'], tags: new Set(['a']) } },
    ],
    [
        'ofTagged',
        array(discriminatedUnion('kind', [A, B])),
        [
            { kind: 'A', a: 'x' },
            { kind: 'B', b: 1 },
        ],
    ],
    [
        'ofMulti',
        list(discriminatedUnion(['kind'], [A, B])),
        [{ kind: 'A', a: 'x' }],
        [{ kind: 'B', b: 1 }],
    ],
    [
        'setOfRefined',
        set(refine(string, (s): s is string => s.length > 1)),
        new Set(['ab', 'cd']),
    ],
    ['setOfNumbers', set(number), new Set([1, 2.5])],
    ['nested', array(array(number)), [[1], [2, 3]]],
    [
        'object',
        object({ a: string, b: optional(number), c: fill(string, 'z') }),
        { a: 'x', b: 1, c: 'y' },
    ],
    ['nullable', nullable(string), 'x', null],
    ['nullValue', nullValue, null],
    ['opaque', opaque],
    ['lossy', opaque('lossy'), 'x', 1, { a: [true, null] }],
    ['refuse', opaque('refuse'), 'x', { a: [true, null] }],
    ['refined', refine(string, (s): s is string => s.length > 1), 'ab'],
    [
        'held',
        held(string, string, {
            encode: (s: string) => s.toUpperCase(),
            decode: (s: string) => s.toLowerCase(),
        }),
    ],
    [
        'legacy',
        legacy({
            current: string,
            older: { decode: (attribute: unknown) => String(attribute) },
        }),
        'x',
    ],
    [
        'refinedObject',
        object({
            name: refine(string, (s): s is string => s.length > 1),
        }),
        { name: 'ab' },
    ],
    ['union', union([string, number]), 'x', 1],
    ['objects', union([A, B]), { kind: 'A', a: 'x' }, { kind: 'B', b: 1 }],
    [
        'tagged',
        discriminatedUnion('kind', [A, B]),
        { kind: 'A', a: 'x' },
        { kind: 'B', b: 1 },
    ],
]

/**
 * A pool of codecs drawn from the public constructors, to a depth bound, from a seed. Each draw
 * carries the values that its construction admits, built from the values of its parts, so a wrong
 * term cannot hide behind them. The seeds are the inputs that break a carrier. A name is the
 * construction in words, so two draws of one construction are one entry.
 */
const leaves: readonly Entry[] = [
    ['string', string, 'x'],
    ['number', number, 1.5],
    ['boolean', boolean, true],
    ['binary', binary, bytes[0]],
    ["'A'|'B'", string('A', 'B'), 'A', 'B'],
    ['null', nullValue, null],
]

const seeds: readonly Entry[] = [
    ['object()', object({}), {}],
    ['array(never)', array(never as never), []],
    ['union(never,string)', union([never as never, string]), 'x'],
    ['nullable(never)', nullable(never as never), null],
    ["'A'", string('A'), 'A'],
    ['set(binary)', set(binary), new Set(bytes)],
    [
        'list(string,spread(number))',
        list(string, spread(number)),
        ['a', 1, 2],
        ['a'],
    ],
    [
        'list(string,spread(number),boolean)',
        list(string, spread(number), boolean),
        ['a', 1, true],
        ['a', true],
    ],
    [
        'object(inner:object(v:string))',
        object({ inner: object({ v: string }) }),
        { inner: { v: 'x' } },
    ],
]

/** A drawn codec in the place of a codec of one type: the draw knows no type of its own. */
const as_ = (codec: AnyCodec): typeof string => codec as never

const grow = (rng: Rng, depth: number): Entry => {
    const at = <T>(xs: readonly T[]): T =>
        xs[Math.floor(rng() * xs.length)] as T
    if (depth === 0) return at(leaves)
    const [n1, c1, ...w1] = grow(rng, depth - 1)
    const [n2, c2, ...w2] = grow(rng, depth - 1)
    const [a, b] = [w1[0], w2[0]]
    const built: readonly Entry[] = [
        [`array(${n1})`, array(as_(c1)), [a], []],
        [`list(${n1},${n2})`, list(as_(c1), as_(c2)), [a, b]],
        [
            `list(${n1},spread(${n2}))`,
            list(as_(c1), spread(as_(c2))),
            [a, b, b],
        ],
        [
            `list(${n1},spread(${n2}),${n1})`,
            list(as_(c1), spread(as_(c2)), as_(c1)),
            [a, b, a],
        ],
        [
            `object(a:${n1},b:${n2})`,
            object({ a: as_(c1), b: as_(c2) }),
            { a, b },
        ],
        [`nullable(${n1})`, nullable(as_(c1)), ...w1, null],
    ]
    return at(built)
}

const kindsOf = (term: unknown, out = new Set<string>()): Set<string> => {
    if (typeof term !== 'object' || term === null) return out
    if ('kind' in term && typeof term.kind === 'string') out.add(term.kind)
    for (const part of Object.values(term)) kindsOf(part, out)
    return out
}

/** The kinds that the menu of the generator builds. A run that draws fewer tests nothing. */
const menu = [
    'string',
    'number',
    'boolean',
    'binary',
    'null',
    'object',
    'list',
    'union',
]

const drawPool = (
    seed: number,
    draws: number,
    depth: number,
): readonly Entry[] => {
    const rng = rngFrom(seed)
    const grown = Array.from({ length: draws }, () => grow(rng, depth))
    const kinds = new Set(grown.flatMap(([, c]) => [...kindsOf(termOf(c))]))
    const missing = menu.filter((k) => !kinds.has(k))
    if (missing.length > 0)
        throw new CodecError(
            `the drawn pool holds no codec of the kinds ${missing.join(', ')}, with seed ${seed}, so the run tests nothing`,
        )
    const byName = new Map<string, Entry>()
    for (const e of [...seeds, ...grown])
        if (!byName.has(e[0])) byName.set(e[0], e)
    return [...byName.values()].map(
        (e): Entry => [`drawn ${e[0]}`, e[1], ...e.slice(2)],
    )
}

const pool: readonly Entry[] = [...constructed, ...drawPool(20261129, 60, 3)]

describe('a codec of a constructor and the codec of its term agree', () => {
    it('each name of the pool is distinct, so no codec runs under the name of another', () => {
        const names = pool.map(([name]) => name)
        expect(names.filter((n, i) => names.indexOf(n) !== i)).toEqual([])
        expect(constructed.filter(([n]) => withItem.includes(n))).toHaveLength(
            withItem.length,
        )
    })

    for (const [name, codec] of pool) {
        it(`${name}: encode and decode agree on each drawn value`, () => {
            const rebuilt = codecOfTerm(
                copyOf(termOf(codec)) as Term,
            ) as AnyCodec
            expect(rebuilt).not.toBe(codec)
            const rng = rngFrom(20261126)
            let drawn = 0
            for (let k = 0; k < 20; k++) {
                const value = arbitraryOf(codec, rng, 3)
                const written = codec.encode(value as never)
                const same = rebuilt.encode(value as never)
                expect(structuralEquals(written, same)).toBe(true)
                if (written instanceof Error) continue
                const read = codec.decode(written as never)
                const again = rebuilt.decode(written as never)
                expect(structuralEquals(read, again)).toBe(true)
                drawn++
            }
            expect(drawn).toBeGreaterThan(0)
        })
    }

    /**
     * The values that no codec of the pool wrote: the intended values of each other codec, and the
     * inputs that a type does not name. An erased codec is called with any of them, so the codec
     * must check the value that the codec encodes.
     */
    const cyclic: Record<string, unknown> = {}
    cyclic.self = cyclic
    const foreign: readonly unknown[] = [
        ...pool.flatMap(([, , ...intended]) => intended),
        undefined,
        null,
        Symbol('foreign'),
        () => 'foreign',
        cyclic,
        Number.NaN,
        Number.POSITIVE_INFINITY,
        -0,
        0n,
    ]

    it('encode of a foreign value returns a value or a CodecError and never throws', () => {
        const thrown: string[] = []
        let written = 0
        let refused = 0
        for (const [name, codec] of pool)
            for (const value of foreign)
                try {
                    if (encodeAny(codec, value) instanceof CodecError) refused++
                    else written++
                } catch (error) {
                    thrown.push(
                        `${name} on ${typeof value}: ${error instanceof Error ? error.message : String(error)}`,
                    )
                }
        expect(thrown).toEqual([])
        // a run that only writes, or only refuses, tests nothing about the check of the codec
        expect(written).toBeGreaterThan(0)
        expect(refused).toBeGreaterThan(0)
    })

    it('encode throws only what an accessor of the value throws, so no codec throws of its own', () => {
        const accessor = new Error('the accessor of the value')
        const trap = new Proxy(
            {},
            {
                get: () => {
                    throw accessor
                },
            },
        )
        const hostile = [
            {
                get a(): never {
                    throw accessor
                },
                get kind(): never {
                    throw accessor
                },
            },
            trap,
        ]
        const foreignThrows: unknown[] = []
        for (const [, codec] of pool)
            for (const value of hostile)
                try {
                    encodeAny(codec, value)
                } catch (error) {
                    if (error !== accessor) foreignThrows.push(error)
                }
        expect(foreignThrows).toEqual([])
    })

    const withItem = [
        'object',
        'objects',
        'tagged',
        'inObject',
        'open',
        'marks',
    ]
    for (const [name, codec] of constructed.filter(([n]) =>
        withItem.includes(n),
    )) {
        it(`${name}: the item reading agrees on each drawn value`, () => {
            const rebuilt = codecOfTerm(
                copyOf(termOf(codec)) as Term,
            ) as AnyCodec
            const mine = item(codec as never) as unknown as AnyCodec
            const theirs = item(rebuilt as never) as unknown as AnyCodec
            const rng = rngFrom(20261127)
            let drawn = 0
            for (let k = 0; k < 20; k++) {
                const value = arbitraryOf(codec, rng, 3)
                const written = mine.encode(value as never)
                expect(
                    structuralEquals(written, theirs.encode(value as never)),
                ).toBe(true)
                if (written instanceof Error) continue
                expect(
                    structuralEquals(
                        mine.decode(written as never),
                        theirs.decode(written as never),
                    ),
                ).toBe(true)
                drawn++
            }
            expect(drawn).toBeGreaterThan(0)
        })
    }

    /**
     * Each refusal of a choice among literals is one text on the two routes: the options that were
     * available, and the names that a record carried. A refusal that differs between the routes
     * is a second statement of the meaning drifting.
     */
    const written = [
        1,
        'zzz',
        'A',
        true,
        null,
        undefined,
        { a: 1 },
        {},
        [1],
        new Set(),
        Uint8Array.of(9),
        bytes[0],
        bytes[1],
        seven,
        numOne,
        twoAndAHalf,
    ]
    const stored = [
        { S: 'zzz' },
        { S: 'A' },
        { S: 5 },
        { N: '7' },
        { N: '1' },
        { N: '2.5' },
        { N: 'x' },
        { BOOL: true },
        { BOOL: false },
        { B: Uint8Array.of(9) },
        { B: bytes[1] },
        { M: { a: { S: 'x' } } },
        { M: {} },
        { L: [] },
        {},
        null,
        'x',
    ]
    const text = (result: unknown): unknown =>
        result instanceof Error ? result.message : result
    for (const [name, codec] of literals) {
        it(`${name}: each refusal reads the same on the two routes`, () => {
            const rebuilt = codecOfTerm(
                copyOf(termOf(codec)) as Term,
            ) as AnyCodec
            expect(rebuilt).not.toBe(codec)
            for (const value of written) {
                const mine = codec.encode(value as never)
                const theirs = rebuilt.encode(value as never)
                expect(structuralEquals(text(mine), text(theirs))).toBe(true)
                expect(mine instanceof Error).toBe(theirs instanceof Error)
            }
            for (const attribute of stored) {
                const mine = codec.decode(attribute as never)
                const theirs = rebuilt.decode(attribute as never)
                expect(structuralEquals(text(mine), text(theirs))).toBe(true)
                expect(mine instanceof Error).toBe(theirs instanceof Error)
            }
        })
    }

    /**
     * The refusals of a container at its declaration are one text on the two routes: the
     * constructor runs the judgment of its own kind, and the all-kinds route runs the judgment of
     * the term, and a list that nothing fills or a set of another member is refused by both.
     */
    const refusal = (build: () => unknown): string | undefined => {
        try {
            build()
        } catch (error) {
            return error instanceof Error ? error.message : String(error)
        }
        return undefined
    }
    it('a list with a position that nothing fills is refused with one text', () => {
        const constructed = refusal(() =>
            // @ts-expect-error a declared position at `never` is refused in the type too
            list(never, string),
        )
        const term = refusal(() =>
            codecOfTerm({
                kind: 'list',
                pre: [{ kind: 'never' }, { kind: 'string' }],
                suf: [],
            }),
        )
        expect(constructed).toMatch(/position 0 of the declared positions/)
        expect(constructed).toBe(term)
    })
    it('a set of an element that writes no S, N or B is refused with one text', () => {
        const constructed = refusal(() => set(boolean as never))
        const term = refusal(() =>
            codecOfTerm({ kind: 'set', elem: { kind: 'boolean' } }),
        )
        expect(constructed).toMatch(/a set holds strings, numbers or binary/)
        expect(constructed).toBe(term)
    })

    it('a container refuses an element that carries no pair, because it cannot take the pair from a term', () => {
        const bare = {
            encode: string.encode,
            decode: string.decode,
            unsafeEncode: string.unsafeEncode,
            unsafeDecode: string.unsafeDecode,
            def: string.def,
        }
        expect(() => array(bare as never)).toThrow(/carries none/)
    })

    it('an object with a field that nothing fills is refused with one text', () => {
        const constructed = refusal(() =>
            // @ts-expect-error a field at `never` is refused in the type too
            object({ a: never }),
        )
        const term = refusal(() =>
            codecOfTerm({
                kind: 'object',
                body: {
                    fields: { a: { mark: 'req', t: { kind: 'never' } } },
                },
            }),
        )
        expect(constructed).toMatch(/'a' is declared at `never`/)
        expect(constructed).toBe(term)
    })

    it('a union with two options that are not shown compatible is refused with one text', () => {
        const options = [decimal, string('A', 'B')] as const
        const constructed = refusal(() =>
            union(options as unknown as readonly AnyCodec[]),
        )
        const term = refusal(() =>
            codecOfTerm({
                kind: 'union',
                options: options.map((o) => copyOf(termOf(o)) as Term),
            }),
        )
        expect(constructed).toMatch(/are not shown compatible/)
        expect(constructed).toBe(term)
    })

    it('a union of a union and an object reads the same item on the two routes', () => {
        const inner = union([A, B])
        const outer = union([inner, object({ other: string })])
        const rebuilt = codecOfTerm(copyOf(termOf(outer)) as Term) as AnyCodec
        const stored = { M: { kind: { S: 'B' }, b: { N: '3' } } }
        expect(outer.decode(stored as never)).toEqual(
            rebuilt.decode(stored as never),
        )
        expect(item(outer as never).decode(stored.M as never)).toEqual(
            item(rebuilt as never).decode(stored.M as never),
        )
    })

    it('never refuses each write and each read with one text on the two routes', () => {
        const rebuilt = codecOfTerm({ kind: 'never' }) as AnyCodec
        const text = (r: unknown): unknown =>
            r instanceof Error ? r.message : r
        expect(text(never.encode(1 as never))).toMatch(
            /`never` admits no value/,
        )
        expect(text(never.encode(1 as never))).toBe(
            text(rebuilt.encode(1 as never)),
        )
        expect(text(never.decode({ S: 'a' } as never))).toBe(
            text(rebuilt.decode({ S: 'a' } as never)),
        )
    })

    it('nullValue writes null as NULL and refuses another value', () => {
        expect(nullValue.encode(null)).toEqual({ NULL: true })
        expect(nullValue.decode({ NULL: true })).toBeNull()
        expect(nullValue.encode('x' as never)).toBeInstanceOf(Error)
    })

    it('native writes the marshaller form of a plain value, on the two routes', () => {
        const rebuilt = codecOfTerm(copyOf(termOf(native)) as Term) as AnyCodec
        const value = { a: 'x', b: [true, null] }
        const written = {
            M: { a: { S: 'x' }, b: { L: [{ BOOL: true }, { NULL: true }] } },
        }
        expect(native.encode(value)).toEqual(written)
        expect(rebuilt.encode(value as never)).toEqual(written)
        expect(native.decode(written as never)).toEqual(value)
    })
})

/**
 * The SDK marshaller is the external anchor for the attribute format, and the two routes above
 * compare one term with itself. A constructor that builds a wrong term passes the routes, because
 * both routes read the wrong term. The SDK reads no term of ours, so a wrong term writes bytes that
 * the SDK does not write.
 *
 * The adaptations are the ones of `conformance.spec.ts`: a set sorts its elements, and a value
 * beyond `MAX_SAFE_INTEGER` is out of the range of the SDK. One more: the SDK refuses `undefined`
 * unless the call asks for the removal, and a codec omits an attribute that holds `undefined`.
 */
const beyondSafe = (value: unknown): boolean =>
    typeof value === 'number'
        ? Math.abs(value) > Number.MAX_SAFE_INTEGER
        : value instanceof Set || Array.isArray(value)
          ? [...value].some(beyondSafe)
          : typeof value === 'object' &&
            value !== null &&
            !(value instanceof Uint8Array) &&
            Object.values(value).some(beyondSafe)

const withSortedSets = (value: unknown): unknown =>
    value instanceof Set
        ? new Set([...value].sort())
        : Array.isArray(value)
          ? value.map(withSortedSets)
          : typeof value === 'object' &&
              value !== null &&
              !(value instanceof Uint8Array)
            ? Object.fromEntries(
                  Object.entries(value).map(([k, v]) => [k, withSortedSets(v)]),
              )
            : value

const theSdk: Reference<unknown> = {
    marshall: (entity) =>
        sdk.marshall(withSortedSets(entity) as Record<string, unknown>, {
            removeUndefinedValues: true,
        }) as AttributeMap,
}

/** The codecs of the pool that the SDK cannot express, each with the reason. */
const beyondTheSdk = new Map<string, string>([
    ['oneNumber', 'the SDK has no value for a DynamoNumber'],
    ['numbers', 'the SDK has no value for a DynamoNumber'],
    ['decimals', 'the SDK writes a string as S and never as N'],
    ['decimal', 'the SDK writes a string as S and never as N'],
    [
        'opaque',
        'the drawn value holds a DynamoNumber, which the SDK has no value for',
    ],
    ['held', 'the adapter of the codec is unknown to the SDK'],
])

describe('the bytes of a codec of the pool are the bytes of the SDK', () => {
    it('each skipped name is a name of the pool', () => {
        const names = constructed.map(([name]) => name)
        expect(
            [...beyondTheSdk.keys()].filter((n) => !names.includes(n)),
        ).toEqual([])
    })

    for (const [name, codec, ...intended] of pool) {
        const reason = beyondTheSdk.get(name)
        if (reason !== undefined) {
            it.skip(`${name}: skipped, ${reason}`, () => {})
            continue
        }
        it(`${name}: the SDK writes the bytes of the codec over the intended values and the drawn values`, () => {
            expect(intended.length).toBeGreaterThan(0)
            const subject = item(
                object({ v: codec as never }),
            ) as unknown as Checkable<unknown>
            for (const v of intended) {
                expect(
                    firstDifference(
                        subject.unsafeEncode({ v }),
                        theSdk.marshall({ v }),
                    ),
                ).toBeUndefined()
            }
            checkAgainst(subject, theSdk, {
                count: 40,
                seed: 20261128,
                filter: (entity) => !beyondSafe(entity),
            })
        })
    }
})

describe('a drawn pool that holds too few kinds is refused, and is no green run', () => {
    it('a depth of zero draws leaves only, and the run is refused with its seed', () => {
        expect(() => drawPool(7, 20, 0)).toThrow(
            /holds no codec of the kinds .*, with seed 7, so the run tests nothing/,
        )
    })
})
