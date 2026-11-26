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
import { describe, expect, it } from 'vitest'
import { codecOfTerm } from '../../allKinds'
import { DynamoNumber } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    fill,
    item,
    list,
    mdunion,
    never,
    nullable,
    number,
    object,
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
import { dynamoNumber } from '../../prisms'
import type { Term } from '../../term'
import { arbitraryOf, rngFrom, structuralEquals } from '../../testing'

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
const literals: Record<string, AnyCodec> = {
    one: string('A'),
    choice: string('A', 'B'),
    flags: boolean(true, false),
    oneBinary: binary(bytes[0]),
    binaries: binary(...bytes),
    oneNumber: dynamoNumber(numOne),
    numbers: dynamoNumber(numOne, twoAndAHalf),
    floats: number(1, 2),
    decimals: decimal('1', '2.5'),
    inObject: object({ kind: string('A', 'B'), n: number(1, 2) }),
    inArray: array(string('A', 'B')),
}

const constructed: Record<string, AnyCodec> = {
    ...literals,
    string,
    number,
    decimal,
    boolean,
    binary,
    literal: string('x', 'y'),
    list: array(string),
    strings: set(string),
    tuple: list(string, number),
    tail: list(string, spread(number), boolean),
    middle: list(string, spread(number), boolean, binary),
    listOfLiterals: list(string('A', 'B'), spread(string('C'))),
    setOfLiterals: set(string('A', 'B')),
    setOfBinary: set(binary),
    ofObjects: array(A),
    open: object({ a: string }, [string, optional(number)]),
    marks: object({
        a: undefinable(string),
        b: optional(boolean),
        c: fill(number, 1),
    }),
    deep: object({
        inner: object({ list: array(string('A', 'B')), tags: set(string) }),
    }),
    ofTagged: array(discriminatedUnion('kind', [A, B])),
    ofMulti: list(mdunion(['kind'], [A, B])),
    setOfRefined: set(refine(string, (s): s is string => s.length > 1)),
    numbers: set(number),
    nested: array(array(number)),
    object: object({ a: string, b: optional(number), c: fill(string, 'z') }),
    nullable: nullable(string),
    refined: refine(string, (s): s is string => s.length > 1),
    union: union([string, number]),
    objects: union([A, B]),
    tagged: discriminatedUnion('kind', [A, B]),
}

describe('a codec of a constructor and the codec of its term agree', () => {
    for (const [name, codec] of Object.entries(constructed)) {
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

    for (const name of [
        'object',
        'objects',
        'tagged',
        'inObject',
        'open',
        'marks',
    ]) {
        it(`${name}: the item reading agrees on each drawn value`, () => {
            const codec = constructed[name] as AnyCodec
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
    for (const [name, codec] of Object.entries(literals)) {
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
})
