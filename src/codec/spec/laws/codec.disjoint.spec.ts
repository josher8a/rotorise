/**
 * Disjointness over terms: `Calculus.Closed.disjoint` on this side of the bridge.
 *
 * The rule each test names is the one the model proves. `true` says that no value and no
 * attribute is shared. `false` states nothing: the test is sound, not complete. So a pair that
 * shares a value is pinned at `false`, and a pair that the test cannot read is pinned at `false`
 * too, with the reason.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec } from '../../codec'
import {
    array,
    boolean,
    decimal,
    held,
    never,
    nullValue,
    number,
    object,
    opaque,
    optional,
    ref,
    refine,
    scope,
    string,
    undefinable,
    union,
    withLegacyRead,
} from '../../codec'
import { disjoint, viewsDisjoint } from '../../scoped'
import type { Field, Term } from '../../term'

const termOf = (codec: { readonly def: Term }): Term => codec.def

/** The test in both orders: the answer of a sound test does not read the order. */
const apart = (x: Term, y: Term): boolean => {
    const one = disjoint(x, y)
    expect(disjoint(y, x)).toBe(one)
    return one
}

describe('two primitives are disjoint where they share no value', () => {
    it('keeps two bases apart and two literals of one base apart', () => {
        expect(apart(termOf(string), termOf(boolean))).toBe(true)
        expect(apart(termOf(string('A')), termOf(string('B')))).toBe(true)
    })

    it('keeps a literal beside its own base together', () => {
        expect(apart(termOf(string('A')), termOf(string))).toBe(false)
        expect(apart(termOf(string), termOf(string))).toBe(false)
    })

    it('keeps the bottom apart from every term', () => {
        expect(apart(termOf(never), termOf(string))).toBe(true)
        expect(apart(termOf(object({ a: string })), termOf(never))).toBe(true)
    })
})

describe('two sets are disjoint where their elements are, because a stored set is not empty', () => {
    it('keeps two literal sets with no shared member apart', () => {
        expect(
            apart(termOf(string.set('a', 'b')), termOf(string.set('c'))),
        ).toBe(true)
    })

    it('keeps two literal sets with a shared member together', () => {
        expect(
            apart(termOf(string.set('a', 'b')), termOf(string.set('b', 'c'))),
        ).toBe(false)
    })
})

describe('an adapter is disjoint from the bottom alone, and the views read it', () => {
    /**
     * `string` and `decimal` admit the same text and store it at `S` and at `N`, so a value they
     * share is stored two ways. The caller views share the text, so the certificate refuses.
     */
    it('refuses string beside decimal, and a set of string beside a set of decimal', () => {
        for (const [x, y] of [
            [string, decimal],
            [string('1'), decimal],
            [string, decimal('1')],
            [string.set(), decimal.set()],
        ] as const) {
            expect(apart(termOf(x), termOf(y))).toBe(false)
            expect(viewsDisjoint(termOf(x), termOf(y))).toBe(false)
            expect(viewsDisjoint(termOf(y), termOf(x))).toBe(false)
        }
    })

    /**
     * `number` and `decimal` write different value kinds and read the same member `N`. The caller
     * views are disjoint and the stored views are not, so the certificate refuses.
     */
    it('refuses the number family beside the decimal family, because both read N', () => {
        for (const [x, y] of [
            [number, decimal],
            [number.set(), decimal.set()],
        ] as const) {
            expect(viewsDisjoint(termOf(x), termOf(y))).toBe(false)
            expect(viewsDisjoint(termOf(y), termOf(x))).toBe(false)
        }
    })

    /** `decimal` holds text and stores `N`, and `boolean` shares neither, so the views are apart. */
    it('certifies decimal beside boolean through the views, where the raw terms decline', () => {
        expect(apart(termOf(decimal), termOf(boolean))).toBe(false)
        expect(viewsDisjoint(termOf(decimal), termOf(boolean))).toBe(true)
    })
})

describe('opaque admits every value, so it is disjoint from the bottom alone', () => {
    it('keeps opaque together with an object, a base and the null point', () => {
        expect(apart(termOf(opaque()), termOf(object({ a: string })))).toBe(
            false,
        )
        expect(apart(termOf(opaque()), termOf(string))).toBe(false)
        expect(
            apart(
                { kind: 'union', options: [termOf(string), termOf(nullValue)] },
                termOf(opaque()),
            ),
        ).toBe(false)
    })
})

/**
 * A refinement admits a part of what its inner term admits. So a refinement is disjoint from each
 * partner that its inner term is disjoint from, whatever the predicate is.
 */
describe('a refinement by a closure is disjoint where its inner term is', () => {
    const nonEmpty = refine(string, (s: string): s is string => s.length > 0)

    it('keeps the closure apart from what its inner term keeps apart', () => {
        expect(apart(termOf(nonEmpty), termOf(boolean))).toBe(true)
        expect(apart(termOf(nonEmpty), termOf(array(decimal)))).toBe(true)
    })

    it('declines where the inner term shares a value, because a closure is not data', () => {
        expect(apart(termOf(nonEmpty), termOf(string))).toBe(false)
        expect(apart(termOf(string('A')), termOf(nonEmpty))).toBe(false)
    })

    it('declines a data refinement beside an adapter, which the raw test does not read', () => {
        const one: Term = {
            kind: 'refine',
            inner: termOf(string),
            q: {
                kind: 'members',
                literal: { kind: 'alternatives', base: 'string', ls: ['1'] },
            },
        }
        expect(apart(one, termOf(decimal))).toBe(false)
    })
})

/**
 * A field with a fallback reads a map without the name to a value with the name, so the model
 * counts the field as held. A refinement over a term that holds such a field reads no data
 * predicate, on either side, and its inner term bounds it. No public constructor builds a
 * `members` refinement, so each test builds the raw term.
 */
describe('a refinement over a term that holds a fallback field reads no predicate below it, as the model does', () => {
    const among = (inner: Term, member: string): Term => ({
        kind: 'refine',
        inner,
        q: {
            kind: 'members',
            literal: { kind: 'alternatives', base: 'string', ls: [member] },
        },
    })
    const withFallback: Term = {
        kind: 'object',
        body: {
            fields: { a: { mark: 'fallback', t: termOf(string), v: 'd' } },
        },
    }
    const required: Term = {
        kind: 'object',
        body: { fields: { a: { mark: 'req', t: termOf(string) } } },
    }

    it('reads no predicate of a left refinement over a fallback field', () => {
        expect(disjoint(among(withFallback, 'a'), among(required, 'b'))).toBe(
            false,
        )
    })

    it('drops the predicate of a right refinement over a fallback field at the split', () => {
        const right = among(
            { kind: 'union', options: [withFallback, termOf(string)] },
            'b',
        )
        expect(disjoint(among(termOf(string), 'a'), right)).toBe(false)
    })

    it('reads no predicate of a right refinement chain over a fallback field', () => {
        expect(disjoint(among(required, 'b'), among(withFallback, 'a'))).toBe(
            false,
        )
    })
})

describe('two objects are disjoint where one name holds two fields apart', () => {
    const body = (fields: Record<string, Field>): Term => ({
        kind: 'object',
        body: { fields },
    })

    /** A closed body refuses a name it does not declare, so a name the other requires is apart. */
    it('keeps two closed objects apart where one requires a name the other refuses', () => {
        expect(
            apart(termOf(object({ a: string })), termOf(object({ b: string }))),
        ).toBe(true)
        expect(
            apart(
                termOf(object({ a: string })),
                termOf(object({ a: string, b: boolean })),
            ),
        ).toBe(true)
        expect(
            apart(body({ x: { mark: 'req', t: termOf(string) } }), body({})),
        ).toBe(true)
    })

    /** Two fields that both admit a map without the name share that map. */
    it('keeps two objects together where no name is required on either side', () => {
        expect(
            apart(
                body({ x: { mark: 'optional', t: termOf(string) } }),
                body({ y: { mark: 'optional', t: termOf(string) } }),
            ),
        ).toBe(false)
    })

    /**
     * A `withLegacyRead` field reads a map without the name to its stand-in, so it requires the
     * name on no side of a read.
     */
    it('keeps a stand-in field together with an optional field and with an empty object', () => {
        const standIn = object({
            a: withLegacyRead({ current: string, whenMissing: 'x' }),
        })
        expect(
            apart(termOf(object({ a: optional(boolean) })), termOf(standIn)),
        ).toBe(false)
        expect(apart(termOf(standIn), termOf(standIn))).toBe(false)
        expect(
            apart(
                body({ x: { mark: 'fallback', t: termOf(string), v: 'd' } }),
                body({}),
            ),
        ).toBe(false)
    })

    it('keeps a required field apart from a stand-in field whose terms are disjoint', () => {
        const standIn = object({
            a: withLegacyRead({ current: string, whenMissing: 'x' }),
        })
        expect(apart(termOf(object({ a: boolean })), termOf(standIn))).toBe(
            true,
        )
        expect(apart(termOf(object({ a: string })), termOf(standIn))).toBe(
            false,
        )
    })

    /**
     * **An `undefinable` field is an `optional` field.** The row stores `undefined` as an absent
     * name, so the field admits a map without the name, and a required name is apart from the
     * field where the two terms are disjoint.
     */
    it('keeps a required field apart from an undefinable field whose terms are disjoint', () => {
        const maybe = termOf(object({ a: undefinable(boolean) }))
        expect(apart(maybe, termOf(object({ a: string })))).toBe(true)
        expect(viewsDisjoint(maybe, termOf(object({ a: string })))).toBe(true)
        expect(apart(maybe, termOf(object({ a: boolean })))).toBe(false)
        expect(apart(maybe, termOf(object({ a: optional(string) })))).toBe(
            false,
        )
    })

    /**
     * **A body holds every undeclared name at its open block.** A required name is apart from the
     * other body's block where the two terms are disjoint.
     */
    it('reads an open block at every name the other body declares', () => {
        const open = termOf(object({ a: string }, [string, optional(string)]))
        const map = termOf(object([string, optional(string)]))
        const sets = termOf(object([string, optional(string.set('a', 'b'))]))
        expect(apart(open, map)).toBe(false)
        expect(apart(open, sets)).toBe(true)
    })
})

describe('a union is disjoint from a partner where each option is', () => {
    it('keeps a union together with a partner that one option shares', () => {
        expect(apart(termOf(union([string, boolean])), termOf(string))).toBe(
            false,
        )
    })

    it('keeps a union apart from a partner that no option shares', () => {
        expect(apart(termOf(union([string, boolean])), termOf(nullValue))).toBe(
            true,
        )
    })
})

describe('two list shapes are disjoint where one position of each common length is', () => {
    const listOf = (
        pre: readonly Term[],
        spread: Term | undefined,
        suf: readonly Term[],
    ): Term =>
        spread === undefined
            ? { kind: 'list', pre, suf }
            : { kind: 'list', pre, spread, suf }

    it('keeps two fixed arities of different lengths apart', () => {
        expect(
            apart(
                listOf([termOf(string)], undefined, []),
                listOf([termOf(string), termOf(string)], undefined, []),
            ),
        ).toBe(true)
    })

    it('keeps a fixed arity apart from a spreading shape that cannot reach its length', () => {
        expect(
            apart(
                listOf([termOf(string), termOf(string)], termOf(string), []),
                listOf([termOf(string)], undefined, []),
            ),
        ).toBe(true)
    })

    it('keeps two rows of one length apart at one disjoint position', () => {
        expect(
            apart(
                listOf([termOf(string)], undefined, []),
                listOf([termOf(boolean)], undefined, []),
            ),
        ).toBe(true)
        expect(
            apart(
                listOf([termOf(string), termOf(boolean)], undefined, []),
                listOf([termOf(string('a')), termOf(boolean)], undefined, []),
            ),
        ).toBe(false)
    })

    /** Every array holds the empty list, so two arrays share it whatever their elements are. */
    it('keeps two arrays together, because both hold the empty list', () => {
        expect(apart(termOf(array(string)), termOf(array(boolean)))).toBe(false)
    })

    /**
     * **Where one spreading side dominates, the row at `max p1 p2 + max s1 s2` decides.** Where
     * neither side dominates, the test declines.
     */
    it('reads the common row where one spreading side dominates, and declines elsewhere', () => {
        expect(
            apart(
                listOf([termOf(string)], termOf(string), []),
                listOf([termOf(boolean), termOf(string)], termOf(string), []),
            ),
        ).toBe(true)
        expect(
            apart(
                listOf([termOf(boolean), termOf(string)], termOf(string), [
                    termOf(string),
                ]),
                listOf([termOf(string)], termOf(string), [
                    termOf(string),
                    termOf(boolean),
                ]),
            ),
        ).toBe(false)
    })
})

describe('two recursive terms are disjoint where their bodies are', () => {
    const { json, other } = scope({
        json: union([string, array(ref('json'))]),
        other: union([string, array(ref('other'))]),
    })

    it('keeps two recursive terms together where the bodies share a value, and ends', () => {
        expect(apart(json.def as Term, other.def as Term)).toBe(false)
    })

    it('keeps a recursive term apart from a partner that no stage shares', () => {
        expect(apart(json.def as Term, termOf(nullValue))).toBe(true)
    })
})

/**
 * The test splits the right operand at every depth, as it reads the left operand. A right
 * refinement keeps its predicate on each option below it, and a right recursive term is read
 * whole and unfolded. So no right `refine` and no right recursive term hides an option, and the
 * verdict does not read the order of the operands.
 */
describe('the verdict does not read the order of the operands', () => {
    const among = (inner: Term, member: string): Term => ({
        kind: 'refine',
        inner,
        q: {
            kind: 'members',
            literal: { kind: 'alternatives', base: 'string', ls: [member] },
        },
    })
    const listOf = (head: AnyCodec): AnyCodec =>
        scope({ self: union([head, object({ k: ref('self') })]) }).self
    const booleans = listOf(boolean)
    const strings = refine(
        listOf(string) as never,
        (_v: unknown): _v is unknown => true,
    ) as unknown as AnyCodec

    it('keeps a refinement apart from a right union that a refinement restricts to another member', () => {
        const xb = among(termOf(string), 'b')
        const yb: Term = {
            kind: 'union',
            options: [
                among(
                    {
                        kind: 'union',
                        options: [
                            among(termOf(string), 'a'),
                            { kind: 'number' },
                        ],
                    },
                    'b',
                ),
                { kind: 'number' },
            ],
        }
        expect(apart(xb, yb)).toBe(true)
    })

    it('keeps a refinement apart from a right recursive term whose stages it shares no member with', () => {
        const stages: Term = {
            kind: 'union',
            options: [
                among(termOf(string), 'a'),
                {
                    kind: 'object',
                    body: {
                        fields: {
                            k: {
                                mark: 'req',
                                t: { kind: 'lazy', get: () => stages },
                            },
                        },
                    },
                },
            ],
        }
        expect(apart(among(termOf(string), 'b'), stages)).toBe(true)
    })

    it('keeps two recursive terms apart where a refinement covers the right one', () => {
        expect(apart(termOf(booleans), termOf(strings))).toBe(true)
    })

    it('certifies a recursive term beside an adapter over a refined recursive term in both orders', () => {
        const adapted = held(
            string as never,
            strings as never,
            {
                encode: (v: never) => v,
                decode: (v: never) => v,
            } as never,
        ) as unknown as AnyCodec
        expect(() => union([booleans, adapted] as never)).not.toThrow()
        expect(() => union([adapted, booleans] as never)).not.toThrow()
    })
})
