/**
 * The meet over terms: `Calculus.Term.meet` on this side of the bridge.
 *
 * The rule each test names is the one the model proves, and the refusals are the ones the model
 * states. A refusal is not the bottom: `undefined` says no term states the intersection, and
 * `never` says the intersection is empty. Four defects in the Lean development were this
 * distinction going wrong, so the pairs that share a value are pinned one by one.
 */
import { describe, expect, it } from 'vitest'
import {
    binary,
    boolean,
    decimal,
    never,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import type { Body, Field, Term } from '../../term'
import { meetTerms } from '../../term'

const termOf = (codec: { readonly def: Term }): Term => codec.def
const bottom: Term = { kind: 'never' }

describe('the meet is the intersection of two admissions', () => {
    it('answers the finer term where one base restricts the other', () => {
        expect(meetTerms(termOf(string('A')), termOf(string))).toEqual(
            termOf(string('A')),
        )
        expect(meetTerms(termOf(string), termOf(string))).toEqual(
            termOf(string),
        )
    })

    it('answers the bottom where the two admit no common value', () => {
        expect(meetTerms(termOf(string), termOf(boolean))).toEqual(bottom)
        expect(meetTerms(termOf(string('A')), termOf(string('B')))).toEqual(
            bottom,
        )
    })

    it('lets the bottom absorb', () => {
        expect(meetTerms(termOf(never), termOf(string))).toEqual(bottom)
        expect(meetTerms(termOf(object({ a: string })), termOf(never))).toEqual(
            bottom,
        )
    })
})

describe('a pair that shares what it writes two ways has no meet', () => {
    /**
     * `string` and `decimal` admit the same text and store it at `S` and at `N`, so a value they
     * share is stored two ways. The bottom would claim they share none.
     */
    it('refuses string against decimal rather than answering the bottom', () => {
        expect(meetTerms(termOf(string), termOf(decimal))).toBeUndefined()
        expect(meetTerms(termOf(decimal), termOf(string))).toBeUndefined()
        expect(meetTerms(termOf(string('1')), termOf(decimal))).toBeUndefined()
        expect(meetTerms(termOf(decimal('1')), termOf(string))).toBeUndefined()
    })

    /** The same pair one container out: both write a `strSet`, stored at `SS` and at `NS`. */
    it('refuses a set of string against a set of decimal', () => {
        expect(
            meetTerms(termOf(string.set()), termOf(decimal.set())),
        ).toBeUndefined()
    })

    /**
     * `number` and `decimal` write different value kinds and read the same member `N`, so the
     * bottom is right about the write side and wrong about the read side.
     */
    it('refuses the number family against the decimal family', () => {
        expect(meetTerms(termOf(number), termOf(decimal))).toBeUndefined()
        expect(
            meetTerms(termOf(number.set()), termOf(decimal.set())),
        ).toBeUndefined()
    })
})

describe('a factor whose admission is a function states no meet', () => {
    it('refuses an opaque partner it cannot read as a closed form', () => {
        expect(
            meetTerms(termOf(opaque()), termOf(object({ a: string }))),
        ).toBeUndefined()
    })

    /** `opaque` is a closed form at the self-identifying kinds, so those answer the base. */
    it('answers the base where opaque is the wider closed form', () => {
        expect(meetTerms(termOf(opaque()), termOf(string))).toEqual(
            termOf(string),
        )
        expect(meetTerms(termOf(opaque()), termOf(boolean))).toEqual(
            termOf(boolean),
        )
        expect(meetTerms(termOf(opaque()), termOf(binary))).toEqual(
            termOf(binary),
        )
    })
})

describe('two object bodies meet over the names both declare', () => {
    it('intersects the declared names and unions the required ones', () => {
        const met = meetTerms(
            termOf(object({ a: string, b: optional(boolean) })),
            termOf(object({ a: string('A'), c: optional(number) })),
        )
        expect(met).toEqual({
            kind: 'object',
            body: {
                fields: { a: { mark: 'req', t: termOf(string('A')) } },
                rest: 'refuse',
            },
        })
    })

    /**
     * A required name the other factor does not declare makes the object the bottom: the name must
     * be present and the other factor refuses a value carrying it.
     */
    it('is the bottom where one factor requires a name the other refuses', () => {
        expect(
            meetTerms(
                termOf(object({ a: string })),
                termOf(object({ b: string })),
            ),
        ).toEqual(bottom)
    })

    /**
     * Under `drop` the read side skips an undeclared name rather than refusing it, so the declared
     * set bounds the read from below and the write from above. The two halves agree only where the
     * `drop` factor's declared set contains the other's.
     */
    it('meets strict objects with incompatible required keys at the bottom', () => {
        expect(
            meetTerms(
                termOf(object({ a: string })),
                termOf(object({ a: string, b: boolean })),
            ),
        ).toEqual(bottom)
    })

    /**
     * `optional` and `withLegacyRead` agree on presence and part on what they read at an absent name:
     * one reads a map without it, the other a map carrying the stand-in.
     */
    it('refuses an optional field against a required slot with a stand-in', () => {
        expect(
            meetTerms(
                termOf(object({ a: optional(string) })),
                termOf(
                    object({
                        a: withLegacyRead({
                            current: string,
                            whenMissing: 'x',
                        }),
                    }),
                ),
            ),
        ).toBeUndefined()
    })

    /** Two stand-ins the model has no equality for. `docs/defects.md` carries the pair. */
    it('refuses two required slots with stand-ins at one name', () => {
        expect(
            meetTerms(
                termOf(
                    object({
                        a: withLegacyRead({
                            current: string,
                            whenMissing: 'x',
                        }),
                    }),
                ),
                termOf(
                    object({
                        a: withLegacyRead({
                            current: string,
                            whenMissing: 'x',
                        }),
                    }),
                ),
            ),
        ).toBeUndefined()
    })

    /** `req` against `withLegacyRead` is `req`, and the stand-in goes: a read never finds the name absent. */
    it('takes the stronger mark and drops a stand-in req makes unreachable', () => {
        expect(
            meetTerms(
                termOf(object({ a: string })),
                termOf(
                    object({
                        a: withLegacyRead({
                            current: string,
                            whenMissing: 'x',
                        }),
                    }),
                ),
            ),
        ).toEqual({
            kind: 'object',
            body: {
                fields: { a: { mark: 'req', t: termOf(string) } },
                rest: 'refuse',
            },
        })
    })

    /**
     * **A record against a body refuses, in both orders.** The model's `record` is an object whose
     * open block holds every name, and `objObj` refuses a pair unless both open blocks are absent.
     * A row the model does not state is a rule the host would be inventing. The pair below is
     * empty, and the host still answers `undefined`, because no model row certifies the bottom.
     */
    it('refuses a record against an object or a record, because the model meets no open block', () => {
        const open = termOf(object({ a: string }, [string, optional(string)]))
        const closed = termOf(object({ a: string }))
        const map = termOf(record(string))
        const sets = termOf(record(string.set('a', 'b')))
        for (const [x, y] of [
            [open, map],
            [closed, map],
            [map, sets],
            [open, sets],
        ] as const) {
            expect(meetTerms(x, y)).toBeUndefined()
            expect(meetTerms(y, x)).toBeUndefined()
        }
    })
})

describe('a union distributes and the survivors carry the certificate', () => {
    it('meets each option and drops the bottoms', () => {
        const met = meetTerms(termOf(union([string, boolean])), termOf(string))
        expect(met).toEqual(termOf(string))
    })

    /**
     * The meet is the lattice's meet and an uncertified union is not in the lattice, so the pair
     * has no meet to state. A `drop` object option is what fails the certificate.
     */
    it('refuses where the option list does not certify', () => {
        const uncertified: Term = {
            kind: 'union',
            options: [
                { kind: 'object', body: { fields: {}, rest: 'drop' } },
                termOf(string),
            ],
        }
        expect(meetTerms(uncertified, termOf(string))).toBeUndefined()
    })
})

/**
 * The pairs `Calculus.Meet` pins as worked examples, answered here.
 *
 * Each one is an `example` in `Meet.lean` with the model's answer written out. They are the
 * differential this side of the bridge can run without emitting a term: the model states the
 * answer, and this asserts the port gives the same one.
 */
describe('two list shapes meet by their lengths', () => {
    const listOf = (
        pre: readonly Term[],
        spread: Term | undefined,
        suf: readonly Term[],
    ): Term =>
        spread === undefined
            ? { kind: 'list', pre, suf }
            : { kind: 'list', pre, spread, suf }

    /**
     * **A fixed arity flattens to one prefix of that length.** The side without a spread fixes the
     * arity, so the answer states that arity and nothing else: keeping the longer prefix and the
     * longer suffix is wrong there, because the two overhangs collide and there is no spread left
     * to meet them against.
     */
    it('flattens to the fixed arity where one side has no spread', () => {
        expect(
            meetTerms(
                listOf([termOf(string)], termOf(string), []),
                listOf(
                    [termOf(string('a')), termOf(string('b'))],
                    undefined,
                    [],
                ),
            ),
        ).toEqual(
            listOf([termOf(string('a')), termOf(string('b'))], undefined, []),
        )
    })

    /**
     * **A length one side refuses is the empty intersection, not a refusal to answer.** The shorter
     * fixed arity is below the other side's declared positions, so the two share no value and the
     * meet is the bottom.
     */
    it('answers the bottom where the fixed arity is out of the other side reach', () => {
        expect(
            meetTerms(
                listOf([termOf(string), termOf(string)], termOf(string), []),
                listOf([termOf(string)], undefined, []),
            ),
        ).toEqual(bottom)
    })

    /**
     * **Two spreading shapes answer where one dominates the other in both coordinates.** This is
     * the cell the tuple rows used to decline: unequal declared arity with a tail on each side. The
     * answer is the row at `max p1 p2 + max s1 s2`, which is the exact intersection exactly there.
     */
    it('answers unequal arities where each side spreads and one dominates', () => {
        expect(
            meetTerms(
                listOf([termOf(string)], termOf(string), []),
                listOf(
                    [termOf(string('a')), termOf(string('b'))],
                    termOf(string('c')),
                    [],
                ),
            ),
        ).toEqual(
            listOf(
                [termOf(string('a')), termOf(string('b'))],
                termOf(string('c')),
                [],
            ),
        )
    })

    /**
     * **Where neither side dominates, no single list states the intersection, so the meet refuses.**
     * One side declares more positions at the front and the other more at the back, so the
     * intersection begins at `max (p1+s1) (p2+s2)` while any list the answer could spell begins at
     * `max p1 p2 + max s1 s2`. The window between the two is a set of lengths that needs two shapes,
     * and a refusal is the honest answer rather than the wider list.
     */
    it('refuses where neither side dominates the other', () => {
        expect(
            meetTerms(
                listOf([termOf(string), termOf(string)], termOf(string), [
                    termOf(string),
                ]),
                listOf([termOf(string)], termOf(string), [
                    termOf(string),
                    termOf(string),
                ]),
            ),
        ).toBeUndefined()
    })

    /** Equal arity with no spread on either side meets position for position. */
    it('meets equal arities position for position', () => {
        expect(
            meetTerms(
                listOf([termOf(string), termOf(boolean)], undefined, []),
                listOf([termOf(string('a')), termOf(boolean)], undefined, []),
            ),
        ).toEqual(listOf([termOf(string('a')), termOf(boolean)], undefined, []))
    })

    /** Unequal arity with no spread on either side shares no value at all. */
    it('answers the bottom for unequal arities with no spread', () => {
        expect(
            meetTerms(
                listOf([termOf(string)], undefined, []),
                listOf([termOf(string), termOf(string)], undefined, []),
            ),
        ).toEqual(bottom)
    })

    /**
     * **A declared position at the bottom empties the list, and a spread at the bottom does not.**
     * `Term.listOf` is the normalisation, and the difference is what a value of exactly the declared
     * length does: it fills every declared position and omits every spread position.
     */
    it('empties the list where a declared position meets the bottom', () => {
        expect(
            meetTerms(
                listOf([termOf(string)], undefined, []),
                listOf([termOf(boolean)], undefined, []),
            ),
        ).toEqual(bottom)
    })
})

describe('the worked pairs the model pins', () => {
    const body = (
        fields: Record<string, Field>,
        rest: Body['rest'] = 'refuse',
    ): Term => ({
        kind: 'object',
        body: { fields, rest },
    })

    /**
     * `array(string) ∧ list(string('a'))` — a spread against a fixed arity flattens to that
     * arity, which is `listMeetRow`'s second branch.
     */
    it('meets a spread against a fixed arity by flattening to that arity', () => {
        expect(
            meetTerms(
                { kind: 'list', pre: [], spread: termOf(string), suf: [] },
                { kind: 'list', pre: [termOf(string('a'))], suf: [] },
            ),
        ).toEqual({ kind: 'list', pre: [termOf(string('a'))], suf: [] })
    })

    /** A refinement carries the cell, and so does a container: a refusal survives the map. */
    it('carries a refusal out through a refinement and a container', () => {
        expect(
            meetTerms(
                {
                    kind: 'refine',
                    inner: termOf(string),
                    q: {
                        kind: 'members',
                        literal: {
                            kind: 'alternatives',
                            base: 'string',
                            ls: ['1'],
                        },
                    },
                },
                termOf(decimal),
            ),
        ).toBeUndefined()
        expect(
            meetTerms(
                { kind: 'list', pre: [], spread: termOf(string), suf: [] },
                { kind: 'list', pre: [], spread: termOf(decimal), suf: [] },
            ),
        ).toBeUndefined()
    })

    /** `opaque` holds the null point, so no option of the union is dropped. */
    it('keeps every option where opaque holds each one', () => {
        const options = [termOf(string), termOf(nullValue)]
        expect(meetTerms({ kind: 'union', options }, termOf(opaque()))).toEqual(
            {
                kind: 'union',
                options,
            },
        )
    })

    /** …and against the null term alone the string cell is the bottom, so one option survives. */
    it('answers the one survivor where the other option is the bottom', () => {
        expect(
            meetTerms(
                {
                    kind: 'union',
                    options: [termOf(string), termOf(nullValue)],
                },
                termOf(nullValue),
            ),
        ).toEqual(termOf(nullValue))
    })

    /**
     * An unshared `withLegacyRead` name refuses, where an unshared `req` name is the bottom. The write
     * side must write the name and the partner refuses it, so nothing is written; the read side
     * needs no name at all and both factors read the map that omits it.
     */
    it('parts an unshared withLegacyRead name from an unshared required one', () => {
        expect(
            meetTerms(
                body(
                    { x: { mark: 'fallback', t: termOf(string), v: 'd' } },
                    'refuse',
                ),
                body({}),
            ),
        ).toBeUndefined()
        expect(
            meetTerms(
                body({ x: { mark: 'req', t: termOf(string) } }),
                body({}),
            ),
        ).toEqual(bottom)
    })

    /**
     * Two `drop` bodies declaring one name each: on the read side each skips the name it does not
     * declare, and the intersection, declaring nothing, reads every map. No object states both
     * halves.
     */
    it('keeps the empty strict object where optional keys do not overlap', () => {
        expect(
            meetTerms(
                body({ x: { mark: 'optional', t: termOf(string) } }),
                body({ y: { mark: 'optional', t: termOf(string) } }),
            ),
        ).toEqual(body({}))
        // The empty strict body admits the same map as the optional-key body.
        expect(
            meetTerms(
                body({}),
                body({ y: { mark: 'optional', t: termOf(string) } }),
            ),
        ).toEqual(body({}))
    })

    /**
     * Two `refuse` factors keep the intersection, and an empty intersection at `optional` is the
     * object declaring nothing rather than the bottom: a value satisfies it by carrying no name.
     */
    it('keeps the empty intersection as an object and not as the bottom', () => {
        expect(
            meetTerms(
                body({ x: { mark: 'optional', t: termOf(string) } }),
                body({ y: { mark: 'optional', t: termOf(string) } }),
            ),
        ).toEqual(body({}))
    })
})
