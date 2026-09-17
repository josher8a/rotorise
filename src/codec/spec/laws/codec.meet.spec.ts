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
    fallback,
    never,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    string,
    union,
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
            termOf(object({ a: string, b: optional(boolean) }, 'refuse')),
            termOf(object({ a: string('A'), c: optional(number) }, 'refuse')),
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
                termOf(object({ a: string }, 'refuse')),
                termOf(object({ b: string }, 'refuse')),
            ),
        ).toEqual(bottom)
    })

    /**
     * Under `drop` the read side skips an undeclared name rather than refusing it, so the declared
     * set bounds the read from below and the write from above. The two halves agree only where the
     * `drop` factor's declared set contains the other's.
     */
    it('refuses a drop factor that does not contain the other declared set', () => {
        expect(
            meetTerms(
                termOf(object({ a: string }, 'drop')),
                termOf(object({ a: string, b: boolean }, 'refuse')),
            ),
        ).toBeUndefined()
    })

    /**
     * `optional` and `fallback` agree on presence and part on what they read at an absent name:
     * one reads a map without it, the other a map carrying the stand-in.
     */
    it('refuses an optional field against a fallback field', () => {
        expect(
            meetTerms(
                termOf(object({ a: optional(string) }, 'refuse')),
                termOf(object({ a: fallback(string, 'x') }, 'refuse')),
            ),
        ).toBeUndefined()
    })

    /** Two stand-ins the model has no equality for. `docs/defects.md` carries the pair. */
    it('refuses two fallback fields at one name', () => {
        expect(
            meetTerms(
                termOf(object({ a: fallback(string, 'x') }, 'refuse')),
                termOf(object({ a: fallback(string, 'x') }, 'refuse')),
            ),
        ).toBeUndefined()
    })

    /** `req` against `fallback` is `req`, and the stand-in goes: a read never finds the name absent. */
    it('takes the stronger mark and drops a stand-in req makes unreachable', () => {
        expect(
            meetTerms(
                termOf(object({ a: string }, 'refuse')),
                termOf(object({ a: fallback(string, 'x') }, 'refuse')),
            ),
        ).toEqual({
            kind: 'object',
            body: {
                fields: { a: { mark: 'req', t: termOf(string) } },
                rest: 'refuse',
            },
        })
    })

    /** Only a `codec` rest reads an undeclared name the way a record does. */
    it('refuses an object against a record unless the rest is a codec', () => {
        expect(
            meetTerms(
                termOf(object({ a: string }, 'refuse')),
                termOf(record(string)),
            ),
        ).toBeUndefined()
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
describe('the worked pairs the model pins', () => {
    const body = (fields: Record<string, Field>, rest: Body['rest']): Term => ({
        kind: 'object',
        body: { fields, rest },
    })

    /** `array(string) ∧ tuple(string('a'))` — an array against a tuple is the tuple. */
    it('meets an array against a tuple positionwise', () => {
        expect(
            meetTerms(
                { kind: 'array', elem: termOf(string) },
                { kind: 'tuple', elems: [termOf(string('a'))] },
            ),
        ).toEqual({ kind: 'tuple', elems: [termOf(string('a'))] })
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
                { kind: 'array', elem: termOf(string) },
                { kind: 'array', elem: termOf(decimal) },
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
     * An unshared `fallback` name refuses, where an unshared `req` name is the bottom. The write
     * side must write the name and the partner refuses it, so nothing is written; the read side
     * needs no name at all and both factors read the map that omits it.
     */
    it('parts an unshared fallback name from an unshared required one', () => {
        expect(
            meetTerms(
                body(
                    { x: { mark: 'fallback', t: termOf(string), v: 'd' } },
                    'refuse',
                ),
                body({}, 'refuse'),
            ),
        ).toBeUndefined()
        expect(
            meetTerms(
                body({ x: { mark: 'req', t: termOf(string) } }, 'refuse'),
                body({}, 'refuse'),
            ),
        ).toEqual(bottom)
    })

    /**
     * Two `drop` bodies declaring one name each: on the read side each skips the name it does not
     * declare, and the intersection, declaring nothing, reads every map. No object states both
     * halves.
     */
    it('refuses two drop bodies whose declared sets do not contain each other', () => {
        expect(
            meetTerms(
                body({ x: { mark: 'optional', t: termOf(string) } }, 'drop'),
                body({ y: { mark: 'optional', t: termOf(string) } }, 'drop'),
            ),
        ).toBeUndefined()
        // …and the mirror, where the `drop` factor skips `y` and the `refuse` factor reads it
        expect(
            meetTerms(
                body({}, 'drop'),
                body({ y: { mark: 'optional', t: termOf(string) } }, 'refuse'),
            ),
        ).toBeUndefined()
    })

    /**
     * Two `refuse` factors keep the intersection, and an empty intersection at `optional` is the
     * object declaring nothing rather than the bottom: a value satisfies it by carrying no name.
     */
    it('keeps the empty intersection as an object and not as the bottom', () => {
        expect(
            meetTerms(
                body({ x: { mark: 'optional', t: termOf(string) } }, 'refuse'),
                body({ y: { mark: 'optional', t: termOf(string) } }, 'refuse'),
            ),
        ).toEqual(body({}, 'refuse'))
    })
})
