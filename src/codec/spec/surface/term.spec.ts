/**
 * The functions of a term, against the rules they are ported from.
 *
 * Each test names the rule of the judgement, of choice or of the equations that the answer serves, not the answer. The terms are
 * built as data rather than through the constructors on purpose: the point of `term.ts` is that the
 * model's language is expressible directly, so a test that could only reach a term through a codec
 * would be testing the conversion twice and the language never.
 */

import { describe, expect, it } from 'vitest'
import { DynamoNumber } from '../../attribute'
import type { AnyCodec } from '../../codec'
import { decimal, opaque, refine, string } from '../../codec'
import { assignmentOf } from '../../denote'
import { failed, orThrow } from '../../result'
import { flatOf } from '../../scoped'
import type { Field, RefSlot, Term } from '../../term'
import {
    componentsOf,
    holdsNoValue,
    member,
    occV,
    ownsNullOf,
    unboundRefs,
} from '../../term'

const erase = (codec: unknown): AnyCodec => codec as AnyCodec

const str: Term = { kind: 'string' }
/** A `ref` whose scope binds its name to the term. */
const refTo = (target: Term): Term => ({
    kind: 'ref',
    slot: { name: 'T', bound: { T: target } },
})
const bool: Term = { kind: 'boolean' }

describe('the member a term stores', () => {
    /**
     * The rule `(union)` concludes `μ` where every option agrees and `⊤` otherwise. `⊤` is the honest
     * index for a term that writes two members, and it is what costs the union (W) and its
     * read-side corollary — so the difference between the two answers is a difference in which
     * laws pin the term, not a nicety.
     */
    it('a union stores one member only where every option stores that member', () => {
        expect(
            member({ kind: 'union', options: [str, { kind: 'number' }] }),
        ).toBe(undefined)
        expect(
            member({
                kind: 'union',
                options: [
                    { kind: 'number' },
                    { kind: 'set', elem: { kind: 'number' } },
                ],
            }),
        ).toBe(undefined)
        // one option is the model's `union(c) ≡ c` at the index
        expect(member({ kind: 'union', options: [str] })).toBe('S')
    })

    /**
     * The judgement gives two terms a `⊤` index and gives each a different reason: a `ref` could be asked but
     * answering walks through the `ref`, and `opaque` writes whatever the value turns out to be. A term
     * with no member is one only (MP) constrains. A union of several members answers nothing for a
     * third reason, which is `unanimous` and is asked in its own test.
     */
    it('the two terms whose member the term does not determine answer nothing', () => {
        expect(member(refTo(str))).toBe(undefined)
        expect(member({ kind: 'opaq' })).toBe(undefined)
    })

    /**
     * The equation `μ(w(c)) = μ(c)` for the wrappers. This is what keeps a key's attribute type stable
     * under a refactor: putting a `refine` or a `withLegacyRead` around a sort key must not change what the
     * index is built on.
     */
    it('a wrapper stores what it wraps, so a key survives being wrapped', () => {
        const dec: Term = { kind: 'number' }
        expect(
            member({
                kind: 'refine',
                inner: dec,
                q: { is: () => true, what: 'any' },
            }),
        ).toBe('N')
        expect(member({ kind: 'legacy', inner: dec, r: () => undefined })).toBe(
            'N',
        )
        expect(
            member({
                kind: 'held',
                inner: dec,
                outer: { kind: 'string' },
                f: () => '1',
                g: () => 1,
            }),
        ).toBe('N')
    })

    /**
     * The rule `(set)`: a set's member is `setMember` of its element's member. An element of any other
     * member has no stored set, which is the DynamoDB set obligation, and the index says `⊤`.
     */
    it("a set stores the set member of its element's member, and nothing for any other member", () => {
        expect(member({ kind: 'set', elem: { kind: 'string' } })).toBe('SS')
        expect(member({ kind: 'set', elem: { kind: 'binary' } })).toBe('BS')
        expect(member({ kind: 'set', elem: { kind: 'boolean' } })).toBe(
            undefined,
        )
    })
})

describe('the occupancy of a term', () => {
    /**
     * **A thunk carries a term, so both projections read through it.** The model has no thunk: the
     * emitter prints the term that a thunk returns, so the model reads that term on both
     * projections. Only the member is lost.
     *
     * **This answered `⊤` on both sides until it was measured, and `⊤` was the unsound
     * direction rather than the safe one.** The claim was that an over-approximation costs a
     * certificate and never buys a wrong one. It was backwards here: the guard then refused a
     * union when two occupancies *met*, so an unknown occupancy made it decline to refuse.
     * A union of a thunk of `string` and `string` was accepted at the declaration, and a write
     * then reported two options admitting one value — the migration from declaration time to
     * write time that the calculus exists to stop. `lazy` was the only term answering unknown on
     * both projections, which is why it was the only hole.
     *
     * The other half of the old reason was that reading through throws on the recursive entity
     * the thunk exists to allow. It does not: forcing at the declaration is what `object()`
     * already does, and `codec.recursive.spec.ts` declares such an entity and still passes.
     */
    it('a ref answers what its target answers, and the member is what it loses', () => {
        const recursive = refTo(str)
        expect(occV(recursive)).toEqual(occV(str))
        expect(member(recursive)).toBe(undefined)
    })

    /**
     * `held` writes where its held side does, because the held side restricts every value `f`
     * receives, while its `g` only post-processes a read. `withLegacyRead`'s `r` widens exactly the
     * reading and adds no way to write.
     */
    it('an adapter writes where its held side does', () => {
        const at: Term = {
            kind: 'held',
            inner: { kind: 'number' },
            outer: { kind: 'string' },
            f: () => '',
            g: () => 0,
        }
        expect(occV(at)).toEqual(['string'])
        // a foreign held side is the top, so the adapter writes every slot
        expect(occV({ ...at, outer: { kind: 'opaq' } })).toEqual(
            occV({ kind: 'opaq' }),
        )
    })

    it('a read widening writes where its inner term does', () => {
        const older: Term = {
            kind: 'legacy',
            inner: { kind: 'number' },
            r: () => undefined,
        }
        expect(occV(older)).toEqual(['number'])
    })

    /**
     * The rule `(opaque)` is **total**: it holds a number as a `DynamoNumber`, so it writes every slot
     * and reads every member. That is the model's `occTop` at the exact `opaq`.
     *
     * **The closed form, and `undefined` would be the wrong answer.** Separation tells apart the two things
     * a `⊤` covers: *unknown*, which is `held`, `custom` and a host `lazy`, and *everything*,
     * which is what `opaque` is by design. An `opaque` answering `undefined` would claim its
     * occupancy cannot be read, about the one term whose occupancy is completely known, and the
     * declaration guard would decline to compare it.
     *
     * **The `'refuse'` policy declares every slot but `number`**, so its write side is as before
     * it was a `held`. Its read side is the canonical term's, `N` included: a wider occupancy is
     * sound, and it refuses the unions a `Pred` complement would separate.
     */
    it('the total opaque answers every slot, never `⊤`', () => {
        expect(occV({ kind: 'opaq' })).toContain('number')
        expect(occV({ kind: 'opaq' })).toContain('numSet')
        expect(occV({ kind: 'opaq' })).toContain('string')
        expect(occV({ kind: 'opaq' })).not.toBe(undefined)
        expect(occV(erase(opaque('refuse')).def)).not.toContain('number')
        expect(occV(erase(opaque('refuse')).def)).toContain('string')
        expect(occV(erase(opaque('lossy')).def)).toContain('number')
    })

    /**
     * A null point is the null term joined by a union, which is what {@link nullable} builds, so
     * the occupancy gains it through the union's own row rather than through a wrapper of its own.
     */
    it('a union carrying the null term holds the null point', () => {
        const maybe: Term = { kind: 'union', options: [str, { kind: 'null' }] }
        expect(occV(maybe)).toEqual(['string', 'null'])
    })

    /**
     * `decimal` is an adapter over `number`, so every set base is disjoint from every other.
     */
    it('the set bases are disjoint on the write side', () => {
        for (const base of ['string', 'number', 'binary'] as const) {
            const one: Term = { kind: 'set', elem: { kind: base } }
            for (const other of ['string', 'number', 'binary'] as const) {
                if (base === other) continue
                const two: Term = { kind: 'set', elem: { kind: other } }
                expect(occV(one)).not.toEqual(occV(two))
            }
        }
    })
})

describe('the tag a variant answers to', () => {
    const literal: Term = { kind: 'literal', base: 'string', v: 'A' }
    const variant = (field: Field) =>
        assignmentOf(['kind'], { fields: { kind: field } })

    /** The rule `(dunion)`: the tag is read off the variant's own required literal. */
    it('a required string literal at the discriminator names the tag', () => {
        expect(variant({ mark: 'req', t: literal })).toEqual({ kind: 'A' })
    })

    /**
     * A `withLegacyRead` discriminator would fill an absent tag with a value no tag set vouched for, and
     * (C) would then re-encode a variant no tag selects; an `optional` one would let the tag be
     * absent altogether. Both name no tag, which is what makes the arity premise reachable.
     */
    it('a discriminator that may be absent or stood in for names no tag', () => {
        expect(failed(variant({ mark: 'optional', t: literal }))).toBe(true)
        expect(failed(variant({ mark: 'fallback', t: literal, v: 'A' }))).toBe(
            true,
        )
    })

    /** A tag is a stored string or numeral, so a literal at any other base names none. */
    it('a discriminator that is not a literal at a stored base names no tag', () => {
        expect(failed(variant({ mark: 'req', t: bool }))).toBe(true)
        expect(
            failed(
                variant({
                    mark: 'req',
                    t: { kind: 'literal', base: 'boolean', v: true },
                }),
            ),
        ).toBe(true)
    })
})

describe('the term `.set()` writes', () => {
    /**
     * The rule `(set)` is the finite-powerset lift of an element term, so a restriction rides at the
     * element: the set of `refine(decimal, q)` holds that refinement as its element, and the
     * predicate tests the text the caller holds.
     */
    it('a set over a restricted element holds the restriction at the element', () => {
        const positive = refine(
            decimal,
            (value: string): value is string => !value.startsWith('-'),
            { describe: 'non-negative' },
        )
        const term = erase(positive.set()).def
        expect(term).toEqual({ kind: 'set', elem: positive.def })
        // the element writes `N`, so the set writes `NS`
        expect(member(term)).toBe('NS')
    })

    /**
     * …and a set over a *literal* element carries the alternatives as data at the element, which
     * is what makes the disjointness test able to read them.
     */
    it('a set over a literal carries the alternatives, so the declaration can read them', () => {
        const term = erase(string.set('a', 'b')).def
        expect(term).toEqual({
            kind: 'set',
            elem: {
                kind: 'union',
                options: [
                    { kind: 'literal', base: 'string', v: 'a' },
                    { kind: 'literal', base: 'string', v: 'b' },
                ],
            },
        })
        expect(member(term)).toBe('SS')
    })

    /** …and a set over a bare base holds the base as its element. */
    it('a set over a bare base holds the base as its element', () => {
        expect(erase(string.set()).def).toEqual({
            kind: 'set',
            elem: { kind: 'string' },
        })
    })

    /**
     * The term indexes the value by the base. A decimal literal is the pair that shows why: its
     * value is text and it stores `N`, so neither the member nor the JS type of the value recovers
     * the base.
     */
    it("a literal's value is indexed by the base that stores it", () => {
        expect(erase(string('A')).def).toEqual({
            kind: 'literal',
            base: 'string',
            v: 'A',
        })
        // a decimal literal is that same literal at the numeric base, under the text adapter
        const dec = erase(decimal('1')).def
        expect(dec.kind).toBe('held')
        expect((dec as { inner: Term }).inner).toEqual({
            kind: 'literal',
            base: 'number',
            v: orThrow(DynamoNumber.from('1')),
        })
    })

    /**
     * **Several alternatives are a union of singletons**, which is the rule the model states: a
     * literal carries one value, and a set of them is a certified union whose members are told
     * apart because the values differ. The builder stays a builder because the hand-written union
     * costs the type checker linearly in the alternatives where the call is flat.
     */
    it('builds a union of singleton literals where several values are named', () => {
        const several = erase(decimal('1', '2.5')).def
        expect(several.kind).toBe('held')
        expect((several as { inner: Term }).inner).toEqual({
            kind: 'union',
            options: [
                {
                    kind: 'literal',
                    base: 'number',
                    v: orThrow(DynamoNumber.from('1')),
                },
                {
                    kind: 'literal',
                    base: 'number',
                    v: orThrow(DynamoNumber.from('2.5')),
                },
            ],
        })
    })
})

/**
 * **A reader reads the slot of each `ref` at the call.** A scope binds no slot of a fragment: the
 * scope binds a closed copy. So a read of an open root is not kept. Each test binds the slot by
 * hand after a first call, and the second call answers from the bound term.
 */
describe('a reader during construction reads the term, where a scope binds a name late', () => {
    const open = (): { readonly t: Term; readonly slot: RefSlot } => {
        const slot: RefSlot = { name: 'T' }
        return { t: { kind: 'ref', slot }, slot }
    }

    it('holdsNoValue holds a value at a ref that no scope binds, and holds no value once the name is never', () => {
        const { t, slot } = open()
        expect(holdsNoValue(t)).toBe(false)
        slot.bound = { T: { kind: 'never' } }
        expect(holdsNoValue(t)).toBe(true)
    })

    it('ownsNullOf leaves undetermined a free variable, and reads the point once the name is bound', () => {
        const { t, slot } = open()
        expect(ownsNullOf(t)).toBe(undefined)
        slot.bound = { T: { kind: 'null' } }
        expect(ownsNullOf(t)).toBe(true)
    })

    it('occV lets a free variable write every slot, and reads the slot once the name is bound', () => {
        const { t, slot } = open()
        expect(occV(t).length).toBeGreaterThan(1)
        slot.bound = { T: str }
        expect(occV(t)).toEqual(['string'])
    })

    it('member reads no ref, so a free variable and a bound name both answer nothing', () => {
        const { t, slot } = open()
        expect(member(t)).toBe(undefined)
        slot.bound = { T: str }
        expect(member(t)).toBe(undefined)
    })

    it('unboundRefs finds the slot of a free name, and none once a scope binds it', () => {
        const { t, slot } = open()
        expect([...unboundRefs([t])]).toEqual([slot])
        slot.bound = { T: str }
        expect([...unboundRefs([t])]).toEqual([])
    })

    it('componentsOf finds a cycle only once the name is bound, which is how the scope orders its entries', () => {
        const { t, slot } = open()
        const root: Term = {
            kind: 'object',
            body: { fields: { next: { mark: 'req', t } } },
        }
        expect(componentsOf([root])).toEqual([])
        slot.bound = { T: root }
        expect(componentsOf([root]).length).toBe(1)
    })
})

describe('the flat scope of a root', () => {
    const rootOver = (t: Term): Term => ({
        kind: 'object',
        body: { fields: { x: { mark: 'req', t } } },
    })

    /** The readers that run after a scope closes each read one flat scope of the root. */
    it('is built one time for a closed root, so each reader after the scope closes reads one scope', () => {
        const root = rootOver(str)
        expect(flatOf(root)).toBe(flatOf(root))
    })

    /**
     * An open root holds a `ref` that a scope binds later, and the child that the name reaches is
     * an entry once the name is bound. A scope read kept for the open root gives the root no entry
     * for that child.
     */
    it('is read again for an open root, because a scope that binds a name adds the entries of the name', () => {
        const slot: RefSlot = { name: 'T' }
        const root = rootOver({ kind: 'ref', slot })
        const entries = (t: Term): number => {
            const flat = flatOf(t)
            return flat.kind === 'flat' ? flat.bodies.length : -1
        }
        const before = entries(root)
        slot.bound = { T: str }
        expect(entries(root)).toBeGreaterThan(before)
    })
})
