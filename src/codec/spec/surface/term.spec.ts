/**
 * The five functions of a term, against the rules they are ported from.
 *
 * Each test names the rule of §3, §5 or §6 that the answer serves, not the answer. The terms are
 * built as data rather than through the constructors on purpose: the point of `term.ts` is that the
 * model's language is expressible directly, so a test that could only reach a term through a codec
 * would be testing the conversion twice and the language never.
 */

import { describe, expect, it } from 'vitest'
import { DynamoNumber } from '../../attribute'
import type { AnyCodec } from '../../codec'
import { decimal, opaque, refine, string } from '../../codec'
import { orThrow } from '../../result'
import type { Term } from '../../term'
import { identifies, member, occA, occV, specOf, tagsOf } from '../../term'

const erase = (codec: unknown): AnyCodec => codec as AnyCodec

const str: Term = { kind: 'string' }
const bool: Term = { kind: 'boolean' }

describe('the member a term stores', () => {
    /**
     * §5 `(union)` concludes `μ` where every option agrees and `⊤` otherwise. `⊤` is the honest
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
                options: [{ kind: 'number' }, { kind: 'set', base: 'number' }],
            }),
        ).toBe(undefined)
        // one option is the model's `union(c) ≡ c` at the index
        expect(member({ kind: 'union', options: [str] })).toBe('S')
    })

    /**
     * §3 gives two terms a `⊤` index and gives each a different reason: `lazy` could be asked but
     * answering forces the thunk, and `opaque` writes whatever the value turns out to be. A term
     * with no member is one only (MP) constrains. A union of several members answers nothing for a
     * third reason, which is `unanimous` and is asked in its own test.
     */
    it('the two terms whose member the term does not determine answer nothing', () => {
        expect(member({ kind: 'lazy', get: () => str })).toBe(undefined)
        expect(member({ kind: 'opaq' })).toBe(undefined)
    })

    /**
     * §6's `μ(w(c)) = μ(c)` for the wrappers. This is what keeps a key's attribute type stable
     * under a refactor: putting a `refine` or a `withLegacyRead` around a sort key must not change what the
     * index is built on.
     */
    it('a wrapper stores what it wraps, so a key survives being wrapped', () => {
        const dec: Term = { kind: 'number' }
        expect(
            member({
                kind: 'refine',
                inner: dec,
                q: { kind: 'closure', q: { is: () => true, what: 'any' } },
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
     * §3 `(set)`: a set's member is its base's, and the two numeric bases store the same one.
     * That collision is why the base is an index rather than something a reader recovers.
     */
    it('a set stores its base member, and the two numeric bases store the same one', () => {
        expect(member({ kind: 'set', base: 'string' })).toBe('SS')
        expect(member({ kind: 'set', base: 'binary' })).toBe('BS')
    })
})

describe('the occupancies a declaration is separated by', () => {
    /**
     * **A thunk carries a term, so both projections read through it.** `Meet.lean` heads the
     * section "`lazy` is transparent, and it constrains nothing", and the model reads through on
     * both: `occV (.lazy t) = occV t` and `occA (.lazy t) = occA t`. Only the member is lost,
     * because `μSyn (.lazy t)` is `none`.
     *
     * **This answered `⊤` on both sides until it was measured, and `⊤` was the unsound
     * direction rather than the safe one.** The claim was that an over-approximation costs a
     * certificate and never buys a wrong one. It is backwards here: the guard refuses a union
     * when two occupancies *meet*, so an unknown occupancy makes it decline to refuse.
     * `union([lazy(string), string])` was accepted at the declaration, and `checkUniqueAdmission`
     * then reported two options admitting one value — the migration from declaration time to
     * write time that the calculus exists to stop. `lazy` was the only term answering unknown on
     * both projections, which is why it was the only hole.
     *
     * The other half of the old reason was that reading through throws on the recursive entity
     * the thunk exists to allow. It does not: forcing at the declaration is what `object()`
     * already does, and `codec.recursive.spec.ts` declares such an entity and still passes.
     */
    it('a lazy answers what its term answers, and the member is what it loses', () => {
        const recursive: Term = { kind: 'lazy', get: () => str }
        expect(occV(recursive)).toEqual(occV(str))
        expect(occA(recursive)).toEqual(occA(str))
        expect(member(recursive)).toBe(undefined)
    })

    /**
     * §5: `held` and `withLegacyRead` swap sides, and the swap is the whole content of the two families
     * being asked separately. `held` writes where its held side does, because the held side
     * restricts every value `f` receives, while its `g` only post-processes a read.
     * `withLegacyRead`'s `r` widens exactly the reading and adds no way to write.
     */
    it('an adapter writes where its held side does and reads where its inner term does', () => {
        const at: Term = {
            kind: 'held',
            inner: { kind: 'number' },
            outer: { kind: 'string' },
            f: () => '',
            g: () => 0,
        }
        expect(occV(at)).toEqual(['string'])
        expect(occA(at)).toEqual(['N'])
        // a foreign held side is the top, so the adapter writes every slot
        expect(occV({ ...at, outer: { kind: 'opaq' } })).toEqual(
            occV({ kind: 'opaq' }),
        )
    })

    it('a read widening is the mirror: its inner term on the write side, opaque on the read', () => {
        const older: Term = {
            kind: 'legacy',
            inner: { kind: 'number' },
            r: () => undefined,
        }
        expect(occV(older)).toEqual(['number'])
        expect(occA(older)).toBe(undefined)
    })

    /**
     * §3 `(opaque)` is **total**: it holds a number as a `DynamoNumber`, so it writes every slot
     * and reads every member. That is the model's `occTop` at the exact `opaq`.
     *
     * **The closed form, and `undefined` would be the wrong answer.** §5 separates the two things
     * a `⊤` covers: *unknown*, which is `held`, `custom` and a host `lazy`, and *everything*,
     * which is what `opaque` is by design. An `opaque` answering `undefined` would claim its
     * occupancy cannot be read, about the one term whose occupancy is completely known, and the
     * declaration guard would decline to compare it.
     *
     * **The `'refuse'` policy declares every slot but `number`**, so its write side is as before
     * it was a `held`. Its read side is the canonical term's, `N` included: a wider occupancy is
     * sound, and it refuses the unions a `Pred` complement would separate.
     */
    it('the total opaque answers every slot and every member, never `⊤`', () => {
        expect(occV({ kind: 'opaq' })).toContain('number')
        expect(occV({ kind: 'opaq' })).toContain('numSet')
        expect(occV({ kind: 'opaq' })).toContain('string')
        expect(occA({ kind: 'opaq' })).toContain('N')
        expect(occA({ kind: 'opaq' })).toContain('NS')
        expect(occV({ kind: 'opaq' })).not.toBe(undefined)
        expect(occV(erase(opaque('refuse')).def)).not.toContain('number')
        expect(occV(erase(opaque('refuse')).def)).toContain('string')
        expect(occA(erase(opaque('refuse')).def)).toContain('N')
        expect(occV(erase(opaque('lossy')).def)).toContain('number')
    })

    /**
     * A null point is the null term joined by a union, which is what {@link nullable} builds, so
     * both sides gain it through the union's own row rather than through a wrapper of their own.
     */
    it('a union carrying the null term holds the null point on both sides of the pair', () => {
        const maybe: Term = { kind: 'union', options: [str, { kind: 'null' }] }
        expect(occV(maybe)).toEqual(['string', 'null'])
        expect(occA(maybe)).toEqual(['S', 'NULL'])
    })

    /**
     * §5 asks the two families separately and never reconciles them, and it needs a pair that
     * fails on one side only to be worth doing.
     *
     * **The set bases no longer provide one.** `set(string)` against `set(decimal)` wrote one
     * constructor and stored two members, and `set(number)` against `set(decimal)` was the mirror;
     * `decimal` is an adapter over `number` now, so every set base is disjoint from every other on
     * both sides and the two questions agree on all of them.
     *
     * **An adapter provides one, and it is the construct the carriers are built from.** `held`
     * has distinct rows: it reads where its inner term reads, and writes where its held side
     * writes. A foreign held side is the top, because this library cannot read a foreign schema.
     * So two adapters over disjoint bases with foreign held sides separate on the stored side and
     * not on the written one.
     */
    it('an adapter separates on one side only, which is why both are asked', () => {
        const heldString: Term = {
            kind: 'held',
            inner: { kind: 'string' },
            outer: { kind: 'opaq' },
            f: () => '',
            g: () => '',
        }
        const heldNumber: Term = {
            kind: 'held',
            inner: { kind: 'number' },
            outer: { kind: 'opaq' },
            f: () => '',
            g: () => '',
        }
        // stored apart, because the read side reads through to the base
        expect(occA(heldString)).toEqual(['S'])
        expect(occA(heldNumber)).toEqual(['N'])
        // and not written apart, because a foreign held side is the top on the write side
        expect(occV(heldString)).toEqual(occV({ kind: 'opaq' }))
        expect(occV(heldNumber)).toEqual(occV({ kind: 'opaq' }))
    })

    it('and the set bases agree on both sides, so none of them is that pair', () => {
        for (const base of ['string', 'number', 'binary'] as const) {
            const one: Term = { kind: 'set', base }
            for (const other of ['string', 'number', 'binary'] as const) {
                if (base === other) continue
                const two: Term = { kind: 'set', base: other }
                expect(occV(one)).not.toEqual(occV(two))
                expect(occA(one)).not.toEqual(occA(two))
            }
        }
    })
})

describe("an object option's name spec", () => {
    /**
     * §5: a union admits an object option when every present name is declared and every required
     * name is present, so an `opt` binding **widens** admission. Two objects declaring only
     * optional names both admit the empty map however disjoint their names, which is the ambiguity
     * the name test cannot see — and it can only be stated because the spec records the two facts
     * separately.
     */
    it('an optional name is declared and not required, which is what widens admission', () => {
        const body: Term = {
            kind: 'object',
            body: {
                fields: {
                    id: { mark: 'req', t: str },
                    note: { mark: 'optional', t: str },
                    kind: { mark: 'fallback', t: str, v: 'x' },
                },
            },
        }
        // `withLegacyRead` concludes `req` (§4): the absence is in the row, never in the value
        expect(specOf(body)).toEqual({ id: true, note: false, kind: true })
    })

    /** Only an object is chosen by names; everything else is chosen by being attempted. */
    it('nothing but an object has a name spec', () => {
        expect(specOf(str)).toBe(undefined)
    })
})

describe('the tags a variant answers to', () => {
    const variant = (
        field: Term extends never ? never : Parameters<typeof tagsOf>[1],
    ) => tagsOf('kind', field)

    /** §5 `(dunion)`: the tag is read off the variant's own required string literal. */
    it('a required string literal at the discriminator names the tags', () => {
        expect(
            variant({
                kind: 'object',
                body: {
                    fields: {
                        kind: {
                            mark: 'req',
                            t: { kind: 'literal', base: 'string', v: 'A' },
                        },
                    },
                },
            }),
        ).toEqual(['A'])
    })

    /**
     * A `withLegacyRead` discriminator would fill an absent tag with a value no tag set vouched for, and
     * (C) would then re-encode a variant no tag selects; an `optional` one would let the tag be
     * absent altogether. Both answer no tag, which is what makes the arity premise reachable.
     */
    it('a discriminator that may be absent or stood in for names no tag', () => {
        const withMark = (mark: 'optional' | 'fallback'): Term => ({
            kind: 'object',
            body: {
                fields: {
                    kind:
                        mark === 'optional'
                            ? {
                                  mark,
                                  t: {
                                      kind: 'literal',
                                      base: 'string',
                                      v: 'A',
                                  },
                              }
                            : {
                                  mark,
                                  t: {
                                      kind: 'literal',
                                      base: 'string',
                                      v: 'A',
                                  },
                                  v: 'A',
                              },
                },
            },
        })
        expect(variant(withMark('optional'))).toEqual([])
        expect(variant(withMark('fallback'))).toEqual([])
    })

    /** A tag is a stored string, so a literal at any other base names none. */
    it('a discriminator that is not a string literal names no tag', () => {
        expect(
            variant({
                kind: 'object',
                body: {
                    fields: { kind: { mark: 'req', t: bool } },
                },
            }),
        ).toEqual([])
        expect(
            variant({
                kind: 'object',
                body: {
                    fields: {
                        kind: {
                            mark: 'req',
                            t: { kind: 'literal', base: 'boolean', v: true },
                        },
                    },
                },
            }),
        ).toEqual([])
    })

    it('a term that is not an object names no tag', () => {
        expect(variant(str)).toEqual([])
    })
})

describe('the term `.set()` writes', () => {
    /**
     * §3 `(set)` is indexed by a base, so a set over a restricted element is spelled as a
     * restriction of the **set** — which is not a loss, and the model proves it is not:
     * `setCodec_restrict` and `setCodec_restrict_p` say the set of a restriction and the
     * restriction of a set are one pair, on `e` and on `p`. `each` is `liftQ` at the term level.
     */
    it('a set over a restricted element is a restriction of the set, not a loss', () => {
        const positive = refine(
            decimal,
            (value: string): value is string => !value.startsWith('-'),
            { describe: 'non-negative' },
        )
        const term = erase(positive.set()).def
        expect(term.kind).toBe('refine')
        // `decimal` is an adapter over the one numeric base, so the set is built at that base and
        // the conversion is mapped over it. The restriction stays outside, because the predicate
        // tests the text the caller holds and not the numeral the table does
        const held = (term as { inner: Term }).inner
        expect(held.kind).toBe('held')
        expect((held as { inner: Term }).inner).toEqual({
            kind: 'set',
            base: 'number',
        })
        expect((term as { q: { kind: string } }).q.kind).toBe('each')
        // the member is the set's and reaches no element, which is what `Term.set` being indexed
        // by a base buys: `refine` preserves the member (§6)
        expect(member(term)).toBe('NS')
    })

    /**
     * …and a set over a *literal* element carries the alternatives as data, which is what makes
     * `identifies` able to read them. The model's spelling is `liftQ (inL k ls)`, where `ls` is a
     * `NEFinset` and not a function — a closure decides nothing a declaration can see.
     */
    it('a set over a literal carries the alternatives, so the declaration can read them', () => {
        const term = erase(string.set('a', 'b')).def
        expect(term).toEqual({
            kind: 'refine',
            inner: { kind: 'set', base: 'string' },
            q: {
                kind: 'each',
                of: {
                    kind: 'members',
                    literal: {
                        kind: 'alternatives',
                        base: 'string',
                        ls: ['a', 'b'],
                    },
                },
            },
        })
        expect(identifies(term)).toBe(true)
        expect(member(term)).toBe('SS')
    })

    /** …and a bare base does have one, which is the whole of what `SetBase` indexes. */
    it('a set over a bare base is the base, and nothing about the element survives', () => {
        expect(erase(string.set()).def).toEqual({
            kind: 'set',
            base: 'string',
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

describe('what a term decides about its own values', () => {
    /**
     * **Every part of a list decides, the spread included**, because a value longer than the
     * declared positions is decided *by the spread*. §5's fourth discharger row is about a term
     * deciding which values are its own, and a spread whose admission is not data decides nothing a
     * declaration can see — the same reason `held` is left out.
     *
     * This is one rule where there used to be two: the `array` row read its element and the `tuple`
     * row read the declared positions and left the tail alone, so a tail at a base certified a union
     * it had no warrant for.
     */
    it('a list decides only where its prefix, spread and suffix all decide', () => {
        const alternatives = erase(string('a')).def
        expect(identifies({ kind: 'list', pre: [alternatives], suf: [] })).toBe(
            true,
        )
        expect(
            identifies({
                kind: 'list',
                pre: [alternatives],
                spread: alternatives,
                suf: [alternatives],
            }),
        ).toBe(true)
        // the spread is a base, which admits values it cannot tell from another option's
        expect(
            identifies({
                kind: 'list',
                pre: [alternatives],
                spread: str,
                suf: [],
            }),
        ).toBe(false)
        // and so is a suffix position
        expect(
            identifies({
                kind: 'list',
                pre: [alternatives],
                spread: alternatives,
                suf: [str],
            }),
        ).toBe(false)
    })
})
