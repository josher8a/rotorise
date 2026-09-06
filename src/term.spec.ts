/**
 * The five functions of a term, against the rules they are ported from.
 *
 * Each test names the rule of §3, §5 or §6 that the answer serves, not the answer. The terms are
 * built as data rather than through the constructors on purpose: the point of `term.ts` is that the
 * model's language is expressible directly, so a test that could only reach a term through a codec
 * would be testing the conversion twice and the language never.
 */

import { describe, expect, it } from 'vitest'
import type { AnyCodec } from './codec'
import {
    array,
    binary as binaryOf,
    boolean as booleanOf,
    decimal,
    discriminatedUnion,
    held,
    lazy,
    legacy,
    nullable,
    nullValue,
    number as numberOf,
    object,
    opaque,
    record,
    refine,
    string,
    tuple,
    union,
} from './codec'
import type { Term } from './term'
import {
    identifies,
    member,
    occA,
    occV,
    specOf,
    tagsOf,
    termFromDef,
} from './term'

const erase = (codec: unknown): AnyCodec => codec as AnyCodec

const isText = (value: string): value is string => typeof value === 'string'
const tagged = discriminatedUnion('kind', [
    object({ kind: string('a'), x: string }),
    object({ kind: string('b'), y: string }),
] as never)
const heldPair = held(string, {
    encode: (value: readonly string[]) => value.join(','),
    decode: (stored: string) => stored.split(','),
})

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
            member({ kind: 'union', options: [str, { kind: 'decimal' }] }),
        ).toBe(undefined)
        expect(
            member({
                kind: 'union',
                options: [{ kind: 'number' }, { kind: 'decimal' }],
            }),
        ).toBe('N')
        // one option is the model's `union(c) ≡ c` at the index
        expect(member({ kind: 'union', options: [str] })).toBe('S')
    })

    /**
     * §3 gives four terms a `⊤` index and gives each a different reason: `nullable` writes its
     * subterm's member or `NULL` and names neither, `lazy` could be asked but answering forces the
     * thunk, `custom` is a pair of opaque functions with nothing to ask, and `opaque` writes
     * whatever the value turns out to be. A term with no member is one only (MP) constrains.
     */
    it('the four terms whose member the term does not determine answer nothing', () => {
        expect(member({ kind: 'nullable', inner: str })).toBe(undefined)
        expect(member({ kind: 'lazy', get: () => str })).toBe(undefined)
        expect(
            member({
                kind: 'custom',
                ce: () => ({ S: 'x' }) as never,
                cp: () => 'x',
            }),
        ).toBe(undefined)
        expect(member({ kind: 'opaq', lossy: true })).toBe(undefined)
    })

    /**
     * §6's `μ(w(c)) = μ(c)` for the wrappers. This is what keeps a key's attribute type stable
     * under a refactor: putting a `refine` or a `legacy` around a sort key must not change what the
     * index is built on.
     */
    it('a wrapper stores what it wraps, so a key survives being wrapped', () => {
        const dec: Term = { kind: 'decimal' }
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
            member({ kind: 'held', inner: dec, f: () => '1', g: () => 1 }),
        ).toBe('N')
    })

    /**
     * §3 `(set)`: a set's member is its base's, and the two numeric bases store the same one.
     * That collision is why the base is an index rather than something a reader recovers.
     */
    it('a set stores its base member, and the two numeric bases store the same one', () => {
        expect(member({ kind: 'set', base: 'string' })).toBe('SS')
        expect(member({ kind: 'set', base: 'binary' })).toBe('BS')
        expect(member({ kind: 'set', base: 'number' })).toBe(
            member({ kind: 'set', base: 'decimal' }),
        )
    })
})

describe('the occupancies a declaration is separated by', () => {
    /**
     * The one row where this language is wider than the model's, and the reason is a
     * declaration-time one: a host `lazy` holds a closure over a binding that may not exist yet,
     * so reading through it would force a reference to a constant still being defined. `⊤` is the
     * sound direction — an over-approximation costs a certificate and never buys a wrong one — and
     * the alternative throws on the recursive entity the thunk exists to allow.
     */
    it('a lazy is not forced to answer, so a recursive entity can still be declared', () => {
        let forced = 0
        const recursive: Term = {
            kind: 'lazy',
            get: () => {
                forced++
                return str
            },
        }
        expect(occV(recursive)).toBe(undefined)
        expect(occA(recursive)).toBe(undefined)
        expect(member(recursive)).toBe(undefined)
        expect(forced).toBe(0)
    })

    /**
     * §5: `held` and `legacy` swap sides, and the swap is the whole content of the two families
     * being asked separately. `held`'s `f` runs *before* the subterm and can move a value into any
     * constructor, while its `g` only post-processes a read. `legacy`'s `r` widens exactly the
     * reading and adds no way to write.
     */
    it('an adapter is opaque on the write side and its inner term on the read side', () => {
        const at: Term = {
            kind: 'held',
            inner: { kind: 'decimal' },
            f: () => '',
            g: () => 0,
        }
        expect(occV(at)).toBe(undefined)
        expect(occA(at)).toEqual(['N'])
    })

    it('a read widening is the mirror: its inner term on the write side, opaque on the read', () => {
        const older: Term = {
            kind: 'legacy',
            inner: { kind: 'decimal' },
            r: () => undefined,
        }
        expect(occV(older)).toEqual(['string'])
        expect(occA(older)).toBe(undefined)
    })

    /**
     * §3 `(opaque)`: `refuse` is the **absence of the `number` option**, and (MP) is why — a bare
     * `N` cannot say whether it was written as a number, so a codec that guesses changes the stored
     * member on a read-modify-write.
     */
    it('a refusing opaque is every slot but the number one, and every member but N', () => {
        expect(occV({ kind: 'opaq', lossy: true })).toBe(undefined)
        expect(occA({ kind: 'opaq', lossy: true })).toBe(undefined)
        expect(occV({ kind: 'opaq', lossy: false })).not.toContain('number')
        expect(occV({ kind: 'opaq', lossy: false })).toContain('string')
        expect(occA({ kind: 'opaq', lossy: false })).not.toContain('N')
    })

    /** §3 `(nullable)`: the wrapper inserts the null point, so both sides gain it. */
    it('a nullable holds the null point on both sides of the pair', () => {
        expect(occV({ kind: 'nullable', inner: str })).toEqual([
            'null',
            'string',
        ])
        expect(occA({ kind: 'nullable', inner: str })).toEqual(['NULL', 'S'])
    })

    /**
     * §5's two pairs that fail independently, which is why the two families are asked separately
     * and never reconciled. `set(string)` against `set(decimal)` writes one constructor at both and
     * stores two members. `set(number)` against `set(decimal)` is the mirror.
     */
    it('the two set families separate different pairs, and neither separates both', () => {
        const s: Term = { kind: 'set', base: 'string' }
        const d: Term = { kind: 'set', base: 'decimal' }
        const n: Term = { kind: 'set', base: 'number' }
        // written the same, stored differently
        expect(occV(s)).toEqual(occV(d))
        expect(occA(s)).not.toEqual(occA(d))
        // stored the same, written differently
        expect(occA(n)).toEqual(occA(d))
        expect(occV(n)).not.toEqual(occV(d))
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
                rest: 'drop',
            },
        }
        // `fallback` concludes `req` (§4): the absence is in the row, never in the value
        expect(specOf(body)).toEqual({ id: true, note: false, kind: true })
    })

    /** Only an object is chosen by names; everything else is chosen by being attempted. */
    it('nothing but an object has a name spec', () => {
        expect(specOf(str)).toBe(undefined)
        expect(specOf({ kind: 'record', val: str })).toBe(undefined)
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
                            t: { kind: 'literal', base: 'string', ls: ['A'] },
                        },
                    },
                    rest: 'drop',
                },
            }),
        ).toEqual(['A'])
    })

    /**
     * A `fallback` discriminator would fill an absent tag with a value no tag set vouched for, and
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
                                      ls: ['A'],
                                  },
                              }
                            : {
                                  mark,
                                  t: {
                                      kind: 'literal',
                                      base: 'string',
                                      ls: ['A'],
                                  },
                                  v: 'A',
                              },
                },
                rest: 'drop',
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
                    rest: 'drop',
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
                            t: { kind: 'literal', base: 'boolean', ls: [true] },
                        },
                    },
                    rest: 'drop',
                },
            }),
        ).toEqual([])
    })

    it('a term that is not an object names no tag', () => {
        expect(variant(str)).toEqual([])
    })
})

describe('the seam from a definition to its term', () => {
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
        const term = termFromDef(erase(positive.set()).def as never)
        expect(term.kind).toBe('refine')
        expect((term as { inner: Term }).inner).toEqual({
            kind: 'set',
            base: 'decimal',
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
        const term = termFromDef(erase(string.set('a', 'b')).def as never)
        expect(term).toEqual({
            kind: 'refine',
            inner: { kind: 'set', base: 'string' },
            q: {
                kind: 'each',
                of: {
                    kind: 'members',
                    literal: {
                        kind: 'literal',
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
        expect(termFromDef(erase(string.set()).def as never)).toEqual({
            kind: 'set',
            base: 'string',
        })
    })

    /**
     * `Def` carries `base` beside `allowed` with nothing relating them; the term indexes the
     * alternatives by the base. A decimal literal is the pair that shows why: its alternatives are
     * text and it stores `N`, so neither the member nor the JS type of the values recovers the base.
     */
    it("a literal's alternatives are indexed by the base that stores them", () => {
        expect(termFromDef(erase(decimal('1', '2.5')).def as never)).toEqual({
            kind: 'literal',
            base: 'decimal',
            ls: ['1', '2.5'],
        })
        expect(termFromDef(erase(string('A')).def as never)).toEqual({
            kind: 'literal',
            base: 'string',
            ls: ['A'],
        })
    })
})

/**
 * **The progress meter for the pass that makes a codec carry its term.**
 *
 * `termFromDef` converts the definition a constructor writes into the §3 term it denotes. Once a
 * constructor writes the term itself, that conversion is the **identity** on it — so
 * `termFromDef(c.def)` deep-equal to `c.def` is exactly "this constructor has been flipped", one
 * row per constructor, and the checker cannot give that answer because both are the same type
 * today only by accident of shape.
 *
 * Each row records where that constructor stands. The six ground kinds are already identical in
 * both languages and answer `true` without anyone having moved them. The rest answer `false`, and
 * the pass that flips them turns this column all-true.
 *
 * **This table and `termFromDef` are deleted together in the last step of that pass**, the
 * conversion having served as its own test.
 */
describe('a codec carries the term it denotes', () => {
    const flipped = (codec: AnyCodec): boolean => {
        const def = codec.def
        try {
            return JSON.stringify(termFromDef(def)) === JSON.stringify(def)
        } catch {
            return false
        }
    }

    it.each([
        ['string', string, true],
        ['decimal', decimal, true],
        ['number', numberOf, true],
        ['boolean', booleanOf, true],
        ['binary', binaryOf, true],
        ['null', nullValue, true],
        ['literal', string('A'), false],
        ['set', string.set(), false],
        ['array', array(string), false],
        ['tuple', tuple(string), false],
        ['record', record(string), false],
        ['object', object({ a: string }), false],
        ['union', union([string, booleanOf]), false],
        ['dunion', tagged, false],
        // `nullable` is `{ kind, inner }` in both languages already, like the six ground kinds
        ['nullable', nullable(string), true],
        // a thunk on both sides, and the difference is what it *returns*; the comparison
        // cannot see through a function, so this row answers `true` without meaning it and the
        // forced term is covered by the row for whatever the thunk resolves to
        ['lazy', lazy(() => string), true],
        ['opaque', opaque, false],
        ['refine', refine(string, isText), false],
        ['held', heldPair, false],
        ['legacy', legacy({ current: decimal, older: string }), false],
    ] as const)('%s carries its term: %s', (_name, codec, expected) => {
        expect(flipped(erase(codec))).toBe(expected)
    })
})
