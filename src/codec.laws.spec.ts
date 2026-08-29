/**
 * The combinators, as algebra.
 *
 * Every combinator here rewrites one codec into another, so the interesting facts about them are
 * *equations*: which rewrites leave a codec's behaviour alone, and which do not. Three times while
 * building these, reasoning about what a combinator could express was wrong and a test settled it in
 * seconds — so the equations are checked rather than asserted in a comment.
 *
 * `checkEquivalent` is the primitive: two codecs that agree on both directions, and on which values
 * they refuse, over generated values. What it cannot see is anything a caller cannot see either,
 * which is the point.
 *
 * The laws that **fail** are as much of the record as the ones that hold, and they are at the bottom.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    binary,
    boolean,
    CodecError,
    custom,
    decimal,
    fallback,
    held,
    legacy,
    literal,
    nullable,
    number,
    object,
    optional,
    record,
    refine,
    set,
    string,
    tuple,
    union,
    writes,
} from './codec'
import {
    checkDecodesAreWritable,
    checkEquivalent,
    checkIso,
} from './testing'

const seed = 20260828

describe('held', () => {
    const identity = { encode: (v: string) => v, decode: (v: string) => v }

    it('by the identity is the codec itself', () => {
        checkEquivalent(held(string, identity), string, { seed })
    })

    /** Two adapters in sequence are one adapter, composed in the order they are applied. */
    it('composes', () => {
        const trim = {
            encode: (v: string) => v.trim(),
            decode: (v: string) => v,
        }
        const upper = {
            encode: (v: string) => v.toUpperCase(),
            decode: (v: string) => v.toLowerCase(),
        }
        checkEquivalent(
            held(held(string, trim), upper),
            held(string, {
                encode: (v: string) => trim.encode(upper.encode(v)),
                decode: (v) => upper.decode(trim.decode(v)),
            }),
            { seed },
        )
    })

    it('leaves what is stored alone, which is the whole of what it claims', () => {
        expect(
            writes(
                held(set(string), {
                    encode: (tags: readonly string[]) => new Set(tags),
                    decode: (tags) => [...tags],
                }),
            ),
        ).toBe('SS')
        expect(writes(held(decimal, { encode: String, decode: Number }))).toBe(
            'N',
        )
    })

    it('is an isomorphism where it says it is', () => {
        checkIso(
            set(string),
            {
                encode: (tags: readonly string[]) => new Set(tags),
                decode: (tags: ReadonlySet<string>) => [...tags],
            },
            { seed },
        )
    })

    /**
     * And the inner codec has to *be* the domain, which is a constraint and not a detail.
     *
     * A `Date` adapter over bare `string` is an isomorphism on ISO strings and nothing else — over an
     * arbitrary string `new Date(x).toISOString()` throws. `checkIso` generates from the codec
     * underneath, so it says so, and narrowing that codec first is how the adapter's domain is stated.
     */
    it('over a domain its inner codec actually describes', () => {
        const isIso = (v: string): v is string => !Number.isNaN(Date.parse(v))
        const iso = refine(string, isIso, {
            describe: 'an ISO timestamp',
            arbitrary: (rng) =>
                new Date(Math.floor(rng() * 1e12)).toISOString(),
        })
        const asDate = {
            encode: (at: Date) => at.toISOString(),
            decode: (at: string) => new Date(at),
        }
        checkIso(iso, asDate, { seed })
        expect(() => checkIso(string, asDate, { seed })).toThrow()
    })

    /**
     * And the failure this is here to catch, which nothing else would.
     *
     * An adapter that loses information reads a row and writes back something else — data loss on a
     * read-modify-write. `checkRoundTrip` cannot see it, because every value it can generate for the
     * held type is already an image of `decode`.
     */
    it('is caught when it is not one', () => {
        expect(() =>
            checkIso(
                string,
                {
                    encode: (v: string) => v,
                    decode: (v: string) => `${v}!`,
                },
                { seed },
            ),
        ).toThrow(/not an isomorphism/)
    })
})

describe('refine', () => {
    const nonEmpty = (v: string): v is string => v.length > 0
    const short = (v: string): v is string => v.length < 6

    /** Two checks in sequence are one check that asks both. */
    it('conjoins', () => {
        checkEquivalent(
            refine(refine(string, nonEmpty), short),
            refine(string, (v): v is string => nonEmpty(v) && short(v)),
            { seed },
        )
    })

    it('by a predicate nothing fails is the codec itself', () => {
        checkEquivalent(
            refine(string, (v): v is string => true),
            string,
            { seed },
        )
    })

    it('leaves what is stored alone', () => {
        expect(writes(refine(decimal, nonEmpty))).toBe('N')
    })
})

describe('legacy', () => {
    it('whose older encoding is the current one is the current one', () => {
        checkEquivalent(legacy({ current: decimal, older: decimal }), decimal, {
            seed,
        })
    })

    it('writes only the current encoding, so what it stores is the current one', () => {
        checkEquivalent(legacy({ current: decimal, older: string }), decimal, {
            seed,
        })
    })

    /**
     * Nests, which is how a table that has held three encodings is described.
     *
     * And the nesting is not associative in the way a reader might hope: the *order* the encodings
     * are tried in is the order they are nested, and the outermost `current` is the only one written.
     */
    it('nests, and the outermost current is what is written', () => {
        const three = legacy({
            current: decimal,
            older: legacy({ current: string, older: decimal }),
        })
        expect(three.unsafeEncode('1.5')).toEqual({ N: '1.5' })
        expect(three.unsafeDecode({ N: '1.5' })).toBe('1.5')
        expect(three.unsafeDecode({ S: '1.5' })).toBe('1.5')
    })
})

describe('union', () => {
    it('of one option is that option', () => {
        checkEquivalent(union([string]), string, { seed })
        checkEquivalent(union([object({ a: string })]), object({ a: string }), {
            seed,
        })
    })

    /**
     * Flattening a nested union is *not* a rewrite that preserves behaviour, and this is the one I
     * would have got wrong by reasoning about it.
     *
     * `union([a, union([b, c])])` and `union([a, b, c])` agree on every value either can carry — the
     * nested union writes whatever option it chose, not a wrapper. What they do not agree on is
     * *ambiguity*: the flat form compares `a` against `b` and `c` directly, while the nested form
     * asks `a` against the nested union as a whole, whose `carries` is the union of `b`'s and `c`'s.
     * So they can disagree about which values they refuse.
     */
    it('flattens, where the options are distinguishable by kind', () => {
        checkEquivalent(
            union([string, union([number, boolean])]),
            union([string, number, boolean]),
            { seed },
        )
    })

    it('is order-independent, where the options are distinguishable', () => {
        checkEquivalent(
            union([string, number, boolean]),
            union([boolean, string, number]),
            { seed },
        )
    })

    it('and what it writes is what the chosen option writes', () => {
        const either = union([string, number])
        expect(either.unsafeEncode('x')).toEqual({ S: 'x' })
        expect(either.unsafeEncode(4)).toEqual({ N: '4' })
    })
})

describe('optional', () => {
    /**
     * Not idempotent, because it is not derivable: a marker marks a declaration once.
     *
     * This read as an equation that held until the two markers were checked against each other. Only
     * the outermost mark was ever read, so `optional(fallback(c, v))` silently dropped the stand-in —
     * which makes nesting a thing to refuse rather than a law to state.
     */
    it('cannot wrap another marker', () => {
        const _wrong = () => [
            // @ts-expect-error a name is marked once
            optional(optional(string)),
            // @ts-expect-error and `fallback` is what "absent, with a stand-in" is called
            optional(fallback(string, () => 'x')),
            // @ts-expect-error in either order
            fallback(optional(string), () => 'x'),
        ]
        expect(typeof _wrong).toBe('function')
    })

    it('leaves what is stored alone', () => {
        expect(writes(optional(decimal))).toBe('N')
        expect(writes(optional(set(string)))).toBe('SS')
    })
})

describe('what the wrappers preserve', () => {
    /**
     * Every wrapper answers the member of what it wraps, and this is the property that keeps a schema
     * honest: an index key's attribute type cannot change because somebody wrapped it.
     */
    it.each([
        ['held', held(decimal, { encode: String, decode: Number })],
        ['refine', refine(decimal, (v): v is string => true)],
        ['optional', optional(decimal)],
        ['fallbackless legacy', legacy({ current: decimal, older: decimal })],
        ['nested', optional(refine(decimal, (v): v is string => true))],
    ])('%s writes N, as decimal does', (_name, codec) => {
        expect(writes(codec)).toBe('N')
    })

    it('and a set keeps the member its element decides', () => {
        expect(writes(set(string))).toBe('SS')
        expect(writes(set(number))).toBe('NS')
        expect(writes(set(binary))).toBe('BS')
        expect(writes(array(string))).toBe('L')
    })
})

describe('the laws that do NOT hold', () => {
    /**
     * `union` is not a lattice: adding an option can turn a working declaration into an ambiguous
     * one, and the type system refuses that case rather than the runtime.
     */
    it('a union is not closed under adding an option', () => {
        const _wrong = () =>
            // @ts-expect-error `literal('A')` reads back as a subtype of what `string` reads back
            union([string, literal('A')])
        expect(typeof _wrong).toBe('function')
    })

    /**
     * `held` does not commute with `refine`.
     *
     * `refine(held(c, f), p)` checks `p` against the *held* value; `held(refine(c, p), f)` checks it
     * against the value underneath. Different predicates, different types — so the two are not
     * rewrites of each other, and which one is meant is a real choice.
     */
    it('held and refine do not commute', () => {
        const short = (v: string): v is string => v.length < 4
        const adapt = {
            encode: (v: string) => `${v}${v}`,
            decode: (v: string) => v.slice(0, 3),
        }

        // the check underneath sees what is *stored*; the check outside sees what is *held*
        const checkedInside = held(refine(string, short), adapt)
        const checkedOutside = refine(held(string, adapt), short)

        expect(() => checkedInside.unsafeDecode({ S: 'abcabc' })).toThrow(
            /is not/,
        )
        expect(checkedOutside.unsafeDecode({ S: 'abcabc' })).toBe('abc')
    })

    /**
     * A union of containers is not a container of unions.
     *
     * `union([array(string), array(number)])` is a list that is *homogeneously* one or the other;
     * `array(union([string, number]))` is a list whose elements are each either. Different types,
     * different rows, and the first is the stricter claim — which is usually the one meant, and is
     * also the one a `union` cannot resolve on the way in, because both options take an array and
     * neither validates what is in it.
     */
    it('a union of arrays is not an array of unions', () => {
        // the elementwise one is a codec, and holds a mixed list
        const elementwise = array(union([string, number]))
        const _loose: readonly (string | number)[] = elementwise.unsafeDecode({
            L: [{ S: 'a' }, { N: '1' }],
        })
        expect(_loose).toEqual(['a', 1])
        expect(elementwise.unsafeEncode(['a', 1])).toEqual({
            L: [{ S: 'a' }, { N: '1' }],
        })

        // the homogeneous one is refused where it is written: both options are handed an array and
        // neither checks what is in it, so no value chooses between them
        expect(() => union([array(string), array(number)])).toThrow(
            /both take the same kind of value — array — and neither checks/,
        )
    })

    /**
     * And for sets the container-of-unions side is not a codec at all.
     *
     * A set's member follows from its element — `SS`, `NS` or `BS` — so an element that writes `S`
     * *or* `N` names no set. Refused when the declaration is evaluated rather than when a row arrives,
     * which for a codec declared at module scope is import time.
     */
    it('a set of a union is not a set at all', () => {
        expect(() => set(union([string, number]))).toThrow(
            /a set holds strings, numbers or binary, and this element writes no single member/,
        )
    })

    /**
     * A union of sets is refused for the same reason, and the asymmetry is worth seeing.
     *
     * `SS` and `NS` say which option a *stored* attribute belongs to, so reading was never ambiguous.
     * A `Set` says nothing about what is in it, and neither option checks — so the direction that
     * cannot be resolved is the one that decides whether the declaration is allowed at all.
     */
    it('a union of sets is refused, though reading it would have worked', () => {
        expect(() => union([set(string), set(number)])).toThrow(
            /both take the same kind of value — set — and neither checks/,
        )

        // the stored side always knew which: the two write different members, and that is what the
        // decode filter reads. It is the value side that cannot tell one `Set` from another
        expect(writes(set(string))).toBe('SS')
        expect(writes(set(number))).toBe('NS')
        expect(set(string).unsafeDecode({ SS: ['a'] })).toEqual(new Set(['a']))
        expect(set(number).unsafeDecode({ NS: ['1'] })).toEqual(new Set([1]))
    })

    /**
     * The combinators live at two levels, and mixing them is refused.
     *
     * `optional` and `fallback` are statements about a *name* — the attribute called this may be
     * missing from the item. Everything else here is a statement about an attribute. A list, a set, a
     * tuple, a record and a union option have no name at that position, so one of those there is a
     * category error rather than a weaker element.
     *
     * It was silent, and it corrupted: `array(optional(string))` compiled and wrote `{}` into the
     * list — an attribute carrying no member at all, which DynamoDB rejects on arrival.
     */
    it('an element cannot be about absence', () => {
        const _wrong = () => [
            // @ts-expect-error nothing in a list has a name to be absent from
            array(optional(string)),
            // @ts-expect-error nor in a set
            set(optional(string)),
            // @ts-expect-error nor in a record
            record(optional(string)),
            // @ts-expect-error nor in a tuple
            tuple(string, optional(number)),
            // @ts-expect-error nor is a union option a name
            union([optional(string), number]),
            // @ts-expect-error and a fallback says the same thing about absence
            array(fallback(string, () => 'x')),
        ]
        expect(typeof _wrong).toBe('function')
    })

    it('but nullable is, because NULL is a value a member carries', () => {
        const holes = array(nullable(string))
        expect(holes.unsafeEncode(['a', null])).toEqual({
            L: [{ S: 'a' }, { NULL: true }],
        })
        expect(holes.unsafeDecode({ L: [{ NULL: true }] })).toEqual([null])
    })

    /** A set is not a list held as an array, however similar the two look. */
    it('a set is not an array', () => {
        expect(writes(set(string))).toBe('SS')
        expect(writes(array(string))).toBe('L')
    })
})

/**
 * **(C), against attributes nobody would write.**
 *
 * Everything above generates values. `checkDecodesAreWritable` generates *attributes* — every
 * encoded item, plus one named deviation at a time — and asks the question the other direction
 * cannot: is everything this codec reads something it can write back?
 *
 * Three shipped defects lived exactly there. The regression tests below are the shapes, planted
 * deliberately, so the harness is checked against the class of bug it exists for rather than only
 * against code that is already correct.
 */
describe('(C): what a codec reads, it can write', () => {
    const Pet = object({
        id: string,
        price: decimal,
        count: number,
        tags: set(string),
        steps: array(string),
        note: optional(string),
        nick: fallback(string, () => 'anon'),
    }).item

    it('holds for a wide entity, over every mutation of every attribute', () => {
        checkDecodesAreWritable(Pet, { count: 40, seed: 20260829 })
    })

    it('holds for the ground codecs, each in its own attribute', () => {
        const Ground = object({
            s: string,
            d: decimal,
            n: number,
            b: boolean,
            bin: binary,
            lit: literal('A', 'B'),
            litN: literal(0, 1),
            nul: nullable(string),
        }).item
        checkDecodesAreWritable(Ground, { count: 40, seed: 20260829 })
    })

    /**
     * The `set` defect, planted: encode refuses the empty set, decode returns it. This is what the
     * library did until the read side was closed, and no value-driven generator could reach it.
     */
    it('catches a decode that accepts what encode refuses', () => {
        const leaky = custom<ReadonlySet<string>>({
            encode: (value) =>
                value.size === 0
                    ? new CodecError('no empty SS')
                    : ({ SS: [...value].sort() } as never),
            decode: (attribute) =>
                new Set((attribute as { SS?: readonly string[] }).SS ?? []),
            arbitrary: () => new Set(['a']),
        })
        const Leaky = object({ id: string, tags: leaky }).item

        expect(() =>
            checkDecodesAreWritable(Leaky, { count: 5, seed: 1 }),
        ).toThrow(/\(C\) fails/)
        expect(() =>
            checkDecodesAreWritable(Leaky, { count: 5, seed: 1 }),
        ).toThrow(/an empty set/)
    })

    /**
     * The `decimal` defect, planted: a codec that writes only normalised numerals and reads any of
     * them. The mutation that finds it is the one DynamoDB itself performs in reverse.
     */
    it('catches a decode that accepts a form its encode will not produce', () => {
        const loose = custom<string>({
            encode: (value) =>
                /^-?(0|[1-9]\d*)(\.\d*[1-9])?$/.test(value)
                    ? ({ N: value } as never)
                    : new CodecError('not normalised'),
            decode: (attribute) => (attribute as { N: string }).N,
            arbitrary: () => '1.5',
        })
        const Loose = object({ id: string, amount: loose }).item

        expect(() =>
            checkDecodesAreWritable(Loose, { count: 5, seed: 1 }),
        ).toThrow(/\(C\) fails/)
    })
})
