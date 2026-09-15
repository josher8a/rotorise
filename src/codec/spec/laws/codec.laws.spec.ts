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
import type { AttributeMap } from '../../attribute'
import { memberOf } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    binary,
    boolean,
    CodecError,
    custom,
    decimal,
    discriminatedUnion,
    failed,
    fallback,
    held,
    lazy,
    legacy,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    refine,
    rest,
    string,
    tuple,
    union,
} from '../../codec'
import { accepts } from '../../denote'
import {
    arbitraryOf,
    checkDecodesAreWritable,
    checkEquivalent,
    checkIso,
    checkStable,
    rngFrom,
} from '../../testing'

const seed = 20260828

/**
 * The member a codec actually **writes**, read off the attribute rather than out of the
 * declaration.
 *
 * `member` reads the term and reports what the term says it stores. That is the right answer for
 * the resolver, which has only a declaration to go on, and the wrong assertion for a law — §6's
 * member-preservation row is a claim about `e`, so a test that asks `member` passes on a codec
 * whose term is right and whose `encode` is wrong, and fails a rewrite that keeps every behaviour
 * and reorganises the terms. Where the claim is the law, this is what to ask.
 */
const memberWritten = (codec: AnyCodec, value: unknown): string | undefined =>
    memberOf(codec.encode(value as never) as never)

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
            memberWritten(
                held(string.set(), {
                    encode: (tags: readonly string[]) => new Set(tags),
                    decode: (tags) => [...tags],
                }) as AnyCodec,
                ['a', 'b'],
            ),
        ).toBe('SS')
        expect(
            memberWritten(
                held(decimal, {
                    encode: String,
                    decode: Number,
                }) as AnyCodec,
                1.5,
            ),
        ).toBe('N')
    })

    it('is an isomorphism where it says it is', () => {
        checkIso(
            string.set(),
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
        ).toThrow(CodecError)
    })
})

/**
 * **The five obligations the model carries as premises and this library does not type.**
 *
 * Each is a side condition §3 or §2 asks of a constructor that takes a caller's function or value.
 * Three are decidable from what the caller hands over and are now refused where the declaration is
 * — `fallback`'s stand-in, `legacy`'s `ran(r) ⊆ dom(e)`, and a `rest` out of position. Two are not
 * decidable at all, so what is pinned here is the failure mode, which is the only thing a test can
 * say about an obligation nothing enforces.
 */
describe('the obligations a caller owes', () => {
    /**
     * `held`'s `IsoCancels`, unrefused. An adapter that *normalises* is not an isomorphism, and
     * every read-modify-write on such a row rewrites the value: `'a'` is written `'A'` and read
     * back `'A'`, so the row drifts once and then sticks.
     *
     * `checkIso` is the discharge route and does catch it, which is what makes this a written
     * obligation rather than an unknown one.
     */
    it('held: an adapter that normalises breaks (R), and nothing refuses it', () => {
        const normalising = held(string, {
            encode: (v: string) => v.toUpperCase(),
            decode: (v: string) => v,
        })
        expect(normalising.unsafeEncode('a')).toEqual({ S: 'A' })
        expect(normalising.unsafeDecode({ S: 'A' })).toBe('A')

        // (R) asks for 'a' back, and the pair is lawful-looking at every other test in this file
        expect(
            normalising.unsafeDecode(normalising.unsafeEncode('a')),
        ).not.toBe('a')
        expect(() =>
            checkIso(string, {
                encode: (v: string) => v.toUpperCase(),
                decode: (v: string) => v,
            }),
        ).toThrow(CodecError)
    })

    /**
     * `legacy`'s coherence half, which has **no observable witness** — and that is the finding
     * rather than a gap in the test. The current encoding is tried first and the older one only on
     * its failure, so where both could read an attribute the older one is never consulted. A
     * reader that disagrees outright is invisible.
     */
    it('legacy: a disagreeing older reader is never consulted, so nothing can see it', () => {
        const disagreeing = legacy({
            current: string,
            older: { decode: () => 'DISAGREE' as string },
        })
        expect(disagreeing.unsafeDecode({ S: 'hi' })).toBe('hi')
        // and it is consulted only where the current encoding refuses
        expect(disagreeing.unsafeDecode({ N: '1' })).toBe('DISAGREE')
    })

    /** `legacy`'s first half, now refused at the read that produces the unwritable value. */
    it('legacy: an older reading the current encoding cannot write is refused', () => {
        const migrating = legacy({
            current: string('A'),
            older: { decode: () => 'B' as 'A' },
        })
        expect(() => migrating.unsafeDecode({ N: '1' })).toThrow(CodecError)
        expect(() => migrating.unsafeDecode({ N: '1' })).toThrow(CodecError)
    })

    /** `fallback`'s stand-in, now refused at the declaration. */
    it('fallback: a stand-in the codec cannot write is refused at construction', () => {
        expect(() => fallback(string('A'), 'B' as 'A')).toThrow(CodecError)
        expect(() => fallback(string('A'), 'A' as const)).not.toThrow()
    })

    /** `RestGoesLast`, past the cast that defeats the type. */
    it('tuple: a rest out of position is refused at construction', () => {
        // the whole call is cast, because `RestGoesLast` constrains the parameter list rather
        // than any one element — which is the type doing its job, and the cast is the witness
        const unchecked = tuple as unknown as (
            ...elements: readonly unknown[]
        ) => unknown
        expect(() => unchecked(rest(string), number)).toThrow(CodecError)
        expect(() => tuple(string, rest(number))).not.toThrow()
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
            refine(string, (_v): _v is string => true),
            string,
            { seed },
        )
    })

    it('leaves what is stored alone', () => {
        expect(
            memberWritten(refine(decimal, nonEmpty) as AnyCodec, '1.5'),
        ).toBe('N')
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
            optional(fallback(string, 'x')),
            // @ts-expect-error in either order
            fallback(optional(string), 'x'),
        ]
        expect(typeof _wrong).toBe('function')
    })

    it('leaves what is stored alone', () => {
        expect(memberWritten(optional(decimal).codec as AnyCodec, '1.5')).toBe(
            'N',
        )
        expect(
            memberWritten(
                optional(string.set()).codec as AnyCodec,
                new Set(['a']),
            ),
        ).toBe('SS')
    })
})

/**
 * `nullable` is a builder, not a wrapper: it joins the null term to its subterm with a union, and
 * asks at construction whether the subterm already reaches the point. So its laws are laws about
 * what that question answers.
 */
describe('nullable', () => {
    /**
     * **§6's idempotence row.** `nullable(nullable(c)) ≡ nullable(c)`.
     *
     * True by construction rather than as an equation the proof has to earn: the inner call builds
     * `union([c, null])`, which reaches the point, so the outer call returns it unchanged. The test
     * is here because that reasoning is about the reading, and a reading that answered `false` for
     * a union carrying the null term would build `union([union([c, null]), null])` and claim the
     * point twice.
     */
    it('is idempotent', () => {
        checkEquivalent(nullable(nullable(string)), nullable(string), { seed })
        checkEquivalent(nullable(nullable(decimal)), nullable(decimal), {
            seed,
        })
    })

    /**
     * **A term whose null point is decided by a function is refused, not guessed.**
     *
     * `held` carries the caller's adapter, so whether it reaches the point is not readable off the
     * term. Guessing `false` builds `union([held, null])` and claims a point the adapter may
     * already write, which is (R) failing: the adapter here maps `'SENTINEL'` to `null`, so the
     * inner term writes and reads `{ NULL: true }` itself and the added option would shadow it.
     * Guessing `true` drops a point the adapter may not reach. So the builder refuses, and names
     * the spelling that does work.
     */
    it('refuses a term whose null point it cannot read, and names the spelling', () => {
        const adapter = {
            encode: (v: string) => (v === 'SENTINEL' ? null : v),
            decode: (v: string | null) => (v === null ? 'SENTINEL' : v),
        }
        expect(() => nullable(held(nullable(string), adapter))).toThrow(
            /held\(nullable\(inner\), adapter\)/,
        )
    })

    /**
     * **…and the spelling it names round-trips.**
     *
     * `held(nullable(inner), adapter)` puts the point inside the adapter rather than outside it, so
     * the adapter's `null` is the inner term's own `NULL` and there is one writer of the point.
     * This is the term the refusal above points at, and it is a law that must hold.
     */
    it('and the null point inside the adapter round-trips through it', () => {
        const sentinel = held(nullable(string), {
            encode: (v: string) => (v === 'SENTINEL' ? null : v),
            decode: (v: string | null) => (v === null ? 'SENTINEL' : v),
        })

        const written = sentinel.unsafeEncode('SENTINEL')
        expect(written).toEqual({ NULL: true })
        expect(sentinel.unsafeDecode(written)).toBe('SENTINEL')

        // and the values the adapter does not claim still round-trip
        expect(sentinel.unsafeDecode(sentinel.unsafeEncode('a'))).toBe('a')
    })
})

describe('what the wrappers preserve', () => {
    /**
     * Every wrapper answers the member of what it wraps, and this is the property that keeps a schema
     * honest: an index key's attribute type cannot change because somebody wrapped it.
     */
    it.each([
        ['held', held(decimal, { encode: String, decode: Number }), 1.5],
        ['refine', refine(decimal, (_v): _v is string => true), '1.5'],
        [
            'fallbackless legacy',
            legacy({ current: decimal, older: decimal }),
            '1.5',
        ],
        [
            'nested',
            refine(
                refine(decimal, (_v): _v is string => true),
                (_v): _v is string => true,
            ),
            '1.5',
        ],
    ] as readonly (readonly [string, AnyCodec, unknown])[])(
        '%s writes N, as decimal does',
        (_name, codec, value) => {
            expect(memberWritten(codec, value)).toBe('N')
        },
    )

    it('and a set keeps the member its element decides', () => {
        expect(memberWritten(string.set() as AnyCodec, new Set(['a']))).toBe(
            'SS',
        )
        expect(memberWritten(number.set() as AnyCodec, new Set([1]))).toBe('NS')
        expect(
            memberWritten(
                binary.set() as AnyCodec,
                new Set([new Uint8Array([1])]),
            ),
        ).toBe('BS')
        expect(memberWritten(array(string) as AnyCodec, ['a'])).toBe('L')
    })
})

describe('the laws that do NOT hold', () => {
    /**
     * `union` is not a lattice: adding an option can turn a working declaration into an ambiguous
     * one, and the type system refuses that case rather than the runtime.
     */
    it('a union is not closed under adding an option', () => {
        const _wrong = () =>
            // @ts-expect-error `string('A')` reads back as a subtype of what `string` reads back
            union([string, string('A')])
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
            CodecError,
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
        expect(() => union([array(string), array(number)])).toThrow(CodecError)
    })

    /**
     * And for sets the container-of-unions side is not a codec at all.
     *
     * A set's member follows from its element — `SS`, `NS` or `BS` — so an element that writes `S`
     * *or* `N` names no set. Refused when the declaration is evaluated rather than when a row arrives,
     * which for a codec declared at module scope is import time.
     */
    it('a set of a union is not a set at all', () => {
        const either = refine(
            union([string, number]),
            (value): value is string | number => value !== null,
        )
        // @ts-expect-error a union writes no single member, so the type declines the capability
        expect(() => either.set()).toThrow(CodecError)
    })

    /**
     * **A union of sets was refused and is not any more, and an empty container is what decides it.**
     *
     * The old reason was that "a `Set` says nothing about what is in it, and neither option checks",
     * so the value side could not be resolved and the declaration was refused. Both halves of that
     * are now false: the elements check, and the declaration guard asks whether the two are
     * separated by what they hold.
     *
     * The asymmetry that survives is the sharper one, and it is admission's own: `[]` is admitted by
     * every `array` and an empty `Set` is admitted by none, because **DynamoDB has no empty set**.
     * So `union([array(string), array(number)])` stays refused — one shared value, and it is the
     * one carrying nothing to tell them apart — while these two sets share no value at all.
     */
    it('a union of sets resolves, now that its elements check', () => {
        const either = union([string.set(), number.set()])
        expect(either.unsafeEncode(new Set(['a']) as never)).toEqual({
            SS: ['a'],
        })
        expect(either.unsafeEncode(new Set([1]) as never)).toEqual({
            NS: ['1'],
        })
        // a mixed set is admitted by neither, and says so rather than writing half of it
        expect(() => either.unsafeEncode(new Set(['a', 1]) as never)).toThrow(
            CodecError,
        )

        // the stored side always knew which, and that has not changed
        expect(memberWritten(string.set() as AnyCodec, new Set(['a']))).toBe(
            'SS',
        )
        expect(memberWritten(number.set() as AnyCodec, new Set([1]))).toBe('NS')
        expect(either.unsafeDecode({ SS: ['a'] })).toEqual(new Set(['a']))
        expect(either.unsafeDecode({ NS: ['1'] })).toEqual(new Set([1]))

        // and the container *with* an empty inhabitant is still refused, for that reason
        expect(() => union([array(string), array(number)])).toThrow(CodecError)
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
            // @ts-expect-error nor in a record
            record(optional(string)),
            // @ts-expect-error nor in a tuple
            tuple(string, optional(number)),
            // @ts-expect-error nor is a union option a name
            union([optional(string), number]),
            // @ts-expect-error and a fallback says the same thing about absence
            array(fallback(string, 'x')),
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
        expect(memberWritten(string.set() as AnyCodec, new Set(['a']))).toBe(
            'SS',
        )
        expect(memberWritten(array(string) as AnyCodec, ['a'])).toBe('L')
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
        tags: string.set(),
        steps: array(string),
        note: optional(string),
        nick: fallback(string, 'anon'),
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
            lit: string('A', 'B'),
            litN: number(0, 1),
            nul: nullable(string),
        }).item
        checkDecodesAreWritable(Ground, { count: 40, seed: 20260829 })
    })

    /**
     * **(Q), stability, over the same two entities.**
     *
     * `decode ∘ encode ∘ decode = decode` — §2's corollary, and what **(R)** becomes when the values
     * come from a *table* rather than from a generator. The two differ exactly by **(C)**, which is
     * the containment most likely to be untrue, so asking (R) of generated values and never asking
     * (Q) of stored ones leaves the gap this file exists to close.
     *
     * It was exercised in two files, both of them about one entity apiece. Here it runs over the
     * whole table the other laws use, and over stored forms a generator cannot produce: DynamoDB
     * normalises `N`, so `'1.50'` comes back `'1.5'` and only a fixed point survives one pass.
     */
    const itemsOf = <T>(
        subject: { encode: (v: T) => unknown },
        source: AnyCodec,
        count: number,
        itemSeed: number,
    ): AttributeMap[] => {
        const rng = rngFrom(itemSeed)
        const items: AttributeMap[] = []
        for (let i = 0; i < count; i++) {
            const written = subject.encode(arbitraryOf(source, rng, 4) as T)
            if (!failed(written)) items.push(written as AttributeMap)
        }
        return items
    }

    it('is stable for a wide entity, over items it wrote itself', () => {
        checkStable(Pet, itemsOf(Pet, Pet as unknown as AnyCodec, 40, 20260829))
    })

    /**
     * And over a row where **(Q) and (R) actually part company**, which is the only kind that says
     * anything the round-trip tests do not. A set is stored unordered, so `encode ∘ decode` is free
     * to return the members in another order: the *item* is not recovered, and the *value* is. That
     * is the whole content of stability — one pass through storage reaches a fixed point, and the
     * fixed point is a value rather than an attribute.
     *
     * Not `decimal`: `'1.50'` is *refused*, not normalised. Closing the (C) defect below made a
     * numeral outside DynamoDB's stored form unreadable rather than readable-and-unwritable, so
     * there is no lossy numeral left to make the point with.
     */
    it('is stable where the stored form is not recovered exactly', () => {
        const Stored = object({ tags: string.set() }).item
        const stored = { tags: { SS: ['c', 'a', 'b'] } }

        checkStable(Stored, [stored])

        // (Q) holds because the value is a set; (R) on the *item* is what does not hold
        const once = Stored.unsafeDecode(stored)
        expect(once).toEqual({ tags: new Set(['c', 'a', 'b']) })
        expect(Stored.unsafeDecode(Stored.unsafeEncode(once))).toEqual(once)
        expect(Stored.unsafeEncode(once)).not.toEqual(stored)
        expect(Stored.unsafeEncode(once)).toEqual({
            tags: { SS: ['a', 'b', 'c'] },
        })
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
        ).toThrow(CodecError)
        expect(() =>
            checkDecodesAreWritable(Leaky, { count: 5, seed: 1 }),
        ).toThrow(CodecError)
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
        ).toThrow(CodecError)
    })
})

/**
 * **Admission against `encode`, in the one direction that is true.**
 *
 * `accepts` is §3's `Adm : Term → Value → Bool` asked of the pair, and the model proved `Adm` exact
 * at all 21
 * constructors. The obvious law here is therefore `accepts(c, v) ⟺ !failed(c.encode(v))`, and half
 * of it used to be false — not because the port was wrong, but because **encoding did not
 * validate**. A codec's input is typed, so `string.encode(5)` wrote `{ S: 5 }` and
 * `array(string).encode([5])` wrote `{ L: [{ S: 5 }] }`. `carries`'s own docstring said this for
 * as long as it existed; what was missing was anything that measured how far it went.
 *
 * **That was true and is not any more.** The list of codecs where the converse failed was this
 * file's deliverable while the question was open — twenty-three of thirty-two — and the question
 * was whether `encode` should consult `admits`, which is a behaviour change and was JH's call.
 * It was taken: every row now runs the predicate admission runs, so the law below is the iff.
 *
 * What the old nine exact rows were exact *for* is still the interesting part, because it is what
 * the other twenty-three had to be given:
 *
 * - the five literals and `null` validated because their admissible set is **data this library
 *   owns** — `ℓ` is frozen at construction, so the check is decidable and `encode` ran it.
 * - `opaque` and `custom` are exact because their rows **ask the codec** rather than describing it.
 *   A question cannot disagree with its answer. That is the model's own move at `custom`, and the
 *   reason `opaque`'s rows were converted to match — and it is why those two are the one pair
 *   `encode` must *not* consult admission for: admission reaches them by calling `encode`.
 *
 * Everything else was loose at the value kinds it was handed but never checked, and now checks.
 */
describe('`accepts`, and the direction of the law that is true', () => {
    const isTag = (v: string): v is `t-${string}` => v.startsWith('t-')

    /** One entry per `Term` kind, plus the literal at each base and the two `opaque` policies. */
    const codecs: readonly (readonly [string, AnyCodec])[] = [
        ['string', string],
        ['string(...)', string('A', 'B')],
        ['decimal', decimal],
        ["decimal('1')", decimal('1', '2.5')],
        ['number', number],
        ['number(...)', number(0, 1, 2)],
        ['boolean', boolean],
        ['boolean(true)', boolean(true)],
        ['null', nullValue],
        ['binary', binary],
        ['binary(...)', binary(new Uint8Array([1, 2]))],
        ['opaque', opaque],
        ["opaque('lossy')", opaque('lossy')],
        ['set', string.set()],
        ['set(decimal)', decimal.set()],
        ['array', array(string)],
        ['tuple', tuple(string, number)],
        ['tuple(rest)', tuple(string, rest(number))],
        ['record', record(decimal)],
        ['attributes', object({ a: string, b: number }).item],
        ['attributes(open)', object({ a: string }, decimal).item],
        ['nullable', nullable(string)],
        ['legacy', legacy({ current: decimal, older: string })],
        ['refine', refine(string, isTag, { arbitrary: () => 't-x' as const })],
        [
            'held',
            held(string.set(), {
                encode: (tags: readonly string[]) => new Set(tags),
                decode: (tags: ReadonlySet<string>) => [...tags],
            }),
        ],
        ['lazy', lazy(() => string)],
        [
            'custom',
            custom<string>({
                encode: (v) => ({ S: v }) as never,
                decode: (a) => (a as { S: string }).S,
            }),
        ],
        [
            'tagged',
            discriminatedUnion('type', [
                object({ type: string('CHECKUP'), petId: string }),
                object({
                    type: string('SHOT'),
                    petId: string,
                    vaccine: string,
                }),
            ]),
        ],
        [
            'untagged',
            union([
                object({ petId: string, price: decimal }),
                object({ petIds: array(string) }),
            ]),
        ],
    ] as unknown as readonly (readonly [string, AnyCodec])[]

    /**
     * Every codec's own generated values, crossed with every codec — which is the whole method.
     *
     * A generator only ever produces values its own codec admits, so a pool drawn from one codec
     * exercises the implication and finds nothing. The looseness lives in the *cross* terms: a
     * `number` handed a `decimal`'s string, a `set` handed a `string`. The hand-written tail is for
     * the kinds no generator in the table produces — a plain object whose names are right and whose
     * values are not, which is the only way to reach an object option's looseness.
     */
    const pool: unknown[] = []
    for (const [, one] of codecs) {
        for (const seed of [1, 7, 0x5eed]) {
            try {
                pool.push(arbitraryOf(one, rngFrom(seed), 3))
            } catch {
                // a hand-written codec generates nothing unless it says how
            }
        }
    }
    pool.push(
        5,
        'yes',
        true,
        null,
        undefined,
        [],
        [5],
        {},
        new Set(),
        new Set([5]),
        new Set(['a', 5]),
        new Uint8Array([9]),
        'bytes',
        Number.NaN,
        1e400,
        '1.50',
        0,
        -1,
        { a: 5, b: 0 },
        { a: 5, b: 'x' },
        { a: 'x', b: 'y' },
        { petId: 5, price: 5 },
        { petId: 'p', price: 5 },
        { type: 'CHECKUP', petId: 5 },
        { type: 'NOPE', petId: 'p' },
    )

    /** `encode` is a `Result`-returning function that can still *throw*: `held`'s adapter does. */
    const writesIt = (one: AnyCodec, value: unknown): boolean => {
        try {
            return !failed(one.encode(value as never))
        } catch {
            return false
        }
    }

    /**
     * **The law.** Nothing `accepts` accepts is refused by `encode`, at any codec in the table over
     * any value in the pool. This is the half that makes `accepts` usable as a *filter*: a union
     * resolver, or an `encode` that validated, could rely on it without narrowing what either
     * writes today.
     */
    it('is sound: nothing it admits does `encode` refuse', () => {
        const unsound: string[] = []
        for (const [name, one] of codecs) {
            for (const value of pool) {
                if (accepts(one, value) && !writesIt(one, value)) {
                    unsound.push(`${name} @ ${String(value)}`)
                }
            }
        }
        expect(unsound).toEqual([])
    })

    /**
     * **The law, both ways, at every codec in the table over every value in the pool.**
     *
     * This was two tests and a list. The list was twenty-three codecs whose `encode` wrote a value
     * `admits` rejects, and it was the deliverable while the question "should `encode` validate?"
     * was open. It is closed, so the list is empty and the two halves are one assertion.
     *
     * How it went: gating the five **ground** rows on the predicates `admits` already used closed
     * seventeen, because twelve of the twenty-three were loose only through their elements — a
     * `tuple` took a `Uint8Array` of the right length because its positions did, and `attributes`,
     * the wrappers, `legacy`, `held`, `lazy` and both unions inherited the same way. The remaining
     * six were loose in their own row and got their own gate: `set` asked `instanceof Set` before
     * spreading, `array` and `tuple` asked `Array.isArray`, `record` asked `asRecord`, and `refine`
     * started running its predicate on the way in.
     *
     * **Every gate is the predicate `admits` was already using**, not a second description of it.
     * That is the whole reason this can be an iff rather than two lists kept in agreement: there is
     * one test per kind and two callers of it.
     *
     * If this fails, one of the two moved. A failure naming a codec on the `accepts`-accepts side
     * means `encode` got stricter than the row; on the `encode`-writes side, that `accepts` was
     * loosened — which is the drift the whole apparatus exists to catch.
     */
    it('holds both ways, everywhere', () => {
        const disagree: string[] = []
        for (const [name, one] of codecs) {
            for (const value of pool) {
                if (accepts(one, value) !== writesIt(one, value)) {
                    disagree.push(
                        `${name} @ ${String(value)}: admits=${accepts(one, value)} writes=${writesIt(one, value)}`,
                    )
                }
            }
        }
        expect(disagree).toEqual([])
    })

    /** The rows the brief called out, spelled as the one-liners they are. */
    it('answers the specific rows the model states', () => {
        // the ground rows validate now, so `accepts` and `encode` agree at all five
        expect(accepts(string, 5)).toBe(false)
        expect(failed(string.encode(5 as never))).toBe(true)
        expect(accepts(boolean, 'yes')).toBe(false)
        expect(failed(boolean.encode('yes' as never))).toBe(true)
        expect(accepts(binary, 'bytes')).toBe(false)
        expect(failed(binary.encode('bytes' as never))).toBe(true)
        // `toString` is defined on everything, which is what the numeral gate alone did not catch
        expect(accepts(number, '5')).toBe(false)
        expect(failed(number.encode('5' as never))).toBe(true)
        // and `isStoredNumeral` stringifies, so a one-element array read as a numeral
        expect(accepts(decimal, ['1'])).toBe(false)
        expect(failed(decimal.encode(['1'] as never))).toBe(true)

        // and the containers, which needed their own gate rather than their elements'
        expect(accepts(array(string), [5])).toBe(false)
        expect(failed(array(string).encode([5] as never))).toBe(true)
        expect(accepts(array(string), 'abc')).toBe(false)
        expect(failed(array(string).encode('abc' as never))).toBe(true)
        expect(accepts(string.set(), 'abc')).toBe(false)
        expect(failed(string.set().encode('abc' as never))).toBe(true)

        // an empty array is admitted and an empty set is not, and both are right: `L` has an empty
        // inhabitant and DynamoDB's sets do not
        expect(accepts(array(string), [])).toBe(true)
        expect(accepts(string.set(), new Set())).toBe(false)

        // `held` is asked about the value it holds, and its adapter throws on one it does not own
        const asSet = held(string.set(), {
            encode: (tags: readonly string[]) => new Set(tags),
            decode: (tags: ReadonlySet<string>) => [...tags],
        })
        expect(accepts(asSet, ['a', 'b'])).toBe(true)
        expect(accepts(asSet, 5)).toBe(false)

        // `refine` runs its predicate in both directions now, which was the last row to close
        const tagged = refine(string, isTag)
        expect(accepts(tagged, 't-1')).toBe(true)
        expect(accepts(tagged, 'x')).toBe(false)
        expect(failed(tagged.encode('x' as never))).toBe(true)
        expect(failed(tagged.encode('t-1'))).toBe(false)

        // There is no longer a case for "a codec with no definition makes no claim", and the
        // assertion that used to sit here is gone with it. It read
        // `accepts({} as AnyCodec, 'anything')` — a cast manufacturing a value the type forbids, to
        // check a branch reachable only by making it. `def` is required, so the branch is gone and
        // the cast would be the only thing keeping it alive.
    })
})
