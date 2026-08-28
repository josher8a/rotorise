/**
 * Literals over numbers, which is how an enum indexed by number is expressed.
 *
 * A literal is the one ground term whose stored member follows from its *values* rather than from its
 * name: text is `S`, digits are `N`. So the same constructor covers a string enum and a numeric one,
 * and a mix of the two is refused — one codec cannot write two members.
 *
 * The held value is the number, not its text. `N` carries digits on the wire, and reading one back as
 * `'0'` would make the literal type a lie.
 */
import { describe, expect, it } from 'vitest'
import type { N, NS, S, SS } from './attribute'
import {
    CodecError,
    carries,
    decides,
    discriminatedUnion,
    literal,
    number,
    object,
    set,
    string,
    union,
    writes,
} from './codec'
import { checkRoundTrip } from './testing'

/** The shape these are usually written in. */
const Status = { DRAFT: 0, LISTED: 1, SOLD: 2 } as const
type Status = (typeof Status)[keyof typeof Status]

const status = literal(...(Object.values(Status) as Status[]))

describe('a numeric literal', () => {
    it('is stored as N', () => {
        expect(writes(status)).toBe('N')
        expect(status.unsafeEncode(1)).toEqual({ N: '1' })
    })

    it('is held as the number, not as its digits', () => {
        const back: Status = status.unsafeDecode({ N: '2' })
        expect(back).toBe(2)
        expect(typeof back).toBe('number')
    })

    it('types the attribute as N, and a string literal as S', () => {
        const numeric: N = status.unsafeEncode(0)
        const text: S = literal('DRAFT').unsafeEncode('DRAFT')
        expect([numeric, text]).toHaveLength(2)
    })

    it('checks the admissible set in both directions', () => {
        expect(() => status.unsafeDecode({ N: '7' })).toThrow(
            /7 is not one of 0, 1, 2/,
        )
        expect(() => status.unsafeEncode(7 as Status)).toThrow(CodecError)
    })

    it('refuses the digits stored as text', () => {
        expect(() => status.unsafeDecode({ S: '1' })).toThrow(
            /expected attribute member 'N', found 'S'/,
        )
    })

    it('keeps the constant brand for a single value', () => {
        const draft = literal(0)
        // the brand is type-level, and the annotation is the assertion; `decides` is what reads the
        // value back at runtime, and is what a key component is built from
        type Only = typeof draft.constant
        const _narrowed: 0 = null as unknown as Only
        expect(decides(draft)).toBe(0)
        // and two admissible values decide nothing, which is the point of `decides`
        expect(decides(status)).toBeUndefined()
    })

    it('takes a number, which is what a union filters on', () => {
        expect(carries(status)).toEqual(['number'])
    })

    it('round-trips', () => {
        checkRoundTrip(object({ status }).item, { count: 100, seed: 20260828 })
    })
})

describe('a numeric tag', () => {
    /**
     * `readTag` always accepted `S` or `N` — a tag is stored as one or the other — so the only thing
     * standing between a numeric enum and a discriminated union was the literal.
     */
    type Row = { kind: 0; draftedAt: string } | { kind: 1; listedAt: string }

    const Rows = discriminatedUnion('kind', [
        object({ kind: literal(0), draftedAt: string }),
        object({ kind: literal(1), listedAt: string }),
    ])

    it('chooses the variant', () => {
        expect(Rows.item.unsafeEncode({ kind: 1, listedAt: 'now' })).toEqual({
            kind: { N: '1' },
            listedAt: { S: 'now' },
        })
    })

    it('and reads it back, tag included, as a number', () => {
        const back: Row = Rows.item.unsafeDecode({
            kind: { N: '0' },
            draftedAt: { S: 'x' },
        })
        expect(back).toEqual({ kind: 0, draftedAt: 'x' })
    })

    it('reaches a variant by its numeric tag', () => {
        expect(
            Rows.item.variant(0).field('draftedAt').unsafeEncode('t'),
        ).toEqual({ S: 't' })
    })

    it('refuses a tag no variant names', () => {
        expect(() =>
            Rows.item.unsafeDecode({ kind: { N: '9' }, draftedAt: { S: 'x' } }),
        ).toThrow(/'9' is not a variant of 'kind'/)
    })
})

/**
 * A set of a literal, which is how a fixed vocabulary is stored.
 *
 * The member follows all the way up: a literal of text is `S`, so a set of it is `SS`; a literal of
 * digits is `N`, so a set of it is `NS`. Nothing new was needed for this — `set` reads its element's
 * member, and the element now has one either way.
 */
describe('a set of a literal', () => {
    const tags = set(literal('a', 'b', 'c'))
    const codes = set(literal(1, 2, 3, 4))

    it('writes SS for text and NS for digits', () => {
        expect(writes(tags)).toBe('SS')
        expect(writes(codes)).toBe('NS')
        const asSS: SS = tags.unsafeEncode(new Set(['c', 'a']))
        const asNS: NS = codes.unsafeEncode(new Set([3, 1]))
        expect(asSS).toEqual({ SS: ['a', 'c'] })
        expect(asNS).toEqual({ NS: ['1', '3'] })
    })

    it('holds a set of the literal union', () => {
        const back: ReadonlySet<1 | 2 | 3 | 4> = codes.unsafeDecode({
            NS: ['1', '3'],
        })
        expect(back).toEqual(new Set([1, 3]))
    })

    it('checks each member, naming where it failed', () => {
        expect(() => codes.unsafeDecode({ NS: ['9'] })).toThrow(
            /at \[0\]: 9 is not one of 1, 2, 3, 4/,
        )
        expect(() => tags.unsafeDecode({ SS: ['z'] })).toThrow(
            /at \[0\]: 'z' is not one of 'a', 'b', 'c'/,
        )
    })

    /**
     * `NS` is sorted as text, so `10` precedes `2` in the table — and a set is unordered, so the law
     * holds anyway. This is the case that would break if a set were an array.
     */
    it('round-trips digits that do not sort numerically', () => {
        const codec = set(literal(1, 2, 10))
        const value = new Set([10, 2] as const)
        expect(codec.unsafeEncode(value)).toEqual({ NS: ['10', '2'] })
        expect(codec.unsafeDecode(codec.unsafeEncode(value))).toEqual(value)
    })

    it('round-trips over generated values', () => {
        checkRoundTrip(object({ tags, codes }).item, {
            count: 100,
            seed: 20260828,
        })
    })

    /**
     * And a union of two such sets is allowed, which is the interesting part.
     *
     * Both options are given a `Set`, so the kind cannot choose between them — but a literal element
     * *refuses* a value that is not its own, so trying can. `union(set(string), set(number))` stays
     * refused for exactly the reason this one is not: those elements check nothing.
     */
    it('and a union of two literal sets resolves, where a union of plain sets cannot', () => {
        const either = union([set(literal('a', 'b')), set(literal(1, 2))])
        expect(either.unsafeEncode(new Set<'a' | 'b'>(['a']))).toEqual({
            SS: ['a'],
        })
        expect(either.unsafeEncode(new Set<1 | 2>([2]))).toEqual({ NS: ['2'] })
        expect(either.unsafeDecode({ NS: ['1'] })).toEqual(new Set([1]))

        expect(() => union([set(string), set(number)])).toThrow(
            /both take the same kind of value — set — and neither checks/,
        )
    })
})

describe('what mixing kinds would ask for', () => {
    it('is refused, because one codec writes one member', () => {
        const _wrong = () =>
            // @ts-expect-error a literal is stored as S or as N and cannot be both
            literal('A', 0)
        expect(_wrong).toThrow(
            /a literal is stored as 'S' or as 'N' and cannot be both/,
        )
    })

    it('though a union of the two is fine, since the kinds differ', () => {
        const either = union([literal('A'), literal(0)])
        expect(either.unsafeEncode('A')).toEqual({ S: 'A' })
        expect(either.unsafeEncode(0)).toEqual({ N: '0' })
        expect(either.unsafeDecode({ N: '0' })).toBe(0)
    })
})
