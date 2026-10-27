/**
 * The type of a slice by a union pattern reads the parts of the normal form of an option, as the run
 * time does.
 *
 * The run time splits an option into the join of its parts before it reads a union pattern. A
 * literal set is the join of its literals, `boolean` is `true` and `false`, an object distributes
 * over a union at a field, and a list distributes at a position. The option stays whole where each
 * part fits one member. Each test assigns a value that the run time produces to the decoded type,
 * and a result that the run time empties has the type `never`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { Decoded } from '../../codec'
import {
    boolean,
    CodecError,
    exclude,
    extract,
    held,
    list,
    object,
    refine,
    string,
    union,
} from '../../codec'
import type { Term } from '../../term'

const optionsOf = (codec: { readonly def: Term }): readonly Term[] =>
    codec.def.kind === 'union' ? codec.def.options : []

describe('an option stays whole where each part of its normal form fits a member', () => {
    const wide = union([object({ x: string('a', 'b') })])
    const split = union([
        object({ x: string('a') }),
        object({ x: string('b') }),
    ])

    it('keeps an option whose literal set the members cover, as the run time keeps it', () => {
        const kept = extract(wide, split)
        expect(optionsOf(kept)).toHaveLength(1)
        const both: Decoded<typeof kept> = { x: 'a' }
        const other: Decoded<typeof kept> = { x: 'b' }
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly x: 'a' | 'b'
        }>()
        expect([both, other]).toHaveLength(2)
    })

    it('drops the covered option from the exclusion', () => {
        const rest = exclude(wide, split)
        expect(optionsOf(rest)).toHaveLength(0)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<never>()
    })

    it('keeps the option of three literals where three members cover it', () => {
        const three = union([object({ x: string('a', 'b', 'c') })])
        const members = union([
            object({ x: string('a') }),
            object({ x: string('b') }),
            object({ x: string('c') }),
        ])
        const kept = extract(three, members)
        expect(optionsOf(kept)).toHaveLength(1)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly x: 'a' | 'b' | 'c'
        }>()
        const rest = exclude(three, members)
        expect(optionsOf(rest)).toHaveLength(0)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<never>()
    })

    it('drops an option whose literal set the members leave a literal of', () => {
        const three = union([object({ x: string('a', 'b', 'c') })])
        const kept = extract(three, split)
        expect(optionsOf(kept)).toHaveLength(0)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        // the exclusion keeps the option whole: the run time splits a literal set into no part
        const rest = exclude(three, split)
        expect(optionsOf(rest)).toHaveLength(1)
        const value: Decoded<typeof rest> = { x: 'a' }
        expect(value).toEqual({ x: 'a' })
    })

    it('reads the product of two fields: a part of the product that no member covers drops the option', () => {
        const two = union([
            object({ x: string('a', 'b'), y: string('c', 'd') }),
        ])
        const members = union([
            object({ x: string('a') }),
            object({ y: string('c') }),
        ])
        const kept = extract(two, members)
        expect(optionsOf(kept)).toHaveLength(0)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        const rest = exclude(two, members)
        expect(optionsOf(rest)).toHaveLength(1)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<{
            readonly x: 'a' | 'b'
            readonly y: 'c' | 'd'
        }>()
    })

    it('reads boolean as the join of true and false', () => {
        const flag = union([object({ x: boolean, y: string })])
        const members = union([
            object({ x: boolean(true) }),
            object({ x: boolean(false) }),
        ])
        const kept = extract(flag, members)
        expect(optionsOf(kept)).toHaveLength(1)
        const row: Decoded<typeof kept> = { x: true, y: 'k' }
        expect(row.y).toBe('k')
        expect(optionsOf(exclude(flag, members))).toHaveLength(0)
    })

    it('reads a literal set below an object that the pattern members name', () => {
        const nested = union([object({ o: object({ x: string('a', 'b') }) })])
        const members = union([
            object({ o: object({ x: string('a') }) }),
            object({ o: object({ x: string('b') }) }),
        ])
        const kept = extract(nested, members)
        expect(optionsOf(kept)).toHaveLength(1)
        const row: Decoded<typeof kept> = { o: { x: 'b' } }
        expect(row.o.x).toBe('b')
    })

    it('reads a literal set at a position of a list', () => {
        const pair = union([object({ r: list(string('a', 'b')) })])
        const members = union([
            object({ r: list(string('a')) }),
            object({ r: list(string('b')) }),
        ])
        const kept = extract(pair, members)
        expect(optionsOf(kept)).toHaveLength(1)
        const row: Decoded<typeof kept> = { r: ['b'] }
        expect(row.r).toEqual(['b'])
    })

    it('keeps an object union at a field whole beside another key', () => {
        const A = object({ t: string('a') })
        const B = object({ t: string('b') })
        const held2 = union([object({ k: string('k'), x: union([A, B]) })])
        const kept = extract(held2, union([object({ x: A }), object({ x: B })]))
        expect(optionsOf(kept)).toHaveLength(1)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly k: 'k'
            readonly x: { readonly t: 'a' } | { readonly t: 'b' }
        }>()
    })
})

describe('a refinement and an adapter are one part', () => {
    const isA = (value: 'a' | 'b'): value is 'a' | 'b' => value === 'a'
    const split = union([
        object({ x: string('a') }),
        object({ x: string('b') }),
    ])

    /**
     * The run time reads a refinement as one part. A refinement of a literal set is no join of the
     * literals, so the option is no member of the pattern, and the extraction drops it.
     */
    it('drops an option whose field is a refinement that the members do not cover', () => {
        const refined = union([object({ x: refine(string('a', 'b'), isA) })])
        const kept = extract(refined, split)
        expect(optionsOf(kept)).toHaveLength(0)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
    })

    /**
     * The run time reads an adapter as one part, and a plain clause never meets an adapter, so the
     * adapter option fits no member. The type reads the adapter by its library inner term and keeps
     * the option where it cannot decide, which is wider than the run time and sound.
     */
    it('drops an option whose field is an adapter over a literal set, as the run time drops it', () => {
        const tag = held(string, string('a', 'b'), {
            encode: (value: 'a' | 'b') => value,
            decode: (value: string) =>
                value === 'a' || value === 'b'
                    ? value
                    : new CodecError(`'${value}' is not a literal`),
        })
        const adapted = union([object({ x: tag })])
        const kept = extract(adapted, split)
        expect(optionsOf(kept)).toHaveLength(0)
        const probe: Decoded<typeof kept> = null as never
        expect(probe).toBeNull()
    })
})

describe('a split that passes the bound keeps the option', () => {
    /**
     * The type reads at most 32 parts of one option. Past the bound the fit is unknown, so the slice
     * keeps the option, which is wider than the run time and sound. The extraction keeps the option
     * where the run time keeps it. The exclusion keeps the option where the run time drops it.
     */
    const first = [
        'l00',
        'l01',
        'l02',
        'l03',
        'l04',
        'l05',
        'l06',
        'l07',
        'l08',
        'l09',
        'l10',
        'l11',
        'l12',
        'l13',
        'l14',
        'l15',
        'l16',
    ] as const
    const rest = [
        'l17',
        'l18',
        'l19',
        'l20',
        'l21',
        'l22',
        'l23',
        'l24',
        'l25',
        'l26',
        'l27',
        'l28',
        'l29',
        'l30',
        'l31',
        'l32',
    ] as const
    const big = union([object({ x: string(...first, ...rest) })])
    const members = union([
        object({ x: string(...first) }),
        object({ x: string(...rest) }),
    ])

    it('keeps the extraction, as the run time keeps it', () => {
        const kept = extract(big, members)
        expect(optionsOf(kept)).toHaveLength(1)
        const row: Decoded<typeof kept> = { x: 'l32' }
        expect(row.x).toBe('l32')
    })

    it('keeps the exclusion where the run time drops the option', () => {
        const rest = exclude(big, members)
        expect(optionsOf(rest)).toHaveLength(0)
        const row: Decoded<typeof rest> = { x: 'l00' }
        expect(row.x).toBe('l00')
    })
})
