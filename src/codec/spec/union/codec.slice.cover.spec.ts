/**
 * A union pattern reads member by member, and a union of one pattern is that pattern.
 *
 * The spelling of a pattern must not change the options that a slice gives. The type of a slice
 * states one option for each part, so a run time that gives more options than the type states
 * disagrees with its own type. The pets below stand in for any union of objects at two fields.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AnyCodec, UnionCodec } from '../../codec'
import { exclude, extract, object, string, union } from '../../codec'
import { failed } from '../../result'

const species = (kind: string) => object({ kind: string(kind) })
const color = (name: string) => object({ name: string(name) })
const Dog = species('DOG')
const Cat = species('CAT')
const Bird = species('BIRD')
const Black = color('BLACK')
const White = color('WHITE')
const Pets = object({
    species: union([Dog, Cat, Bird]),
    color: union([Black, White]),
})
const only = (kind: AnyCodec, shade: AnyCodec) =>
    object({ species: kind, color: shade })

const optionsOf = (codec: AnyCodec): number =>
    codec.def.kind === 'union' ? codec.def.options.length : 1

const rows = ['DOG', 'CAT', 'BIRD'].flatMap((kind) =>
    ['BLACK', 'WHITE'].map((name) => ({
        species: { kind },
        color: { name },
    })),
)
const admitted = (codec: AnyCodec): boolean[] =>
    rows.map(
        (row) => !failed((codec as never as AnyCodec).encode(row as never)),
    )

describe('exclude of a union of one pattern gives the options that exclude of the pattern gives', () => {
    const pattern = only(Dog, Black)

    it('gives the same option count', () => {
        expect(optionsOf(exclude(Pets, union([pattern])))).toBe(
            optionsOf(exclude(Pets, pattern)),
        )
        expect(optionsOf(extract(Pets, union([pattern])))).toBe(
            optionsOf(extract(Pets, pattern)),
        )
    })

    it('admits the same rows', () => {
        expect(admitted(exclude(Pets, union([pattern])))).toEqual(
            admitted(exclude(Pets, pattern)),
        )
        expect(admitted(exclude(Pets, pattern))).toEqual([
            false,
            true,
            true,
            true,
            true,
            true,
        ])
    })
})

describe('exclude of a union of patterns gives the options that excluding each pattern in turn gives', () => {
    const patterns = [only(Dog, Black), only(Cat, White)]
    const turn = patterns.reduce<AnyCodec>(
        (rest, one) => exclude(rest, one) as AnyCodec,
        Pets,
    )

    it('gives the same option count and the same rows', () => {
        const whole = exclude(Pets, union(patterns as never))
        expect(optionsOf(whole)).toBe(optionsOf(turn))
        expect(admitted(whole)).toEqual(admitted(turn))
    })

    it('keeps the rows that no pattern fits, and extract keeps the rest', () => {
        const kept = extract(Pets, union(patterns as never))
        const left = exclude(Pets, union(patterns as never))
        expect(
            admitted(kept).map((one, at) => one !== admitted(left)[at]),
        ).toEqual(rows.map(() => true))
    })
})

/**
 * The type of a slice states the options that the run time gives. The pets have three fields, and
 * each pattern splits some of them. A union of one pattern is the pattern, a fold excludes one
 * pattern after the other, and a member that is no object holds no part of an object.
 */
describe('the type of a slice states the options that the run time gives', () => {
    type Arity<C> =
        // biome-ignore lint/suspicious/noExplicitAny: the type arguments of the union are not read
        C extends UnionCodec<any, infer O extends readonly unknown[], any>
            ? O['length']
            : never
    const kind = <const K extends string>(value: K) =>
        object({ kind: string(value) })
    const shade = <const K extends string>(value: K) =>
        object({ name: string(value) })
    const size = <const K extends string>(value: K) =>
        object({ size: string(value) })
    const Stock = object({
        species: union([kind('DOG'), kind('CAT'), kind('BIRD')]),
        color: union([shade('BLACK'), shade('WHITE')]),
        size: union([size('SMALL'), size('LARGE')]),
    })
    const dogs = object({ species: kind('DOG') })
    const whiteSmall = object({ color: shade('WHITE'), size: size('SMALL') })
    const catsLarge = object({ species: kind('CAT'), size: size('LARGE') })

    it('gives one option for a union of one pattern and for the pattern', () => {
        const wrapped = exclude(Stock, union([dogs]))
        const plain = exclude(Stock, dogs)
        expectTypeOf<Arity<typeof wrapped>>().toEqualTypeOf<1>()
        expectTypeOf<Arity<typeof plain>>().toEqualTypeOf<1>()
        expect([optionsOf(wrapped), optionsOf(plain)]).toEqual([1, 1])
    })

    it('gives two options for the exclusion and the extraction of two patterns', () => {
        const left = exclude(Stock, union([dogs, whiteSmall]))
        const kept = extract(Stock, union([dogs, whiteSmall]))
        expectTypeOf<Arity<typeof left>>().toEqualTypeOf<2>()
        expectTypeOf<Arity<typeof kept>>().toEqualTypeOf<2>()
        expect([optionsOf(left), optionsOf(kept)]).toEqual([2, 2])
    })

    it('gives the options of excluding each pattern in turn', () => {
        const turn = exclude(exclude(Stock, dogs), whiteSmall)
        expectTypeOf<Arity<typeof turn>>().toEqualTypeOf<2>()
        expect(optionsOf(turn)).toBe(2)
    })

    /**
     * TypeScript 6 states 2 options for the fold of three patterns where TypeScript 7 and the run time
     * give 3, so the type of these two is asserted at the run time only.
     */
    it('gives three options for the fold of three patterns', () => {
        const three = exclude(Stock, union([dogs, whiteSmall, catsLarge]))
        const turn = exclude(exclude(Stock, dogs), whiteSmall)
        const last = exclude(turn, catsLarge)
        expect([optionsOf(three), optionsOf(last)]).toEqual([3, 3])
    })

    it('reads a member that is no object as a part that no object fits', () => {
        const mixed = exclude(Stock, union([dogs, string]))
        const kept = extract(Stock, union([dogs, string]))
        expectTypeOf<Arity<typeof mixed>>().toEqualTypeOf<1>()
        expectTypeOf<Arity<typeof kept>>().toEqualTypeOf<1>()
        expect([optionsOf(mixed), optionsOf(kept)]).toEqual([1, 1])
    })
})
