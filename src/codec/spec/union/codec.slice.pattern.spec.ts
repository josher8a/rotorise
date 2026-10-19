/**
 * The argument of `extract` and `exclude` is a codec: the pattern that says which options to keep.
 *
 * An option fits a pattern where every value that it holds lies inside what the pattern holds, and
 * an object pattern names the keys that it needs. An object with a union at a field is the union of
 * the objects, so an option splits at each field that the pattern names and that holds a union of
 * objects, and the parts that fit stay. Every test that compares a slice with the original does so
 * on a pool of rows, valid and damaged.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import type { Decoded } from '../../codec'
import {
    CodecError,
    decimal,
    discriminatedUnion,
    number,
    object,
    optional,
    product,
    refine,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'
import { disjoint } from '../../scoped'
import type { Term } from '../../term'

type Dec = Decoded<typeof decimal>

const optionsOf = (codec: { readonly def: Term }): readonly Term[] =>
    codec.def.kind === 'union' ? codec.def.options : []

const categories = union([
    object({ category: string('DOG'), breed: string }),
    object({ category: string('CAT'), coat: string }),
])
const statuses = union([
    object({ status: string('AVAILABLE'), price: decimal }),
    object({ status: string('PENDING'), deposit: decimal }),
    object({ status: string('SOLD'), soldFor: decimal }),
])
const pet = product(categories, statuses)
const order = union([
    object({ kind: string('ADOPT'), pet }),
    object({ kind: string('RETURN'), pet, note: string }),
])

const petRow = (category: string, status: string): AttributeValue => ({
    M: {
        category: { S: category },
        ...(category === 'DOG'
            ? { breed: { S: 'beagle' } }
            : { coat: { S: 'tabby' } }),
        status: { S: status },
        ...{
            [{ AVAILABLE: 'price', PENDING: 'deposit', SOLD: 'soldFor' }[
                status
            ] as string]: { N: '5' },
        },
    },
})
const orderRow = (
    kind: string,
    category: string,
    status: string,
): AttributeValue => ({
    M: {
        kind: { S: kind },
        pet: petRow(category, status),
        ...(kind === 'RETURN' ? { note: { S: 'scratched' } } : {}),
    },
})
const valid = ['ADOPT', 'RETURN'].flatMap((kind) =>
    ['DOG', 'CAT'].flatMap((category) =>
        ['AVAILABLE', 'PENDING', 'SOLD'].map((status) =>
            orderRow(kind, category, status),
        ),
    ),
)
/** Each valid row, damaged at the top and under `pet`, and each row at a foreign tag. */
const pool: AttributeValue[] = [
    ...valid,
    ...valid.flatMap((row) => {
        const m = (row as { M: Record<string, AttributeValue> }).M
        const inner = (m.pet as { M: Record<string, AttributeValue> }).M
        return [
            { M: { ...m, extra: { S: 'x' } } },
            { M: { ...m, pet: { S: 'oops' } } },
            {
                M: {
                    ...m,
                    pet: { M: { ...inner, status: { S: 'UNKNOWN' } } },
                },
            },
            { M: { ...m, kind: { S: 'ARCHIVED' } } },
        ] as AttributeValue[]
    }),
]

const decodes = (
    codec: { readonly decode: (a: AttributeValue) => unknown },
    row: AttributeValue,
) => {
    const out = codec.decode(row)
    return failed(out) ? undefined : out
}

describe('an object with a union at a field is the union of the objects', () => {
    const dogs = object({
        pet: pet.extract(object({ category: string('DOG') })),
    })
    const kept = order.extract(dogs)
    const rest = order.exclude(dogs)

    it('splits each option at the field, and each slice is a certified union', () => {
        expect(optionsOf(kept)).toHaveLength(6)
        expect(optionsOf(rest)).toHaveLength(6)
        for (const slice of [kept, rest]) {
            const options = optionsOf(slice)
            for (const [at, one] of options.entries()) {
                for (const other of options.slice(at + 1)) {
                    expect(disjoint(one, other)).toBe(true)
                }
            }
        }
    })

    it('splits every valid row between the extraction and the exclusion, as the original reads it', () => {
        for (const row of valid) {
            const inKept = decodes(kept, row)
            const inRest = decodes(rest, row)
            expect(inKept === undefined, JSON.stringify(row)).not.toBe(
                inRest === undefined,
            )
            expect(inKept ?? inRest).toEqual(decodes(order, row))
        }
    })

    it('reads no pool value that the original does not read, and writes what it reads', () => {
        for (const row of pool) {
            const was = decodes(order, row)
            const now = decodes(kept, row) ?? decodes(rest, row)
            expect(now, JSON.stringify(row)).toEqual(was)
            if (now !== undefined) {
                expect(
                    (decodes(kept, row) ? kept : rest).unsafeEncode(
                        now as never,
                    ),
                ).toEqual(row)
            }
        }
    })

    it('keeps an option whole where the option fits the pattern whole', () => {
        const whole = order.extract(object({ pet }))
        expect(optionsOf(whole)).toHaveLength(2)
        expect(order.exclude(object({ pet })).def.kind).toBe('never')
    })
})

describe('a pattern that nests keeps the objects whose member it keeps', () => {
    const pattern = object({
        kind: string('ADOPT'),
        pet: pet.extract(object({ status: string('AVAILABLE') })),
    })
    const kept = order.extract(pattern)
    const rest = order.exclude(pattern)

    it('keeps one option for each member of the field that the pattern keeps', () => {
        expect(optionsOf(kept)).toHaveLength(2)
        expect(optionsOf(rest)).toHaveLength(10)
    })

    it('types the kept options as the split type reads them', () => {
        type Dog = {
            readonly category: 'DOG'
            readonly breed: string
            readonly status: 'AVAILABLE'
            readonly price: Dec
        }
        type Cat = {
            readonly category: 'CAT'
            readonly coat: string
            readonly status: 'AVAILABLE'
            readonly price: Dec
        }
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            | { readonly kind: 'ADOPT'; readonly pet: Dog }
            | { readonly kind: 'ADOPT'; readonly pet: Cat }
        >()
        expectTypeOf<
            Extract<Decoded<typeof rest>, { kind: 'ADOPT' }>['pet']['status']
        >().toEqualTypeOf<'PENDING' | 'SOLD'>()
    })

    it('takes a pattern without a literal at the root', () => {
        const dogs = order.extract(
            object({
                pet: pet.extract(object({ category: string('DOG') })),
            }),
        )
        expectTypeOf<
            Decoded<typeof dogs>['pet']['category']
        >().toEqualTypeOf<'DOG'>()
    })

    it('reaches a choice two levels down', () => {
        const visit = union([
            object({
                kind: string('BOOKED'),
                appointment: object({ id: string, pet }),
            }),
            object({ kind: string('WALKIN'), id: string }),
        ])
        const available = visit.extract(
            object({
                appointment: object({
                    pet: pet.extract(object({ status: string('AVAILABLE') })),
                }),
            }),
        )
        expect(optionsOf(available)).toHaveLength(2)
        expectTypeOf<
            Decoded<typeof available>['kind']
        >().toEqualTypeOf<'BOOKED'>()
        expectTypeOf<
            Decoded<typeof available>['appointment']['pet']['status']
        >().toEqualTypeOf<'AVAILABLE'>()
    })

    it('crosses the members of two nested keys', () => {
        const swap = union([object({ give: pet, take: pet })]).extract(
            object({
                give: pet.extract(object({ category: string('DOG') })),
                take: pet.extract(object({ status: string('AVAILABLE') })),
            }),
        )
        expect(optionsOf(swap)).toHaveLength(6)
    })
})

describe('a union that holds other kinds beside objects slices by any codec', () => {
    const mixed = union([
        string,
        object({ kind: string('DOG'), age: decimal }),
        object({ kind: string('CAT') }),
        number,
    ])

    it('keeps the members that fit a base', () => {
        const strings = mixed.extract(string)
        expect(optionsOf(strings)).toHaveLength(1)
        expectTypeOf<Decoded<typeof strings>>().toEqualTypeOf<string>()
        expect(strings.decode({ S: 'x' })).toBe('x')
        expect(failed(strings.decode({ N: '1' }))).toBe(true)
    })

    it('keeps the objects that fit an object pattern, and the rest in the exclusion', () => {
        const dogs = mixed.extract(object({ kind: string('DOG') }))
        expectTypeOf<Decoded<typeof dogs>>().toEqualTypeOf<{
            readonly kind: 'DOG'
            readonly age: Dec
        }>()
        expect(optionsOf(mixed.exclude(string))).toHaveLength(3)
    })
})

describe('a pattern that describes no member is refused', () => {
    it('refuses a key that no member declares, at a nested level too', () => {
        const atRoot = () =>
            // @ts-expect-error no member declares the key
            order.extract(object({ nope: string('x') }))
        const nested = () =>
            // @ts-expect-error no member of the field declares the key
            order.extract(object({ pet: object({ nope: string('x') }) }))
        expect(atRoot).toThrow(CodecError)
        expect(nested).toThrow(CodecError)
    })

    it('refuses a literal at a base that no member pins at the key', () => {
        const wrongBase = () =>
            // @ts-expect-error a decimal literal at a key that the members pin to a string
            order.extract(object({ kind: decimal('1') }))
        expect(wrongBase).toThrow(CodecError)
    })

    /**
     * A refinement narrows a literal by a predicate, and no function decides whether a member lies
     * inside a closure. The type passes the pattern, because the refinement keeps the literal mark,
     * so the run time refuses at the call and no empty slice stands for an answer.
     */
    it('refuses a pattern field that holds a refinement', () => {
        const refined = refine(
            string('ADOPT', 'RETURN'),
            (v): v is 'ADOPT' => v === 'ADOPT',
        )
        const byPredicate = () => order.extract(object({ kind: refined }))
        expect(byPredicate).toThrow(/holds a refinement/)
    })

    it('keeps no option for a literal at the right base that no member pins', () => {
        const none = order.extract(object({ kind: string('UNKNOWN') }))
        expect(none.def.kind).toBe('never')
    })

    it('refuses a split of an object that has an open key entry', () => {
        const open = union([
            object({
                kind: string('LISTED'),
                tags: union([
                    object({ id: string('tag-1') }, [string, optional(string)]),
                    object({ id: string('tag-2') }, [string, optional(string)]),
                ]),
            }),
            object({ kind: string('UNLISTED'), tags: object({ id: string }) }),
        ])
        const split = () =>
            open.extract(object({ tags: object({ id: string('tag-1') }) }))
        expect(split).toThrow(/open key entry/)
    })

    it('refuses a split of a dissection, whose table is keyed by literals', () => {
        const byKind = discriminatedUnion('kind', [
            object({ kind: string('ADOPT'), pet }),
            object({ kind: string('RETURN'), pet }),
        ])
        const split = () =>
            byKind.extract(
                object({
                    pet: pet.extract(object({ status: string('AVAILABLE') })),
                }),
            )
        expect(split).toThrow(/keeps its members whole/)
        expect(optionsOf(byKind.extract(object({ pet })))).toHaveLength(2)
    })
})
