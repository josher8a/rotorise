/**
 * The argument of `extract` and `exclude` is a codec: the pattern that says which options to keep.
 *
 * An option fits a pattern where every value that it holds lies inside what the pattern holds, and
 * an object pattern names the keys that it needs. The slice goes into a field that holds a union and
 * the result stays compact, as TypeScript's `Extract` reads it: `{ k, pet: U }` against `{ pet: P }`
 * is `{ k, pet: Extract<U, P> }`. So the extraction has no option that the original lacks. Every
 * test that compares a slice with the original does so on a pool of rows, valid and damaged.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import type { Decoded } from '../../codec'
import {
    CodecError,
    decimal,
    discriminatedUnion,
    exclude,
    extract,
    meet,
    number,
    object,
    optional,
    refine,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'
import { disjoint } from '../../scoped'
import type { Term } from '../../term'
import { clauseLiteralsOf } from '../../term'

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
const pet = meet(categories, statuses)
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

describe('a slice goes into a field that holds a union and stays compact', () => {
    const dogs = object({
        pet: extract(pet, object({ category: string('DOG') })),
    })
    const kept = extract(order, dogs)
    const rest = exclude(order, dogs)

    it('keeps each option in place with a narrower union, and each slice is a certified union', () => {
        expect(optionsOf(kept)).toHaveLength(2)
        expect(optionsOf(rest)).toHaveLength(2)
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
        const whole = extract(order, object({ pet }))
        expect(optionsOf(whole)).toHaveLength(2)
        expect(exclude(order, object({ pet })).def.kind).toBe('never')
    })
})

describe('a pattern that nests keeps the members of the field that it keeps', () => {
    const pattern = object({
        kind: string('ADOPT'),
        pet: extract(pet, object({ status: string('AVAILABLE') })),
    })
    const kept = extract(order, pattern)
    const rest = exclude(order, pattern)

    it('keeps one option, and rejects the other members of its field and the option of another kind', () => {
        expect(optionsOf(kept)).toHaveLength(1)
        expect(optionsOf(rest)).toHaveLength(2)
    })

    it('types the kept option with the union at the field', () => {
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
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly kind: 'ADOPT'
            readonly pet: Dog | Cat
        }>()
        expectTypeOf<
            Extract<Decoded<typeof rest>, { kind: 'ADOPT' }>['pet']['status']
        >().toEqualTypeOf<'PENDING' | 'SOLD'>()
    })

    it('takes a pattern without a literal at the root', () => {
        const dogs = extract(
            order,
            object({
                pet: extract(pet, object({ category: string('DOG') })),
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
        const available = extract(
            visit,
            object({
                appointment: object({
                    pet: extract(pet, object({ status: string('AVAILABLE') })),
                }),
            }),
        )
        expect(optionsOf(available)).toHaveLength(1)
        expectTypeOf<
            Decoded<typeof available>['kind']
        >().toEqualTypeOf<'BOOKED'>()
        expectTypeOf<
            Decoded<typeof available>['appointment']['pet']['status']
        >().toEqualTypeOf<'AVAILABLE'>()
    })

    it('crosses the members of two nested keys', () => {
        const swap = extract(
            union([object({ give: pet, take: pet })]),
            object({
                give: extract(pet, object({ category: string('DOG') })),
                take: extract(pet, object({ status: string('AVAILABLE') })),
            }),
        )
        expect(optionsOf(swap)).toHaveLength(1)
    })
})

describe('the slice is the Extract of TypeScript, applied inside the field', () => {
    type Pet = Decoded<typeof pet>
    type Dogs = Extract<Pet, { readonly category: 'DOG' }>
    type Model =
        | { readonly kind: 'ADOPT'; readonly pet: Dogs }
        | { readonly kind: 'RETURN'; readonly pet: Dogs; readonly note: string }
    const dogs = object({
        pet: extract(pet, object({ category: string('DOG') })),
    })
    const kept = extract(order, dogs)

    it('types the extraction as the form that a model writes', () => {
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<Model>()
    })

    it('lets a value of the model form stand for a value of the slice', () => {
        const model = {} as Model
        const decoded: Decoded<typeof kept> = model
        expect(decoded).toBe(model)
    })

    it('keeps no option that the original lacks, and each option its own tag', () => {
        const tagsOf = (codec: { readonly def: Term }) =>
            optionsOf(codec).map((one) => {
                const pins = clauseLiteralsOf(one)
                return pins?.kind?.alts.ls[0]
            })
        const patterns = [
            dogs,
            object({ kind: string('ADOPT'), pet }),
            object({
                kind: string('RETURN'),
                pet: extract(pet, object({ status: string('SOLD') })),
            }),
            object({
                pet: extract(
                    pet,
                    object({
                        category: string('CAT'),
                        status: string('PENDING'),
                    }),
                ),
            }),
        ]
        for (const pattern of patterns) {
            const slice = extract(order, pattern)
            expect(optionsOf(slice).length).toBeLessThanOrEqual(
                optionsOf(order).length,
            )
            expect(
                tagsOf(slice).every((tag) => tagsOf(order).includes(tag)),
            ).toBe(true)
        }
    })

    it('rejects with one option for each split key, because the complement of a product is no product', () => {
        const swap = union([object({ give: pet, take: pet })])
        const both = object({
            give: extract(pet, object({ category: string('DOG') })),
            take: extract(pet, object({ status: string('AVAILABLE') })),
        })
        expect(optionsOf(extract(swap, both))).toHaveLength(1)
        expect(optionsOf(exclude(swap, both))).toHaveLength(2)
        const single = object({
            take: extract(pet, object({ status: string('AVAILABLE') })),
        })
        expect(optionsOf(exclude(swap, single))).toHaveLength(1)
    })

    it('splits an option at a union pattern, and the parts still partition the values', () => {
        const eitherPet = union([
            object({ pet: extract(pet, object({ category: string('DOG') })) }),
            object({ pet: extract(pet, object({ status: string('SOLD') })) }),
        ])
        const kept = extract(order, eitherPet)
        const rest = exclude(order, eitherPet)
        for (const row of valid) {
            const inKept = decodes(kept, row)
            const inRest = decodes(rest, row)
            expect(inKept === undefined, JSON.stringify(row)).not.toBe(
                inRest === undefined,
            )
            expect(inKept ?? inRest).toEqual(decodes(order, row))
        }
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
        const strings = extract(mixed, string)
        expect(optionsOf(strings)).toHaveLength(1)
        expectTypeOf<Decoded<typeof strings>>().toEqualTypeOf<string>()
        expect(strings.decode({ S: 'x' })).toBe('x')
        expect(failed(strings.decode({ N: '1' }))).toBe(true)
    })

    it('keeps the objects that fit an object pattern, and the rest in the exclusion', () => {
        const dogs = extract(mixed, object({ kind: string('DOG') }))
        expectTypeOf<Decoded<typeof dogs>>().toEqualTypeOf<{
            readonly kind: 'DOG'
            readonly age: Dec
        }>()
        expect(optionsOf(exclude(mixed, string))).toHaveLength(3)
    })

    it('slices a union of literals that no union former built, as the Extract of its literals', () => {
        const ab = string('A', 'B')
        const a = extract(ab, string('A'))
        expectTypeOf<Decoded<typeof a>>().toEqualTypeOf<'A'>()
        expect(a.decode({ S: 'A' })).toBe('A')
        expect(failed(a.decode({ S: 'B' }))).toBe(true)
        const b = exclude(ab, string('A'))
        expectTypeOf<Decoded<typeof b>>().toEqualTypeOf<'B'>()
        expect(b.decode({ S: 'B' })).toBe('B')
    })
})

describe('a pattern that describes no member is refused', () => {
    it('refuses a key that no member declares, at a nested level too', () => {
        const atRoot = () =>
            // @ts-expect-error no member declares the key
            extract(order, object({ nope: string('x') }))
        const nested = () =>
            // @ts-expect-error no member of the field declares the key
            extract(order, object({ pet: object({ nope: string('x') }) }))
        expect(atRoot).toThrow(CodecError)
        expect(nested).toThrow(CodecError)
    })

    it('refuses a literal at a base that no member pins at the key', () => {
        const wrongBase = () =>
            // @ts-expect-error a decimal literal at a key that the members pin to a string
            extract(order, object({ kind: decimal('1') }))
        expect(wrongBase).toThrow(CodecError)
    })

    /**
     * A refinement narrows a literal by a predicate, and no function decides whether a member lies
     * inside a closure. The type and the run time each refuse the pattern at the call, so no empty
     * slice stands for an answer.
     */
    it('refuses a pattern field that holds a refinement', () => {
        const refined = refine(
            string('ADOPT', 'RETURN'),
            (v): v is 'ADOPT' => v === 'ADOPT',
        )
        // @ts-expect-error a pattern key that holds a refinement describes no member
        const byPredicate = () => extract(order, object({ kind: refined }))
        expect(byPredicate).toThrow(/holds a refinement/)
    })

    it('keeps no option for a literal at the right base that no member pins', () => {
        const none = extract(order, object({ kind: string('UNKNOWN') }))
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
            extract(open, object({ tags: object({ id: string('tag-1') }) }))
        expect(split).toThrow(/open key entry/)
    })

    it('refuses a split of a dissection, whose table is keyed by literals', () => {
        const byKind = discriminatedUnion('kind', [
            object({ kind: string('ADOPT'), pet }),
            object({ kind: string('RETURN'), pet }),
        ])
        const split = () =>
            extract(
                byKind,
                object({
                    pet: extract(pet, object({ status: string('AVAILABLE') })),
                }),
            )
        expect(split).toThrow(/keeps its members whole/)
        expect(optionsOf(extract(byKind, object({ pet })))).toHaveLength(2)
    })
})
