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
import type { AnyCodec, Decoded } from '../../codec'
import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    exclude,
    extract,
    fits,
    held,
    list,
    meet,
    never,
    number,
    object,
    opaque,
    optional,
    refine,
    string,
    termOf,
    union,
} from '../../codec'
import { failed } from '../../result'
import { disjoint } from '../../scoped'
import type { Term } from '../../term'
import { clauseLiteralsOf } from '../../term'

type Dec = Decoded<typeof decimal>

const defOf = (codec: AnyCodec) => codec.def

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

describe('a pattern that no member fits extracts never and excludes all', () => {
    it('extracts never for a key that no member declares, at a nested level too', () => {
        const atRoot = extract(order, object({ nope: string('x') }))
        const nested = extract(
            order,
            object({ pet: object({ nope: string('x') }) }),
        )
        expectTypeOf<Decoded<typeof atRoot>>().toEqualTypeOf<never>()
        expectTypeOf<Decoded<typeof nested>>().toEqualTypeOf<never>()
        expect(atRoot.def.kind).toBe('never')
        expect(nested.def.kind).toBe('never')
    })

    it('excludes all for a key that no member declares, at a nested level too', () => {
        const atRoot = exclude(order, object({ nope: string('x') }))
        const nested = exclude(
            order,
            object({ pet: object({ nope: string('x') }) }),
        )
        expectTypeOf<Decoded<typeof atRoot>>().toEqualTypeOf<
            Decoded<typeof order>
        >()
        expectTypeOf<Decoded<typeof nested>>().toEqualTypeOf<
            Decoded<typeof order>
        >()
        expect(atRoot.def).toEqual(order.def)
        expect(nested.def).toEqual(order.def)
    })

    it('extracts never for a literal at a base that no member pins at the key', () => {
        const wrongBase = extract(order, object({ kind: decimal('1') }))
        expectTypeOf<Decoded<typeof wrongBase>>().toEqualTypeOf<never>()
        expect(wrongBase.def.kind).toBe('never')
    })

    it('keeps no option for a literal at the right base that no member pins', () => {
        const none = extract(order, object({ kind: string('UNKNOWN') }))
        expect(none.def.kind).toBe('never')
    })

    it('extracts never from never, and excludes never from never', () => {
        const kept = extract(never, object({ kind: string('ADOPT') }))
        const rest = exclude(never, object({ kind: string('ADOPT') }))
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<never>()
        expect(kept.def.kind).toBe('never')
        expect(rest.def.kind).toBe('never')
    })

    /**
     * A pattern that no part of a member fits changes no member, so the dissection keeps each
     * member whole in the exclusion and keeps nothing in the extraction.
     */
    it('excludes each member of a dissection whole for a pattern that no member fits', () => {
        const byKind = discriminatedUnion('kind', [
            object({ kind: string('ADOPT'), pet }),
            object({ kind: string('RETURN'), pet }),
        ])
        const unfit = object({ pet: object({ category: decimal('1') }) })
        const rest = exclude(byKind, unfit)
        const kept = extract(byKind, unfit)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof byKind>
        >()
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        expect(optionsOf(rest)).toEqual(optionsOf(byKind))
        expect(kept.def.kind).toBe('never')
    })
})

describe('a pattern that the host cannot read is refused', () => {
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
        // @ts-expect-error a pattern key that holds a refinement is refused
        const byPredicate = () => extract(order, object({ kind: refined }))
        expect(byPredicate).toThrow(/holds a refinement/)
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

/**
 * **The order of the slice is the order of the meet.** `opaque` holds every value, so every member
 * fits it. A set fits a set whose element holds its element. The type of the slice states the same
 * order.
 */
describe('fits is the order of the meet, at the top and at a set', () => {
    it('extracts every member by opaque, the top of the order, and excludes none', () => {
        const members = union([object({ a: string }), object({ b: string })])
        const kept = extract(members, opaque)
        const rest = exclude(members, opaque)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            { readonly a: string } | { readonly b: string }
        >()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<never>()
        expect(optionsOf(kept)).toEqual(optionsOf(members))
        expect(rest.def.kind).toBe('never')
    })

    it('extracts a set by a set pattern whose element holds the element of the set', () => {
        const mixed = union([binary.set(), string])
        const kept = extract(mixed, binary.set())
        const rest = exclude(mixed, binary.set())
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<ReturnType<typeof binary.set>>
        >()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<string>()
        expect(optionsOf(kept).map((one) => one.kind)).toEqual(['set'])
        expect(optionsOf(rest).map((one) => one.kind)).toEqual(['string'])
    })
})

/**
 * **A union pattern covers a part of the option, and the option fits where each part fits.** The
 * parts of the option are the join-prime terms of its normal form: a finite base splits into its
 * literals, and an object or a list splits at a union that sits at a field or at a position. A list
 * of a union is one part, because the list holds mixed lists. A refinement is one part, because
 * the host cannot read the predicate.
 */
describe('fits splits the option into its parts before it reads a union pattern', () => {
    const both = union([boolean(true), boolean(false)])
    const cell = (a: boolean, b: boolean) =>
        object({ a: boolean(a), b: boolean(b) })

    it('keeps the member whose base a union of every literal of the base covers', () => {
        const members = union([object({ k: boolean }), object({ n: number })])
        const kept = extract(members, object({ k: both }))
        expect(optionsOf(kept).map((one) => one.kind)).toEqual(['object'])
    })

    it('fits a base to the union of its literals', () => {
        expect(fits(termOf(boolean), termOf(both))).toBe(true)
    })

    it('fits an object at a field to the union of its literals at that field', () => {
        expect(
            fits(termOf(object({ k: boolean })), termOf(object({ k: both }))),
        ).toBe(true)
    })

    it('fits two boolean fields to the four combinations', () => {
        const four = union([
            cell(true, true),
            cell(true, false),
            cell(false, true),
            cell(false, false),
        ])
        expect(
            fits(termOf(object({ a: boolean, b: boolean })), termOf(four)),
        ).toBe(true)
        const three = union([
            cell(true, true),
            cell(true, false),
            cell(false, true),
        ])
        expect(
            fits(termOf(object({ a: boolean, b: boolean })), termOf(three)),
        ).toBe(false)
    })

    it('fits a tuple position to the union of its literals at that position', () => {
        const split = union([
            list(boolean(true), string),
            list(boolean(false), string),
        ])
        expect(fits(termOf(list(boolean, string)), termOf(split))).toBe(true)
    })

    it('does not fit a list of a base to the union of the lists of its literals, because the list holds mixed lists', () => {
        const split = union([array(boolean(true)), array(boolean(false))])
        expect(fits(termOf(array(boolean)), termOf(split))).toBe(false)
    })

    it('stops the split at 1024 parts and answers no fit past the limit, because the parts of an object are a product of its fields', () => {
        const fields = (n: number) =>
            Object.fromEntries(
                Array.from({ length: n }, (_, at) => [`f${at}`, boolean]),
            )
        const halves = union([
            object({ f0: boolean(true) }),
            object({ f0: boolean(false) }),
        ])
        // ten boolean fields are 2^10 = 1024 parts, which is the limit
        expect(fits(termOf(object(fields(10))), termOf(halves))).toBe(true)
        expect(fits(termOf(object(fields(11))), termOf(halves))).toBe(false)
    })

    it('does not fit a refinement of a base to the union of its literals, because the predicate is opaque', () => {
        const refined = refine(boolean, (v): v is boolean => v === true)
        expect(fits(termOf(refined), termOf(both))).toBe(false)
    })
})

/**
 * **A `held` part fits a pattern only where the two terms are one term.** The run time reads the
 * adapter, which is an opaque function, and the decoded type of the part says nothing about the
 * stored rows that the function relates. So the type answers no fit against a base, and keeps the
 * option in both slices where it cannot see the adapter.
 */
describe('the slice of a union that holds a caller adapter', () => {
    const tag = held(string, string, {
        encode: (v: string) => v,
        decode: (v: string) => v,
    })
    const mixed = union([object({ x: tag }), object({ x: number })])

    it('keeps the adapter option in the exclusion of a base, because the part fits no base', () => {
        const rest = exclude(mixed, object({ x: string }))
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof mixed>
        >()
        const kept: Decoded<typeof rest> = { x: 's' }
        expect(kept).toEqual({ x: 's' })
        expect(failed(rest.decode({ M: { x: { S: 's' } } }))).toBe(false)
        expect(failed(rest.decode({ M: { x: { N: '1' } } }))).toBe(false)
    })

    it('extracts no adapter option for a base pattern, and the type holds no value', () => {
        const kept = extract(mixed, object({ x: string }))
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        expect(defOf(kept)).toEqual(never.def)
        expect(
            fits(termOf(object({ x: tag })), termOf(object({ x: string }))),
        ).toBe(false)
    })
})
