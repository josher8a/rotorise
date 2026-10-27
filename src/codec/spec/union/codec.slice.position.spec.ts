/**
 * A pattern reaches a position of a fixed list.
 *
 * A fixed list is a product of its positions, as an object is a product of its keys. The kept part and
 * the cover read a position as they read a key. An `array` has no declared position, so a fixed pattern
 * against an array is refused.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import type { Decoded } from '../../codec'
import {
    array,
    decimal,
    exclude,
    extract,
    list,
    meet,
    object,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'
import type { Term } from '../../term'

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
type Pet = Decoded<typeof pet>
const plan = union([
    object({ type: string('ONE'), route: list(pet) }),
    object({ type: string('TWO'), route: list(pet, pet), note: string }),
])

const petRow = (category: string, status: string): AttributeValue => ({
    M: {
        category: { S: category },
        ...(category === 'DOG'
            ? { breed: { S: 'beagle' } }
            : { coat: { S: 'tabby' } }),
        status: { S: status },
        [{ AVAILABLE: 'price', PENDING: 'deposit', SOLD: 'soldFor' }[
            status
        ] as string]: { N: '5' },
    },
})
const pets = ['DOG', 'CAT'].flatMap((c) =>
    ['AVAILABLE', 'PENDING', 'SOLD'].map((s) => petRow(c, s)),
)
const valid: AttributeValue[] = [
    ...pets.map((p) => ({ M: { type: { S: 'ONE' }, route: { L: [p] } } })),
    ...pets.flatMap((a) =>
        pets.map((b) => ({
            M: { type: { S: 'TWO' }, route: { L: [a, b] }, note: { S: 'n' } },
        })),
    ),
]
const pool: AttributeValue[] = [
    ...valid,
    ...valid.flatMap((row) => {
        const m = (row as { M: Record<string, AttributeValue> }).M
        const route = (m.route as { L: AttributeValue[] }).L
        return [
            { M: { ...m, route: { L: [...route, route[0]] } } },
            { M: { ...m, route: { L: route.slice(1) } } },
            { M: { ...m, route: { L: [{ S: 'oops' }, ...route.slice(1)] } } },
            { M: { ...m, type: { S: 'THREE' } } },
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

describe('a pattern reaches a position of a fixed list as it reaches a key', () => {
    const pattern = object({
        route: list(
            object({ category: string('DOG') }),
            object({ status: string('AVAILABLE') }),
        ),
    })
    const kept = extract(plan, pattern)
    const rest = exclude(plan, pattern)

    it('keeps the option of that arity, with a narrower union at each position', () => {
        expect(optionsOf(kept)).toHaveLength(1)
        type Model = {
            readonly type: 'TWO'
            readonly route: readonly [
                Extract<Pet, { readonly category: 'DOG' }>,
                Extract<Pet, { readonly status: 'AVAILABLE' }>,
            ]
            readonly note: string
        }
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<Model>()
    })

    it('rejects with the other arity whole and one option for each split position', () => {
        expect(optionsOf(rest)).toHaveLength(3)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            | { readonly type: 'ONE'; readonly route: readonly [Pet] }
            | {
                  readonly type: 'TWO'
                  readonly route: readonly [
                      Extract<Pet, { readonly category: 'CAT' }>,
                      Pet,
                  ]
                  readonly note: string
              }
            | {
                  readonly type: 'TWO'
                  readonly route: readonly [
                      Extract<Pet, { readonly category: 'DOG' }>,
                      Exclude<Pet, { readonly status: 'AVAILABLE' }>,
                  ]
                  readonly note: string
              }
        >()
    })

    it('splits every valid row between the extraction and the exclusion, as the original reads it', () => {
        for (const row of valid) {
            const inKept = decodes(kept, row)
            const inRest = decodes(rest, row)
            expect(inKept === undefined, JSON.stringify(row)).not.toBe(
                inRest === undefined,
            )
            expect(inKept ?? inRest).toEqual(decodes(plan, row))
        }
    })

    it('reads no pool value that the original does not read, and writes what it reads', () => {
        let read = 0
        for (const row of pool) {
            const was = decodes(plan, row)
            const now = decodes(kept, row) ?? decodes(rest, row)
            expect(now, JSON.stringify(row)).toEqual(was)
            if (now !== undefined) {
                read++
                expect(
                    (decodes(kept, row) ? kept : rest).unsafeEncode(
                        now as never,
                    ),
                ).toEqual(row)
            }
        }
        expect(read).toBe(valid.length)
    })

    it('keeps an option whole where each position fits whole', () => {
        const whole = extract(plan, object({ route: list(pet, pet) }))
        expect(optionsOf(whole)).toHaveLength(1)
        expect(optionsOf(whole)[0]).toBe(optionsOf(plan)[1])
    })

    it('takes a slice of the field as the pattern at a position', () => {
        const dogs = extract(pet, object({ category: string('DOG') }))
        const one = extract(plan, object({ route: list(dogs) }))
        expectTypeOf<Decoded<typeof one>>().toEqualTypeOf<{
            readonly type: 'ONE'
            readonly route: readonly [
                Extract<Pet, { readonly category: 'DOG' }>,
            ]
        }>()
    })
})

describe('a list of free length has no positions to reach', () => {
    const many = union([object({ route: array(pet) })])

    it('extracts never for a fixed pattern, because an array declares no position', () => {
        const fixed = extract(
            many,
            object({ route: list(object({ category: string('DOG') })) }),
        )
        expectTypeOf<Decoded<typeof fixed>>().toEqualTypeOf<never>()
        expect(fixed.def.kind).toBe('never')
    })
})

describe('a pattern at a position that no member fits extracts never, as at a key', () => {
    it('extracts never for a key that no member of the position declares', () => {
        const typo = extract(
            plan,
            object({ route: list(object({ nope: string('x') })) }),
        )
        expectTypeOf<Decoded<typeof typo>>().toEqualTypeOf<never>()
        expect(typo.def.kind).toBe('never')
    })

    it('extracts never for a literal that no member of the position pins at that base', () => {
        const wrongBase = extract(
            plan,
            object({ route: list(object({ category: decimal('1') })) }),
        )
        expectTypeOf<Decoded<typeof wrongBase>>().toEqualTypeOf<never>()
        expect(wrongBase.def.kind).toBe('never')
    })

    it('extracts never for a key that no member declares at a position of a list held at a position', () => {
        const held = union([
            object({
                r: list(
                    list(
                        union([
                            object({ category: string('DOG'), breed: string }),
                            object({ category: string('CAT'), coat: string }),
                        ]),
                    ),
                ),
            }),
        ])
        const typo = extract(
            held,
            object({ r: list(list(object({ nope: string('x') }))) }),
        )
        expectTypeOf<Decoded<typeof typo>>().toEqualTypeOf<never>()
        expect(typo.def.kind).toBe('never')
        const wrongBase = extract(
            held,
            object({ r: list(list(object({ category: decimal('1') }))) }),
        )
        expectTypeOf<Decoded<typeof wrongBase>>().toEqualTypeOf<never>()
        expect(wrongBase.def.kind).toBe('never')
    })
})

describe('a union pattern splits an option at a position as it splits one at a field', () => {
    const Dog = object({ category: string('DOG'), breed: string })
    const Cat = object({ category: string('CAT'), coat: string })
    type Dog = Decoded<typeof Dog>
    type Cat = Decoded<typeof Cat>
    const dog: AttributeValue = {
        M: { category: { S: 'DOG' }, breed: { S: 'beagle' } },
    }
    const cat: AttributeValue = {
        M: { category: { S: 'CAT' }, coat: { S: 'tabby' } },
    }

    it('keeps the option whole where the pattern members cover its field', () => {
        const held = union([object({ x: union([Dog, Cat]) })])
        const kept = extract(
            held,
            union([object({ x: Dog }), object({ x: Cat })]),
        )
        expect(optionsOf(kept)).toHaveLength(1)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly x: Dog | Cat
        }>()
    })

    it('keeps the option whole where the pattern members cover its position', () => {
        const held = union([object({ r: list(union([Dog, Cat])) })])
        const pattern = union([
            object({ r: list(Dog) }),
            object({ r: list(Cat) }),
        ])
        const kept = extract(held, pattern)
        expect(optionsOf(kept)).toHaveLength(1)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly r: readonly [Dog | Cat]
        }>()
        // the members cover the position, so nothing is rejected
        expect(optionsOf(exclude(held, pattern))).toHaveLength(0)
        for (const row of [dog, cat]) {
            const value = { M: { r: { L: [row] } } } as AttributeValue
            expect(decodes(kept, value)).toEqual(decodes(held, value))
        }
    })

    it('keeps the one pattern member of the arity of each option', () => {
        const held = union([
            object({ r: list(union([Dog, Cat])) }),
            object({ r: list(union([Dog, Cat]), union([Dog, Cat])) }),
        ])
        const pattern = union([
            object({ r: list(Dog) }),
            object({ r: list(Dog, Cat) }),
        ])
        const kept = extract(held, pattern)
        const rest = exclude(held, pattern)
        expect(optionsOf(kept)).toHaveLength(2)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            { readonly r: readonly [Dog] } | { readonly r: readonly [Dog, Cat] }
        >()
        const rows = [
            [dog],
            [cat],
            [dog, dog],
            [dog, cat],
            [cat, dog],
            [cat, cat],
        ].map((r) => ({ M: { r: { L: r } } }) as AttributeValue)
        for (const row of rows) {
            const inKept = decodes(kept, row)
            const inRest = decodes(rest, row)
            expect(inKept === undefined, JSON.stringify(row)).not.toBe(
                inRest === undefined,
            )
            expect(inKept ?? inRest).toEqual(decodes(held, row))
        }
        // only the rows that the pattern names are kept
        expect(
            rows.filter((row) => decodes(kept, row) !== undefined),
        ).toHaveLength(2)
    })

    it('splits one option at a field and at a position by one union pattern', () => {
        const held = union([
            object({ x: union([Dog, Cat]), r: list(union([Dog, Cat])) }),
        ])
        const pattern = union([
            object({ x: Dog, r: list(Cat) }),
            object({ x: Cat, r: list(Dog) }),
        ])
        const kept = extract(held, pattern)
        const rest = exclude(held, pattern)
        expect(optionsOf(kept)).toHaveLength(2)
        expect(optionsOf(rest)).toHaveLength(2)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            | { readonly x: Dog; readonly r: readonly [Cat] }
            | { readonly x: Cat; readonly r: readonly [Dog] }
        >()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            | { readonly x: Dog; readonly r: readonly [Dog] }
            | { readonly x: Cat; readonly r: readonly [Cat] }
        >()
        for (const x of [dog, cat]) {
            for (const r of [dog, cat]) {
                const row = { M: { x, r: { L: [r] } } } as AttributeValue
                const inKept = decodes(kept, row)
                const inRest = decodes(rest, row)
                expect(inKept === undefined, JSON.stringify(row)).not.toBe(
                    inRest === undefined,
                )
                expect(inKept ?? inRest).toEqual(decodes(held, row))
            }
        }
    })

    it('keeps a list held at a position of a list whole, as a position of a list', () => {
        const held = union([object({ r: list(list(union([Dog, Cat]))) })])
        const pattern = union([
            object({ r: list(list(Dog)) }),
            object({ r: list(list(Cat)) }),
        ])
        const kept = extract(held, pattern)
        expect(optionsOf(kept)).toHaveLength(1)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<{
            readonly r: readonly [readonly [Dog | Cat]]
        }>()
        expect(optionsOf(exclude(held, pattern))).toHaveLength(0)
        for (const row of [dog, cat]) {
            const value = {
                M: { r: { L: [{ L: [row] }] } },
            } as AttributeValue
            expect(decodes(kept, value)).toEqual(decodes(held, value))
        }
    })
})
