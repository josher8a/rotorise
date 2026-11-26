/**
 * The type compares an object of a union against the member that the value chooses.
 *
 * The codec of a union writes a member that admits the value, and such a member holds the literal of
 * the value at each name where the member holds a literal. So `toEntry` and `keyUpdates` refuse at run
 * time a name that only another member holds. The type states the same rule: a member that the value
 * contradicts at a literal name is no candidate. A union that holds no literal name chooses every member.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    array,
    CodecError,
    discriminatedUnion,
    item,
    number,
    object,
    string,
    union,
} from '../../codec'

const refusalOf = (given: unknown): CodecError => {
    expect(given).toBeInstanceOf(CodecError)
    return given as CodecError
}

type A = { kind: 'a'; x: number }
type B = { kind: 'b'; y: string }
type Pet = {
    petId: string
    pet: A | B
    mix: readonly (A | B)[]
    deep: { in: A | B }
}
const AB = discriminatedUnion('kind', [
    object({ kind: string('a'), x: number }),
    object({ kind: string('b'), y: string }),
])
const Pets = tableEntry<Pet>()(
    { PK: ['petId'] },
    {
        codec: item(
            object({
                petId: string,
                pet: AB,
                mix: array(AB),
                deep: object({ in: AB }),
            }),
        ),
    },
)
const base: Pet = {
    petId: 'p',
    pet: { kind: 'a', x: 1 },
    mix: [],
    deep: { in: { kind: 'a', x: 1 } },
}

type Dog = { kind: 'dog'; petId: string; bark: string }
type Cat = { kind: 'cat'; petId: string; lives: number }
const Animals = tableEntry<Dog | Cat>()(
    { PK: ['petId'] },
    {
        codec: item(
            discriminatedUnion('kind', [
                object({ kind: string('dog'), petId: string, bark: string }),
                object({ kind: string('cat'), petId: string, lives: number }),
            ]),
        ),
    },
)

describe('a name of another member is refused where the value chooses a member', () => {
    it('toEntry refuses a name of the other member in an object of a union', () => {
        const refusal = refusalOf(
            Pets.toEntry({
                ...base,
                pet: {
                    kind: 'a',
                    x: 1,
                    // @ts-expect-error the value chooses the member with kind 'a', and the member has no 'y'
                    y: 's',
                },
            }),
        )
        expect(refusal.reason).toContain(
            "no option admits this value with attributes 'kind', 'x', 'y'",
        )
        expect(refusal.message).toContain('at pet')
    })

    it('toEntry refuses a name of the other member in an element of a list of a union', () => {
        const refusal = refusalOf(
            Pets.toEntry({
                ...base,
                mix: [
                    {
                        kind: 'a',
                        x: 1,
                        // @ts-expect-error the element chooses the member with kind 'a', and the member has no 'y'
                        y: 's',
                    },
                ],
            }),
        )
        expect(refusal.reason).toContain(
            "no option admits this value with attributes 'kind', 'x', 'y'",
        )
        expect(refusal.message).toContain('mix[0]')
    })

    it('toEntry refuses a name of the other variant in an entity that is a union', () => {
        const refusal = refusalOf(
            Animals.toEntry({
                kind: 'dog',
                petId: 'p',
                bark: 'x',
                // @ts-expect-error the entity chooses the member with kind 'dog', and the member has no 'lives'
                lives: 1,
            }),
        )
        expect(refusal.reason).toBe(
            "'lives' is not an attribute this codec declares",
        )
    })

    it('toEntry refuses a name of the other member in a union below an object', () => {
        const refusal = refusalOf(
            Pets.toEntry({
                ...base,
                deep: {
                    in: {
                        kind: 'b',
                        y: 's',
                        // @ts-expect-error the value chooses the member with kind 'b', and the member has no 'x'
                        x: 1,
                    },
                },
            }),
        )
        expect(refusal.reason).toContain(
            "no option admits this value with attributes 'kind', 'y', 'x'",
        )
        expect(refusal.message).toContain('deep.in')
    })

    it('keyUpdates refuses a name of the other member in an object of a union', () => {
        const refusal = refusalOf(
            Pets.keyUpdates({
                pet: {
                    kind: 'a',
                    x: 1,
                    // @ts-expect-error the value chooses the member with kind 'a', and the member has no 'y'
                    y: 's',
                },
            }),
        )
        expect(refusal.reason).toContain(
            "no option admits this value with attributes 'kind', 'x', 'y'",
        )
        expect(refusal.message).toContain('at pet')
    })

    it('keyUpdates refuses a name of the other member in an element of a list of a union', () => {
        const refusal = refusalOf(
            Pets.keyUpdates({
                mix: [
                    {
                        kind: 'a',
                        x: 1,
                        // @ts-expect-error the element chooses the member with kind 'a', and the member has no 'y'
                        y: 's',
                    },
                ],
            }),
        )
        expect(refusal.reason).toContain(
            "no option admits this value with attributes 'kind', 'x', 'y'",
        )
        expect(refusal.message).toContain('mix[0]')
    })

    it('keyUpdates refuses a name of the other variant in an entity that is a union', () => {
        const refusal = refusalOf(
            Animals.keyUpdates({
                kind: 'dog',
                bark: 'x',
                // @ts-expect-error the change chooses the member with kind 'dog', and the member has no 'lives'
                lives: 1,
            }),
        )
        expect(refusal.reason).toBe("no attribute is declared at 'lives'")
    })

    it('keyUpdates refuses a name of the other member in a union below an object', () => {
        const refusal = refusalOf(
            Pets.keyUpdates({
                deep: {
                    in: {
                        kind: 'b',
                        y: 's',
                        // @ts-expect-error the value chooses the member with kind 'b', and the member has no 'x'
                        x: 1,
                    },
                },
            }),
        )
        expect(refusal.reason).toContain(
            "no option admits this value with attributes 'kind', 'y', 'x'",
        )
        expect(refusal.message).toContain('deep.in')
    })
})

describe('a valid value of each member is accepted', () => {
    it('toEntry builds a value of each member of a union, in an object, in a list and below an object', () => {
        for (const given of [
            base,
            { ...base, pet: { kind: 'b', y: 's' } },
            {
                ...base,
                mix: [
                    { kind: 'a', x: 1 },
                    { kind: 'b', y: 's' },
                ],
            },
            { ...base, deep: { in: { kind: 'b', y: 's' } } },
        ] satisfies Pet[]) {
            expect(Pets.toEntry(given)).not.toBeInstanceOf(CodecError)
        }
    })

    it('toEntry builds a value of each variant of an entity that is a union, in a fresh literal and in a variable', () => {
        const cat: Cat = { kind: 'cat', petId: 'p', lives: 9 }
        const dog = { kind: 'dog', petId: 'p', bark: 'x' } as const
        expect(Animals.toEntry(cat)).not.toBeInstanceOf(CodecError)
        expect(Animals.toEntry(dog)).not.toBeInstanceOf(CodecError)
        expect(
            Animals.toEntry({ kind: 'cat', petId: 'p', lives: 1 }),
        ).not.toBeInstanceOf(CodecError)
    })

    it('keyUpdates builds a change of each member of a union', () => {
        for (const given of [
            { pet: { kind: 'a', x: 1 } },
            { pet: { kind: 'b', y: 's' } },
            { mix: [{ kind: 'b', y: 's' }] },
            { deep: { in: { kind: 'b', y: 's' } } },
        ] satisfies Partial<Pet>[]) {
            expect(Pets.keyUpdates(given)).not.toBeInstanceOf(CodecError)
        }
        expect(
            Animals.keyUpdates({ kind: 'cat', lives: 1 }),
        ).not.toBeInstanceOf(CodecError)
        expect(
            Animals.keyUpdates({ kind: 'dog', bark: 'x' }),
        ).not.toBeInstanceOf(CodecError)
    })
})

describe('a union that holds no literal name chooses every member', () => {
    type Plain = { petId: string; plain: { x: number } | { y: string } }
    const Plains = tableEntry<Plain>()(
        { PK: ['petId'] },
        {
            codec: item(
                object({
                    petId: string,
                    plain: union([
                        object({ x: number }),
                        object({ y: string }),
                    ]),
                }),
            ),
        },
    )

    it('toEntry builds a value of each member, and the type accepts a name of any member', () => {
        expect(
            Plains.toEntry({ petId: 'p', plain: { x: 1 } }),
        ).not.toBeInstanceOf(CodecError)
        expect(
            Plains.toEntry({ petId: 'p', plain: { y: 's' } }),
        ).not.toBeInstanceOf(CodecError)
        // The value holds no literal, so no member drops, and the type accepts the names of both members.
        const both = Plains.toEntry({ petId: 'p', plain: { x: 1, y: 's' } })
        expect(refusalOf(both).reason).toContain('no option admits this value')
    })
})

describe('a union of members that hold the same literal drops no member', () => {
    type Same = {
        petId: string
        same: { kind: 'a'; x: number } | { kind: 'a'; y: string }
    }
    const Sames = tableEntry<Same>()(
        { PK: ['petId'] },
        {
            codec: item(
                object({
                    petId: string,
                    same: union([
                        object({ kind: string('a'), x: number }),
                        object({ kind: string('a'), y: string }),
                    ]),
                }),
            ),
        },
    )

    it('toEntry builds a value of the second member, at run time and in the type', () => {
        expect(
            Sames.toEntry({ petId: 'p', same: { kind: 'a', y: 's' } }),
        ).not.toBeInstanceOf(CodecError)
        expect(
            Sames.toEntry({ petId: 'p', same: { kind: 'a', x: 1 } }),
        ).not.toBeInstanceOf(CodecError)
    })

    it('keyUpdates builds a change of the second member, at run time and in the type', () => {
        expect(
            Sames.keyUpdates({ same: { kind: 'a', y: 's' } }),
        ).not.toBeInstanceOf(CodecError)
    })
})

describe('a candidate that holds a union of literals keeps each member that holds one of them', () => {
    type Tri =
        | { petId: string; kind: 'a'; x: number }
        | { petId: string; kind: 'b'; y: string }
        | { petId: string; z: number }
    const Tris = tableEntry<Tri>()({ PK: ['petId'] })

    it('keyUpdates builds a change whose kind is one of two literals, beside a member with no kind', () => {
        const either = { kind: 'a', x: 1 } as {
            kind: 'a' | 'b'
            x?: number
            y?: string
        }
        expect(Tris.keyUpdates(either)).toEqual({ set: {}, remove: [] })
    })
})

describe('only a literal name drops a member, because an object type is open', () => {
    type Meta =
        | { id: string; meta: { a: string } }
        | { id: string; meta: { b: number } }
    const Metas = tableEntry<Meta>()({ PK: ['id'] })

    it('keyUpdates builds a change whose object holds a name of the other member as an optional name', () => {
        const open = { a: 'x' } as { a: string; b?: number }
        expect(Metas.keyUpdates({ meta: open })).toEqual({
            set: {},
            remove: [],
        })
    })
})
