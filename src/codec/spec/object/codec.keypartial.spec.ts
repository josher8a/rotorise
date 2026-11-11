/**
 * The type of a partial key ends where a component can be absent.
 *
 * With `allowPartial` the builder stops at the first component whose value is `undefined`, `null`
 * or `''`, and prints the components before it. A template literal prints `${undefined}` as
 * `"undefined"`, so a type that prints the absent value lists a key that no row holds. The type of a
 * partial key is the set of prefixes that the builder prints: the prefix before an absent component
 * is a member, and the continuation reads the value without the absent members. A transform with a
 * default never ends the prefix, because the default fills the absent value. A full key throws at an
 * absent value, and its type does not change.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Species = 'CAT' | 'DOG'
type Breed = 'PUG' | 'LAB'

type Pet = {
    petId: string
    species: Species
    breed: Breed
    age: number
}

const Pets = tableEntry<Pet>()({ GSI1SK: ['species', 'breed', 'age'] })

const partial = { allowPartial: true } as const

/** The untyped builder: the run time builds the keys that the type must hold. */
const build = Pets.key as unknown as (
    name: 'GSI1SK',
    item: object,
    config?: object,
) => unknown

describe('the type of a partial key', () => {
    it('ends at the prefix before a component that can be absent', () => {
        const key = Pets.key(
            'GSI1SK',
            { species: 'CAT', breed: undefined as Breed | undefined, age: 3 },
            partial,
        )
        expectTypeOf(key).toEqualTypeOf<
            | 'SPECIES#CAT'
            | 'SPECIES#CAT#BREED#PUG'
            | 'SPECIES#CAT#BREED#LAB'
            | 'SPECIES#CAT#BREED#PUG#AGE#3'
            | 'SPECIES#CAT#BREED#LAB#AGE#3'
        >()
        expect(key).toBe('SPECIES#CAT')
    })

    it('holds each key that the run time builds, so the type is never narrower than the run time', () => {
        type Keys = ReturnType<
            typeof Pets.key<
                'GSI1SK',
                typeof partial,
                { species: 'CAT'; breed: Breed | undefined; age: 3 }
            >
        >
        const built: readonly (readonly [object, Keys])[] = [
            [{ species: 'CAT', age: 3 }, 'SPECIES#CAT'],
            [{ species: 'CAT', breed: null, age: 3 }, 'SPECIES#CAT'],
            [{ species: 'CAT', breed: '', age: 3 }, 'SPECIES#CAT'],
            [
                { species: 'CAT', breed: 'PUG', age: 3 },
                'SPECIES#CAT#BREED#PUG#AGE#3',
            ],
            [{ species: 'CAT', breed: 'LAB' }, 'SPECIES#CAT#BREED#LAB'],
        ]
        for (const [item, expected] of built) {
            expect(build('GSI1SK', item, partial)).toBe(expected)
        }
    })

    it("ends at a component of the type `null` or `''` as it ends at `undefined`", () => {
        type Nullable = { id: string; breed: Breed; size: 'S' | 'L' | '' }
        const Kennels = tableEntry<Nullable>()({ SK: ['breed', 'size'] })
        const key = Kennels.key(
            'SK',
            { breed: 'PUG', size: 'S' as 'S' | 'L' | '' },
            partial,
        )
        expectTypeOf(key).toEqualTypeOf<
            'BREED#PUG' | 'BREED#PUG#SIZE#S' | 'BREED#PUG#SIZE#L'
        >()
        expect(Kennels.key('SK', { breed: 'PUG', size: '' }, partial)).toBe(
            'BREED#PUG',
        )
        expect(
            Kennels.key('SK', { breed: 'PUG', size: null as never }, partial),
        ).toBe('BREED#PUG')
    })

    it('keeps the type of a full key, which throws at an absent value', () => {
        const key = Pets.key('GSI1SK', { species: 'CAT', breed: 'PUG', age: 3 })
        expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT#BREED#PUG#AGE#3'>()
        expect(() => build('GSI1SK', { species: 'CAT', age: 3 })).toThrow(
            /not found/,
        )
    })
})

describe('the type of a partial key, where a component has a default or a transform', () => {
    type Stay = {
        petId: string
        species: Species
        nickname?: string
        owner: string
    }
    const Stays = tableEntry<Stay>()({
        WITH_DEFAULT: [
            'species',
            [
                'nickname',
                (x: string | undefined) => (x ?? '').toUpperCase(),
                'NONE',
            ],
        ],
        NO_DEFAULT: ['species', ['owner', (x: string) => `o${x}`]],
    })

    it('never ends the prefix at a component with a default, because the default fills the absent value', () => {
        const key = Stays.key('WITH_DEFAULT', { species: 'CAT' }, partial)
        expect(key).toBe('SPECIES#CAT#NICKNAME#NONE')
        const member: typeof key = 'SPECIES#CAT#NICKNAME#NONE'
        expect(member).toBe(key)
    })

    it('ends the prefix at a transform with no default where the input is absent, and the type holds the prefix', () => {
        const key = Stays.key(
            'NO_DEFAULT',
            { species: 'CAT', owner: undefined as string | undefined },
            partial,
        )
        expect(key).toBe('SPECIES#CAT')
        const member: typeof key = 'SPECIES#CAT'
        expect(member).toBe(key)
    })
})

describe('the type of a partial key, where a component reads a path or sits in an arm of a match', () => {
    type Visit = {
        petId: string
        species: Species
        vaccine: { vet: 'ALICE' | 'BOB'; dose: number }
    }
    const Visits = tableEntry<Visit>()({
        SK: ['species', 'vaccine.vet', 'vaccine.dose'],
    })

    it('ends at a path component that can be absent', () => {
        const key = Visits.key(
            'SK',
            {
                species: 'CAT',
                vaccine: {
                    dose: 2,
                    vet: undefined as 'ALICE' | 'BOB' | undefined,
                },
            },
            partial,
        )
        expectTypeOf(key).toEqualTypeOf<
            | 'SPECIES#CAT'
            | 'SPECIES#CAT#VET#ALICE'
            | 'SPECIES#CAT#VET#BOB'
            | 'SPECIES#CAT#VET#ALICE#DOSE#2'
            | 'SPECIES#CAT#VET#BOB#DOSE#2'
        >()
        expect(key).toBe('SPECIES#CAT')
    })

    type Listing =
        | { kind: 'KENNEL'; id: string; breed: Breed; age: number }
        | { kind: 'FOSTER'; id: string; age: number }
    const Listings = tableEntry<Listing>()({
        PK: ['id'],
        SK: {
            discriminator: 'kind',
            spec: { KENNEL: ['age', 'breed'], FOSTER: ['age'] },
        },
    })

    it('ends at a component of an arm of a nested match', () => {
        const key = Listings.key(
            'SK',
            { kind: 'KENNEL', age: 3, breed: undefined as Breed | undefined },
            partial,
        )
        expectTypeOf(key).toEqualTypeOf<
            'AGE#3' | 'AGE#3#BREED#PUG' | 'AGE#3#BREED#LAB'
        >()
        expect(key).toBe('AGE#3')
    })
})

it('keeps the type of a key with no component that can be absent', () => {
    type Plain = { id: string; species: Species; age: number }
    const E = tableEntry<Plain>()({ SK: ['species', 'age'] })
    const key = E.key('SK', { species: 'CAT', age: 3 }, partial)
    expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT' | 'SPECIES#CAT#AGE#3'>()
})

describe('the components that a call of key must give', () => {
    const full = { species: 'CAT', breed: 'PUG', age: 3 } as const
    const shallow = { species: 'CAT', breed: 'PUG' } as const

    it('refuses a call that lacks a component with no default, in the type and at run time', () => {
        expect(() =>
            // @ts-expect-error the component `age` has no default, so a full key needs it
            Pets.key('GSI1SK', { species: 'CAT', breed: 'PUG' }),
        ).toThrow(/Attribute age not found/)
        expect(() =>
            // @ts-expect-error a depth of three keeps the component `age`, which has no default
            Pets.key('GSI1SK', { species: 'CAT', breed: 'PUG' }, { depth: 3 }),
        ).toThrow(/Attribute age not found/)
        expect(Pets.key('GSI1SK', full)).toBe('SPECIES#CAT#BREED#PUG#AGE#3')
    })

    it('keeps the requirement of a full key with `enforceBoundary` alone', () => {
        expect(() =>
            // @ts-expect-error `enforceBoundary` does not remove the component `age`
            Pets.key('GSI1SK', shallow, { enforceBoundary: true }),
        ).toThrow(/Attribute age not found/)
        expect(Pets.key('GSI1SK', full, { enforceBoundary: true })).toBe(
            'SPECIES#CAT#BREED#PUG#AGE#3',
        )
    })

    type Stay = {
        petId: string
        species: Species
        nickname?: string
        age: number
    }
    const Stays = tableEntry<Stay>()({
        SK: [
            'species',
            [
                'nickname',
                (x: string | undefined) => (x ?? '').toUpperCase(),
                'NONE',
            ],
            'age',
        ],
    })

    it('makes a component with a default optional, with no depth and inside a depth, and the key prints the default', () => {
        expect(Stays.key('SK', { species: 'CAT', age: 3 })).toBe(
            'SPECIES#CAT#NICKNAME#NONE#AGE#3',
        )
        expect(Stays.key('SK', { species: 'CAT', age: 3 }, { depth: 3 })).toBe(
            'SPECIES#CAT#NICKNAME#NONE#AGE#3',
        )
        expect(() =>
            // @ts-expect-error the component `age` has no default, even beside a component with one
            Stays.key('SK', { species: 'CAT' }),
        ).toThrow(/Attribute age not found/)
    })

    type Shelter =
        | { kind: 'KENNEL'; age: number; nickname?: string }
        | { kind: 'CATTERY'; id: string }
    const Shelters = tableEntry<Shelter>()({
        SK: {
            discriminator: 'kind',
            spec: {
                KENNEL: [
                    'age',
                    [
                        'nickname',
                        (x: string | undefined) => (x ?? '').toUpperCase(),
                        'NONE',
                    ],
                ],
                CATTERY: ['id'],
            },
        },
    })

    it('gives an arm of a match the same two facts: a component with no default is required, and a component with a default is optional', () => {
        expect(Shelters.key('SK', { kind: 'KENNEL', age: 3 })).toBe(
            'AGE#3#NICKNAME#NONE',
        )
        expect(() =>
            // @ts-expect-error the component `age` of the arm KENNEL has no default
            Shelters.key('SK', { kind: 'KENNEL' }),
        ).toThrow(/Attribute age not found/)
    })

    type Visit = {
        species: Species
        vaccine: { vet: 'ALICE' | 'BOB'; dose?: number }
    }
    const Visits = tableEntry<Visit>()({
        SK: [
            'species',
            'vaccine.vet',
            ['vaccine.dose', (x: number | undefined) => String(x ?? 0), 0],
        ],
    })

    it('gives a component at a path the same two facts', () => {
        expect(
            Visits.key('SK', { species: 'CAT', vaccine: { vet: 'ALICE' } }),
        ).toBe('SPECIES#CAT#VET#ALICE#DOSE#0')
        expect(() =>
            // @ts-expect-error the component `vaccine.vet` has no default
            Visits.key('SK', { species: 'CAT' }),
        ).toThrow(/Attribute vaccine\.vet not found/)
    })
})
