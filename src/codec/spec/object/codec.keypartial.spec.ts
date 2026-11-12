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
 *
 * The type counts segments as the run time does. A prefix of no segment prints the empty text, and a
 * component that prints one empty segment is no prefix of no segment. A name that the call lacks has
 * the value `undefined`, so it ends the print as an absent component does. A component that is
 * never absent leaves no prefix before it.
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
                { species: 'CAT'; breed: Breed | undefined; age: 3 | undefined }
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

    it('ends the prefix at a transform with no default where the call lacks the name', () => {
        const key = Stays.key('NO_DEFAULT', { species: 'CAT' }, partial)
        expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT'>()
        expect(key).toBe('SPECIES#CAT')
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
            | 'SPECIES#CAT#VET#ALICE#DOSE#2'
            | 'SPECIES#CAT#VET#BOB#DOSE#2'
        >()
        expect(key).toBe('SPECIES#CAT')
    })

    it('ends the print at a path component that the call lacks', () => {
        const given: { species: 'CAT' } = { species: 'CAT' }
        const key = Visits.key('SK', given, partial)
        expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT'>()
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

it('gives the whole key where no component can be absent, because no prefix is a result', () => {
    type Plain = { id: string; species: Species; age: number }
    const E = tableEntry<Plain>()({ SK: ['species', 'age'] })
    const key = E.key('SK', { species: 'CAT', age: 3 }, partial)
    expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT#AGE#3'>()
    expect(key).toBe('SPECIES#CAT#AGE#3')
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

describe('the type of a partial key reads the components that the call lacks', () => {
    it('ends the print at the first component that the call lacks, and holds no later slot', () => {
        const given: { species: 'CAT' } = { species: 'CAT' }
        const key = Pets.key('GSI1SK', given, partial)
        expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT'>()
        expect(key).toBe('SPECIES#CAT')
    })

    it('ends the print at the component after the last that the call gives', () => {
        const given: { species: 'CAT'; breed: 'PUG' } = {
            species: 'CAT',
            breed: 'PUG',
        }
        const key = Pets.key('GSI1SK', given, partial)
        expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT#BREED#PUG'>()
        expect(key).toBe('SPECIES#CAT#BREED#PUG')
    })

    it('adds the boundary after the print that stops at a component that the call lacks', () => {
        const given: { species: 'CAT' } = { species: 'CAT' }
        const key = Pets.key('GSI1SK', given, {
            allowPartial: true,
            enforceBoundary: true,
        })
        expectTypeOf(key).toEqualTypeOf<'SPECIES#CAT#'>()
        expect(key).toBe('SPECIES#CAT#')
    })
})

describe('the type of a partial key holds the empty text where the first component can be absent', () => {
    type Placed = { shelterId: string; petId: string }
    const Shelters = tableEntry<Placed>()({ SK: ['shelterId', 'petId'] })
    const unnamed: Placed = { shelterId: '', petId: 'p1' }
    const named: Placed = { shelterId: 's', petId: 'p1' }

    it('holds the empty text, and the run time gives it where the first value is empty', () => {
        const key = Shelters.key('SK', unnamed, partial)
        expectTypeOf(key).toEqualTypeOf<
            '' | `SHELTERID#${string}` | `SHELTERID#${string}#PETID#${string}`
        >()
        expect(key).toBe('')
        expect(Shelters.key('SK', named, partial)).toBe('SHELTERID#s#PETID#p1')
    })

    it('holds the empty text with the boundary, because a print of no segment has no boundary', () => {
        const key = Shelters.key('SK', unnamed, {
            allowPartial: true,
            enforceBoundary: true,
        })
        expectTypeOf(key).toEqualTypeOf<
            '' | `SHELTERID#${string}#` | `SHELTERID#${string}#PETID#${string}`
        >()
        expect(key).toBe('')
    })

    it('is the empty text where the first value is the literal empty text', () => {
        type Blank = { shelterId: ''; petId: string }
        const Blanks = tableEntry<Blank>()({ SK: ['shelterId', 'petId'] })
        const blank: Blank = { shelterId: '', petId: 'p1' }
        const key = Blanks.key('SK', blank, partial)
        expectTypeOf(key).toEqualTypeOf<''>()
        expect(key).toBe('')
    })
})

describe('the type of a partial key, where a component is in the case that it can be absent', () => {
    it('ends the print before a component in the middle that can be absent, and the run time gives each member', () => {
        type Held = { species: 'CAT'; breed: 'PUG'; age: 3 }
        const Helds = tableEntry<Held>()({
            GSI1SK: ['species', 'breed', 'age'],
        })
        type Given = { species: 'CAT'; breed: 'PUG' | undefined; age: 3 }
        const without: Given = { species: 'CAT', breed: undefined, age: 3 }
        const withBreed: Given = { species: 'CAT', breed: 'PUG', age: 3 }
        const first = Helds.key('GSI1SK', without, partial)
        const second = Helds.key('GSI1SK', withBreed, partial)
        expectTypeOf(first).toEqualTypeOf<
            'SPECIES#CAT' | 'SPECIES#CAT#BREED#PUG#AGE#3'
        >()
        expectTypeOf(second).toEqualTypeOf<typeof first>()
        expect(first).toBe('SPECIES#CAT')
        expect(second).toBe('SPECIES#CAT#BREED#PUG#AGE#3')
    })

    it('ends the print before a plain component of the type `S | empty`, because the empty text is absent', () => {
        type Either = { shelterId: 'S' | ''; petId: 'p' }
        const Eithers = tableEntry<Either>()({ SK: ['shelterId', 'petId'] })
        const empty: Either = { shelterId: '', petId: 'p' }
        const present: Either = { shelterId: 'S', petId: 'p' }
        const first = Eithers.key('SK', empty, partial)
        expectTypeOf(first).toEqualTypeOf<'' | 'SHELTERID#S#PETID#p'>()
        expect(first).toBe('')
        expect(Eithers.key('SK', present, partial)).toBe('SHELTERID#S#PETID#p')
    })

    it('never ends the print before a transform of the type `S | empty`, because the transform prints the empty text', () => {
        type Either = { shelterId: 'S' | ''; petId: 'p' }
        const Eithers = tableEntry<Either>()({
            SK: [['shelterId', (value: 'S' | '') => value], 'petId'],
        })
        const empty: Either = { shelterId: '', petId: 'p' }
        const present: Either = { shelterId: 'S', petId: 'p' }
        const first = Eithers.key('SK', empty, partial)
        expectTypeOf(first).toEqualTypeOf<
            'SHELTERID#S#PETID#p' | 'SHELTERID##PETID#p'
        >()
        expect(first).toBe('SHELTERID##PETID#p')
        expect(Eithers.key('SK', present, partial)).toBe('SHELTERID#S#PETID#p')
    })

    it('never ends the print before a transform with a default on an optional attribute, because the default fills the value', () => {
        type Named = { species: 'CAT'; nickname?: string }
        const Names = tableEntry<Named>()({
            SK: [
                'species',
                [
                    'nickname',
                    (x: string | undefined) => (x ?? '').toUpperCase(),
                    'NONE',
                ],
            ],
        })
        const absent: Named = { species: 'CAT' }
        const present: Named = { species: 'CAT', nickname: 'rex' }
        const first = Names.key('SK', absent, partial)
        expectTypeOf(first).toEqualTypeOf<`SPECIES#CAT#NICKNAME#${string}`>()
        expect(first).toBe('SPECIES#CAT#NICKNAME#NONE')
        expect(Names.key('SK', present, partial)).toBe(
            'SPECIES#CAT#NICKNAME#REX',
        )
    })

    it('ends the print before a path component of the type `S | empty`, because the empty text is absent', () => {
        type Placed = { shelter: { code: 'S' | '' }; petId: 'p' }
        const Places = tableEntry<Placed>()({ SK: ['shelter.code', 'petId'] })
        const empty: Placed = { shelter: { code: '' }, petId: 'p' }
        const present: Placed = { shelter: { code: 'S' }, petId: 'p' }
        const first = Places.key('SK', empty, partial)
        expectTypeOf(first).toEqualTypeOf<'' | 'CODE#S#PETID#p'>()
        expect(first).toBe('')
        expect(Places.key('SK', present, partial)).toBe('CODE#S#PETID#p')
    })

    it('ends the print before a path component with a tag of the type `S | empty`, because the empty text is absent', () => {
        type Placed = { shelter: { code: 'S' | '' }; petId: 'p' }
        const Places = tableEntry<Placed>()({
            SK: [['shelter.code', { tag: 'AT' }], 'petId'],
        })
        const empty: Placed = { shelter: { code: '' }, petId: 'p' }
        const present: Placed = { shelter: { code: 'S' }, petId: 'p' }
        const first = Places.key('SK', empty, partial)
        expectTypeOf(first).toEqualTypeOf<'' | 'AT#S#PETID#p'>()
        expect(first).toBe('')
        expect(Places.key('SK', present, partial)).toBe('AT#S#PETID#p')
    })

    it('never ends the print before a transform of a path of the type `S | empty`, because the transform prints the empty text', () => {
        type Placed = { shelter: { code: 'S' | '' }; petId: 'p' }
        const Places = tableEntry<Placed>()({
            SK: [['shelter.code', (value: 'S' | '') => value], 'petId'],
        })
        const empty: Placed = { shelter: { code: '' }, petId: 'p' }
        const present: Placed = { shelter: { code: 'S' }, petId: 'p' }
        const first = Places.key('SK', empty, partial)
        expectTypeOf(first).toEqualTypeOf<'CODE#S#PETID#p' | 'CODE##PETID#p'>()
        expect(first).toBe('CODE##PETID#p')
        expect(Places.key('SK', present, partial)).toBe('CODE#S#PETID#p')
    })
})
