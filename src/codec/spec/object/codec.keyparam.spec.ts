/**
 * **A transform reads the value of its component.** The parameter of a transform function states the
 * type of the value that the component reads, so the type refuses a parameter of another type, on the
 * element that holds the function. A parameter that accepts more than the value is allowed, because
 * the function reads each value of the component. A parameter that accepts less is refused, because
 * the run time passes a value that the function does not read. The rule holds at a name, at a name
 * that can be absent, at a name that can be `null`, at a path, and in an arm of a match.
 *
 * The constraint of the schema states the parameter of each record, and the record states the name at
 * `at`, so a function with no annotation reads the type of the value at that name. A change of the
 * constraint that types the parameter `any` removes the refusal at a name and fails these tests.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Pet = {
    petId: string
    age: number
    note?: string
    nul: string | null
    tagged: 'A' | 'B'
    owner?: { id: string }
    shelter: { code: string }
    kind: 'X' | 'Y'
}

const pet: Pet = {
    petId: 'p1',
    age: 3,
    nul: null,
    tagged: 'A',
    shelter: { code: 'c' },
    kind: 'X',
}

describe('a transform reads the value of its component: the type refuses a parameter of another type', () => {
    it('refuses a parameter of another type at a name that is always present', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `age` is a number
                { at: 'age', value: (x: string) => x },
            ],
        })
    })

    it('refuses a parameter of another type at a name that can be absent, with a default of the right type', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string
                { at: 'note', value: (x: number) => String(x), default: 'd' },
            ],
        })
    })

    it('refuses a default of another type at a name that can be absent', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string, so the default is a string
                { at: 'note', value: (x: string) => x, default: 5 },
            ],
        })
    })

    it('refuses a parameter and a default of another type at a name that can be absent', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string
                { at: 'note', value: (x: number) => String(x), default: 5 },
            ],
        })
    })

    it('refuses a parameter that accepts the default only, at a name that can be absent', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string, and the parameter reads the literal 'd' only
                { at: 'note', value: (x: 'd') => x, default: 'd' },
            ],
        })
    })

    it('refuses a parameter of another type at a name that can be null', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `nul` is a string or null
                { at: 'nul', value: (x: number) => String(x) },
            ],
        })
    })

    it('refuses a parameter that accepts one of the literals of the value only', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `tagged` is 'A' or 'B'
                { at: 'tagged', value: (x: 'A') => x },
            ],
        })
    })

    it('refuses a parameter of another type at a path', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `shelter.code` is a string
                { at: 'shelter.code', value: (x: number) => String(x) },
            ],
        })
    })

    it('refuses a parameter of another type at a path that can be absent, with a default', () => {
        tableEntry<Pet>()({
            PK: [
                {
                    // @ts-expect-error the value at `owner.id` is a string
                    at: 'owner.id',
                    // @ts-expect-error the value at `owner.id` is a string
                    value: (x: number) => String(x),
                    // @ts-expect-error the value at `owner.id` is a string
                    default: 'none',
                },
            ],
        })
    })

    it('refuses a parameter of another type in an arm of a match, at a name', () => {
        tableEntry<Pet>()({
            // @ts-expect-error the value at `age` is a number
            PK: {
                discriminator: 'kind',
                spec: {
                    X: [{ at: 'age', value: (x: string) => x }],
                    Y: ['petId'],
                },
            },
        })
    })

    it('refuses a parameter of another type in an arm of a match, at a path', () => {
        tableEntry<Pet>()({
            PK: {
                discriminator: 'kind',
                spec: {
                    X: [
                        // @ts-expect-error the value at `shelter.code` is a string
                        { at: 'shelter.code', value: (x: number) => String(x) },
                    ],
                    Y: ['petId'],
                },
            },
        })
    })

    it('refuses a parameter of another type in a case of a match', () => {
        tableEntry<Pet>()({
            PK: {
                discriminator: 'kind',
                cases: [
                    // @ts-expect-error the value at `age` is a number
                    [['X'], [{ at: 'age', value: (x: string) => x }]],
                    [['Y'], ['petId']],
                ],
            },
        })
    })

    it('refuses a parameter of another type next to a name that is right, on the element that is wrong', () => {
        tableEntry<Pet>()({
            PK: [
                'petId',
                // @ts-expect-error the value at `age` is a number
                { at: 'age', value: (x: string) => x },
            ],
        })
    })
})

describe('a transform reads the value of its component: the type accepts a parameter that accepts the value', () => {
    it('accepts a parameter that accepts more than the value, and the run time passes the value to it', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'age', value: (x: string | number) => `n${String(x)}` }],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('AGE#n3')
    })

    it('accepts a parameter of the type of the value at a name, and the run time passes the value to it', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'age', value: (x: number) => `n${x + 1}` }],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('AGE#n4')
    })

    it('accepts a parameter of the type of the value at a name that can be absent, with a default', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'note', value: (x: string) => x, default: 'd' }],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('NOTE#d')
        expect(Pets.unsafeKey('SK', { ...pet, note: 'z' })).toBe('NOTE#z')
    })
})

describe('a function with no annotation reads the type of the value of its component', () => {
    it('gives the parameter the type of the attribute at a name', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [
                {
                    at: 'age',
                    value: (x) => {
                        expectTypeOf(x).toEqualTypeOf<number>()
                        return x.toFixed(0)
                    },
                },
            ],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('AGE#3')
    })

    it('gives the parameter the type of the value without undefined, at a name that can be absent', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [
                {
                    at: 'note',
                    default: 'd',
                    value: (x) => {
                        expectTypeOf(x).toEqualTypeOf<string>()
                        return x.trim()
                    },
                },
            ],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('NOTE#d')
    })

    it('gives the parameter the type of the attribute in an arm of a match', () => {
        const Pets = tableEntry<Pet>()({
            PK: {
                discriminator: 'kind',
                spec: {
                    X: [
                        {
                            at: 'age',
                            value: (x) => {
                                expectTypeOf(x).toEqualTypeOf<number>()
                                return x.toFixed(0)
                            },
                        },
                    ],
                    Y: ['petId'],
                },
            },
        })
        expect(Pets.unsafeKey('PK', pet)).toBe('AGE#3')
    })
})
