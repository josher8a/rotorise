/**
 * **A transform reads the value of its component.** The parameter of a transform function states the
 * type of the value that the component reads, so the type refuses a parameter of another type, on the
 * element that holds the function. A parameter that accepts more than the value is allowed, because
 * the function reads each value of the component. A parameter that accepts less is refused, because
 * the run time passes a value that the function does not read. The rule holds at a name, at a name
 * that can be absent, at a name that can be `null`, at a path, and in an arm of a match.
 *
 * The constraint of the schema states the parameter of each function arm. A change of the constraint
 * that types the parameter `any`, so that the arms share one signature, removes the refusal at a name
 * and fails these tests.
 */
import { describe, expect, it } from 'vitest'
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
                ['age', (x: string) => x],
            ],
        })
    })

    it('refuses a parameter of another type at a name that can be absent, with a default of the right type', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string
                ['note', (x: number) => String(x), 'd'],
            ],
        })
    })

    it('refuses a default of another type at a name that can be absent', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string, so the default is a string
                ['note', (x: string) => x, 5],
            ],
        })
    })

    it('refuses a parameter and a default of another type at a name that can be absent', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string
                ['note', (x: number) => String(x), 5],
            ],
        })
    })

    it('refuses a parameter that accepts the default only, at a name that can be absent', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `note` is a string, and the parameter reads the literal 'd' only
                ['note', (x: 'd') => x, 'd'],
            ],
        })
    })

    it('refuses a parameter of another type at a name that can be null', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `nul` is a string or null
                ['nul', (x: number) => String(x)],
            ],
        })
    })

    it('refuses a parameter that accepts one of the literals of the value only', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `tagged` is 'A' or 'B'
                ['tagged', (x: 'A') => x],
            ],
        })
    })

    it('refuses a parameter of another type at a path', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `shelter.code` is a string
                ['shelter.code', (x: number) => String(x)],
            ],
        })
    })

    it('refuses a parameter of another type at a path that can be absent, with a default', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error the value at `owner.id` is a string
                ['owner.id', (x: number) => String(x), 'none'],
            ],
        })
    })

    it('refuses a parameter of another type in an arm of a match, at a name', () => {
        tableEntry<Pet>()({
            // @ts-expect-error the value at `age` is a number
            PK: {
                discriminator: 'kind',
                spec: {
                    X: [['age', (x: string) => x]],
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
                    // @ts-expect-error the value at `shelter.code` is a string
                    X: [['shelter.code', (x: number) => String(x)]],
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
                    [['X'], [['age', (x: string) => x]]],
                    [['Y'], ['petId']],
                ],
            },
        })
    })

    it('refuses a parameter of another type next to a name that is right', () => {
        tableEntry<Pet>()({
            PK: [
                // @ts-expect-error a list that holds a wrong parameter is refused as a whole
                'petId',
                // @ts-expect-error the value at `age` is a number
                ['age', (x: string) => x],
            ],
        })
    })
})

describe('a transform reads the value of its component: the type accepts a parameter that accepts the value', () => {
    it('accepts a parameter that accepts more than the value, and the run time passes the value to it', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [['age', (x: string | number) => `n${String(x)}`]],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('AGE#n3')
    })

    it('accepts a parameter of the type of the value at a name, and the run time passes the value to it', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [['age', (x: number) => `n${x + 1}`]],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('AGE#n4')
    })

    it('accepts a parameter of the type of the value at a name that can be absent, with a default', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [['note', (x: string) => x, 'd']],
        })
        expect(Pets.unsafeKey('SK', pet)).toBe('NOTE#d')
        expect(Pets.unsafeKey('SK', { ...pet, note: 'z' })).toBe('NOTE#z')
    })
})
