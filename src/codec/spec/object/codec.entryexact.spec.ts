/**
 * `toEntry` and `keyUpdates` check the names and the values of the input, and the type refuses the
 * input that is wrong.
 *
 * `toEntry` reads each attribute of the entity, so a text where the entity holds a number prints a
 * key that `toItem` never writes. `keyUpdates` reads a change by the names of the entity, and a
 * name that the entity does not hold is read as a dotted path by one reader and as an attribute by
 * another. The refusal lands on the input, so the wrong call does not compile.
 *
 * `Exact` compares the names at the top level only. A name in excess below an object compiles, and
 * no test here pins that case.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { number, optional, string } from '../../codec'

type Pet = { petId: string; age: number; nick?: string }
const Pets = tableEntry<Pet>()({ PK: ['petId'], GSI1SK: 'age' })

type Visit = {
    id: string
    owner: { name: string; age: number }
}
const Visits = tableEntry<Visit>()({ PK: ['id'] })

const Coded = tableEntry<Pet>()(
    { PK: ['petId'] },
    { codec: { petId: string, age: number, nick: optional(string) } },
)

type Dog = { kind: 'dog'; petId: string; bark: string }
type Cat = { kind: 'cat'; petId: string; lives: number }
const Animals = tableEntry<Dog | Cat>()({ PK: ['petId'] })

describe('toEntry refuses an item whose value or name is wrong', () => {
    it('accepts an item that holds each name with the type of the entity', () => {
        expect(Pets.toEntry({ petId: 'p', age: 3 }).PK).toBe('PETID#p')
        expect(Animals.toEntry({ kind: 'cat', petId: 'p', lives: 9 }).PK).toBe(
            'PETID#p',
        )
    })

    it('refuses a text where the entity holds a number', () => {
        const refused = () =>
            // @ts-expect-error the type of the value is wrong
            Pets.toEntry({ petId: 'p', age: '3' })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses an item that lacks a name of the entity', () => {
        const refused = () =>
            // @ts-expect-error the name age is missing
            Pets.toEntry({ petId: 'p' })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a wrong value below an object', () => {
        const refused = () =>
            Visits.toEntry({
                id: 'v',
                // @ts-expect-error the type of the value below the object is wrong
                owner: { name: 'a', age: '1' },
            })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a missing name below an object', () => {
        const refused = () =>
            Visits.toEntry({
                id: 'v',
                // @ts-expect-error the name age is missing below the object
                owner: { name: 'a' },
            })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a wrong value at an entry with a codec', () => {
        const refused = () =>
            // @ts-expect-error the type of the value is wrong
            Coded.toEntry({ petId: 'p', age: '3' })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a missing name at an entry with a codec', () => {
        const refused = () =>
            // @ts-expect-error the name age is missing
            Coded.toEntry({ petId: 'p' })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a member of a union entity that lacks a name of that member', () => {
        const refused = () =>
            // @ts-expect-error the name bark is missing from the dog
            Animals.toEntry({ kind: 'dog', petId: 'p' })
        expect(refused).toBeTypeOf('function')
    })
})

type Owned = {
    petId: string
    note: string
    owner: { name: string; nick: string }
}
const Owned = tableEntry<Owned>()({
    PK: ['petId'],
    GSI1PK: ['owner.name'],
})

describe('keyUpdates refuses a change with a name that the entity does not hold', () => {
    it('accepts a change that holds the names of the entity', () => {
        expect(Owned.keyUpdates({ note: 'n' }).set).toEqual({})
    })

    it('refuses a dotted name that the entity does not hold, alone, as the weak type of the change already refuses', () => {
        const refused = () =>
            // @ts-expect-error the entity holds owner, and owner.nick is no attribute
            Owned.keyUpdates({ 'owner.nick': 'bob' })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a dotted name that the entity does not hold, beside a name that it holds', () => {
        const refused = () =>
            // @ts-expect-error the entity holds note, and owner.name is no attribute
            Owned.keyUpdates({ note: 'n', 'owner.name': 'bob' })
        expect(refused).toBeTypeOf('function')
    })

    it('refuses a name that no member of a union entity holds', () => {
        const refused = () =>
            // @ts-expect-error no member of the union holds the name legs
            Animals.keyUpdates({ kind: 'dog', legs: 4 })
        expect(refused).toBeTypeOf('function')
    })
})
