/**
 * An item of the entity is a call of `key`.
 *
 * The run time reads the value of a key at a path with one own property for each name, and an object
 * that is absent, or an option that lacks the name, gives `undefined`. The parameter of `key` states
 * the same read: it keeps the marks and the unions of the entity on the path. So an item of the
 * declared type fits, where the parameter does not state a name that the item may lack. A value of
 * another type at the path, and an argument with no component, stay refused.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

describe('an item of the entity is a call of key', () => {
    describe('a key of one path below an optional object', () => {
        type Owned = { petId: string; owner?: { id: string } }
        const Owners = tableEntry<Owned>()({ PK: ['petId'], SK: 'owner.id' })

        it('takes an item whose object is absent, because the run time gives undefined there', () => {
            const owned: Owned = { petId: 'p1', owner: { id: 'o1' } }
            const unowned: Owned = { petId: 'p2' }
            expect(Owners.unsafeKey('SK', owned)).toBe('o1')
            expect(Owners.unsafeKey('SK', unowned)).toBeUndefined()
            expect(Owners.unsafeKey('SK', {})).toBeUndefined()
        })

        it('refuses a value of another type at the path', () => {
            // @ts-expect-error `owner.id` is a string
            expect(Owners.unsafeKey('SK', { owner: { id: 5 } })).toBe(5)
        })

        it('keeps the type of the key for a given object', () => {
            expectTypeOf(
                Owners.unsafeKey('SK', { owner: { id: 'o' } }),
            ).toEqualTypeOf<'o'>()
            expectTypeOf(
                Owners.unsafeKey('SK', { petId: 'p', owner: { id: 'o' } }),
            ).toEqualTypeOf<'o'>()
        })
    })

    describe('a key of one path through a union where one option lacks the name', () => {
        type Doc = {
            id: string
            meta: { kind: 'a'; a: string } | { kind: 'b'; b: string }
        }
        const Docs = tableEntry<Doc>()({ PK: ['id'], SK: 'meta.a' })
        const doc = Docs.key
        const first: Doc = { id: 'd1', meta: { kind: 'a', a: 'x' } }
        const second: Doc = { id: 'd2', meta: { kind: 'b', b: 'y' } }

        it('takes an item of each option, because the run time gives undefined for the option that lacks the name', () => {
            expect(Docs.unsafeKey('SK', first)).toBe('x')
            expect(Docs.unsafeKey('SK', second)).toBeUndefined()
            expect(
                Docs.unsafeKey('SK', { id: 'd', meta: { kind: 'a', a: 'x' } }),
            ).toBe('x')
        })

        it('takes an item of each option where the option lacks a name above the last name', () => {
            type Nested = {
                id: string
                meta:
                    | { kind: 'a'; a: { id: string } }
                    | { kind: 'b'; b: string }
            }
            const Nests = tableEntry<Nested>()({ PK: ['id'], SK: 'meta.a.id' })
            const kept: Nested = {
                id: 'n1',
                meta: { kind: 'a', a: { id: 'x' } },
            }
            const lacking: Nested = { id: 'n2', meta: { kind: 'b', b: 'y' } }
            expect(Nests.unsafeKey('SK', kept)).toBe('x')
            expect(Nests.unsafeKey('SK', lacking)).toBeUndefined()
        })

        it('refuses a value of another type at the path, and an argument with no component', () => {
            // @ts-expect-error `meta.a` is a string
            const wrong = doc('SK', { meta: { kind: 'a', a: 5 } })
            expect(wrong).toBe(5)
            // @ts-expect-error the option that lacks `a` holds no number there
            const bad = doc('SK', { meta: { kind: 'b', b: 'y', a: 5 } })
            expect(bad).toBe(5)
            // @ts-expect-error `meta` is required
            const none = doc('SK', {})
            expect(none).toBeUndefined()
        })

        it('keeps the type of the key for a given option', () => {
            expectTypeOf(
                Docs.unsafeKey('SK', { id: 'd', meta: { kind: 'a', a: 'x' } }),
            ).toEqualTypeOf<'x'>()
        })
    })

    describe('a key of a composite and a transform at a path', () => {
        type Visit = { id: string; owner: { id: string; n: number } }
        const Visits = tableEntry<Visit>()({
            PK: ['id'],
            SK: ['owner.id', 'owner.n'],
        })
        type Stay = { id: string; stay?: { n: number } }
        const Stays = tableEntry<Stay>()({
            PK: ['id'],
            SK: [{ at: 'stay.n', value: (n: number) => `${n}`, default: 0 }],
        })

        it('takes an item of the entity, for a list of paths and for a transform at a path below an optional object', () => {
            const visit: Visit = { id: 'v1', owner: { id: 'x', n: 1 } }
            const kept: Stay = { id: 's1', stay: { n: 3 } }
            const absent: Stay = { id: 's2' }
            expect(Visits.unsafeKey('SK', visit)).toBe('ID#x#N#1')
            expect(Stays.unsafeKey('SK', kept)).toBe('N#3')
            expect(Stays.unsafeKey('SK', absent)).toBe('N#0')
        })

        it('refuses a value of another type at the path of the list and of the transform', () => {
            // @ts-expect-error `owner.n` is a number
            const list = Visits.unsafeKey('SK', { owner: { id: 'x', n: 'z' } })
            expect(list).toBe('ID#x#N#z')
            // @ts-expect-error the transform reads a number
            const transform = Stays.unsafeKey('SK', { stay: { n: 'z' } })
            expect(transform).toBe('N#z')
        })

        it('keeps the type of the key, with and without allowPartial', () => {
            expectTypeOf(
                Visits.unsafeKey('SK', { owner: { id: 'x', n: 1 } }),
            ).toEqualTypeOf<'ID#x#N#1'>()
            expectTypeOf(
                Visits.unsafeKey(
                    'SK',
                    { owner: { id: 'x', n: 1 } },
                    { allowPartial: true },
                ),
            ).toEqualTypeOf<'ID#x#N#1'>()
        })
    })

    describe('a match on a path where one option holds two literals', () => {
        type Placed = {
            petId: string
            meta: { status: 'IN' | 'OUT' }
            kennel: string
        }
        const Beds = tableEntry<Placed>()({
            PK: ['petId'],
            SK: {
                discriminator: 'meta.status',
                spec: { IN: ['kennel'], OUT: ['petId'] },
            },
        })
        const bed = Beds.unsafeKey
        const placed: Placed = {
            petId: 'p1',
            meta: { status: 'IN' },
            kennel: 'k1',
        }

        it('takes an item of the declared type, and the run time selects the arm by the value', () => {
            expect(Beds.unsafeKey('SK', placed)).toBe('KENNEL#k1')
            expect(
                Beds.unsafeKey('SK', { ...placed, meta: { status: 'OUT' } }),
            ).toBe('PETID#p1')
        })

        it('keeps the arm of a literal: the type states the components of that arm', () => {
            expectTypeOf(
                Beds.unsafeKey('SK', { meta: { status: 'IN' }, kennel: 'k' }),
            ).toEqualTypeOf<'KENNEL#k'>()
            expectTypeOf(
                Beds.unsafeKey('SK', { meta: { status: 'OUT' }, petId: 'p' }),
            ).toEqualTypeOf<'PETID#p'>()
            expectTypeOf(
                Beds.unsafeKey('SK', {
                    meta: { status: 'IN' },
                    kennel: 'k',
                    petId: 'p',
                }),
            ).toEqualTypeOf<'KENNEL#k'>()
        })

        it('refuses a call that lacks a component of its arm, names the other arm, or holds a value of another type', () => {
            // @ts-expect-error the arm of IN reads `kennel`
            const lacks = () => bed('SK', { meta: { status: 'IN' } })
            expect(lacks).toThrow()
            // @ts-expect-error the arm of IN reads `kennel`, not `petId`
            const o = () => bed('SK', { meta: { status: 'IN' }, petId: 'p' })
            expect(o).toThrow()
            // @ts-expect-error the literal at the path selects the arm, and OUT reads `petId`
            const w = () => bed('SK', { meta: { status: 'OUT' }, kennel: 'k' })
            expect(w).toThrow()
            // @ts-expect-error `kennel` is a string
            const wrong = bed('SK', { meta: { status: 'IN' }, kennel: 5 })
            expect(wrong).toBe('KENNEL#5')
            // @ts-expect-error an item holds the discriminator
            const none = () => bed('SK', {})
            expect(none).toThrow()
        })

        it('keeps the type of toEntry for the item of an arm', () => {
            const entry = Beds.unsafeToEntry({
                petId: 'p',
                meta: { status: 'IN' },
                kennel: 'k',
            })
            expectTypeOf(entry.PK).toEqualTypeOf<'PETID#p'>()
            expectTypeOf(entry.SK).toEqualTypeOf<'KENNEL#k'>()
        })
    })
})
