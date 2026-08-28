/**
 * Key maintenance.
 *
 * The hand-written form is fifty lines whose whole job is: when `status` or `updatedAt` change,
 * also rewrite `GSI1SK`, `GSI2PK` and `GSI2SK`. Every update path has to call it, and a new path
 * that forgot to would leave three indexes pointing at values the item no longer has — the write
 * succeeding, nothing failing, until something reads the index.
 *
 * Kept apart from encoding on purpose. Folding it into a patch would change what patching means
 * against using the schema alone, and it is not the same beast: encoding an attribute needs a
 * codec, rebuilding a key needs only the schema.
 */
import { describe, expect, it } from 'vitest'
import { literal, number, optional, string } from './codec'
import { tableEntry } from './Rotorise'

type Adoption = {
    adoptionId: string
    userId: string
    status: 'DRAFT' | 'READY' | 'PACKING' | 'CANCELED'
    updatedAt: string
    currentLegIndex: number
    adoptionGroupId?: string
}

/** A schema of the size these grow to, minus the parts that do not bear on keys. */
const Adoption = tableEntry<Adoption>()(
    {
        PK: ['adoptionId'],
        SK: ['adoptionId'],
        GSI1PK: ['userId'],
        GSI1SK: ['status', 'updatedAt'],
        GSI2PK: ['status'],
        GSI2SK: ['updatedAt'],
        GSI3PK: [['adoptionGroupId', (x?: string) => x, '']],
        GSI3SK: ['adoptionId'],
    },
    {
        codec: {
            adoptionId: string,
            userId: string,
            status: literal('DRAFT', 'READY', 'PACKING', 'CANCELED'),
            updatedAt: string,
            currentLegIndex: number,
            adoptionGroupId: optional(string),
        },
    },
)

const change = {
    status: 'PACKING',
    updatedAt: '2026-08-26T00:00:00.000Z',
} as const

describe('the keys a change invalidates', () => {
    it('rebuilds exactly the three maintainAdoptionKeys rebuilds', () => {
        const keys = Adoption.keyUpdates(change)

        expect(Object.keys(keys).sort()).toEqual(['GSI1SK', 'GSI2PK', 'GSI2SK'])
        expect(keys.GSI1SK).toEqual({
            S: 'STATUS#PACKING#UPDATEDAT#2026-08-26T00:00:00.000Z',
        })
        expect(keys.GSI2PK).toEqual({ S: 'STATUS#PACKING' })
        expect(keys.GSI2SK).toEqual({ S: 'UPDATEDAT#2026-08-26T00:00:00.000Z' })
    })

    it('leaves alone the keys the change does not touch', () => {
        const keys = Adoption.keyUpdates(change)
        // PK/SK and GSI3 come from adoptionId, GSI1PK from userId — none are changing
        for (const untouched of ['PK', 'SK', 'GSI1PK', 'GSI3PK', 'GSI3SK']) {
            expect(keys).not.toHaveProperty(untouched)
        }
    })

    it('returns nothing when no key component changes', () => {
        expect(Adoption.keyUpdates({ currentLegIndex: 1 })).toEqual({})
    })

    it('does not encode the attributes — that is the codec, separately', () => {
        expect(Adoption.codec.unsafeEncodePartial(change)).toEqual({
            status: { S: 'PACKING' },
            updatedAt: { S: '2026-08-26T00:00:00.000Z' },
        })
        // an UpdateItem is the two put together, by the caller who knows they want both
        expect({
            ...Adoption.codec.unsafeEncodePartial(change),
            ...Adoption.keyUpdates(change),
        }).toEqual({
            status: { S: 'PACKING' },
            updatedAt: { S: '2026-08-26T00:00:00.000Z' },
            GSI1SK: {
                S: 'STATUS#PACKING#UPDATEDAT#2026-08-26T00:00:00.000Z',
            },
            GSI2PK: { S: 'STATUS#PACKING' },
            GSI2SK: { S: 'UPDATEDAT#2026-08-26T00:00:00.000Z' },
        })
    })
})

describe('a component the change does not carry', () => {
    it('is a compile error, not a runtime one', () => {
        // GSI1SK is built from status *and* updatedAt; changing one alone cannot rebuild it.
        // A thunk, so this asserts the type and never runs — the runtime guard below is a backstop
        // for callers who reach this through a cast.
        // @ts-expect-error 'updatedAt' has to be supplied as context
        const _incomplete = () => Adoption.keyUpdates({ status: 'CANCELED' })
        expect(typeof _incomplete).toBe('function')
    })

    it('is still refused at runtime, for a caller who cast past the type', () => {
        const untyped = Adoption.keyUpdates as (c: object) => unknown
        expect(() => untyped({ status: 'CANCELED' })).toThrow(
            /'GSI1SK' is built from 'status', 'updatedAt'.*'updatedAt' is not given/s,
        )
    })

    it('is asked for by name, and by type', () => {
        const keys = Adoption.keyUpdates(
            { status: 'CANCELED' },
            { updatedAt: '2026-08-26T00:00:00.000Z' },
        )
        expect(keys.GSI1SK).toEqual({
            S: 'STATUS#CANCELED#UPDATEDAT#2026-08-26T00:00:00.000Z',
        })
        expect(keys.GSI2PK).toEqual({ S: 'STATUS#CANCELED' })
    })

    it('will not accept the wrong thing as context', () => {
        const _wrongContext = () =>
            Adoption.keyUpdates(
                { status: 'CANCELED' },
                // @ts-expect-error 'userId' is not what GSI1SK is missing
                { userId: 'u1' },
            )
        expect(typeof _wrongContext).toBe('function')
    })

    it('asks for nothing once the change is self-sufficient', () => {
        // no second argument, because there is nothing left to ask for
        expect(Object.keys(Adoption.keyUpdates(change))).toHaveLength(3)
    })
})
