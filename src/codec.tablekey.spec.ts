/**
 * Saying which keys address the table.
 *
 * A key is `['adoptionId']` whether it addresses the table or an index, so nothing in a schema
 * distinguishes them — and the difference decides whether a key may be rewritten at all. DynamoDB
 * will not update a key attribute: the partition and sort key are the item's address, and changing
 * one means writing a different item.
 */
import { describe, expect, it } from 'vitest'
import { number, string } from './codec'
import { RotoriseError, table, tableEntry } from './Rotorise'

type Adoption = {
    adoptionId: string
    userId: string
    status: 'DRAFT' | 'PACKING' | 'CANCELED'
    updatedAt: string
    currentLegIndex: number
}

const Adoption = tableEntry<Adoption>()(
    {
        PK: table(['adoptionId']),
        SK: table(['adoptionId']),
        GSI1PK: ['userId'],
        GSI1SK: ['status', 'updatedAt'],
        GSI2PK: ['status'],
    },
    {
        codec: {
            adoptionId: string,
            userId: string,
            status: string('DRAFT', 'PACKING', 'CANCELED'),
            updatedAt: string,
            currentLegIndex: number,
        },
    },
)

describe('a change that would move the item', () => {
    it('is a compile error', () => {
        // PK and SK are built from adoptionId; rewriting it is a different item
        // @ts-expect-error this changes an attribute the table key is built from
        const _moves = () => Adoption.keyUpdates({ adoptionId: 'other' })
        expect(typeof _moves).toBe('function')
    })

    it('is refused at runtime too, and says what to do instead', () => {
        const untyped = Adoption.keyUpdates as (c: object) => unknown
        expect(() => untyped({ adoptionId: 'other' })).toThrow(RotoriseError)
        expect(() => untyped({ adoptionId: 'other' })).toThrow(
            /'PK' is the table's own key.*write the new item and delete the old one/s,
        )
    })
})

describe('index keys are still rebuilt', () => {
    it('rebuilds them and never emits a table key', () => {
        const keys = Adoption.keyUpdates({
            status: 'CANCELED',
            updatedAt: '2026-08-26T00:00:00.000Z',
        })
        expect(Object.keys(keys).sort()).toEqual(['GSI1SK', 'GSI2PK'])
        expect(keys).not.toHaveProperty('PK')
        expect(keys).not.toHaveProperty('SK')
    })

    it('does not ask for context on behalf of a table key', () => {
        // GSI1SK needs status and updatedAt; PK needs adoptionId, which is nobody's business here
        const keys = Adoption.keyUpdates(
            { status: 'CANCELED' },
            { updatedAt: '2026-08-26T00:00:00.000Z' },
        )
        expect(keys.GSI1SK).toEqual({
            S: 'STATUS#CANCELED#UPDATEDAT#2026-08-26T00:00:00.000Z',
        })
    })
})

describe('the Key of a request', () => {
    it('builds just the table keys, replacing a hand-written entryKeys', () => {
        expect(Adoption.keys({ adoptionId: 'q1' })).toEqual({
            PK: { S: 'ADOPTIONID#q1' },
            SK: { S: 'ADOPTIONID#q1' },
        })
    })

    it('has no no-names form when the schema never said which keys those are', () => {
        const Unmarked = tableEntry<Adoption>()({ PK: ['adoptionId'] })
        // @ts-expect-error the schema does not say which keys address the table
        const _noTableKeys = () => Unmarked.keys({ adoptionId: 'q1' })
        expect(typeof _noTableKeys).toBe('function')
        // naming them still works, because that asks nothing of the schema
        expect(Unmarked.keys(['PK'], { adoptionId: 'q1' })).toEqual({
            PK: { S: 'ADOPTIONID#q1' },
        })
    })
})

describe('a schema that marks nothing', () => {
    const Unmarked = tableEntry<Adoption>()({
        PK: ['adoptionId'],
        GSI2PK: ['status'],
    })

    it('keeps rebuilding everything, as before', () => {
        // marking is opt-in, so an existing schema is unchanged — including the
        // unsound part, where PK is rebuilt and DynamoDB would reject the update
        expect(Unmarked.keyUpdates({ adoptionId: 'q2' })).toEqual({
            PK: { S: 'ADOPTIONID#q2' },
        })
    })
})
