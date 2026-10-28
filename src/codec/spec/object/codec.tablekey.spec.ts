/**
 * Saying which keys address the table.
 *
 * A key is `['adoptionId']` whether it addresses the table or an index, so nothing in a schema
 * distinguishes them — and the difference decides whether a key may be rewritten at all. DynamoDB
 * will not update a key attribute: the partition and sort key are the item's address, and changing
 * one means writing a different item.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, table, tableEntry } from '../../../Rotorise'
import { number, string } from '../../codec'

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
            /'PK' is the table's own key.*Write the new item and delete the old one/s,
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

    it('refuses a write of one component of an index key, and names the other', () => {
        // @ts-expect-error GSI1SK is built from status and updatedAt, and the write holds status alone
        const _partial = () => Adoption.keyUpdates({ status: 'CANCELED' })
        expect(typeof _partial).toBe('function')
        const untyped = Adoption.keyUpdates as (c: object) => unknown
        expect(() => untyped({ status: 'CANCELED' })).toThrow(
            /'GSI1SK' is built from 'status', 'updatedAt'.*Write 'updatedAt' in the change/s,
        )
    })

    it('asks for nothing on behalf of a table key that the write does not reach', () => {
        // GSI1SK needs status and updatedAt; PK needs adoptionId, which no component of the write joins
        const keys = Adoption.keyUpdates({
            status: 'CANCELED',
            updatedAt: '2026-08-26T00:00:00.000Z',
        })
        expect(keys.GSI1SK).toEqual({
            S: 'STATUS#CANCELED#UPDATEDAT#2026-08-26T00:00:00.000Z',
        })
    })
})

describe('a block that holds a component of a table key', () => {
    type Order = { TAG: string; id: string; buyerId: string; note: string }
    const Orders = tableEntry<Order>()({
        PK: table(['TAG', 'id']),
        SK: table(['TAG', 'id']),
        GSI1PK: ['TAG', 'buyerId'],
    })

    it('is frozen, so a write of one attribute of the block is refused', () => {
        // buyerId is tied to TAG by GSI1PK, and TAG is a component of PK
        // @ts-expect-error the block of buyerId holds TAG, a component of the table key PK
        const _frozen = () => Orders.keyUpdates({ buyerId: 'b1' })
        expect(typeof _frozen).toBe('function')
    })

    it('is frozen, so a write of the whole block is refused too', () => {
        // @ts-expect-error the write touches TAG, a component of the table key PK
        const _whole = () => Orders.keyUpdates({ buyerId: 'b1', TAG: 'T' })
        expect(typeof _whole).toBe('function')
    })

    it('names the table key and the component that joins it, at runtime', () => {
        const untyped = Orders.keyUpdates as (c: object) => unknown
        expect(() => untyped({ buyerId: 'b1' })).toThrow(
            /'PK' is the table's own key.*writes 'buyerId'.*holds 'TAG', 'id' of 'PK'.*freezes its block/s,
        )
    })

    it('leaves a write that no key reaches alone', () => {
        expect(Orders.keyUpdates({ note: 'n' })).toEqual({})
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
