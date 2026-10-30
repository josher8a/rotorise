/**
 * The condition of a query, on the table or on a secondary index.
 *
 * A query selects one partition by the whole partition key, and narrows the partition by a
 * condition on the sort key. The `key` option names the keys of the table, and the `indexes` option
 * names the keys of each index, so the entry knows which keys a query on each one reads. The
 * condition holds names and encoded values, and an expression library builds the expression.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { KeyCondition } from '../../../Rotorise'
import { RotoriseError, tableEntry } from '../../../Rotorise'

type Pet = {
    petId: string
    shelterId: string
    status: 'AVAILABLE' | 'ADOPTED'
    updatedAt: string
    age: number
}

const Pets = tableEntry<Pet>()(
    {
        PK: ['petId'],
        SK: ['petId'],
        GSI1PK: ['shelterId'],
        GSI1SK: ['status', 'updatedAt'],
        GSI2SK: 'age',
    },
    {
        key: { partition: 'PK', sort: 'SK' },
        indexes: {
            GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' },
            GSI2: { partition: 'GSI1PK', sort: 'GSI2SK' },
            BY_SHELTER: { partition: 'GSI1PK' },
        },
    },
)

describe('a query on the table reads the keys that the key option names', () => {
    it('gives the partition key and the whole sort key, and names no index', () => {
        const condition = Pets.keyCondition({ petId: 'p1' })
        expect(condition).toEqual({
            partition: { name: 'PK', value: { S: 'PETID#p1' } },
            sort: { name: 'SK', equals: { S: 'PETID#p1' } },
        })
        expect('index' in condition).toBe(false)
    })
})

describe('a query on an index reads the keys that the index names', () => {
    it('gives equals where the attributes give the whole sort key', () => {
        expect(
            Pets.keyCondition('GSI1', {
                shelterId: 's1',
                status: 'AVAILABLE',
                updatedAt: '2026',
            }),
        ).toEqual({
            index: 'GSI1',
            partition: { name: 'GSI1PK', value: { S: 'SHELTERID#s1' } },
            sort: {
                name: 'GSI1SK',
                equals: { S: 'STATUS#AVAILABLE#UPDATEDAT#2026' },
            },
        })
    })

    it('gives beginsWith with the boundary where the attributes give a leading part of the sort key', () => {
        // the boundary keeps STATUS#AVAILABLE from selecting STATUS#AVAILABLE_SOON
        expect(
            Pets.keyCondition('GSI1', { shelterId: 's1', status: 'AVAILABLE' })
                .sort,
        ).toEqual({ name: 'GSI1SK', beginsWith: { S: 'STATUS#AVAILABLE#' } })
    })

    it('gives no sort condition where the attributes hold no component of the sort key', () => {
        const condition = Pets.keyCondition('GSI1', { shelterId: 's1' })
        expect(condition).toEqual({
            index: 'GSI1',
            partition: { name: 'GSI1PK', value: { S: 'SHELTERID#s1' } },
        })
    })

    it('a sort key of one number attribute is an N condition, so the query orders by number', () => {
        expect(
            Pets.keyCondition('GSI2', { shelterId: 's1', age: 3 }).sort,
        ).toEqual({ name: 'GSI2SK', equals: { N: '3' } })
    })

    it('an index with no sort key gives no sort condition', () => {
        expect(
            Pets.keyCondition('BY_SHELTER', { shelterId: 's1', age: 3 }),
        ).toEqual({
            index: 'BY_SHELTER',
            partition: { name: 'GSI1PK', value: { S: 'SHELTERID#s1' } },
        })
    })

    it('the type carries the index and the names of its keys', () => {
        const condition = Pets.keyCondition('GSI1', { shelterId: 's1' })
        expectTypeOf(condition.index).toEqualTypeOf<'GSI1'>()
        expectTypeOf(condition.partition.name).toEqualTypeOf<'GSI1PK'>()
        expectTypeOf(
            Pets.keyCondition('BY_SHELTER', { shelterId: 's1' }),
        ).not.toHaveProperty('sort')
        // @ts-expect-error the indexes option declares no such index
        const _unknown = () => Pets.keyCondition('GSI9', { shelterId: 's1' })
        expect(typeof _unknown).toBe('function')
    })
})

describe('one adapter reads the condition of every query', () => {
    it('the condition of each index is a KeyCondition, and its sort condition stays readable', () => {
        const sortOf = (condition: KeyCondition) => condition.sort
        expect(
            sortOf(
                Pets.keyCondition('GSI1', {
                    shelterId: 's1',
                    status: 'ADOPTED',
                }),
            ),
        ).toEqual({ name: 'GSI1SK', beginsWith: { S: 'STATUS#ADOPTED#' } })
        expect(
            sortOf(Pets.keyCondition('BY_SHELTER', { shelterId: 's1' })),
        ).toBe(undefined)
    })
})

describe('a query that selects no partition or no prefix is refused', () => {
    it('refuses a partition key that lacks a component, because a query reads one whole partition', () => {
        expect(() =>
            Pets.keyCondition('GSI1', { status: 'AVAILABLE' }),
        ).toThrow(RotoriseError)
    })

    it('refuses a later sort component without the first, because no prefix selects it', () => {
        expect(() =>
            Pets.keyCondition('GSI1', { shelterId: 's1', updatedAt: '2026' }),
        ).toThrow("'GSI1SK' gives no key and no prefix for these attributes")
    })

    it('refuses an index name that the indexes option does not declare', () => {
        const untyped = Pets.keyCondition as (
            index: string,
            attributes: object,
        ) => unknown
        expect(() => untyped('GSI9', { shelterId: 's1' })).toThrow(
            "the indexes option declares no index 'GSI9'",
        )
    })
})

describe('construction refuses roles of an index that address no item', () => {
    it('refuses an index role that names no key of the schema', () => {
        expect(() =>
            tableEntry<Pet>()(
                { PK: ['petId'] },
                // @ts-expect-error GSI1PK is no key of the schema
                { indexes: { GSI1: { partition: 'GSI1PK' } } },
            ),
        ).toThrow(
            "the index 'GSI1' names 'GSI1PK', which is no key of the schema",
        )
    })

    it('refuses one key in the two roles of an index', () => {
        expect(() =>
            tableEntry<Pet>()(
                { PK: ['petId'], GSI1PK: ['shelterId'] },
                {
                    indexes: {
                        // @ts-expect-error the sort key and the partition key are one key
                        GSI1: { partition: 'GSI1PK', sort: 'GSI1PK' },
                    },
                },
            ),
        ).toThrow(
            "the index 'GSI1' names 'GSI1PK' as the sort key and the partition key",
        )
    })
})
