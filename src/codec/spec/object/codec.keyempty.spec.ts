/**
 * A full key is never empty, and a partial key may be.
 *
 * DynamoDB stores no empty key, so a full key that prints the empty string addresses no item. A key
 * of one attribute has no part, so its key is full, and an empty value refuses on every route. A list
 * of components prints the name of each component, so a full key of a list is empty only where
 * a transform prints a value with no tag, and the value is empty. A partial
 * key is a call with `allowPartial`, or with a `depth` below the count of components, and the public
 * `key` returns it as a `begins_with` prefix, so the empty prefix is the answer where no part is
 * present.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'

type Pet = { petId: string; shelterId: string; nick: string }

const Pets = tableEntry<Pet>()(
    {
        PK: ['petId'],
        SK: 'nick',
        GSI1PK: ['shelterId'],
        GSI1SK: 'nick',
        GSI2SK: [['petId', (_id: string) => '']],
        GSI3SK: [['nick', (text: string) => ({ value: text })]],
    },
    {
        key: { partition: 'PK', sort: 'SK' },
        indexes: {
            GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' },
            GSI2: { partition: 'GSI1PK', sort: 'GSI2SK' },
            GSI3: { partition: 'GSI1PK', sort: 'GSI3SK' },
        },
    },
)

const unnamed = { petId: 'p1', shelterId: 's1', nick: '' }

describe('a full key of one attribute refuses the empty string, on every route', () => {
    it('refuses in key, and names the key and the attribute', () => {
        expect(() => Pets.key('SK', unnamed)).toThrow(RotoriseError)
        expect(() => Pets.key('SK', unnamed)).toThrow(
            "Key SK: the attribute 'nick' is empty",
        )
    })

    it('refuses in key under allowPartial, because one attribute has no part', () => {
        expect(() =>
            // @ts-expect-error the type gives a key of one attribute no config, and a caller with no type passes one
            Pets.key('SK', unnamed, { allowPartial: true }),
        ).toThrow("the attribute 'nick' is empty")
    })

    it('refuses in keys and in toEntry', () => {
        expect(() => Pets.keys(['SK'], unnamed)).toThrow(
            "the attribute 'nick' is empty",
        )
        expect(() => Pets.toEntry(unnamed)).toThrow(
            "the attribute 'nick' is empty",
        )
    })

    it('refuses in keyUpdates, on a key that is not a key of the table', () => {
        const Indexed = tableEntry<Pet>()(
            { PK: ['petId'], GSI1SK: 'nick' },
            { key: { partition: 'PK' } },
        )
        expect(() => Indexed.keyUpdates({ nick: '' })).toThrow(
            "cannot be rebuilt from this change: Key GSI1SK: the attribute 'nick' is empty",
        )
    })

    it('refuses a condition on the sort key, and does not drop the condition', () => {
        expect(() => Pets.keyCondition('GSI1', unnamed)).toThrow(
            "the attribute 'nick' is empty",
        )
    })
})

describe('a full key of a list of components prints the name of a tagged component', () => {
    it('prints the name of a component whose transform prints the empty string', () => {
        expect(Pets.key('GSI2SK', unnamed)).toBe('PETID#')
    })
})

describe('a full key whose print is the empty text refuses, as a key of one attribute does', () => {
    it('refuses where one component prints a value with no tag and the value is empty', () => {
        expect(() => Pets.key('GSI3SK', unnamed)).toThrow(RotoriseError)
        expect(() => Pets.key('GSI3SK', unnamed)).toThrow(
            'Key GSI3SK: the print of the components is empty',
        )
    })

    it('gives the empty prefix where the same print is a partial key', () => {
        expect(Pets.key('GSI3SK', unnamed, { depth: 0 })).toBe('')
    })
})

describe('a partial key may be the empty string, because it is a begins_with prefix', () => {
    it('is empty at a depth of 0', () => {
        expect(Pets.key('PK', unnamed, { depth: 0 })).toBe('')
    })

    it('is empty under allowPartial where the first part is absent', () => {
        expect(Pets.key('PK', {} as never, { allowPartial: true })).toBe('')
    })

    it('is not empty where a part is present', () => {
        expect(Pets.key('PK', unnamed, { allowPartial: true })).toBe('PETID#p1')
    })
})
