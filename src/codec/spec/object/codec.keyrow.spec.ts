/**
 * The row is the key part joined over the row without its key names, and a key is the segments that
 * the parts print.
 *
 * A key that builds no value is no attribute of the row, whatever the item or the codec wrote at the
 * name of the key. Every route that holds a row gives that key no value. The refusal of a key that
 * cannot print is the refusal of the first rule that fails in the model order: an absent part first,
 * then a separator in a part that is printed.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'
import { item, object, optional, string } from '../../codec'

describe('a key that builds no value', () => {
    type Pet = { petId: string; status: 'ADOPTED' | 'AVAILABLE' }
    // an open entry: the rest of the codec admits a name that no field declares, a key name included
    const Pets = tableEntry<Pet>()(
        {
            PK: ['petId'],
            GSI1PK: {
                discriminator: 'status',
                spec: { ADOPTED: null, AVAILABLE: ['petId'] },
            },
        } as never,
        {
            codec: item(
                object(
                    { petId: string, status: string('ADOPTED', 'AVAILABLE') },
                    [string, optional(string)],
                ) as never,
            ) as never,
        } as never,
    ) as unknown as {
        unsafeToItem: (item: object) => Record<string, unknown>
        toItem: (item: object) => unknown
        toEntry: (item: object) => Record<string, unknown>
        keyUpdates: (changed: object) => {
            set: Record<string, unknown>
            remove: string[]
        }
        fromItem: (row: object) => unknown
    }
    const stale = { petId: 'p1', status: 'ADOPTED', GSI1PK: 'stale' }
    const clean = { petId: 'p1', status: 'ADOPTED' }

    it('is no attribute of the row that toItem writes', () => {
        expect(Pets.unsafeToItem(clean)).not.toHaveProperty('GSI1PK')
        expect(Pets.unsafeToItem(clean)).toHaveProperty('PK', { S: 'PETID#p1' })
    })

    it('is no attribute of the entry that toEntry writes', () => {
        expect(Pets.toEntry(clean)).not.toHaveProperty('GSI1PK')
        expect(Pets.toEntry(clean)).toHaveProperty('PK', 'PETID#p1')
    })

    it('is removed and not set by keyUpdates, as the two routes above give it no value', () => {
        const { set, remove } = Pets.keyUpdates(stale)
        expect(remove).toEqual(['GSI1PK'])
        expect(set).not.toHaveProperty('GSI1PK')
    })

    it('reads back as the entity, through fromItem of toItem', () => {
        expect(Pets.fromItem(Pets.unsafeToItem(clean))).toEqual(clean)
    })

    it('is refused, as a value, by toItem where the write of the codec holds the name of the key', () => {
        const refused = Pets.toItem(stale)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).message).toMatch(
            /^'GSI1PK' is a key of the schema, and the write of the codec holds an attribute of that name/,
        )
    })

    it('is refused by toEntry for the same entity', () => {
        expect(() => Pets.toEntry(stale)).toThrow(RotoriseError)
        expect(() => Pets.toEntry(stale)).toThrow(
            /^'GSI1PK' is a key of the schema, and the write of the codec holds an attribute of that name/,
        )
    })
})

describe('a key that cannot print', () => {
    type Pet = { petId: string; species: string }
    const Pets = tableEntry<Pet>()({
        PK: ['petId'],
        GSI1SK: ['species', 'petId'],
    })
    const kindOf = (run: () => unknown) => {
        try {
            run()
        } catch (thrown) {
            expect(thrown).toBeInstanceOf(RotoriseError)
            return (thrown as RotoriseError).kind
        }
        return expect.unreachable()
    }

    it('refuses an absent part before it tests the separator of a part that precedes it', () => {
        // species holds the separator and petId is absent: the print stops at the absent part
        expect(
            kindOf(() => Pets.key('GSI1SK', { species: 'CAT#1' } as never)),
        ).toBe('refused')
    })

    it('refuses the separator of a part that is printed, once the print has stopped at the absent part', () => {
        expect(
            kindOf(() =>
                Pets.key('GSI1SK', { species: 'CAT#1' } as never, {
                    allowPartial: true,
                }),
            ),
        ).toBe('separator')
    })

    it('refuses the separator of a complete key', () => {
        expect(
            kindOf(() => Pets.key('GSI1SK', { species: 'CAT#1', petId: 'p1' })),
        ).toBe('separator')
    })
})

describe('a step that cannot rebuild a key names the key', () => {
    type Pet = { petId: string; species: string; name: string }
    const Pets = tableEntry<Pet>()({
        PK: ['petId'],
        GSI1SK: ['species', 'name'],
    })

    it('puts the key first and keeps the kind of the refusal that the builder gave', () => {
        const run = () =>
            (Pets.keyUpdates as (changed: object) => unknown)({
                species: 'CAT#1',
                name: 'Rex',
            })
        expect(run).toThrow(RotoriseError)
        expect(run).toThrow(
            /^'GSI1SK' cannot be rebuilt from this change: buildCompositeKey: the print of species holds the separator/,
        )
        try {
            run()
        } catch (thrown) {
            expect((thrown as RotoriseError).kind).toBe('separator')
        }
    })
})

describe('a discriminator that holds null', () => {
    type Pet = { petId: string; status: string | null }
    const Pets = tableEntry<Pet>()({
        PK: ['petId'],
        GSI1PK: {
            discriminator: 'status',
            spec: { null: ['petId'], A: ['petId'] },
        },
    } as never) as unknown as {
        key: (name: string, item: object) => unknown
    }

    it('selects no arm, as an absent discriminator selects none', () => {
        const run = () => Pets.key('GSI1PK', { petId: 'p1', status: null })
        expect(run).toThrow(RotoriseError)
        expect(run).toThrow(/Discriminator status not found in the attributes/)
    })
})

describe('a key named __proto__', () => {
    const Pets = tableEntry<{ petId: string }>()(
        { PK: ['petId'], ['__proto__']: ['petId'] } as never,
        { codec: { petId: string } } as never,
    ) as unknown as {
        toEntry: (item: object) => Record<string, unknown>
        unsafeToItem: (item: object) => Record<string, unknown>
    }

    it('is an own attribute of the entry and of the row', () => {
        expect(Object.hasOwn(Pets.toEntry({ petId: 'p1' }), '__proto__')).toBe(
            true,
        )
        expect(
            Object.hasOwn(Pets.unsafeToItem({ petId: 'p1' }), '__proto__'),
        ).toBe(true)
    })
})
