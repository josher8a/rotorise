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
import { RotoriseError, tableEntry } from '../../../Rotorise'
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
        toEntry: (item: object) => Record<string, unknown>
        keyUpdates: (changed: object) => {
            set: Record<string, unknown>
            remove: string[]
        }
        fromItem: (row: object) => unknown
    }
    const stale = { petId: 'p1', status: 'ADOPTED', GSI1PK: 'stale' }

    it('is no attribute of the row that toItem writes, whatever the item holds at its name', () => {
        expect(Pets.unsafeToItem(stale)).not.toHaveProperty('GSI1PK')
        expect(Pets.unsafeToItem(stale)).toHaveProperty('PK', { S: 'PETID#p1' })
    })

    it('is no attribute of the entry that toEntry writes, whatever the item holds at its name', () => {
        expect(Pets.toEntry(stale)).not.toHaveProperty('GSI1PK')
        expect(Pets.toEntry(stale)).toHaveProperty('PK', 'PETID#p1')
    })

    it('is removed and not set by keyUpdates, as the two routes above give it no value', () => {
        const { set, remove } = Pets.keyUpdates(stale)
        expect(remove).toEqual(['GSI1PK'])
        expect(set).not.toHaveProperty('GSI1PK')
    })

    it('reads back as the entity without the stale key, through fromItem of toItem', () => {
        expect(Pets.fromItem(Pets.unsafeToItem(stale))).toEqual({
            petId: 'p1',
            status: 'ADOPTED',
        })
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
