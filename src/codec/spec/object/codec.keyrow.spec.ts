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

    it('is removed and not set by keyUpdates, which builds its own keys', () => {
        const { set, remove } = Pets.keyUpdates(stale)
        expect(remove).toEqual(['GSI1PK'])
        expect(set).not.toHaveProperty('GSI1PK')
    })

    it('drops the key attributes of the row before the read, so the entity reads back without them', () => {
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
            /^'GSI1PK' is a key of the schema, and the entity holds an attribute of that name/,
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
        const run = () => Pets.key('GSI1SK', { species: 'CAT#1' } as never)
        expect(kindOf(run)).toBe('refused')
        expect(run).toThrow(/Attribute petId not found/)
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

describe('a row that a closed entry wrote', () => {
    const Pets = tableEntry<{ petId: string }>()(
        { PK: ['petId'] },
        { codec: { petId: string } },
    ) as unknown as {
        unsafeToItem: (item: object) => Record<string, unknown>
        fromItem: (row: object) => unknown
    }

    it('reads back through fromItem, because the key attributes leave the row before the read', () => {
        const row = Pets.unsafeToItem({ petId: 'p1' })
        expect(row).toHaveProperty('PK')
        // the closed codec refuses an attribute that it does not declare, a key attribute included
        expect(Pets.fromItem(row)).toEqual({ petId: 'p1' })
    })
})

describe('an entity that holds the name of a key', () => {
    type Pet = { petId: string; status: string }
    const keys = {
        PK: ['petId'],
        GSI1PK: {
            discriminator: 'status',
            spec: { ADOPTED: null, AVAILABLE: ['petId'] },
        },
    } as never
    const closed = tableEntry<Pet>()(keys, {
        codec: { petId: string, status: string },
    } as never) as unknown as {
        toItem: (item: object) => unknown
        toEntry: (item: object) => Record<string, unknown>
    }
    const bare = tableEntry<Pet>()(keys) as unknown as {
        toEntry: (item: object) => Record<string, unknown>
    }
    const open = tableEntry<Pet>()(keys, {
        codec: item(
            object({ petId: string, status: string }, [
                string,
                optional(string),
            ] as never) as never,
        ) as never,
    } as never) as unknown as {
        toItem: (item: object) => unknown
        toEntry: (item: object) => Record<string, unknown>
    }
    const stale = { petId: 'p1', status: 'AVAILABLE', GSI1PK: 'mine' }

    it('is refused by toEntry where the codec is closed, as toItem refuses it', () => {
        expect(closed.toItem(stale)).toBeInstanceOf(CodecError)
        expect(() => closed.toEntry(stale)).toThrow(RotoriseError)
        expect(() => closed.toEntry(stale)).toThrow(
            /^'GSI1PK' is a key of the schema, and the entity holds an attribute of that name/,
        )
    })

    it('is refused by toEntry where the entry has no codec, so the entity value is not lost', () => {
        expect(() => bare.toEntry(stale)).toThrow(
            /^'GSI1PK' is a key of the schema, and the entity holds an attribute of that name/,
        )
    })

    it('is refused by toEntry where the open entry refuses the value, as toItem refuses it', () => {
        const number = { petId: 'p1', status: 'AVAILABLE', GSI1PK: 42 }
        expect(open.toItem(number)).toBeInstanceOf(CodecError)
        expect(() => open.toEntry(number)).toThrow(RotoriseError)
    })

    it('holds no attribute at the name of a key that builds no value, where the entity holds undefined', () => {
        const entry = closed.toEntry({
            petId: 'p1',
            status: 'ADOPTED',
            GSI1PK: undefined,
        })
        expect(entry).not.toHaveProperty('GSI1PK')
    })
})
