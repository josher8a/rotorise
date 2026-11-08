/**
 * A key is optional in the codec exactly where it is optional in the entity.
 *
 * `optional` reads a row with no attribute as a value with no key. `undefinable` reads it as a
 * value whose key holds `undefined`. Under `exactOptionalPropertyTypes` the two are two types, and
 * a value of one is no value of the other, so the short codec of an entry refuses a pair that
 * differs.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { optional, string, undefinable } from '../../codec'

describe('the optionality of a key in a short codec', () => {
    it('refuses undefinable where the entity key is optional, because the read holds the key', () => {
        type Owner = { petId: string; nick?: string }
        const Owners = tableEntry<Owner>()(
            { PK: ['petId'] },
            {
                codec: {
                    petId: string,
                    // @ts-expect-error the entity may lack `nick`, and the codec always holds the key
                    nick: undefinable(string),
                },
            },
        )
        const read = Owners.unsafeFromItem({ petId: { S: 'p1' } } as never)
        expect(Object.hasOwn(read, 'nick')).toBe(true)
    })

    it('refuses optional where the entity key is required, because the read lacks the key', () => {
        type Owner = { petId: string; nick: string | undefined }
        const Owners = tableEntry<Owner>()(
            { PK: ['petId'] },
            {
                codec: {
                    petId: string,
                    // @ts-expect-error the entity holds `nick`, and the codec may lack the key
                    nick: optional(string),
                },
            },
        )
        const read = Owners.unsafeFromItem({ petId: { S: 'p1' } } as never)
        expect(Object.hasOwn(read, 'nick')).toBe(false)
    })

    it('admits each mark where the entity states the same optionality', () => {
        type Optional = { petId: string; nick?: string }
        type Undefinable = { petId: string; nick: string | undefined }
        expect(
            tableEntry<Optional>()(
                { PK: ['petId'] },
                { codec: { petId: string, nick: optional(string) } },
            ),
        ).toBeDefined()
        expect(
            tableEntry<Undefinable>()(
                { PK: ['petId'] },
                { codec: { petId: string, nick: undefinable(string) } },
            ),
        ).toBeDefined()
    })
})
