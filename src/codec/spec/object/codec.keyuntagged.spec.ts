/**
 * A union codec that names no variant is refused at the codec, where a key reads a held attribute.
 *
 * An entity that is a union takes a codec that says which variant an item is. A `union` with no
 * discriminator cannot say so, and the run time refuses the codec. The call has two failing
 * arguments, and the compiler reports the first. A key of one attribute that reads a held codec
 * fails first, with a text about the member of the attribute. The cause is the codec, so the type
 * refuses the codec. A tagged codec keeps the refusal of the key, because the key is then the cause.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import {
    array,
    discriminatedUnion,
    held,
    item,
    object,
    string,
    union,
} from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

type Cat = { petId: string; species: 'CAT'; adopted: boolean }
type Dog = { petId: string; species: 'DOG'; adopted: boolean }
type CatTags = { petId: string; species: 'CAT'; tags: string[] }
type DogTags = { petId: string; species: 'DOG'; tags: string[] }

const flag: StandardSchemaV1<boolean> = {
    '~standard': {
        version: 1,
        vendor: 'spec',
        validate: (value) =>
            typeof value === 'boolean'
                ? { value }
                : { issues: [{ message: 'not a boolean' }] },
    },
}
const Adopted = held(string('Y', 'N'), flag, {
    encode: (value: boolean) => (value ? 'Y' : 'N'),
    decode: (text: string) => text === 'Y',
})
const listSchema: StandardSchemaV1<readonly string[]> = {
    '~standard': {
        version: 1,
        vendor: 'spec',
        validate: (value) => ({ value: value as readonly string[] }),
    },
}
const Tags = held(array(string), listSchema, {
    encode: (value: readonly string[]) => value,
    decode: (value: readonly string[]) => value,
})

describe('an untagged union codec is refused at the codec, where the key reads a held attribute', () => {
    it('refuses the codec, and the run time throws for the same codec', () => {
        const build = () =>
            tableEntry<Cat | Dog>()(
                { PK: ['petId'], SK: 'adopted' },
                {
                    // @ts-expect-error the codec names no variant, so the codec is the cause
                    codec: item(
                        union([
                            object({
                                petId: string,
                                species: string('CAT'),
                                adopted: Adopted,
                            }),
                            object({
                                petId: string,
                                species: string('DOG'),
                                adopted: Adopted,
                            }),
                        ]),
                    ),
                },
            )
        expect(build).toThrow(RotoriseError)
        expect(build).toThrow(/neither an item codec nor a tagged one/)
    })

    it('keeps the refusal of the key for a tagged union that holds a list at the key', () => {
        const build = () =>
            tableEntry<CatTags | DogTags>()(
                // @ts-expect-error the key reads a list, which is none of S, N and B
                { PK: ['petId'], SK: 'tags' },
                {
                    codec: item(
                        discriminatedUnion('species', [
                            object({
                                petId: string,
                                species: string('CAT'),
                                tags: Tags,
                            }),
                            object({
                                petId: string,
                                species: string('DOG'),
                                tags: Tags,
                            }),
                        ]),
                    ),
                },
            )
        // the run time reads the key at the write, so the type is the refusal at the call
        expect(typeof build).toBe('function')
    })

    it('accepts a tagged union that holds an attribute stored as S at the key', () => {
        const Adopteds = tableEntry<Cat | Dog>()(
            { PK: ['petId'], SK: 'adopted' },
            {
                codec: item(
                    discriminatedUnion('species', [
                        object({
                            petId: string,
                            species: string('CAT'),
                            adopted: Adopted,
                        }),
                        object({
                            petId: string,
                            species: string('DOG'),
                            adopted: Adopted,
                        }),
                    ]),
                ),
            },
        )
        expect(
            Adopteds.unsafeToEntry({
                petId: 'p',
                species: 'CAT',
                adopted: true,
            }).SK,
        ).toBe('Y')
    })
})
