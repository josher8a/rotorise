/**
 * A schema that holds a malformed key path is refused where the schema is read.
 *
 * A key path joins names with `.`, and holds no empty name and no position. A path that fails this
 * names no attribute of an item, so the failure surfaces at the first key that reads the path, far
 * from the line that wrote the path. The check walks every position that a schema entry can hold a
 * path in, each arm of a match included, because an arm that no item has selected yet is still
 * part of the schema.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Pet = {
    petId: string
    kind: 'DOG' | 'CAT'
    ownerId: string
}

const declare = (schema: object): void => {
    ;(tableEntry<Pet>() as (schema: object) => unknown)(schema)
}

const refusal = /'a\.\.b' is no key path: a key path joins names with '\.'/

describe('a schema that holds a malformed key path', () => {
    it('refuses the path of a plain name', () => {
        expect(() => declare({ PK: 'a..b' })).toThrow(refusal)
    })

    it('refuses the path of a list of names', () => {
        expect(() => declare({ PK: ['petId', 'a..b'] })).toThrow(refusal)
    })

    it('refuses the path at the head of a transform tuple', () => {
        expect(() =>
            declare({ PK: [['a..b', (value: unknown) => value]] }),
        ).toThrow(refusal)
    })

    it('refuses the discriminator of a match', () => {
        expect(() =>
            declare({
                PK: { discriminator: 'a..b', spec: { DOG: ['petId'] } },
            }),
        ).toThrow(refusal)
    })

    it('refuses the path in an arm of a match, whether or not an item selects the arm', () => {
        expect(() =>
            declare({
                PK: {
                    discriminator: 'kind',
                    spec: { DOG: ['petId'], CAT: ['a..b'] },
                },
            }),
        ).toThrow(refusal)
    })

    it('refuses the path in a grouped case of a match', () => {
        expect(() =>
            declare({
                PK: {
                    discriminator: 'kind',
                    cases: [[['DOG', 'CAT'], ['a..b']]],
                },
            }),
        ).toThrow(refusal)
    })

    it('admits a well formed path in each position', () => {
        expect(() =>
            declare({
                PK: ['petId'],
                SK: {
                    discriminator: 'kind',
                    spec: { DOG: ['ownerId'], CAT: ['owner.id'] },
                },
            }),
        ).not.toThrow()
    })
})
