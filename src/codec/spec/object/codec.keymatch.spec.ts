/**
 * A key match nests: an arm of a match is a match.
 *
 * A key spec chooses the components of a key from the item. A match reads one discriminator and
 * selects an arm by its value, and the arm can match on an attribute that only the selected variant
 * has. The case: `tag` is `OBJECT` or `ANIMAL`. Under `ANIMAL` the attribute `specie` is `CAT`,
 * `DOG` or `HORSE`, and under `DOG` the attribute `breed` is `LAB` or `PUG`. `specie` does not
 * exist on `OBJECT`, and `breed` does not exist on `CAT`.
 *
 * The builder reads an arm as an own property at each level, so a literal that names a property of
 * the prototype names no arm. An error names the discriminator and holds no attribute value.
 */
import { describe, expect, it } from 'vitest'
import { keyComponents, RotoriseError, tableEntry } from '../../../Rotorise'

type Creature =
    | { tag: 'OBJECT'; id: string; name: string }
    | { tag: 'ANIMAL'; id: string; specie: 'CAT'; name: string }
    | { tag: 'ANIMAL'; id: string; specie: 'HORSE'; name: string }
    | {
          tag: 'ANIMAL'
          id: string
          specie: 'DOG'
          breed: 'LAB' | 'PUG'
          name: string
      }

const Creatures = tableEntry<Creature>()({
    PK: ['id'],
    SK: {
        discriminator: 'tag',
        spec: {
            OBJECT: ['name'],
            ANIMAL: {
                discriminator: 'specie',
                spec: {
                    CAT: null,
                    HORSE: ['id', 'name'],
                    DOG: {
                        discriminator: 'breed',
                        spec: { LAB: ['breed', 'name'], PUG: 'name' },
                    },
                },
            },
        },
    },
})

const object = { tag: 'OBJECT', id: 'o1', name: 'lamp' } as const
const cat = { tag: 'ANIMAL', id: 'c1', specie: 'CAT', name: 'tom' } as const
const horse = {
    tag: 'ANIMAL',
    id: 'h1',
    specie: 'HORSE',
    name: 'bolt',
} as const
const lab = {
    tag: 'ANIMAL',
    id: 'd1',
    specie: 'DOG',
    breed: 'LAB',
    name: 'rex',
} as const
const pug = { ...lab, id: 'd2', breed: 'PUG', name: 'mo' } as const

/** The untyped builder: a stored or hostile item is data, and the type refuses what it can. */
const build = Creatures.key as unknown as (
    name: 'SK',
    item: object,
    config?: object,
) => unknown

describe('a nested key match', () => {
    it('gives the key of the arm that the path of literals selects', () => {
        expect(Creatures.key('SK', object)).toBe('NAME#lamp')
        expect(Creatures.key('SK', horse)).toBe('ID#h1#NAME#bolt')
        expect(Creatures.key('SK', lab)).toBe('BREED#LAB#NAME#rex')
        const typed: 'BREED#LAB#NAME#rex' = Creatures.key('SK', lab)
        expect(typed).toBe('BREED#LAB#NAME#rex')
    })

    it('reads the attribute of an arm that names one as a raw copy, with no join', () => {
        expect(Creatures.key('SK', pug)).toBe('mo')
    })

    it('reads no `specie` under `OBJECT`', () => {
        expect(build('SK', { ...object, specie: 'DOG' })).toBe('NAME#lamp')
    })

    it('refuses a dog with no `breed`, and names the discriminator', () => {
        const { breed: _breed, ...dog } = lab
        const run = () => build('SK', dog)
        expect(run).toThrow(RotoriseError)
        expect(run).toThrow(/Discriminator breed not found/)
    })

    it('gives no key at a `null` arm below the first level', () => {
        expect(Creatures.key('SK', cat)).toBeUndefined()
    })

    it('refuses a literal that names a property of the prototype, at each level', () => {
        for (const name of [
            'constructor',
            'toString',
            '__proto__',
            'hasOwnProperty',
        ]) {
            expect(() => build('SK', { tag: name }), `tag ${name}`).toThrow(
                RotoriseError,
            )
            expect(
                () => build('SK', { tag: 'ANIMAL', specie: name }),
                `specie ${name}`,
            ).toThrow(RotoriseError)
            expect(
                () =>
                    build('SK', { tag: 'ANIMAL', specie: 'DOG', breed: name }),
                `breed ${name}`,
            ).toThrow(RotoriseError)
        }
    })

    it('holds no attribute value in the error of a discriminator that names no arm or is absent', () => {
        const secret = 'secret-value'
        const items = [
            { tag: secret, id: secret },
            { id: secret, name: secret },
            { tag: 'ANIMAL', specie: secret, id: secret },
            { tag: 'ANIMAL', specie: 'DOG', id: secret, name: secret },
            { tag: 'ANIMAL', specie: 'DOG', breed: secret, id: secret },
        ]
        for (const item of items) {
            let message = ''
            try {
                build('SK', item)
            } catch (thrown) {
                if (!(thrown instanceof RotoriseError)) throw thrown
                message = thrown.message
            }
            expect(message).not.toBe('')
            expect(message).not.toContain(secret)
        }
    })

    it('reads the same entry back for each path of the case', () => {
        for (const item of [object, horse, lab, pug, cat]) {
            const entry = Creatures.toEntry(item)
            expect(Creatures.fromEntry(entry)).toEqual(item)
        }
    })

    it('refuses a key of a path that the entry does not hold', () => {
        const entry = { ...Creatures.toEntry(lab), SK: 'NAME#other' }
        expect(Creatures.fromEntry(entry as never)).toBeInstanceOf(Error)
    })
})

describe('the type of a nested key match', () => {
    it('refuses an inner arm that names an attribute of another variant', () => {
        tableEntry<Creature>()({
            PK: ['id'],
            SK: {
                discriminator: 'tag',
                spec: {
                    OBJECT: ['name'],
                    // @ts-expect-error `breed` exists only on a dog
                    ANIMAL: {
                        discriminator: 'specie',
                        spec: {
                            CAT: null,
                            HORSE: ['breed'],
                            DOG: ['name'],
                        },
                    },
                },
            },
        })
    })

    it('refuses an inner match that lacks a literal', () => {
        tableEntry<Creature>()({
            PK: ['id'],
            SK: {
                discriminator: 'tag',
                spec: {
                    OBJECT: ['name'],
                    // @ts-expect-error `HORSE` has no arm
                    ANIMAL: {
                        discriminator: 'specie',
                        spec: { CAT: null, DOG: ['name'] },
                    },
                },
            },
        })
    })

    it('refuses a match on an attribute that the variant does not have', () => {
        tableEntry<Creature>()({
            PK: ['id'],
            SK: {
                discriminator: 'tag',
                spec: {
                    OBJECT: {
                        // @ts-expect-error `specie` does not exist on an object
                        discriminator: 'specie',
                        spec: { CAT: null },
                    },
                    ANIMAL: ['name'],
                },
            },
        })
    })

    it('says which attribute a key needs, down the path', () => {
        expect(
            keyComponents(
                {
                    discriminator: 'tag',
                    spec: {
                        ANIMAL: {
                            discriminator: 'specie',
                            spec: { DOG: ['breed'], CAT: null },
                        },
                    },
                },
                { tag: 'ANIMAL', specie: 'DOG' },
            ),
        ).toEqual(new Set(['tag', 'specie', 'breed']))
    })
})

describe('the change of a key that a nested match builds', () => {
    it('gives the key of the variant that the change selects', () => {
        expect(Creatures.keyUpdates(lab).SK).toEqual({
            S: 'BREED#LAB#NAME#rex',
        })
    })

    it('needs `breed` where the new `specie` reads it', () => {
        const _needsBreed = () =>
            // @ts-expect-error `breed` is a component of a dog
            Creatures.keyUpdates({ tag: 'ANIMAL', specie: 'DOG', name: 'rex' })
        expect(typeof _needsBreed).toBe('function')
    })

    it('reads every inner variant where the change carries the outer discriminator only', () => {
        const names = keyComponents(
            {
                discriminator: 'tag',
                spec: {
                    ANIMAL: {
                        discriminator: 'specie',
                        spec: { DOG: ['breed'], HORSE: ['id'] },
                    },
                },
            },
            { tag: 'ANIMAL' },
        )
        expect([...names].sort()).toEqual(['breed', 'id', 'specie', 'tag'])
    })

    it('reads no variant for a value that names a property of the prototype', () => {
        const names = keyComponents(
            {
                discriminator: 'tag',
                spec: { ANIMAL: ['name'] },
            },
            { tag: 'constructor' },
        )
        expect([...names]).toEqual(['tag'])
    })
})
