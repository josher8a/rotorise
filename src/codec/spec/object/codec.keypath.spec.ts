/**
 * A key component and a discriminator read a path.
 *
 * A path joins names with `.` and reads into objects only. The name that a path prints is its last
 * name, and a tag in an options object prints in place of the name. The key input is the deep pick of
 * the paths that the key reads: a sibling of a path is not required. A position in brackets is no
 * key path. An absent name anywhere on the path is an absent component, and an error names the path
 * and holds no value.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'

/** The untyped builder of an entry: a stored or hostile item is data. */
const untyped = (entry: { key: unknown }) =>
    entry.key as unknown as (
        name: string,
        item: object,
        config?: object,
    ) => unknown

describe('a key component that reads a path', () => {
    describe('the forms that a transform on the parent attribute writes today', () => {
        it('prints the tag of an options object in place of the name: the owner of a pet transfer', () => {
            type Transfer = {
                id: string
                to: { ownerId: string; name: string }
                from: { ownerId: string; name: string }
            }
            const Transfers = tableEntry<Transfer>()({
                PK: ['id'],
                GSI1PK: [['to.ownerId', { tag: 'ownerId' }]],
                GSI2PK: [['from.ownerId', { tag: 'ownerId' }]],
            })
            const key = Transfers.key('GSI1PK', { to: { ownerId: 'u1' } })
            key satisfies 'ownerId#u1'
            expect(key).toBe('ownerId#u1')
            expect(Transfers.key('GSI2PK', { from: { ownerId: 'u2' } })).toBe(
                'ownerId#u2',
            )
        })

        it('prints the tag of a path that names a collar', () => {
            type Pet = {
                storeId: string
                collar: { tagId: string; color: string }
            }
            const Pets = tableEntry<Pet>()({
                PK: ['storeId', ['collar.tagId', { tag: 'collar' }]],
            })
            expect(
                Pets.key('PK', {
                    storeId: 's1',
                    collar: { tagId: 'c1' },
                }),
            ).toBe('STOREID#s1#collar#c1')
        })

        it('prints a number at a path under a tag: the price of a listing', () => {
            type Listing = {
                id: string
                price: { amount: number; currency: string }
            }
            const Listings = tableEntry<Listing>()({
                GSI1SK: [['price.amount', { tag: 'PRICE' }]],
            })
            const key = Listings.key('GSI1SK', {
                price: { amount: 1.5 },
            })
            expect(key).toBe('PRICE#1.5')
        })

        it('prints two components that read two names of one object', () => {
            type Review = { id: string; pet: { species: string; id: string } }
            const Reviews = tableEntry<Review>()({
                PK: ['pet.species', 'pet.id'],
            })
            expect(
                Reviews.key('PK', { pet: { species: 'dog', id: '42' } }),
            ).toBe('SPECIES#dog#ID#42')
        })

        it('takes the default of a path that is absent, through a transform tuple', () => {
            type Pet = { id: string; vaccine?: { lastDose: string } }
            const Pets = tableEntry<Pet>()({
                PK: ['id'],
                SK: [['vaccine.lastDose', (x: string) => x, '0']],
            })
            expect(untyped(Pets)('SK', { id: 'p' })).toBe('LASTDOSE#0')
            expect(Pets.key('SK', { vaccine: { lastDose: '5' } })).toBe(
                'LASTDOSE#5',
            )
            expect(Pets.toEntry({ id: 'p' }).SK).toBe('LASTDOSE#0')
        })
    })

    it('does not require a sibling of the path in the key input', () => {
        type Transfer = { id: string; to: { ownerId: string; name: string } }
        const Transfers = tableEntry<Transfer>()({
            GSI1PK: ['to.ownerId'],
        })
        expect(Transfers.key('GSI1PK', { to: { ownerId: 'u1' } })).toBe(
            'OWNERID#u1',
        )
        const _lacks = () =>
            // @ts-expect-error the path `to.ownerId` is required
            Transfers.key('GSI1PK', { to: { name: 'n' } })
        expect(typeof _lacks).toBe('function')
    })

    it('reads a path through the options of a union that hold it', () => {
        type Doc = {
            id: string
            meta: { kind: 'a'; a: string } | { kind: 'b'; b: string }
        }
        const Docs = tableEntry<Doc>()({
            PK: ['meta.kind'],
            SK: ['meta.a'],
        })
        expect(Docs.key('SK', { meta: { a: 'x' } })).toBe('A#x')
        expect(Docs.key('PK', { meta: { kind: 'b' } })).toBe('KIND#b')
    })

    describe('the parameter of the transform of a path', () => {
        type Transfer = {
            id: string
            to: { ownerId: string }
            vaccine?: { lastDose: string }
        }

        it('has no contextual type, so a parameter needs an annotation', () => {
            tableEntry<Transfer>()({
                PK: [
                    // @ts-expect-error the parameter has no contextual type: annotate it
                    ['to.ownerId', (x) => String(x)],
                ],
            })
        })

        it('accepts a parameter whose annotation the value at the path fits', () => {
            const Transfers = tableEntry<Transfer>()({
                PK: [['to.ownerId', (x: string) => x]],
            })
            expect(Transfers.key('PK', { to: { ownerId: 'u' } })).toBe(
                'OWNERID#u',
            )
        })

        it('refuses a parameter whose annotation the value at the path does not fit', () => {
            tableEntry<Transfer>()({
                PK: [
                    // @ts-expect-error the value at `to.ownerId` is a string
                    ['to.ownerId', (x: number) => x],
                ],
            })
        })

        it('refuses a path whose value can be absent where no default is given', () => {
            tableEntry<Transfer>()({
                // @ts-expect-error `vaccine.lastDose` can be absent
                PK: ['vaccine.lastDose'],
            })
        })
    })

    it('refuses a path that no option of the entity holds', () => {
        type Transfer = { id: string; to: { ownerId: string } }
        tableEntry<Transfer>()({
            // @ts-expect-error `to.zz` is no path of the entity
            PK: ['to.zz'],
        })
    })

    it('refuses a position in a path, in the type and where the entry is built', () => {
        type Cart = { id: string; items: { sku: string }[] }
        const build = () =>
            tableEntry<Cart>()({
                // @ts-expect-error a key path reads objects only
                PK: ['items[0].sku'],
            })
        expect(build).toThrow(RotoriseError)
        expect(build).toThrow(/items\[0\]\.sku/)
    })

    it('treats an absent name on the path as an absent component, and the error holds no value', () => {
        type Transfer = { id: string; to: { ownerId: string } }
        const Transfers = tableEntry<Transfer>()({
            PK: ['id', 'to.ownerId'],
        })
        const secret = 'secret-value'
        const run = () => untyped(Transfers)('PK', { id: secret, to: {} })
        expect(run).toThrow(RotoriseError)
        expect(run).toThrow(/Attribute to\.ownerId not found/)
        expect(run).not.toThrow(new RegExp(secret))
        expect(
            untyped(Transfers)('PK', { id: 'i' }, { allowPartial: true }),
        ).toBe('ID#i')
        // an inherited property is no value
        const inherited = Object.create({ ownerId: 'u' })
        expect(() =>
            untyped(Transfers)('PK', { id: 'i', to: inherited }),
        ).toThrow(/Attribute to\.ownerId not found/)
    })

    it('holds no attribute value in the error of a top-level component either', () => {
        type Row = { a: string; b: string }
        const Rows = tableEntry<Row>()({ PK: ['a', 'b'] })
        const secret = 'secret-value'
        const run = () => untyped(Rows)('PK', { a: secret })
        expect(run).toThrow(/Attribute b not found/)
        expect(run).not.toThrow(new RegExp(secret))
    })

    it('reads a top-level name that holds a `.` as that attribute, and not as a path', () => {
        type Odd = { 'a.b': string; a: { b: string } }
        const Odds = tableEntry<Odd>()({ PK: ['a.b'] })
        expect(untyped(Odds)('PK', { 'a.b': 'flat', a: { b: 'nested' } })).toBe(
            'A.B#flat',
        )
    })
})

describe('a discriminator that reads a path', () => {
    type Thing =
        | { id: string; tag: 'T1'; meta: { kind: 'dog'; breed: string } }
        | { id: string; tag: 'T1'; meta: { kind: 'cat' } }
        | { id: string; tag: 'T2'; n: string }

    const Things = tableEntry<Thing>()({
        PK: ['id'],
        SK: {
            discriminator: 'tag',
            spec: {
                T1: {
                    discriminator: 'meta.kind',
                    spec: { dog: ['meta.breed'], cat: null },
                },
                T2: ['n'],
            },
        },
    })

    it('selects the arm by the value at the path, at depth two', () => {
        const dog = { tag: 'T1', meta: { kind: 'dog', breed: 'pug' } } as const
        expect(Things.key('SK', dog)).toBe('BREED#pug')
        const cat = { tag: 'T1', meta: { kind: 'cat' } } as const
        expect(Things.key('SK', cat)).toBeUndefined()
        expect(Things.key('SK', { tag: 'T2', n: 'v' })).toBe('N#v')
    })

    it('refuses an absent segment of the path, and a literal that names no arm, with no value in the error', () => {
        const secret = 'secret-value'
        const run = (item: object) => () => untyped(Things)('SK', item)
        expect(run({ tag: 'T1', meta: {} })).toThrow(
            /Discriminator meta\.kind not found/,
        )
        expect(run({ tag: 'T1', meta: { kind: secret } })).toThrow(
            /Discriminator value of meta\.kind/,
        )
        expect(run({ tag: 'T1', meta: { kind: secret } })).not.toThrow(
            new RegExp(secret),
        )
        expect(run({ tag: 'T1', meta: { kind: 'constructor' } })).toThrow(
            RotoriseError,
        )
    })

    it('refuses an inner arm that reads an attribute of another variant', () => {
        tableEntry<Thing>()({
            PK: ['id'],
            SK: {
                discriminator: 'tag',
                spec: {
                    T1: {
                        discriminator: 'meta.kind',
                        // @ts-expect-error `n` exists only on `T2`
                        spec: { dog: ['n'], cat: null },
                    },
                    T2: ['n'],
                },
            },
        })
    })

    it('reads each path of the case back from the entry that wrote it', () => {
        const items = [
            { id: '1', tag: 'T1', meta: { kind: 'dog', breed: 'pug' } },
            { id: '2', tag: 'T1', meta: { kind: 'cat' } },
            { id: '3', tag: 'T2', n: 'v' },
        ] as const
        for (const item of items) {
            expect(Things.fromEntry(Things.toEntry(item))).toEqual(item)
        }
    })
})

describe('the round trip of the entries that read a path', () => {
    it('reads back what toEntry wrote, for a tag, a path and a default', () => {
        type Transfer = { id: string; to: { ownerId: string; name: string } }
        const Transfers = tableEntry<Transfer>()({
            PK: ['id'],
            GSI1PK: [['to.ownerId', { tag: 'ownerId' }]],
        })
        const item = { id: 'a', to: { ownerId: 'u', name: 'n' } }
        expect(Transfers.fromEntry(Transfers.toEntry(item))).toEqual(item)
        const entry = { ...Transfers.toEntry(item), GSI1PK: 'ownerId#other' }
        expect(Transfers.fromEntry(entry as never)).toBeInstanceOf(Error)
    })
})

describe('the change of a key that reads a path', () => {
    type Thing = {
        id: string
        meta: { kind: string; size: number }
        label: string
    }
    const Things = tableEntry<Thing>()({
        PK: ['id'],
        GSI1PK: ['meta.kind', 'label'],
        GSI2PK: [['meta', (m: { kind: string }) => m.kind]],
    })

    it('rebuilds each key that reads a path below a written attribute', () => {
        const keys = Things.keyUpdates({
            meta: { kind: 'k', size: 1 },
            label: 'l',
        })
        expect(keys.GSI1PK).toEqual({ S: 'KIND#k#LABEL#l' })
        expect(keys.GSI2PK).toEqual({ S: 'META#k' })
    })

    it('refuses a write that reaches a key by a path and leaves a component of the key out', () => {
        // @ts-expect-error `label` is a component of the key that the write reaches
        const _lacks = () => Things.keyUpdates({ meta: { kind: 'k', size: 1 } })
        expect(_lacks).toThrow(RotoriseError)
    })

    it('reads a write to a path as a change of each key that reads the attribute above it', () => {
        const write = () =>
            (
                Things.keyUpdates as unknown as (
                    changed: object,
                ) => Record<string, unknown>
            )({ 'meta.kind': 'k', label: 'l' })
        // `GSI2PK` reads the whole of `meta`, and the write gives only a part of it
        expect(write).toThrow(RotoriseError)
    })
})
