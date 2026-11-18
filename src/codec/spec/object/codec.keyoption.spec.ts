/**
 * An arm of a match reads each option that can hold its literal.
 *
 * The run time selects the arm by the value of the item at the discriminator. So the arm of a
 * literal reads each option of the entity whose value at the discriminator can be that literal. An
 * option that holds two literals is an option of each of the two arms. A discriminator that an item
 * can lack selects no arm, and the run time throws for that item. The type refuses such a match at
 * construction, and the refusal names the discriminator.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, tableEntry } from '../../../Rotorise'

type Boarder = {
    petId: string
    status: 'IN' | 'OUT'
    kennel: string
    owner: { id: string }
}
const boarder: Boarder = {
    petId: 'p1',
    status: 'IN',
    kennel: 'k1',
    owner: { id: 'o1' },
}

describe('an arm of a match for an option that holds two literals', () => {
    it('reads the attributes of the option, in the form with `spec` and a path', () => {
        const Boarders = tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                spec: { IN: ['kennel', 'owner.id'], OUT: ['petId'] },
            },
        })
        expect(Boarders.unsafeToEntry(boarder).SK).toBe('KENNEL#k1#ID#o1')
    })

    it('reads the attributes of the option, in the form with `cases`', () => {
        const Boarders = tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                cases: [
                    [['IN'], ['kennel']],
                    [['OUT'], ['petId']],
                ],
            },
        })
        expect(Boarders.unsafeToEntry(boarder).SK).toBe('KENNEL#k1')
    })

    it('reads the attributes of the option, in a match on a path', () => {
        type Placed = {
            petId: string
            meta: { status: 'IN' | 'OUT' }
            kennel: string
        }
        const Placeds = tableEntry<Placed>()({
            PK: ['petId'],
            SK: {
                discriminator: 'meta.status',
                spec: { IN: ['kennel'], OUT: ['petId'] },
            },
        })
        const placed: Placed = {
            petId: 'p1',
            meta: { status: 'IN' },
            kennel: 'k1',
        }
        expectTypeOf(Placeds.unsafeToEntry(placed).SK).toEqualTypeOf<
            `KENNEL#${string}` | `PETID#${string}`
        >()
        expect(Placeds.unsafeToEntry(placed).SK).toBe('KENNEL#k1')
        const placedIn = {
            petId: 'p1',
            meta: { status: 'IN' },
            kennel: 'k1',
        } as const
        expectTypeOf(
            Placeds.unsafeKey('SK', placedIn),
        ).toEqualTypeOf<'KENNEL#k1'>()
        expect(Placeds.unsafeKey('SK', placedIn)).toBe('KENNEL#k1')
    })

    it('reads only the options that hold the literal, in a match on a path', () => {
        type Pathed =
            | { petId: string; meta: { kind: 'CAT' }; kennel: string }
            | { petId: string; meta: { kind: 'DOG' }; ownerId: string }
        const Patheds = tableEntry<Pathed>()({
            PK: ['petId'],
            SK: {
                discriminator: 'meta.kind',
                spec: { CAT: ['kennel'], DOG: ['ownerId'] },
            },
        })
        const cat = {
            petId: 'p1',
            meta: { kind: 'CAT' },
            kennel: 'k1',
        } as const
        expectTypeOf(Patheds.unsafeKey('SK', cat)).toEqualTypeOf<'KENNEL#k1'>()
        expect(Patheds.unsafeKey('SK', cat)).toBe('KENNEL#k1')
        const bare = { meta: { kind: 'CAT' } } as const
        // @ts-expect-error the arm CAT reads `kennel`, and the argument holds none
        const refused = () => Patheds.unsafeKey('SK', bare)
        expect(refused).toThrow(/Attribute kennel not found/)
    })

    it('refuses a name that the option of the arm lacks', () => {
        tableEntry<Boarder>()({
            PK: ['petId'],
            // @ts-expect-error the option of the arm IN holds no attribute `cage`
            SK: {
                discriminator: 'status',
                spec: { IN: ['cage'], OUT: ['petId'] },
            },
        })
        const Cages = tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                spec: { IN: ['kennel'], OUT: ['petId'] },
            },
        })
        expect(Cages.unsafeToEntry(boarder).SK).toBe('KENNEL#k1')
    })

    it('refuses an arm that the discriminator never holds, on the arm, because the arm reads no option', () => {
        tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                spec: {
                    IN: ['kennel'],
                    OUT: ['petId'],
                    // @ts-expect-error `status` never holds 'HELD'
                    HELD: ['petId'],
                },
            },
        })
    })

    it('refuses an arm of no key that the discriminator never holds, on the match, because `null` cannot carry the message', () => {
        tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                // @ts-expect-error `status` never holds 'HELD'
                spec: {
                    IN: ['kennel'],
                    OUT: ['petId'],
                    HELD: null,
                },
            },
        })
    })

    it('refuses an arm of no key that the discriminator never holds, on the match, where another arm reads a path', () => {
        tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                // @ts-expect-error `status` never holds 'HELD'
                spec: {
                    IN: ['owner.id'],
                    OUT: ['petId'],
                    HELD: null,
                },
            },
        })
    })

    it('refuses a dead literal in the form with `spec` as the form with `cases` does, because the two forms state one rule', () => {
        tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                spec: {
                    IN: ['kennel'],
                    OUT: ['petId'],
                    // @ts-expect-error `status` never holds 'HELD'
                    HELD: ['petId'],
                },
            },
        })
        tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                cases: [
                    [['IN'], ['kennel']],
                    // @ts-expect-error `status` never holds 'HELD'
                    [['OUT', 'HELD'], ['petId']],
                ],
            },
        })
    })

    it('admits a match whose arms are the literals of the discriminator, so a schema with no dead arm is not refused', () => {
        const Boarders = tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                spec: { IN: ['kennel'], OUT: null },
            },
        })
        expect(Boarders.unsafeToEntry(boarder).SK).toBe('KENNEL#k1')
    })

    it('refuses a call of key with the discriminator alone, because the arm needs the attribute', () => {
        const Boarders = tableEntry<Boarder>()({
            PK: ['petId'],
            SK: {
                discriminator: 'status',
                spec: { IN: ['kennel'], OUT: ['petId'] },
            },
        })
        const tagOnly: { status: 'IN' } = { status: 'IN' }
        // @ts-expect-error the arm IN reads `kennel`, and the argument holds none
        const refused = () => Boarders.unsafeKey('SK', tagOnly)
        expect(refused).toThrow(/Attribute kennel not found/)
    })
})

type Optional =
    | { petId: string; kind?: 'CAT'; kennel: string }
    | { petId: string; kind: 'DOG'; ownerId: string }
type Lacking =
    | { petId: string; kind: 'CAT'; kennel: string }
    | { petId: string; ownerId: string }

describe('a discriminator that an item can lack', () => {
    it('is refused in the form with `spec`', () => {
        tableEntry<Optional>()({
            PK: ['petId'],
            SK: {
                discriminator: 'kind',
                // @ts-expect-error 'kind' can be absent, and a match selects its arm by the value
                spec: { CAT: ['kennel'], DOG: ['ownerId'] },
            },
        })
        const Pets = tableEntry<Optional>()({ PK: ['petId'] })
        expect(() =>
            Pets.unsafeToEntry({ petId: 'p4', kennel: 'k4' }),
        ).not.toThrow()
    })

    it('is refused in the form with `cases`, and the error lands on the discriminator', () => {
        tableEntry<Optional>()({
            PK: ['petId'],
            SK: {
                // @ts-expect-error 'kind' can be absent, and a match selects its arm by the value
                discriminator: 'kind',
                cases: [
                    [['CAT'], ['kennel']],
                    [['DOG'], ['ownerId']],
                ],
            },
        })
    })

    it('is refused where one option does not hold the discriminator at all', () => {
        tableEntry<Lacking>()({
            PK: ['petId'],
            SK: {
                // @ts-expect-error 'kind' can be absent, and a match selects its arm by the value
                discriminator: 'kind',
                cases: [[['CAT'], ['kennel']]],
            },
        })
    })

    it('throws at run time for an item with no value at the discriminator', () => {
        const Strays = tableEntry<Record<string, unknown>>()({
            PK: ['petId'],
            SK: {
                discriminator: 'kind',
                cases: [[['CAT'], ['kennel']]],
            },
        } as never)
        {
            const refused = Strays.toEntry({ petId: 'p4', ownerId: 'u4' })
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toMatch(/Discriminator kind not found/)
        }
    })
})
