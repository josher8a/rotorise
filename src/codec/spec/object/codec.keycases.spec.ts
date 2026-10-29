/**
 * An arm of a key match groups several literals.
 *
 * A match takes `cases` in place of `spec`. A case is a non-empty list of literals and the arm that
 * they share. The cases are an unordered partition of the literals of the discriminator: no literal
 * is in two cases, and the cases cover each literal. A grouped match is another way to write the
 * map from a literal to an arm, so each key is the key of the ungrouped form.
 */
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'

type OwnerId = string
type Owner = { ownerId: OwnerId; name: string }
type Handoff =
    | { type: 'INTAKE'; id: string; to: Owner }
    | { type: 'ADOPTION'; id: string; to: Owner; from: Owner }
    | { type: 'FOSTER'; id: string; to: Owner; from: Owner }
    | { type: 'RELEASE'; id: string; from: Owner }

const to = (x: Pick<Owner, 'ownerId'>) =>
    ({ tag: 'ownerId', value: x.ownerId }) as const

/** A handoff of a pet: one transform arm under three literals. */
const Grouped = tableEntry<Handoff>()({
    PK: ['id'],
    GSI1PK: {
        discriminator: 'type',
        cases: [
            [['INTAKE', 'ADOPTION', 'FOSTER'], [['to', to]]],
            [['RELEASE'], null],
        ],
    },
    GSI2PK: {
        discriminator: 'type',
        cases: [
            [['INTAKE'], null],
            [['ADOPTION', 'FOSTER', 'RELEASE'], [['from', to]]],
        ],
    },
})

const Ungrouped = tableEntry<Handoff>()({
    PK: ['id'],
    GSI1PK: {
        discriminator: 'type',
        spec: {
            INTAKE: [['to', to]],
            ADOPTION: [['to', to]],
            FOSTER: [['to', to]],
            RELEASE: null,
        },
    },
    GSI2PK: {
        discriminator: 'type',
        spec: {
            INTAKE: null,
            ADOPTION: [['from', to]],
            FOSTER: [['from', to]],
            RELEASE: [['from', to]],
        },
    },
})

const alice: Owner = { ownerId: 'alice', name: 'Alice' }
const bob: Owner = { ownerId: 'bob', name: 'Bob' }
const handoffs: Handoff[] = [
    { type: 'INTAKE', id: 'o1', to: alice },
    { type: 'ADOPTION', id: 'o2', to: alice, from: bob },
    { type: 'FOSTER', id: 'o3', to: bob, from: alice },
    { type: 'RELEASE', id: 'o4', from: bob },
]

/** The untyped builder: a hostile spec or item is data, and the type refuses what it can. */
const untypedEntry = (schema: object) =>
    (
        tableEntry as unknown as () => (schema: object) => {
            key: (name: string, item: object) => unknown
            toEntry: (item: object) => unknown
        }
    )()(schema)

describe('a grouped match', () => {
    it('gives the key of the ungrouped form for each literal of the group', () => {
        for (const handoff of handoffs) {
            expect(Grouped.toEntry(handoff)).toEqual(Ungrouped.toEntry(handoff))
        }
        const key = Grouped.key('GSI1PK', handoffs[1] as never)
        expect(key).toBe('ownerId#alice')
        expect(Grouped.key('GSI2PK', handoffs[3] as never)).toBe('ownerId#bob')
    })

    it('gives no key at a `null` case that groups literals', () => {
        const none = tableEntry<
            | { s: 'A'; id: string }
            | { s: 'B'; id: string }
            | { s: 'C'; id: string }
        >()({
            PK: ['id'],
            SK: {
                discriminator: 's',
                cases: [
                    [['A', 'B'], null],
                    [['C'], ['id']],
                ],
            },
        })
        expect(none.key('SK', { s: 'A', id: 'x' })).toBeUndefined()
        expect(none.key('SK', { s: 'B', id: 'x' })).toBeUndefined()
        expect(none.key('SK', { s: 'C', id: 'x' })).toBe('ID#x')
    })

    it('reads the entry back for each item of the group', () => {
        for (const handoff of handoffs) {
            expect(Grouped.fromEntry(Grouped.toEntry(handoff))).toEqual(handoff)
        }
    })

    it('treats the discriminator of a group as a component of the key, as a match does', () => {
        const { set: updates } = Grouped.keyUpdates({
            type: 'ADOPTION',
            to: alice,
            from: bob,
        })
        expect(updates).toEqual(
            Ungrouped.keyUpdates({ type: 'ADOPTION', to: alice, from: bob })
                .set,
        )
        const _lacks = () =>
            // @ts-expect-error a transfer reads `from` in `GSI2PK`
            Grouped.keyUpdates({ type: 'ADOPTION', to: alice })
        expect(typeof _lacks).toBe('function')
    })

    it('names an item that no case selects, and the name holds no value', () => {
        const entry = untypedEntry({
            SK: {
                discriminator: 'type',
                cases: [[['A', 'B'], ['id']]],
            },
        })
        const run = () => entry.key('SK', { type: 'secret-value', id: 'x' })
        expect(run).toThrow(RotoriseError)
        expect(run).toThrow(/Discriminator value of type not found/)
        expect(run).not.toThrow(/secret-value/)
    })

    it('reads a literal that names a property of the prototype as an own arm, and no other', () => {
        const entry = untypedEntry({
            SK: {
                discriminator: 'type',
                cases: [[['__proto__', 'constructor'], ['id']]],
            },
        })
        expect(entry.key('SK', { type: '__proto__', id: 'x' })).toBe('ID#x')
        expect(entry.key('SK', { type: 'constructor', id: 'x' })).toBe('ID#x')
        expect(() => entry.key('SK', { type: 'toString', id: 'x' })).toThrow(
            RotoriseError,
        )
    })
})

describe('an order of the store', () => {
    type Order =
        | { status: 'PLACED'; id: string; updatedAt: number }
        | { status: 'APPROVED'; id: string; updatedAt: number }
        | { status: 'DELIVERED'; id: string; updatedAt: number }

    const GroupedOrder = tableEntry<Order>()({
        PK: ['id'],
        GSI3SK: {
            discriminator: 'status',
            cases: [
                [['APPROVED', 'DELIVERED'], null],
                [['PLACED'], 'updatedAt'],
            ],
        },
        GSI2PK: {
            discriminator: 'status',
            cases: [
                [['APPROVED', 'DELIVERED'], null],
                [['PLACED'], ['status']],
            ],
        },
    })
    const UngroupedOrder = tableEntry<Order>()({
        PK: ['id'],
        GSI3SK: {
            discriminator: 'status',
            spec: { APPROVED: null, DELIVERED: null, PLACED: 'updatedAt' },
        },
        GSI2PK: {
            discriminator: 'status',
            spec: { APPROVED: null, DELIVERED: null, PLACED: ['status'] },
        },
    })

    it('gives the keys of the ungrouped specs for each status, and none for a settled order', () => {
        for (const status of ['PLACED', 'APPROVED', 'DELIVERED'] as const) {
            const order = { status, id: 'r1', updatedAt: 7 }
            expect(GroupedOrder.toEntry(order)).toEqual(
                UngroupedOrder.toEntry(order),
            )
        }
        const pending = GroupedOrder.toEntry({
            status: 'PLACED',
            id: 'r1',
            updatedAt: 7,
        })
        expect(pending.GSI3SK).toBe(7)
        expect(pending.GSI2PK).toBe('STATUS#PLACED')
        expect(
            GroupedOrder.toEntry({
                status: 'APPROVED',
                id: 'r1',
                updatedAt: 7,
            }),
        ).not.toHaveProperty('GSI2PK')
    })
})

describe('the construction of a grouped match', () => {
    const refused = (cases: unknown, extra: object = {}) =>
        untypedEntry({ SK: { discriminator: 'type', cases, ...extra } })

    it('refuses a literal that two cases name, and names the discriminator and the literal', () => {
        const run = () =>
            refused([
                [['A', 'B'], ['id']],
                [['B', 'C'], null],
            ])
        expect(run).toThrow(RotoriseError)
        expect(run).toThrow('Match on type: the literal B is in two cases')
    })

    it('refuses a literal that one case names twice', () => {
        expect(() => refused([[['A', 'A'], ['id']]])).toThrow(
            'the literal A is in two cases',
        )
    })

    it('refuses a case that names no literal', () => {
        expect(() => refused([[[], ['id']]])).toThrow(RotoriseError)
    })

    it('refuses a match that holds both spec and cases', () => {
        expect(() =>
            refused([[['A'], ['id']]], { spec: { A: ['id'] } }),
        ).toThrow('holds both spec and cases')
    })

    it('refuses a literal that is no string and no number', () => {
        expect(() => refused([[[{}], ['id']]])).toThrow(RotoriseError)
    })

    it('reads a grouped match at each level of a nested match', () => {
        type Pet =
            | { tag: 'OBJECT'; id: string; name: string }
            | { tag: 'ANIMAL'; id: string; specie: 'CAT'; name: string }
            | { tag: 'ANIMAL'; id: string; specie: 'HORSE'; name: string }
            | { tag: 'ANIMAL'; id: string; specie: 'DOG'; name: string }
        const Pets = tableEntry<Pet>()({
            PK: ['id'],
            SK: {
                discriminator: 'tag',
                cases: [
                    [['OBJECT'], ['name']],
                    [
                        ['ANIMAL'],
                        {
                            discriminator: 'specie',
                            cases: [
                                [['CAT', 'HORSE'], null],
                                [['DOG'], ['name']],
                            ],
                        },
                    ],
                ],
            },
        })
        expect(
            Pets.key('SK', { tag: 'ANIMAL', specie: 'DOG', name: 'rex' }),
        ).toBe('NAME#rex')
        expect(
            Pets.key('SK', { tag: 'ANIMAL', specie: 'CAT', name: 'tom' }),
        ).toBeUndefined()
        expect(
            Pets.key('SK', { tag: 'ANIMAL', specie: 'HORSE', name: 'bolt' }),
        ).toBeUndefined()
    })

    it('keeps the mark of `table(...)` on a grouped key', async () => {
        const { table } = await import('../../../Rotorise')
        const Marked = tableEntry<
            { s: 'A'; id: string } | { s: 'B'; id: string }
        >()({
            PK: table({
                discriminator: 's',
                cases: [[['A', 'B'], ['id']]],
            }),
        })
        expect(Marked.keys({ s: 'A', id: 'x' })).toEqual({
            PK: { S: 'ID#x' },
        })
    })
})

describe('the type of a grouped match', () => {
    type Row =
        | { s: 'A'; id: string; n: number }
        | { s: 'B'; id: string }
        | { s: 'C'; id: string }

    it('refuses a literal that two cases name, on the literal of the second case', () => {
        expect(() =>
            tableEntry<Row>()({
                PK: ['id'],
                SK: {
                    discriminator: 's',
                    cases: [
                        [['A', 'B'], ['id']],
                        // @ts-expect-error `B` is in two cases
                        [['B', 'C'], ['id']],
                    ],
                },
            }),
        ).toThrow(RotoriseError)
    })

    it('refuses a literal that no case names, on the discriminator', () => {
        tableEntry<Row>()({
            PK: ['id'],
            SK: {
                // @ts-expect-error `C` has no case
                discriminator: 's',
                cases: [[['A', 'B'], ['id']]],
            },
        })
    })

    it('refuses a literal that the discriminator never holds', () => {
        tableEntry<Row>()({
            PK: ['id'],
            SK: {
                discriminator: 's',
                cases: [
                    // @ts-expect-error `D` is no literal of `s`
                    [['A', 'B', 'C', 'D'], ['id']],
                ],
            },
        })
    })

    it('refuses a case with an empty list of literals', () => {
        expect(() =>
            tableEntry<Row>()({
                PK: ['id'],
                SK: {
                    discriminator: 's',
                    cases: [
                        // @ts-expect-error a case names a literal
                        [[], ['id']],
                        [['A', 'B', 'C'], ['id']],
                    ],
                },
            }),
        ).toThrow(RotoriseError)
    })

    it('refuses a match that holds both spec and cases', () => {
        expect(() =>
            tableEntry<Row>()({
                PK: ['id'],
                SK: {
                    discriminator: 's',
                    // @ts-expect-error a match holds spec or cases
                    spec: { A: ['id'], B: ['id'], C: ['id'] },
                    cases: [[['A', 'B', 'C'], ['id']]],
                },
            }),
        ).toThrow(RotoriseError)
    })

    it('refuses an arm that reads what an option of its group does not hold', () => {
        tableEntry<Handoff>()({
            PK: ['id'],
            SK: {
                discriminator: 'type',
                cases: [
                    // `from` is on a transfer and not on a mint
                    // @ts-expect-error a mint holds no `from`
                    [['INTAKE', 'ADOPTION'], [['from', to]]],
                    [['FOSTER', 'RELEASE'], null],
                ],
            },
        })
    })

    it('gives the key type of the ungrouped form', () => {
        const key = Grouped.key('GSI1PK', { type: 'INTAKE', to: alice })
        key satisfies string | undefined
        const ungrouped = Ungrouped.key('GSI1PK', { type: 'INTAKE', to: alice })
        const same: typeof key = ungrouped
        expect(same).toBe('ownerId#alice')
    })

    it('reads a grouped match under a path discriminator', () => {
        type Event =
            | { id: string; meta: { kind: 'A'; a: string } }
            | { id: string; meta: { kind: 'B'; b: string } }
            | { id: string; meta: { kind: 'C'; c: string } }
        const Events = tableEntry<Event>()({
            PK: ['id'],
            SK: {
                discriminator: 'meta.kind',
                cases: [
                    [['A', 'B'], ['meta.kind']],
                    [['C'], [['meta.c', { tag: 'c' }]]],
                ],
            },
        })
        expect(Events.key('SK', { meta: { kind: 'A' } })).toBe('KIND#A')
        expect(Events.key('SK', { meta: { kind: 'C', c: 'x' } })).toBe('c#x')
    })

    it('refuses a path that an option of its group does not hold, under a path discriminator', () => {
        type Event =
            | { id: string; meta: { kind: 'A'; a: string } }
            | { id: string; meta: { kind: 'B'; b: string } }
            | { id: string; meta: { kind: 'C' } }
        tableEntry<Event>()({
            PK: ['id'],
            SK: {
                discriminator: 'meta.kind',
                cases: [
                    // @ts-expect-error `meta.b` is on a `B` and not on an `A`
                    [['A', 'B'], ['meta.b']],
                    [['C'], null],
                ],
            },
        })
    })
})
