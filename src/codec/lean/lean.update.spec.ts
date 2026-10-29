/**
 * **The key updates of the pool, against the model of a key update.**
 *
 * `keyUpdates` of `src/Rotorise.ts` runs on the keys of a PetStore schema and on a change. A row
 * holds the keys as trees, the components that `keyComponents` read at the item that the update
 * reads, the values that the codec decides, the change, and what `keyUpdates` gave: a refusal of
 * one of three kinds, or a patch where a removed key has no value. The gate checks each row in the
 * kernel against `update` and `Tree.foot`.
 *
 * The host spec of each key comes from the tree of the row, so the host and the row cannot read two
 * specs. The rows draw a change into a `null` arm, a change out of it, a nested match, a change
 * that lacks the discriminator, and a refusal of each kind.
 */
import { writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import { keyComponents, RotoriseError, table, tableEntry } from '../../Rotorise'
import { string } from '../codec'
import {
    leanUpdateModule,
    type UpdateKey,
    type UpdateOutcome,
    type UpdateRow,
    type UpdateTree,
} from '../lean'

type Pairs = readonly (readonly [string, string])[]

/** A leaf of plain components. */
const parts = (...names: string[]): UpdateTree => ({
    kind: 'arm',
    arm: { kind: 'components', names },
})
const nothing: UpdateTree = { kind: 'arm', arm: { kind: 'null' } }
const attr = (name: string): UpdateTree => ({
    kind: 'arm',
    arm: { kind: 'attr', name },
})
const match = (
    discriminator: string,
    ...arms: (readonly [string, UpdateTree])[]
): UpdateTree => ({ kind: 'match', discriminator, arms })

/** The spec that the host reads for a tree. */
const specOf = (tree: UpdateTree): unknown => {
    if (tree.kind === 'match') {
        return {
            discriminator: tree.discriminator,
            spec: Object.fromEntries(
                tree.arms.map(([literal, arm]) => [literal, specOf(arm)]),
            ),
        }
    }
    switch (tree.arm.kind) {
        case 'components':
            return tree.arm.names
        case 'null':
            return null
        case 'attr':
            return tree.arm.name
        case 'missing':
            throw new Error('the host has no spec for the arm that it lacks')
    }
}

type KeyDefinition = {
    readonly name: string
    readonly tree: UpdateTree
    readonly ofTable?: boolean
}

type Schema = {
    readonly name: string
    readonly keys: readonly KeyDefinition[]
    readonly decided: Pairs
}

type Host = {
    readonly keyUpdates: (changed: object) => {
        set: Record<string, { S: string }>
        remove: readonly string[]
    }
}

/** The table entry of `src/` for the keys of a schema, with the constants that the codec decides. */
const entryOf = (schema: Schema): Host => {
    const make = tableEntry<Record<string, unknown>>() as unknown as (
        keys: unknown,
        options: unknown,
    ) => Host
    const names = new Set<string>(schema.decided.map(([name]) => name))
    const visit = (tree: UpdateTree): void => {
        if (tree.kind === 'match') {
            names.add(tree.discriminator)
            for (const [, arm] of tree.arms) visit(arm)
        } else if (tree.arm.kind === 'components') {
            for (const name of tree.arm.names) names.add(name)
        } else if (tree.arm.kind === 'attr') {
            names.add(tree.arm.name)
        }
    }
    for (const key of schema.keys) visit(key.tree)
    const decided = new Map(schema.decided)
    const codec = Object.fromEntries(
        [...names].map((name) => {
            const constant = decided.get(name)
            return [name, constant === undefined ? string : string(constant)]
        }),
    )
    const keys = Object.fromEntries(
        schema.keys.map((key) => [
            key.name,
            key.ofTable ? table(specOf(key.tree) as never) : specOf(key.tree),
        ]),
    )
    return make(keys, { codec })
}

/** What `keyUpdates` gave, with the keys of the patch in the order of the schema. */
const hostOutcome = (
    host: Host,
    schema: Schema,
    changed: Pairs,
): UpdateOutcome => {
    try {
        const { set, remove } = host.keyUpdates(Object.fromEntries(changed))
        const entries: (readonly [string, string | null])[] = []
        for (const { name } of schema.keys) {
            const inSet = Object.hasOwn(set, name)
            const inRemove = remove.includes(name)
            expect(inSet && inRemove, `${name} is in both parts`).toBe(false)
            if (inSet) entries.push([name, set[name]?.S ?? ''])
            if (inRemove) entries.push([name, null])
        }
        return { kind: 'patch', entries }
    } catch (thrown) {
        if (!(thrown instanceof RotoriseError)) throw thrown
        if (/is decided by the codec/.test(thrown.message))
            return { kind: 'decided' }
        if (
            /is the table's own key|has to be rebuilt, but/.test(thrown.message)
        )
            return { kind: 'rewrite' }
        return { kind: 'unbuilt' }
    }
}

/** The components that `keyComponents` read at the item that the update reads. */
const footprintOf = (
    key: KeyDefinition,
    decided: Pairs,
    changed: Pairs,
): string[] => [
    ...keyComponents(specOf(key.tree), {
        ...Object.fromEntries(decided),
        ...Object.fromEntries(changed),
    }),
]

const rowOf = (
    name: string,
    schema: Schema,
    changed: Pairs,
    separator = '#',
): UpdateRow => {
    const keys: UpdateKey[] = schema.keys.map((key) => ({
        name: key.name,
        tree: key.tree,
        ofTable: key.ofTable ?? false,
        footprint: footprintOf(key, schema.decided, changed),
    }))
    return {
        name,
        keys,
        decided: schema.decided,
        changed,
        separator,
        outcome: hostOutcome(entryOf(schema), schema, changed),
    }
}

/** A pet is adopted, or is available at a shelter, and an available pet is a cat or a dog. */
const pets: Schema = {
    name: 'pets',
    decided: [],
    keys: [
        { name: 'PK', tree: parts('petId'), ofTable: true },
        {
            name: 'GSI1PK',
            tree: match(
                'status',
                ['ADOPTED', nothing],
                ['AVAILABLE', parts('shelter')],
            ),
        },
        {
            name: 'GSI2PK',
            tree: match(
                'status',
                ['ADOPTED', parts('owner')],
                [
                    'AVAILABLE',
                    match(
                        'species',
                        ['CAT', parts('shelter')],
                        ['DOG', nothing],
                    ),
                ],
            ),
        },
        { name: 'GSI4PK', tree: attr('nickname') },
    ],
}

/** A shipment of a pet: the codec decides the tag. */
const shipments: Schema = {
    name: 'shipments',
    decided: [['TAG', 'PET']],
    keys: [
        { name: 'SK', tree: parts('TAG', 'shipmentId'), ofTable: true },
        { name: 'GSI1PK', tree: parts('TAG', 'status') },
        { name: 'GSI2PK', tree: parts('provider') },
    ],
}

const cases: readonly [string, Schema, Pairs][] = [
    [
        'into_a_null_arm',
        pets,
        [
            ['status', 'ADOPTED'],
            ['owner', 'ann'],
        ],
    ],
    [
        'out_of_a_null_arm',
        pets,
        [
            ['status', 'AVAILABLE'],
            ['species', 'CAT'],
            ['shelter', 's1'],
        ],
    ],
    [
        'into_a_nested_null_arm',
        pets,
        [
            ['status', 'AVAILABLE'],
            ['species', 'DOG'],
            ['shelter', 's1'],
        ],
    ],
    ['lacks_the_discriminator', pets, [['shelter', 's1']]],
    [
        'lacks_the_inner_discriminator',
        pets,
        [
            ['status', 'AVAILABLE'],
            ['shelter', 's1'],
        ],
    ],
    [
        'names_no_arm',
        pets,
        [
            ['status', 'LOST'],
            ['species', 'CAT'],
            ['shelter', 's1'],
        ],
    ],
    ['moves_the_item', pets, [['petId', 'p2']]],
    ['writes_an_attribute_key', pets, [['nickname', 'rex']]],
    ['writes_no_key_attribute', pets, []],
    ['rebuilds_a_decided_component', shipments, [['status', 'SETTLED']]],
    [
        'writes_the_decided_value',
        shipments,
        [
            ['status', 'SETTLED'],
            ['TAG', 'PET'],
        ],
    ],
    [
        'writes_another_decided_value',
        shipments,
        [
            ['status', 'SETTLED'],
            ['TAG', 'FISH'],
        ],
    ],
    ['rebuilds_one_key', shipments, [['provider', 'p1']]],
    ['holds_the_separator', shipments, [['status', 'A#B']]],
    ['moves_the_item_by_a_component', shipments, [['shipmentId', 's2']]],
]

const rows: readonly UpdateRow[] = cases.map(([name, schema, changed]) =>
    rowOf(`${schema.name}_${name}`, schema, changed),
)

const row = (name: string): UpdateRow => {
    const found = rows.find((candidate) => candidate.name === name)
    if (found === undefined) throw new Error(`no row ${name}`)
    return found
}

describe('the key updates of the pool', () => {
    it('removes the key of a null arm, and sets the key of the other arm', () => {
        expect(row('pets_into_a_null_arm').outcome).toEqual({
            kind: 'patch',
            entries: [
                ['GSI1PK', null],
                ['GSI2PK', 'OWNER#ann'],
            ],
        })
    })

    it('sets the key out of a null arm', () => {
        expect(row('pets_out_of_a_null_arm').outcome).toEqual({
            kind: 'patch',
            entries: [
                ['GSI1PK', 'SHELTER#s1'],
                ['GSI2PK', 'SHELTER#s1'],
            ],
        })
    })

    it('removes the key of a null arm of a nested match', () => {
        expect(row('pets_into_a_nested_null_arm').outcome).toEqual({
            kind: 'patch',
            entries: [
                ['GSI1PK', 'SHELTER#s1'],
                ['GSI2PK', null],
            ],
        })
    })

    it('refuses where the change lacks a discriminator that a touched key reads', () => {
        expect(row('pets_lacks_the_discriminator').outcome).toEqual({
            kind: 'rewrite',
        })
        expect(row('pets_lacks_the_inner_discriminator').outcome).toEqual({
            kind: 'rewrite',
        })
    })

    it('draws a refusal of each kind', () => {
        const kinds = new Set(rows.map((candidate) => candidate.outcome.kind))
        expect(kinds).toEqual(
            new Set(['decided', 'rewrite', 'unbuilt', 'patch']),
        )
    })

    it('reads every arm of a match where the item lacks the discriminator', () => {
        const lacking = row('pets_lacks_the_discriminator').keys.find(
            (key) => key.name === 'GSI2PK',
        )
        expect([...(lacking?.footprint ?? [])].sort()).toEqual([
            'owner',
            'shelter',
            'species',
            'status',
        ])
    })

    it('emits the update rows for the gate', () => {
        const text = leanUpdateModule(rows)
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(join(process.cwd(), 'formal', '.updates.lean'), text)
        }
        expect(text).toContain(
            'theorem updateRows_check : failingUpdates updateRows = []',
        )
        expect(text.trimEnd().endsWith('#assert_axioms_module')).toBe(true)
    })
})
