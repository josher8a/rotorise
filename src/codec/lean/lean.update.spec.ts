/**
 * **The key updates of the pool, against the model of a key update.**
 *
 * `keyUpdates` of `src/Rotorise.ts` runs on the keys of a PetStore schema and on a change. A row
 * holds the keys as trees, the components that `keyComponents` read at the item that the update
 * reads, the values that the codec decides, the change, and what `keyUpdates` gave: a refusal of
 * one of three kinds, or a patch where each written key is the attribute at a member with a text, and
 * a removed key has no value. The member of a key comes from the declaration of the schema, and the
 * member of a written attribute comes from what the host wrote, so the comparator holds the host to
 * the member that `toItem` writes. The gate checks each row in the kernel against `update` and
 * `Tree.foot`.
 *
 * The host spec of each key comes from the tree of the row, so the host and the row cannot read two
 * specs. The rows draw a change into a `null` arm, a change out of it, a nested match, a change
 * that lacks the discriminator, and a refusal of each kind.
 */
import { writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import { keyComponents, RotoriseError, tableEntry } from '../../Rotorise'
import { number, string } from '../codec'
import {
    leanUpdateModule,
    type UpdateKey,
    type UpdateOutcome,
    type UpdateRow,
    type UpdateTree,
} from '../lean'

type Pairs = readonly (readonly [string, string])[]
/** The value of a change at a name: a string, a number, `null` where the change removes the attribute, or an object. */
type Value = string | number | null | { readonly [key: string]: Value }
/** A change: a value at each written name. */
type Changes = readonly (readonly [string, Value])[]

/**
 * The entries of a change, as the model reads them: a string at its path, and a removal. An object
 * replaces the attribute, so it is `null` at its path, and each name of the object is an entry
 * below it.
 */
const flatten = (
    name: string,
    value: Value,
): (readonly [string, string | null])[] =>
    value === null || typeof value === 'string'
        ? [[name, value]]
        : typeof value === 'number'
          ? [[name, String(value)]]
          : [
                [name, null],
                ...Object.entries(value).flatMap(([key, below]) =>
                    flatten(`${name}.${key}`, below),
                ),
            ]

/** The change as the object that `keyUpdates` reads: a removal is an own property `undefined`. */
const changeObject = (changed: Changes): Record<string, unknown> =>
    Object.fromEntries(
        changed.map(([name, value]) => [name, value ?? undefined]),
    )

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
    /** The member of the key is a number: the key reads one number attribute. */
    readonly numeric?: boolean
}

type Schema = {
    readonly name: string
    readonly keys: readonly KeyDefinition[]
    readonly decided: Pairs
    /** The entry has no codec, so a name with a `.` is a path into an object. */
    readonly plain?: boolean
    /** The dotted names that the schema declares as attributes, so the host prints the whole name. */
    readonly declared?: readonly string[]
}

type Host = {
    readonly keyUpdates: (changed: object) => {
        set: Record<string, { S: string } | { N: string }>
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
    const numbers = new Set(
        schema.keys.flatMap((key) =>
            key.numeric &&
            key.tree.kind === 'arm' &&
            key.tree.arm.kind === 'attr'
                ? [key.tree.arm.name]
                : [],
        ),
    )
    const codec = Object.fromEntries(
        [...names].map((name) => {
            const constant = decided.get(name)
            return [
                name,
                numbers.has(name)
                    ? number
                    : constant === undefined
                      ? string
                      : string(constant),
            ]
        }),
    )
    const keys = Object.fromEntries(
        schema.keys.map((key) => [key.name, specOf(key.tree)]),
    )
    // the first key of the table is the partition key, and the second is the sort key
    const [partition, sort] = schema.keys
        .filter((key) => key.ofTable)
        .map((key) => key.name)
    return make(keys, {
        ...(schema.plain ? {} : { codec }),
        ...(partition === undefined ? {} : { key: { partition, sort } }),
    })
}

/**
 * The member and the text that the host wrote at a key. An attribute that is not exactly one of
 * `{ S }` and `{ N }` fails with the name of the key, and so does a key of the SET part with no
 * attribute. No default hides a member that the model does not state.
 */
const writtenAt = (
    name: string,
    attribute: { S: string } | { N: string } | undefined,
): readonly [boolean, string] => {
    const members = attribute === undefined ? [] : Object.keys(attribute)
    if (attribute !== undefined && members.length === 1) {
        if ('S' in attribute) return [false, attribute.S]
        if ('N' in attribute) return [true, attribute.N]
    }
    throw new Error(
        `${name} is written as [${members.join(', ')}], not as S or N`,
    )
}

/** What `keyUpdates` gave, with the keys of the patch in the order of the schema. */
const hostOutcome = (
    host: Host,
    schema: Schema,
    changed: Changes,
): UpdateOutcome => {
    try {
        const { set, remove } = host.keyUpdates(changeObject(changed))
        const entries: (readonly [
            string,
            readonly [boolean, string] | null,
        ])[] = []
        for (const { name } of schema.keys) {
            const inSet = Object.hasOwn(set, name)
            const inRemove = remove.includes(name)
            expect(inSet && inRemove, `${name} is in both parts`).toBe(false)
            if (inSet) entries.push([name, writtenAt(name, set[name])])
            if (inRemove) entries.push([name, null])
        }
        return { kind: 'patch', entries }
    } catch (thrown) {
        if (!(thrown instanceof RotoriseError)) throw thrown
        const { kind } = thrown
        return {
            kind: kind === 'decided' || kind === 'rewrite' ? kind : 'unbuilt',
        }
    }
}

/** The components that `keyComponents` read at the item that the update reads. */
const footprintOf = (
    key: KeyDefinition,
    decided: Pairs,
    changed: Changes,
): string[] => [
    ...keyComponents(specOf(key.tree), {
        ...Object.fromEntries(decided),
        ...changeObject(changed),
    }),
]

const rowOf = (
    name: string,
    schema: Schema,
    changed: Changes,
    separator = '#',
): UpdateRow => {
    const keys: UpdateKey[] = schema.keys.map((key) => ({
        name: key.name,
        numeric: key.numeric ?? false,
        tree: key.tree,
        ofTable: key.ofTable ?? false,
        footprint: footprintOf(key, schema.decided, changed),
    }))
    return {
        name,
        keys,
        decided: schema.decided,
        declared: schema.declared ?? [],
        changed: changed.flatMap(([key, value]) => flatten(key, value)),
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

/** A pet and its owner: a key reads a path into the object of the owner, and the entry has no codec. */
const owners: Schema = {
    name: 'owners',
    decided: [],
    plain: true,
    keys: [
        { name: 'PK', tree: parts('petId'), ofTable: true },
        { name: 'GSI1PK', tree: parts('owner.name') },
    ],
}

/** A pet whose entity holds the dotted name `owner.name` as one attribute, and the entry has no codec. */
const dotted: Schema = {
    name: 'dotted',
    decided: [],
    plain: true,
    declared: ['owner.name'],
    keys: [
        { name: 'PK', tree: parts('petId'), ofTable: true },
        { name: 'GSI1PK', tree: parts('owner.name') },
    ],
}

/** A key that reads the whole attribute of the owner. */
const wholes: Schema = {
    name: 'wholes',
    decided: [],
    plain: true,
    keys: [
        { name: 'PK', tree: parts('petId'), ofTable: true },
        { name: 'GSI1PK', tree: parts('owner') },
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

/** A pet with an age: the sort key of the age is one number attribute, so its member is a number. */
const aged: Schema = {
    name: 'aged',
    decided: [],
    keys: [
        { name: 'PK', tree: parts('petId'), ofTable: true },
        { name: 'GSI1PK', tree: parts('shelter') },
        { name: 'GSI1SK', tree: attr('age'), numeric: true },
    ],
}

const cases: readonly [string, Schema, Changes][] = [
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
    ['writes_an_empty_component', shipments, [['status', '']]],
    [
        'writes_a_dotted_name_that_the_entity_holds',
        dotted,
        [['owner.name', 'ann']],
    ],
    ['moves_the_item_by_a_component', shipments, [['shipmentId', 's2']]],
    ['removes_an_attribute_key', pets, [['nickname', null]]],
    ['removes_a_component_of_a_leaf', shipments, [['provider', null]]],
    ['removes_a_discriminator', pets, [['status', null]]],
    [
        'removes_a_component_of_a_match_arm',
        pets,
        [
            ['status', 'AVAILABLE'],
            ['shelter', null],
            ['species', 'CAT'],
        ],
    ],
    ['removes_a_decided_name', shipments, [['TAG', null]]],
    ['writes_a_parent_of_a_component', owners, [['owner', { name: 'ann' }]]],
    ['writes_an_empty_parent', owners, [['owner', {}]]],
    ['removes_a_parent', owners, [['owner', null]]],
    ['writes_a_child_of_a_component', wholes, [['owner.name', 'ann']]],
    ['writes_a_sibling_of_a_component', owners, [['owner.age', '3']]],
    ['writes_a_child_of_a_path', owners, [['owner.name.first', 'ann']]],
    ['writes_a_number', aged, [['age', 3]]],
    ['writes_a_fraction', aged, [['age', 1.5]]],
    ['removes_a_number', aged, [['age', null]]],
    ['writes_a_key_beside_a_number', aged, [['shelter', 's1']]],
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
                ['GSI2PK', [false, 'OWNER#ann']],
            ],
        })
    })

    it('sets the key out of a null arm', () => {
        expect(row('pets_out_of_a_null_arm').outcome).toEqual({
            kind: 'patch',
            entries: [
                ['GSI1PK', [false, 'SHELTER#s1']],
                ['GSI2PK', [false, 'SHELTER#s1']],
            ],
        })
    })

    it('removes the key of a null arm of a nested match', () => {
        expect(row('pets_into_a_nested_null_arm').outcome).toEqual({
            kind: 'patch',
            entries: [
                ['GSI1PK', [false, 'SHELTER#s1']],
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

    it('removes the key of an attribute that the change removes', () => {
        expect(row('pets_removes_an_attribute_key').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI4PK', null]],
        })
    })

    it('refuses to build the key of a component that the change removes', () => {
        expect(row('shipments_removes_a_component_of_a_leaf').outcome).toEqual({
            kind: 'unbuilt',
        })
        expect(row('pets_removes_a_component_of_a_match_arm').outcome).toEqual({
            kind: 'unbuilt',
        })
    })

    it('refuses as a rewrite where the change removes a discriminator, because the key then reads every arm', () => {
        expect(row('pets_removes_a_discriminator').outcome).toEqual({
            kind: 'rewrite',
        })
    })

    it('rebuilds the key of a component below a written object, and reads its value from the object', () => {
        expect(row('owners_writes_a_parent_of_a_component').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI1PK', [false, 'NAME#ann']]],
        })
    })

    it('gives no component for the empty text, and refuses the key as for an absent value', () => {
        expect(row('shipments_writes_an_empty_component').outcome).toEqual({
            kind: 'unbuilt',
        })
    })

    it('prints the whole name of a dotted name that the entity holds, and the last name of a path', () => {
        expect(
            row('dotted_writes_a_dotted_name_that_the_entity_holds').outcome,
        ).toEqual({
            kind: 'patch',
            entries: [['GSI1PK', [false, 'OWNER.NAME#ann']]],
        })
        expect(row('owners_writes_a_parent_of_a_component').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI1PK', [false, 'NAME#ann']]],
        })
    })

    it('refuses to build the key of a component that a written parent leaves out, or removes', () => {
        expect(row('owners_writes_an_empty_parent').outcome).toEqual({
            kind: 'unbuilt',
        })
        expect(row('owners_removes_a_parent').outcome).toEqual({
            kind: 'unbuilt',
        })
    })

    it('refuses to build the key of a component above a written path', () => {
        expect(row('wholes_writes_a_child_of_a_component').outcome).toEqual({
            kind: 'unbuilt',
        })
        expect(row('owners_writes_a_child_of_a_path').outcome).toEqual({
            kind: 'unbuilt',
        })
    })

    it('leaves a key alone where the written path is no path above or below a component', () => {
        expect(row('owners_writes_a_sibling_of_a_component').outcome).toEqual({
            kind: 'patch',
            entries: [],
        })
    })

    it('refuses the removal of a name that the codec decides', () => {
        expect(row('shipments_removes_a_decided_name').outcome).toEqual({
            kind: 'decided',
        })
    })

    it('writes the member of a number key as N, the member that toItem writes', () => {
        expect(row('aged_writes_a_number').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI1SK', [true, '3']]],
        })
        expect(row('aged_writes_a_fraction').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI1SK', [true, '1.5']]],
        })
    })

    it('removes the key of a number that the change removes, and leaves the number key alone beside it', () => {
        expect(row('aged_removes_a_number').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI1SK', null]],
        })
        expect(row('aged_writes_a_key_beside_a_number').outcome).toEqual({
            kind: 'patch',
            entries: [['GSI1PK', [false, 'SHELTER#s1']]],
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
