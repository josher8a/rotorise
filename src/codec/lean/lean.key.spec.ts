/**
 * **The key rows of the pool, against the model of a derived key.**
 *
 * The key builder of `src/Rotorise.ts` runs on each key spec of the pool, each item of the spec,
 * and each option. A row holds what the builder read and what the builder gave, and the gate checks
 * each row in the kernel against `DerivedKey.build` and `DerivedKey.join`. The pool holds the shapes
 * that the builder reads: a plain component, a transform that gives a tag and a value, a tagless
 * transform, a transform with a default, a discriminated spec, a `null` arm, and an arm that names
 * one attribute, and a match that nests inside an arm. An item can lack the discriminator or hold a literal that names no arm. A value
 * that holds the separator is a row where the segment list is not usable as a key.
 *
 * The parts of a row come from {@link partsOf}, a second reading of the spec. The test joins the
 * parts as the model does, and compares the result with the key of the builder, so a wrong reading
 * fails here before the gate.
 */
import { writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../Rotorise'
import {
    type KeyArm,
    type KeyOutcome,
    type KeyPart,
    type KeyRow,
    type KeyTree,
    leanKeyModule,
} from '../lean'

type Transform = (value: unknown) => unknown
type Tag = { readonly tag: string }
type Component =
    | string
    | readonly [string, Transform, unknown?]
    | readonly [string, Tag]
type Discriminated =
    | {
          readonly discriminator: string
          readonly spec: Readonly<Record<string, Arm>>
      }
    | {
          readonly discriminator: string
          readonly cases: readonly (readonly [readonly string[], Arm])[]
      }
type Arm = readonly Component[] | string | null | Discriminated
type Spec = readonly Component[] | Discriminated
type Item = Readonly<Record<string, unknown>>
type Config = {
    readonly depth?: number
    readonly allowPartial?: boolean
    readonly enforceBoundary?: boolean
}

const tagless: Transform = (x) => ({ value: x })
const tagged: Transform = (x) => ({ tag: 'T', value: x })
const untagged: Transform = (x) => ({ tag: undefined, value: x })
const nulled: Transform = () => ({ value: null })
const bracket: Transform = (x) => `<${String(x)}>`
const doubled: Transform = (x) => ({ tag: 'N', value: Number(x) * 2 })

/** The table entry of `src/` for a schema with one key. */
const entryOf = (spec: Spec, separator: string) => {
    const make = tableEntry<Record<string, unknown>>() as unknown as (
        schema: unknown,
        options: { readonly separator: string },
    ) => {
        readonly key: (name: string, item: object, config?: object) => unknown
        readonly toEntry: (item: object) => Record<string, unknown>
        readonly fromEntry: (entry: object) => unknown
    }
    return make({ K: spec }, { separator })
}

/** The builder of `src/`, reached through the table entry. */
const builderOf = (spec: Spec, separator: string) =>
    entryOf(spec, separator).key

/** What the builder gave: a key, no key, or a throw of the library. */
const hostOutcome = (
    run: ReturnType<typeof builderOf>,
    item: Item,
    config: Config,
): KeyOutcome => {
    try {
        const key = run('K', item, config)
        if (key === undefined || key === null) return { kind: 'nothing' }
        if (typeof key !== 'string')
            throw new Error('the builder gave a non-key')
        return { kind: 'key', key }
    } catch (thrown) {
        if (thrown instanceof RotoriseError) {
            return /holds the separator/.test(thrown.message)
                ? { kind: 'separator' }
                : { kind: 'refused' }
        }
        throw thrown
    }
}

/** The string that `Array.prototype.join` writes for a value. */
const segment = (value: unknown): string =>
    value === undefined || value === null ? '' : String(value)

const segmentsOf = (part: KeyPart & object): string[] =>
    part.kind === 'named'
        ? [part.name, part.value]
        : part.tag === undefined
          ? [part.value]
          : [part.tag, part.value]

/** The value at a path of names, through own properties of objects, or `undefined`. */
const readAt = (item: unknown, path: string): unknown => {
    let current: unknown = item
    for (const name of path.split('.')) {
        if (
            typeof current !== 'object' ||
            current === null ||
            !Object.hasOwn(current, name)
        )
            return undefined
        current = (current as Record<string, unknown>)[name]
    }
    return current
}

/** A copy of an item with a value at a path, or without the name at the path where the value is `DROP`. */
const DROP = Symbol('drop')
const writeAt = (item: Item, path: string, value: unknown): Item => {
    const [head, ...rest] = path.split('.') as [string, ...string[]]
    const { [head]: below, ...others } = item
    if (rest.length === 0)
        return value === DROP ? others : { ...others, [head]: value }
    const inner = typeof below === 'object' && below !== null ? below : {}
    return { ...others, [head]: writeAt(inner as Item, rest.join('.'), value) }
}

/**
 * The parts of a spec for an item, as a second reading of the spec: the components cut to the
 * depth, up to and including the first component that the builder refuses. A component is absent
 * where its value is undefined, and, with no transform, where its value is null or empty. A
 * component is refused as a separator where one of its segments holds the separator.
 */
const partsOf = (
    components: readonly Component[],
    item: Item,
    depth: number | undefined,
    separator: string,
): KeyPart[] => {
    const parts: KeyPart[] = []
    for (const component of depth === undefined
        ? components
        : components.slice(0, depth)) {
        const [name, second, fallback] =
            typeof component === 'string' ? [component] : component
        const transform = typeof second === 'function' ? second : undefined
        const tag =
            typeof second === 'object' && second !== null
                ? second.tag
                : undefined
        const printed = (name.split('.').pop() ?? name).toUpperCase()
        const value = readAt(item, name) ?? fallback
        let part: KeyPart
        if (transform !== undefined && value !== undefined) {
            const out = transform(value)
            if (typeof out === 'object' && out !== null) {
                const { tag, value: inner } = out as {
                    tag?: string
                    value: unknown
                }
                part = { kind: 'shaped', tag, value: segment(inner) }
            } else {
                part = {
                    kind: 'named',
                    name: printed,
                    value: segment(out),
                }
            }
        } else if (value !== undefined && value !== null && value !== '') {
            part =
                tag === undefined
                    ? { kind: 'named', name: printed, value: segment(value) }
                    : { kind: 'shaped', tag, value: segment(value) }
        } else {
            parts.push(undefined)
            break
        }
        parts.push(part)
        if (segmentsOf(part).some((one) => one.includes(separator))) break
    }
    return parts
}

/** The arm that the item of a row reaches, as `KeyMatch.select` states it. */
const selectArm = (tree: KeyTree, item: KeyRow['item']): KeyArm => {
    if (tree.kind === 'arm') return tree.arm
    const value = item.find(([name]) => name === tree.discriminator)?.[1]
    const arm =
        tree.kind === 'cases'
            ? tree.cases.find(([literals]) =>
                  literals.some((literal) => literal === value),
              )?.[1]
            : tree.arms.find(([literal]) => literal === value)?.[1]
    return value === undefined || arm === undefined
        ? { kind: 'missing' }
        : selectArm(arm, item)
}

/** The leaf that the item of a row reaches, or `undefined`. */
const leafOf = (row: KeyRow) => {
    const arm = selectArm(row.tree, row.item)
    return arm.kind === 'leaf' ? arm : undefined
}

/** The segments that the model states for a row, as `DerivedKey.build` states them, or `undefined` where it refuses. */
const modelSegments = (row: KeyRow): string[] | undefined => {
    const arm = selectArm(row.tree, row.item)
    if (arm.kind !== 'leaf') return undefined
    const printed: (KeyPart & object)[] = []
    for (const part of arm.parts) {
        if (part === undefined) {
            if (row.allowPartial) break
            return undefined
        }
        printed.push(part)
    }
    const segments = printed.flatMap(segmentsOf)
    if (row.enforce && printed.length < arm.full) segments.push('')
    return segments
}

/** The key that the model states for a row: the join of the segments, or the printed attribute. */
const modelKey = (row: KeyRow): string | undefined => {
    const arm = selectArm(row.tree, row.item)
    return arm.kind === 'attr'
        ? row.item.find(([name]) => name === arm.name)?.[1]
        : modelSegments(row)?.join(row.separator)
}

const isLawful = (row: KeyRow): boolean => {
    const segments = modelSegments(row)
    return (
        segments !== undefined &&
        segments.length > 0 &&
        segments.every((one) => !one.includes(row.separator))
    )
}

const base: Item = {
    a: '1',
    b: '2',
    c: '3',
    n: 7,
    kind: 'x',
    meta: { a: '1', b: '2', n: 7, kind: 'x' },
}

type Case = {
    readonly name: string
    readonly spec: Spec
    readonly separator?: string
}

/** The key specs of the pool. */
const cases: readonly Case[] = [
    { name: 'plain', spec: ['a', 'b'] },
    { name: 'three', spec: ['a', 'b', 'c'] },
    { name: 'single', spec: ['a'] },
    { name: 'tagless', spec: [['a', tagless], 'b'] },
    { name: 'tagged', spec: [['a', tagged], 'b'] },
    { name: 'untagged', spec: [['a', untagged], 'b'] },
    { name: 'text', spec: [['a', bracket], 'b'] },
    { name: 'number', spec: [['n', doubled], 'a'] },
    { name: 'nulled', spec: [['a', nulled], 'b'] },
    { name: 'default', spec: [['c', tagged, 'dflt'], 'a'] },
    { name: 'defaultText', spec: [['c', bracket, 'dflt'], 'a'] },
    { name: 'numeral', spec: ['n', 'a'] },
    {
        name: 'discriminated',
        spec: {
            discriminator: 'kind',
            spec: { x: ['a', 'b'], y: [['a', tagless]], z: null },
        },
    },
    {
        name: 'attribute',
        spec: {
            discriminator: 'kind',
            spec: { x: 'a', y: ['a', 'b'], z: null },
        },
    },
    {
        name: 'attributeOnly',
        spec: { discriminator: 'kind', spec: { x: 'b', y: 'c' } },
    },
    {
        name: 'nested',
        spec: {
            discriminator: 'tag',
            spec: {
                OBJECT: ['a'],
                ANIMAL: {
                    discriminator: 'specie',
                    spec: {
                        CAT: null,
                        HORSE: [['a', tagged]],
                        DOG: {
                            discriminator: 'breed',
                            spec: { LAB: ['a', 'b'], PUG: 'c' },
                        },
                    },
                },
            },
        },
    },
    {
        name: 'nestedFlat',
        spec: {
            discriminator: 'kind',
            spec: {
                x: {
                    discriminator: 'sub',
                    spec: { p: ['a'], q: 'b', r: null },
                },
                y: ['a', 'b'],
                z: null,
            },
        },
    },
    { name: 'path', spec: ['meta.a', 'b'] },
    { name: 'pathTag', spec: [['meta.a', { tag: 'PRICE' }], 'b'] },
    { name: 'tagOnly', spec: [['a', { tag: 'PRICE' }], 'b'] },
    { name: 'pathTransform', spec: [['meta.n', doubled], 'meta.b'] },
    { name: 'pathDefault', spec: [['meta.c', tagged, 'dflt'], 'a'] },
    {
        name: 'pathDiscriminator',
        spec: {
            discriminator: 'meta.kind',
            spec: { x: ['meta.a'], y: 'meta.b', z: null },
        },
    },
    {
        name: 'nestedPath',
        spec: {
            discriminator: 'kind',
            spec: {
                x: {
                    discriminator: 'meta.kind',
                    spec: {
                        p: [['meta.a', { tag: 'T' }]],
                        q: 'meta.b',
                        r: null,
                    },
                },
                y: ['a', 'meta.b'],
                z: null,
            },
        },
    },
    {
        name: 'grouped',
        spec: {
            discriminator: 'kind',
            cases: [
                [
                    ['x', 'y'],
                    ['a', 'b'],
                ],
                [['z'], null],
            ],
        },
    },
    {
        name: 'groupedAttribute',
        spec: {
            discriminator: 'kind',
            cases: [
                [['x', 'y'], 'a'],
                [['z'], [['a', tagged], 'b']],
            ],
        },
    },
    {
        name: 'groupedNested',
        spec: {
            discriminator: 'tag',
            cases: [
                [['OBJECT'], ['a']],
                [
                    ['ANIMAL'],
                    {
                        discriminator: 'specie',
                        cases: [
                            [['CAT', 'HORSE'], null],
                            [
                                ['DOG'],
                                {
                                    discriminator: 'breed',
                                    cases: [
                                        [
                                            ['LAB', 'PUG'],
                                            ['a', 'b'],
                                        ],
                                    ],
                                },
                            ],
                        ],
                    },
                ],
            ],
        },
    },
    {
        name: 'groupedPath',
        spec: {
            discriminator: 'meta.kind',
            cases: [
                [['x', 'y'], ['meta.a']],
                [['z'], 'meta.b'],
            ],
        },
    },
    { name: 'dashPlain', spec: ['a', 'b'], separator: '-' },
    { name: 'dashTagless', spec: [['a', tagless], 'b'], separator: '-' },
]

const isDiscriminated = (arm: Arm): arm is Discriminated =>
    typeof arm === 'object' && arm !== null && !Array.isArray(arm)

/** The arm of each literal of a match, for a match that groups literals and for one that does not. */
const entriesOf = (arm: Discriminated): (readonly [string, Arm])[] =>
    'cases' in arm
        ? arm.cases.flatMap(([literals, inner]) =>
              literals.map((literal) => [literal, inner] as const),
          )
        : Object.entries(arm.spec)

/** The tree of an arm for an item: each arm is evaluated, and the item selects one. */
const treeOf = (
    arm: Arm,
    item: Item,
    depth: number | undefined,
    separator: string,
): KeyTree =>
    isDiscriminated(arm)
        ? 'cases' in arm
            ? {
                  kind: 'cases',
                  discriminator: arm.discriminator,
                  cases: arm.cases.map(
                      ([literals, inner]) =>
                          [
                              literals,
                              treeOf(inner, item, depth, separator),
                          ] as const,
                  ),
              }
            : {
                  kind: 'match',
                  discriminator: arm.discriminator,
                  arms: Object.entries(arm.spec).map(
                      ([literal, inner]) =>
                          [
                              literal,
                              treeOf(inner, item, depth, separator),
                          ] as const,
                  ),
              }
        : {
              kind: 'arm',
              arm:
                  arm === null
                      ? { kind: 'null' }
                      : typeof arm === 'string'
                        ? { kind: 'attr', name: arm }
                        : {
                              kind: 'leaf',
                              full: arm.length,
                              parts: partsOf(arm, item, depth, separator),
                          },
          }

/** The attributes that a tree reads: each discriminator, and each attribute that an arm names. */
const readNames = (arm: Arm): string[] =>
    isDiscriminated(arm)
        ? [
              arm.discriminator,
              ...entriesOf(arm).flatMap(([, inner]) => readNames(inner)),
          ]
        : typeof arm === 'string'
          ? [arm]
          : []

/** The printed attributes of the item that the tree reads. */
const itemOf = (spec: Spec, item: Item): KeyRow['item'] =>
    [...new Set(readNames(spec))].flatMap((name) => {
        const value = readAt(item, name)
        return value === undefined || value === null
            ? []
            : [[name, String(value)] as const]
    })

/** The components of each list arm of a spec, at each depth. */
const componentsOf = (arm: Arm): readonly (readonly Component[])[] =>
    isDiscriminated(arm)
        ? entriesOf(arm).flatMap(([, inner]) => componentsOf(inner))
        : Array.isArray(arm)
          ? [arm as readonly Component[]]
          : []

/** The attributes that a spec reads, other than its discriminators: components and named attributes. */
const namesOf = (spec: Spec): string[] => [
    ...new Set([
        ...componentsOf(spec)
            .flat()
            .map((c) => (typeof c === 'string' ? c : c[0])),
        ...readNames(spec).filter(
            (name) => !discriminatorsOf(spec).includes(name),
        ),
    ]),
]

const discriminatorsOf = (arm: Arm): string[] =>
    isDiscriminated(arm)
        ? [
              arm.discriminator,
              ...entriesOf(arm).flatMap(([, inner]) => discriminatorsOf(inner)),
          ]
        : []

type Path = Readonly<Record<string, string>>

/** The assignments of discriminators that reach each arm that is not a match. */
const pathsOf = (arm: Arm): Path[] =>
    isDiscriminated(arm)
        ? entriesOf(arm).flatMap(([literal, inner]) =>
              pathsOf(inner).map((path) => ({
                  [arm.discriminator]: literal,
                  ...path,
              })),
          )
        : [{}]

/** Each match of a spec, with the assignments that reach it. */
const stopsOf = (
    arm: Arm,
    prefix: Path = {},
): { prefix: Path; discriminator: string }[] =>
    isDiscriminated(arm)
        ? [
              { prefix, discriminator: arm.discriminator },
              ...entriesOf(arm).flatMap(([literal, inner]) =>
                  stopsOf(inner, { ...prefix, [arm.discriminator]: literal }),
              ),
          ]
        : []

/** The literals that name a property of `Object.prototype`, which name no arm. */
const prototypeNames = [
    'constructor',
    'toString',
    '__proto__',
    'hasOwnProperty',
]

/**
 * The items of a case: for each path of literals the full item, and each used attribute absent,
 * empty, null and with the separator. At each match: an absent discriminator, an empty one, a null
 * one, a literal that names no arm, and each literal that names a property of the prototype.
 */
const itemsOf = (one: Case): Item[] => {
    const sep = one.separator ?? '#'
    const reach = (prefix: Path): Item =>
        Object.entries(prefix).reduce(
            (item, [path, literal]) => writeAt(item, path, literal),
            base,
        )
    const onPaths = pathsOf(one.spec).flatMap((path) => {
        const start = reach(path)
        const items: Item[] = [start]
        for (const name of namesOf(one.spec)) {
            items.push(
                writeAt(start, name, DROP),
                writeAt(start, name, ''),
                writeAt(start, name, null),
                writeAt(start, name, `x${sep}y`),
            )
            if (name.includes('.'))
                items.push(writeAt(start, name.split('.')[0] ?? name, DROP))
        }
        return items
    })
    const atMatches = stopsOf(one.spec).flatMap(({ prefix, discriminator }) => {
        const start = reach(prefix)
        return [
            writeAt(start, discriminator, DROP),
            ...['w', '', null, ...prototypeNames].map((value) =>
                writeAt(start, discriminator, value),
            ),
        ]
    })
    return [...onPaths, ...atMatches]
}

const depths: readonly (number | undefined)[] = [undefined, 0, 1, 2]
const flags: readonly (boolean | undefined)[] = [undefined, true]

/** The rows of the pool, one for each case, item and option, without a repeat. */
const keyRows = (): KeyRow[] => {
    const rows: KeyRow[] = []
    const seen = new Set<string>()
    for (const one of cases) {
        const separator = one.separator ?? '#'
        const run = builderOf(one.spec, separator)
        for (const item of itemsOf(one)) {
            for (const depth of depths)
                for (const allowPartial of flags)
                    for (const enforceBoundary of flags) {
                        const config: Config = {
                            ...(depth === undefined ? {} : { depth }),
                            ...(allowPartial === undefined
                                ? {}
                                : { allowPartial }),
                            ...(enforceBoundary === undefined
                                ? {}
                                : { enforceBoundary }),
                        }
                        const outcome = hostOutcome(run, item, config)
                        const draft = {
                            name: '',
                            tree: treeOf(one.spec, item, depth, separator),
                            item: itemOf(one.spec, item),
                            allowPartial: allowPartial === true,
                            enforce: enforceBoundary === true,
                            separator,
                            outcome,
                            lawful: false,
                        }
                        const lawful = outcome.kind === 'key' && isLawful(draft)
                        const named = `${one.name}_${rows.length}`
                        const row = { ...draft, name: named, lawful }
                        const content = JSON.stringify({ ...row, name: '' })
                        if (seen.has(content)) continue
                        seen.add(content)
                        rows.push(row)
                    }
        }
    }
    return rows
}

describe('the derived key rows, against the model of a key', () => {
    const rows = keyRows()

    it('reads each outcome of the builder as the model states it', () => {
        for (const row of rows) {
            const arm = selectArm(row.tree, row.item)
            const segments = modelSegments(row)
            const holds = segments?.some((one) => one.includes(row.separator))
            switch (row.outcome.kind) {
                case 'nothing':
                    expect(
                        arm.kind === 'null' ||
                            (arm.kind === 'attr' &&
                                modelKey(row) === undefined),
                        row.name,
                    ).toBe(true)
                    break
                case 'refused':
                    expect(
                        arm.kind === 'missing' ||
                            (arm.kind === 'leaf' && segments === undefined),
                        row.name,
                    ).toBe(true)
                    break
                case 'separator':
                    expect(holds, row.name).toBe(true)
                    break
                case 'key':
                    expect(holds ?? false, row.name).toBe(false)
                    expect(row.outcome.key, row.name).toBe(modelKey(row))
                    break
            }
        }
    })

    it('selects no arm for an absent discriminator and for a literal that names no arm, as the host throws', () => {
        const missing = rows.filter(
            (row) => selectArm(row.tree, row.item).kind === 'missing',
        )
        expect(missing.length).toBeGreaterThan(0)
        for (const row of missing)
            expect(row.outcome, row.name).toEqual({ kind: 'refused' })
    })

    it('gives the printed attribute as the key at an arm that names an attribute', () => {
        const attr = rows.filter(
            (row) => selectArm(row.tree, row.item).kind === 'attr',
        )
        expect(attr.some((row) => row.outcome.kind === 'key')).toBe(true)
        expect(attr.some((row) => row.outcome.kind === 'nothing')).toBe(true)
    })

    // The builder reads an arm as an own property, so a literal that names a property of the
    // prototype names no arm: the model selects `missing` and the builder throws, as for any other
    // unknown literal.
    it('refuses a literal that names a property of the prototype, at each level, as the model selects no arm', () => {
        for (const name of prototypeNames) {
            const drawn = rows.filter((row) =>
                row.item.some(([, value]) => value === name),
            )
            expect(drawn.length, name).toBeGreaterThan(0)
            for (const row of drawn)
                expect(row.outcome, `${name} in ${row.name}`).toEqual({
                    kind: 'refused',
                })
        }
    })

    it('draws a nested match, and an item that the inner match selects', () => {
        const nested = rows.filter(
            (row) =>
                row.tree.kind === 'match' &&
                row.tree.arms.some(([, arm]) => arm.kind === 'match'),
        )
        expect(nested.length).toBeGreaterThan(0)
        expect(nested.some((row) => row.outcome.kind === 'key')).toBe(true)
        expect(nested.some((row) => row.outcome.kind === 'nothing')).toBe(true)
        expect(nested.some((row) => row.outcome.kind === 'refused')).toBe(true)
    })

    it('emits a nested tree as a nested match', () => {
        const leaf: KeyTree = {
            kind: 'arm',
            arm: {
                kind: 'leaf',
                full: 1,
                parts: [{ kind: 'named', name: 'B', value: 'pug' }],
            },
        }
        const nested: KeyTree = {
            kind: 'match',
            discriminator: 'TAG',
            arms: [
                [
                    'ANIMAL',
                    {
                        kind: 'match',
                        discriminator: 'SPECIE',
                        arms: [['DOG', leaf]],
                    },
                ],
            ],
        }
        const text = leanKeyModule([
            {
                name: 'nested',
                tree: nested,
                item: [
                    ['TAG', 'ANIMAL'],
                    ['SPECIE', 'DOG'],
                ],
                allowPartial: false,
                enforce: false,
                separator: '#',
                outcome: { kind: 'key', key: 'B#pug' },
                lawful: true,
            },
        ])
        expect(text.match(/\.match_/g)?.length).toBe(2)
    })

    it('reads back each item that the entry wrote, for each spec of the pool', () => {
        let wrote = 0
        for (const one of cases) {
            const entry = entryOf(one.spec, one.separator ?? '#')
            for (const item of itemsOf(one)) {
                let written: Record<string, unknown>
                try {
                    written = entry.toEntry(item)
                } catch (thrown) {
                    if (thrown instanceof RotoriseError) continue
                    throw thrown
                }
                wrote++
                const { K: _key, ...rest } = written
                expect(entry.fromEntry(written), one.name).toEqual(rest)
            }
        }
        expect(wrote).toBeGreaterThan(0)
    })

    it('has a trailing separator where a depth stops before the last component', () => {
        const stop = rows.find(
            (row) =>
                row.name.startsWith('plain_') &&
                row.tree.kind === 'arm' &&
                leafOf(row)?.full === 2 &&
                row.enforce &&
                !row.allowPartial &&
                leafOf(row)?.parts.length === 1 &&
                leafOf(row)?.parts[0]?.kind === 'named' &&
                leafOf(row)?.parts.every(
                    (p) => p?.kind !== 'named' || p.value === '1',
                ),
        )
        expect(stop?.outcome).toEqual({ kind: 'key', key: 'A#1#' })
        expect(stop?.lawful).toBe(true)
    })

    it('has no trailing separator on a full key with the option on', () => {
        const full = rows.find(
            (row) =>
                row.name.startsWith('plain_') &&
                row.enforce &&
                row.tree.kind === 'arm' &&
                leafOf(row)?.parts.length === 2 &&
                leafOf(row)?.parts.every((p) => p !== undefined) &&
                leafOf(row)?.parts[0]?.kind === 'named' &&
                (leafOf(row)?.parts[0] as { value?: string }).value === '1' &&
                leafOf(row)?.parts[1]?.kind === 'named' &&
                (leafOf(row)?.parts[1] as { value?: string }).value === '2',
        )
        expect(full?.outcome).toEqual({ kind: 'key', key: 'A#1#B#2' })
    })

    it('draws a refusal, a refusal of the separator, a null arm and an empty key', () => {
        for (const kind of ['refused', 'separator', 'nothing'] as const)
            expect(rows.some((row) => row.outcome.kind === kind)).toBe(true)
        expect(
            rows.some((row) => row.outcome.kind === 'key' && !row.lawful),
        ).toBe(true)
    })

    it('draws each option and each shape of a part', () => {
        expect(new Set(rows.map((row) => row.allowPartial))).toEqual(
            new Set([true, false]),
        )
        expect(new Set(rows.map((row) => row.enforce))).toEqual(
            new Set([true, false]),
        )
        const shapes = new Set(
            rows.flatMap((row) =>
                (leafOf(row)?.parts ?? []).map((part) =>
                    part === undefined
                        ? 'absent'
                        : part.kind === 'named'
                          ? 'named'
                          : part.tag === undefined
                            ? 'tagless'
                            : 'tagged',
                ),
            ),
        )
        expect(shapes).toEqual(
            new Set(['absent', 'named', 'tagless', 'tagged']),
        )
    })

    it('emits the key rows for the gate', () => {
        const text = leanKeyModule(rows)
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(join(process.cwd(), 'formal', '.keys.lean'), text)
        }
        expect(text).toContain(
            'theorem keyRows_check : failingKeys keyRows = []',
        )
        expect(text.trimEnd().endsWith('#assert_axioms_module')).toBe(true)
    })
})
