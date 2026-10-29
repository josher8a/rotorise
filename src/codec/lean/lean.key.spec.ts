/**
 * **The key rows of the pool, against the model of a derived key.**
 *
 * The key builder of `src/Rotorise.ts` runs on each key spec of the pool, each item of the spec,
 * and each option. A row holds what the builder read and what the builder gave, and the gate checks
 * each row in the kernel against `DerivedKey.build` and `DerivedKey.join`. The pool holds the shapes
 * that the builder reads: a plain component, a transform that gives a tag and a value, a tagless
 * transform, a transform with a default, a discriminated spec, a `null` arm, and an arm that names
 * one attribute. An item can lack the discriminator or hold a literal that names no arm. A value
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
type Component = string | readonly [string, Transform, unknown?]
type Discriminated = {
    readonly discriminator: string
    readonly spec: Readonly<
        Record<string, readonly Component[] | string | null>
    >
}
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
        separator: string,
    ) => {
        readonly key: (name: string, item: object, config?: object) => unknown
        readonly toEntry: (item: object) => Record<string, unknown>
        readonly fromEntry: (entry: object) => unknown
    }
    return make({ K: spec }, separator)
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
        const [name, transform, fallback] =
            typeof component === 'string' ? [component] : component
        const value = item[name] ?? fallback
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
                    name: name.toUpperCase(),
                    value: segment(out),
                }
            }
        } else if (value !== undefined && value !== null && value !== '') {
            part = {
                kind: 'named',
                name: name.toUpperCase(),
                value: segment(value),
            }
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
    const arm = tree.arms.find(([literal]) => literal === value)?.[1]
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

const base: Item = { a: '1', b: '2', c: '3', n: 7, kind: 'x' }

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
    { name: 'dashPlain', spec: ['a', 'b'], separator: '-' },
    { name: 'dashTagless', spec: [['a', tagless], 'b'], separator: '-' },
]

const isDiscriminated = (spec: Spec): spec is Discriminated =>
    !Array.isArray(spec)

/** The arm of a spec as a tree, with the parts that the host evaluated for the item. */
const armTree = (
    arm: readonly Component[] | string | null,
    item: Item,
    depth: number | undefined,
    separator: string,
): KeyTree => ({
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
})

/** The tree of a spec for an item: each arm is evaluated, and the item selects one. */
const treeOf = (
    spec: Spec,
    item: Item,
    depth: number | undefined,
    separator: string,
): KeyTree =>
    isDiscriminated(spec)
        ? {
              kind: 'match',
              discriminator: spec.discriminator,
              arms: Object.entries(spec.spec).map(
                  ([literal, arm]) =>
                      [literal, armTree(arm, item, depth, separator)] as const,
              ),
          }
        : armTree(spec, item, depth, separator)

/** The printed attributes that the tree reads: each discriminator, and each attribute of an arm. */
const itemOf = (spec: Spec, item: Item): KeyRow['item'] => {
    const names = isDiscriminated(spec)
        ? [
              spec.discriminator,
              ...Object.values(spec.spec).filter(
                  (arm): arm is string => typeof arm === 'string',
              ),
          ]
        : []
    return [...new Set(names)].flatMap((name) => {
        const value = item[name]
        return value === undefined || value === null
            ? []
            : [[name, String(value)] as const]
    })
}

const componentsOf = (spec: Spec): readonly (readonly Component[])[] =>
    isDiscriminated(spec)
        ? Object.values(spec.spec).flatMap((arm) =>
              arm === null || typeof arm === 'string' ? [] : [arm],
          )
        : [spec]

const attributesOf = (spec: Spec): string[] =>
    isDiscriminated(spec)
        ? Object.values(spec.spec).filter(
              (arm): arm is string => typeof arm === 'string',
          )
        : []

const namesOf = (spec: Spec): string[] => [
    ...new Set([
        ...componentsOf(spec)
            .flat()
            .map((c) => (typeof c === 'string' ? c : c[0])),
        ...attributesOf(spec),
    ]),
]

/** The items of a case: the full item, and each used attribute absent, empty, null and with the separator. */
const itemsOf = (one: Case): Item[] => {
    const sep = one.separator ?? '#'
    const kinds = isDiscriminated(one.spec)
        ? Object.keys(one.spec.spec)
        : [base.kind]
    const withKinds = kinds.flatMap((kind) => {
        const start: Item = { ...base, kind }
        const items: Item[] = [start]
        for (const name of namesOf(one.spec)) {
            const { [name]: _dropped, ...without } = start
            items.push(
                without,
                { ...start, [name]: '' },
                { ...start, [name]: null },
            )
            items.push({ ...start, [name]: `x${sep}y` })
        }
        return items
    })
    return isDiscriminated(one.spec)
        ? [
              ...withKinds,
              { ...base, kind: 'w' },
              { ...base, kind: '' },
              { ...base, kind: null },
              (({ kind: _kind, ...rest }) => rest)(base),
          ]
        : withKinds
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

    // The builder reads `spec[literal]` through the prototype chain, so a literal that names a
    // property of `Object.prototype` gives no key, where the model selects no arm and the builder
    // throws for any other unknown literal. The row is not in the pool, because the kernel would
    // refuse it. The test passes while the builder is wrong and fails at the fix, which then moves
    // the row into the pool.
    it.fails(
        'refuses a literal that names a property of the prototype, as it refuses any literal that names no arm',
        () => {
            const run = builderOf(
                { discriminator: 'kind', spec: { x: ['a'], z: null } },
                '#',
            )
            for (const kind of [
                'constructor',
                'toString',
                '__proto__',
                'hasOwnProperty',
            ])
                expect(() => run('K', { kind, a: '1' }, {}), kind).toThrow(
                    RotoriseError,
                )
        },
    )

    it('emits a nested tree, which the host does not read yet', () => {
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
