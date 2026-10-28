/**
 * **The key rows of the pool, against the model of a derived key.**
 *
 * The key builder of `src/Rotorise.ts` runs on each key spec of the pool, each item of the spec,
 * and each option. A row holds what the builder read and what the builder gave, and the gate checks
 * each row in the kernel against `DerivedKey.build` and `DerivedKey.join`. The pool holds the shapes
 * that the builder reads: a plain component, a transform that gives a tag and a value, a tagless
 * transform, a transform with a default, a discriminated spec, and a `null` arm. A value that holds
 * the separator is a row where the segment list is not usable as a key.
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
    type KeyOutcome,
    type KeyPart,
    type KeyRow,
    leanKeyModule,
} from '../lean'

type Transform = (value: unknown) => unknown
type Component = string | readonly [string, Transform, unknown?]
type Discriminated = {
    readonly discriminator: string
    readonly spec: Readonly<Record<string, readonly Component[] | null>>
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
        if (key === undefined) return { kind: 'nothing' }
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

/** The segments that the model states for a row, as `DerivedKey.build` states them, or `undefined` where it refuses. */
const modelSegments = (row: KeyRow): string[] | undefined => {
    const printed: (KeyPart & object)[] = []
    for (const part of row.parts) {
        if (part === undefined) {
            if (row.allowPartial) break
            return undefined
        }
        printed.push(part)
    }
    const segments = printed.flatMap(segmentsOf)
    if (row.enforce && printed.length < row.full) segments.push('')
    return segments
}

const modelKey = (row: KeyRow): string | undefined =>
    modelSegments(row)?.join(row.separator)

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
    { name: 'dashPlain', spec: ['a', 'b'], separator: '-' },
    { name: 'dashTagless', spec: [['a', tagless], 'b'], separator: '-' },
]

const isDiscriminated = (spec: Spec): spec is Discriminated =>
    !Array.isArray(spec)

/** The components of the arm that an item reaches, or `null` where the arm is `null`. */
const armOf = (spec: Spec, item: Item): readonly Component[] | null =>
    isDiscriminated(spec) ? (spec.spec[String(item.kind)] ?? null) : spec

const componentsOf = (spec: Spec): readonly (readonly Component[])[] =>
    isDiscriminated(spec)
        ? Object.values(spec.spec).flatMap((arm) => (arm === null ? [] : [arm]))
        : [spec]

const namesOf = (spec: Spec): string[] => [
    ...new Set(
        componentsOf(spec)
            .flat()
            .map((c) => (typeof c === 'string' ? c : c[0])),
    ),
]

/** The items of a case: the full item, and each used attribute absent, empty, null and with the separator. */
const itemsOf = (one: Case): Item[] => {
    const sep = one.separator ?? '#'
    const kinds = isDiscriminated(one.spec)
        ? Object.keys(one.spec.spec)
        : [base.kind]
    return kinds.flatMap((kind) => {
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
                        const shape = armOf(one.spec, item) ?? []
                        const parts =
                            outcome.kind === 'nothing'
                                ? []
                                : partsOf(shape, item, depth, separator)
                        const draft = {
                            name: '',
                            full: outcome.kind === 'nothing' ? 0 : shape.length,
                            allowPartial: allowPartial === true,
                            enforce: enforceBoundary === true,
                            parts,
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
            if (row.outcome.kind === 'nothing') continue
            const segments = modelSegments(row)
            const holds = segments?.some((one) => one.includes(row.separator))
            switch (row.outcome.kind) {
                case 'refused':
                    expect(segments, row.name).toBeUndefined()
                    break
                case 'separator':
                    expect(holds, row.name).toBe(true)
                    break
                case 'key':
                    expect(holds, row.name).toBe(false)
                    expect(row.outcome.key, row.name).toBe(modelKey(row))
                    break
            }
        }
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
                row.full === 2 &&
                row.enforce &&
                !row.allowPartial &&
                row.parts.length === 1 &&
                row.parts[0]?.kind === 'named' &&
                row.parts[0].value === '1',
        )
        expect(stop?.outcome).toEqual({ kind: 'key', key: 'A#1#' })
        expect(stop?.lawful).toBe(true)
    })

    it('has no trailing separator on a full key with the option on', () => {
        const full = rows.find(
            (row) =>
                row.name.startsWith('plain_') &&
                row.enforce &&
                row.parts.length === 2 &&
                row.parts.every((p) => p !== undefined) &&
                row.parts[0]?.kind === 'named' &&
                row.parts[0].value === '1' &&
                row.parts[1]?.kind === 'named' &&
                row.parts[1].value === '2',
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
                row.parts.map((part) =>
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
