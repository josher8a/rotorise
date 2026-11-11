/**
 * **A change and the changed pet agree on the keys.** For each entry of a generated pool, each pet and
 * each part of the pet, the patch of `keyUpdates(part)` holds the key that `toEntry` or `toItem` gives
 * for the pet with each value of the part written at the path of its name, on each key that the patch
 * writes. A key that the patch omits is equal before and after. The pool declares names over `owner` (text, or an object with
 * `name` and `id`), `'owner.name'` and `'owner.id'`, reads `owner`, `'owner.name'` and `'owner.id'`
 * as a list and as a key of one attribute, and builds each entry with no codec, with a closed codec,
 * with an open codec that holds the name of a path in the rest, and with a tagged codec. The schema
 * and the pet of a generated entry are cast, because the pool holds entries that the type refuses.
 * An entry that the construction refuses is counted and is no comparison.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { discriminatedUnion, item, object, optional, string } from '../../codec'

type Owner = 'none' | 'text' | 'object'
const flats = [[], ['owner.name'], ['owner.id'], ['owner.name', 'owner.id']]
const keyNames = ['owner', 'owner.name', 'owner.id'] as const
const forms = ['list', 'one'] as const

const fieldOf = (name: string, owner: Owner) =>
    name === 'owner' && owner === 'object'
        ? object({ name: string, id: string })
        : string

const valueOf = (name: string, owner: Owner, version: 0 | 1) => {
    const tag = version === 0 ? 'a' : 'b'
    return name === 'owner' && owner === 'object'
        ? { name: `${tag}n`, id: `${tag}i` }
        : `${tag}-${name}`
}

const textOf = (key: unknown): string => {
    if (key === undefined) return 'ABSENT'
    if (typeof key === 'string') return key
    const stored = key as { S?: string }
    return stored.S ?? JSON.stringify(key)
}

type Entry = {
    readonly label: string
    readonly keyOf: (pet: Record<string, unknown>) => string
    readonly patch: (part: Record<string, unknown>) => {
        readonly set: Record<string, unknown>
        readonly remove: readonly string[]
    }
    readonly pets: readonly Record<string, unknown>[]
    readonly parts: readonly Record<string, unknown>[]
}

type Run = { entries: Entry[]; refused: number }

const build = (): Run => {
    const run: Run = { entries: [], refused: 0 }
    const names = (owner: Owner, flat: string[]) => [
        ...(owner === 'none' ? [] : ['owner']),
        ...flat,
    ]
    const petOf = (declared: string[], owner: Owner, version: 0 | 1) => ({
        petId: 'p1',
        ...Object.fromEntries(
            declared.map((name) => [name, valueOf(name, owner, version)]),
        ),
    })
    for (const owner of ['none', 'text', 'object'] as const)
        for (const flat of flats)
            for (const key of keyNames)
                for (const form of forms)
                    for (const mode of ['none', 'closed', 'open'] as const) {
                        const declared = names(owner, flat)
                        if (declared.length === 0) continue
                        const open = mode === 'open'
                        // an open codec declares `owner` and holds the flat names in the rest
                        const fields = open
                            ? declared.filter((name) => name === 'owner')
                            : declared
                        const restNames = open
                            ? declared.filter((name) => name !== 'owner')
                            : []
                        const schema = {
                            PK: ['petId'],
                            SK: form === 'list' ? [key] : key,
                        }
                        const codec =
                            mode === 'none'
                                ? undefined
                                : {
                                      petId: string,
                                      ...Object.fromEntries(
                                          fields.map((name) => [
                                              name,
                                              fieldOf(name, owner),
                                          ]),
                                      ),
                                  }
                        let table: {
                            toEntry: (
                                pet: Record<string, unknown>,
                            ) => Record<string, unknown>
                            unsafeToItem: (
                                pet: Record<string, unknown>,
                            ) => Record<string, unknown>
                            keyUpdates: (part: Record<string, unknown>) => {
                                set: Record<string, unknown>
                                remove: string[]
                            }
                        }
                        try {
                            const make = tableEntry<
                                Record<string, unknown>
                            >() as unknown as (
                                schema: unknown,
                                options?: unknown,
                            ) => typeof table
                            table = make(
                                schema,
                                codec === undefined
                                    ? undefined
                                    : {
                                          codec: open
                                              ? item(
                                                    object(codec, [
                                                        string,
                                                        optional(string),
                                                    ]),
                                                )
                                              : codec,
                                      },
                            )
                        } catch {
                            run.refused++
                            continue
                        }
                        const pets = [0, 1].map((v) =>
                            petOf(declared, owner, v as 0 | 1),
                        )
                        const parts = declared.map((name) => ({
                            [name]: valueOf(name, owner, 1),
                        }))
                        run.entries.push({
                            label: `${mode} owner=${owner} flat=[${flat}] ${form} ${key}${restNames.length > 0 ? ` rest=[${restNames}]` : ''}`,
                            keyOf: (pet) =>
                                textOf(
                                    mode === 'none'
                                        ? table.toEntry(pet).SK
                                        : table.unsafeToItem(pet).SK,
                                ),
                            patch: (part) => table.keyUpdates(part),
                            pets,
                            parts,
                        })
                    }
    // a tagged codec: the tag selects the variant, and each variant declares its own names
    for (const owner of ['text', 'object'] as const)
        for (const key of keyNames)
            for (const form of forms) {
                const variant = (kind: string, declared: string[]) =>
                    object({
                        kind: string(kind),
                        petId: string,
                        ...Object.fromEntries(
                            declared.map((name) => [
                                name,
                                fieldOf(name, owner),
                            ]),
                        ),
                    })
                const dog = ['owner.name']
                const cat = ['owner']
                try {
                    const make = tableEntry<
                        Record<string, unknown>
                    >() as unknown as (
                        schema: unknown,
                        options: unknown,
                    ) => {
                        unsafeToItem: (
                            pet: Record<string, unknown>,
                        ) => Record<string, unknown>
                        keyUpdates: (part: Record<string, unknown>) => {
                            set: Record<string, unknown>
                            remove: string[]
                        }
                    }
                    const table = make(
                        {
                            PK: ['petId'],
                            SK: form === 'list' ? [key] : key,
                        },
                        {
                            codec: item(
                                discriminatedUnion('kind', [
                                    variant('DOG', dog),
                                    variant('CAT', cat),
                                ] as never),
                            ),
                        },
                    )
                    for (const [kind, declared] of [
                        ['DOG', dog],
                        ['CAT', cat],
                    ] as const)
                        run.entries.push({
                            label: `tagged ${kind} owner=${owner} ${form} ${key}`,
                            keyOf: (pet) => textOf(table.unsafeToItem(pet).SK),
                            patch: (part) =>
                                table.keyUpdates({ kind, ...part }),
                            pets: [0, 1].map((v) => ({
                                kind,
                                ...petOf(declared, owner, v as 0 | 1),
                            })),
                            parts: declared.map((name) => ({
                                [name]: valueOf(name, owner, 1),
                            })),
                        })
                } catch {
                    run.refused++
                }
            }
    return run
}

/**
 * The pet with the value of each written name written at the path of the name. A name with no `.` is
 * a path of one name, so the write is the spread. A path below a value that is no object is no write.
 */
const written = (
    pet: Record<string, unknown>,
    part: Record<string, unknown>,
): Record<string, unknown> | undefined => {
    const out = structuredClone(pet)
    for (const [name, value] of Object.entries(part)) {
        const names = name.split('.')
        const last = names.pop() as string
        let at: Record<string, unknown> = out
        for (const one of names) {
            const below = at[one]
            if (below === undefined) at[one] = {}
            else if (typeof below !== 'object' || below === null)
                return undefined
            at = at[one] as Record<string, unknown>
        }
        at[last] = value
    }
    return out
}

describe('a change and the changed pet agree on each key of an entry', () => {
    const run = build()

    it('builds entries, and counts the entries that the construction refuses', () => {
        expect(run.entries.length).toBeGreaterThan(0)
        expect(run.refused).toBeGreaterThan(0)
    })

    it('gives the key of toEntry for the pet with each value written at its path, on each key that the patch writes, and the key of the pet on each key that it omits', () => {
        const mismatches: string[] = []
        let patches = 0
        const keyOrRefused = (
            entry: Entry,
            pet: Record<string, unknown>,
        ): string => {
            try {
                return entry.keyOf(pet)
            } catch {
                return 'REFUSED'
            }
        }
        for (const entry of run.entries)
            for (const pet of entry.pets)
                for (const part of entry.parts) {
                    const changed = written(pet, part)
                    if (changed === undefined) {
                        continue
                    }
                    const before = keyOrRefused(entry, pet)
                    const after = keyOrRefused(entry, changed)
                    if (before === 'REFUSED' || after === 'REFUSED') {
                        continue
                    }
                    let patch: ReturnType<Entry['patch']>
                    try {
                        patch = entry.patch(part)
                    } catch {
                        continue
                    }
                    patches++
                    const key = patch.set.SK
                    const got = key === undefined ? before : textOf(key)
                    if (got !== after)
                        mismatches.push(
                            `${entry.label} part=${JSON.stringify(part)}: patch ${got}, changed pet ${after}`,
                        )
                }
        expect(patches).toBeGreaterThan(0)
        expect(mismatches).toEqual([])
    })
})
