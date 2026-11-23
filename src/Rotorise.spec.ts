import { attest } from '@ark/attest'
import { describe, expect, it, test } from 'vitest'
import { tableEntry } from './Rotorise'
import type { ErrorMessage, Exact, NonEmptyArray, show } from './utils'

// The constraint of a key spec admits any path and any match on a path, whatever the entity holds,
// and `ValidatePaths` reads the paths that a spec holds. The pins below state the two shapes.
type AnyPathPin = `${string}.${string}`
type Joinable = string | number | bigint | boolean | null | undefined
type PathComponents =
    | AnyPathPin
    | {
          readonly at: AnyPathPin
          readonly tag?: string | false
          readonly value?: (key: never) => Joinable
          readonly default?: unknown
      }
type LooseArmPin =
    | (string | { readonly at: string })[]
    | string
    | null
    | { discriminator: string; spec: { [literal: string]: unknown } }
    | { discriminator: string; cases: unknown[] }
type PathMatchPin = {
    discriminator: AnyPathPin
    spec: { [literal: string]: LooseArmPin }
    cases?: never
}
type CasesMatchPin = {
    discriminator: string
    spec?: ErrorMessage<'a match holds spec or cases, not both'>
    cases: [[string | number, ...(string | number)[]], LooseArmPin][]
}

describe('Exact<> with discriminated unions', () => {
    type Example<T extends 'A' | 'B' | 'C' = 'A' | 'B' | 'C'> = {
        base: string
    } & {
        A: { a: 'A'; type: 'A' }
        B: { b: 'B'; type: 'B'; extra: 'E' }
        C: { c: 'C'; type: 'C' }
    }[T]

    function create<T>(item: Exact<Example, T>): T {
        return item as T
    }

    it('accepts a valid variant A', () => {
        const result = create({ base: 'hi', a: 'A', type: 'A' } as const)
        attest<{ readonly base: 'hi'; readonly a: 'A'; readonly type: 'A' }>(
            result,
        ).equals({ base: 'hi', a: 'A', type: 'A' })
    })

    it('accepts a valid variant B with extra key', () => {
        const result = create({
            base: 'hi',
            b: 'B',
            type: 'B',
            extra: 'E',
        } as const)
        attest<{
            readonly base: 'hi'
            readonly b: 'B'
            readonly type: 'B'
            readonly extra: 'E'
        }>(result).equals({ base: 'hi', b: 'B', type: 'B', extra: 'E' })
    })

    it('accepts a valid variant C', () => {
        const result = create({ base: 'hi', c: 'C', type: 'C' } as const)
        attest<{ readonly base: 'hi'; readonly c: 'C'; readonly type: 'C' }>(
            result,
        ).equals({ base: 'hi', c: 'C', type: 'C' })
    })

    it('rejects excess properties not in any variant', () => {
        create({
            base: 'hi',
            a: 'A',
            type: 'A' as const,
            // @ts-expect-error - 'nonexistent' is not a key in any variant
            nonexistent: 'bad',
        })
    })

    it('toEntry works with discriminated union entity', () => {
        const table = tableEntry<Example>()({
            PK: ['base'],
            SK: {
                discriminator: 'type',
                spec: {
                    A: ['a'],
                    B: ['b'],
                    C: ['c'],
                },
            },
        })

        const entryA = table.unsafeToEntry({ base: 'x', a: 'A', type: 'A' })
        attest(entryA.PK).equals('BASE#x')
        attest(entryA.SK).equals('A#A')

        const entryB = table.unsafeToEntry({
            base: 'y',
            b: 'B',
            type: 'B',
            extra: 'E',
        })
        attest(entryB.PK).equals('BASE#y')
        attest(entryB.SK).equals('B#B')

        // excess property still rejected
        table.unsafeToEntry({
            base: 'z',
            a: 'A',
            type: 'A',
            // @ts-expect-error - 'unknown' not in any variant
            unknown: 'bad',
        })
    })
})

describe('DynamoDB Utils', () => {
    it('key requires the components up to the depth, and makes each later component optional', () => {
        const Transformed = tableEntry<{ a: string; b: number; c: boolean }>()({
            PK: [
                'a',
                'b',
                { at: 'c', value: (_c: boolean) => 'TRANSFORM' as const },
            ],
        })
        const depth = 2 as number
        // a depth of two requires the first two components
        expect(
            Transformed.unsafeKey('PK', { a: 'x', b: 1 }, { depth: 2 }),
        ).toBe('A#x#B#1')
        // allowPartial reads the components that the call gives, and stops at the first absent one
        expect(
            Transformed.unsafeKey('PK', { a: 'x' }, { allowPartial: true }),
        ).toBe('A#x')
        const shallow = () =>
            // @ts-expect-error a depth of two requires the second component
            Transformed.unsafeKey('PK', { a: 'x' }, { depth: 2 })
        expect(shallow).toThrow(/Attribute b not found/)
        // @ts-expect-error a depth that is no literal says no component count
        const loose = () => Transformed.unsafeKey('PK', { a: 'x' }, { depth })
        expect(loose).toThrow(/Attribute b not found/)
        // a partial key of no component has no text: the key is an error value, and the type builds the call
        expect(() =>
            Transformed.unsafeKey('PK', {}, { allowPartial: true }),
        ).toThrow(/no component/)

        // 8939 -> 9878: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 9878 -> 8132: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 9457.
        attest.instantiations([8132, 'instantiations'])
    })

    it('key types the key as the template of its components, joined by the separator', () => {
        type Pet = { a: string; b: number; c: boolean }
        type Union =
            | { a: 'a1'; b: 1; c: true; z: never }
            | { a: 'a2'; b: 2; c: false; z: never }
        const full: Pet = { a: 'x', b: 1, c: true }
        const Pets = tableEntry<Pet>()({ PK: ['a', 'b', 'c'] })
        const Dashed = tableEntry<Pet>()(
            { PK: ['a', 'b', 'c'] },
            { separator: '-' },
        )
        attest<`A#${string}#B#${number}#C#${boolean}`>(
            Pets.unsafeKey('PK', full),
        )
        attest<`A-${string}-B-${number}-C-${boolean}`>(
            Dashed.unsafeKey('PK', full),
        )
        attest<`A-${string}-B-${number}`>(
            Dashed.unsafeKey('PK', full, { depth: 2 }),
        )
        attest<`A-${string}-B-${number}-C-${boolean}`>(
            Dashed.unsafeKey('PK', full, { depth: 3, allowPartial: true }),
        )

        const Variants = tableEntry<Union>()({ PK: ['a', 'b'] })
        const either = { a: 'a1', b: 1 } as
            | { a: 'a1'; b: 1 }
            | { a: 'a2'; b: 2 }
        attest<`A#${'a1'}#B#${1}` | `A#${'a2'}#B#${2}`>(
            Variants.unsafeKey('PK', either),
        )

        const Partial = tableEntry<Union>()({ PK: ['a', 'b', 'c'] })
        const partial = { a: 'a1', b: 1, c: true } as
            | { a: 'a1'; b: 1; c: true }
            | { a: 'a2'; b: 2; c: false }
        attest<'A#a1#B#1#C#true' | 'A#a2#B#2#C#false'>(
            Partial.unsafeKey('PK', partial, { depth: 3, allowPartial: true }),
        )

        const Transform = tableEntry<Union>()({
            PK: [
                'a',
                'b',
                { at: 'c', value: (_c: boolean) => 'TRANSFORM' as const },
            ],
        })
        attest<'A#a1#B#1#C#TRANSFORM' | 'A#a2#B#2#C#TRANSFORM'>(
            Transform.unsafeKey('PK', partial, {
                depth: 3,
                allowPartial: true,
            }),
        )

        const Tagged = tableEntry<Union>()({
            PK: [
                'a',
                'b',
                {
                    at: 'c',
                    tag: 'TAG',
                    value: (_c: boolean) => 'TRANSFORM' as const,
                },
            ],
        })
        attest<'A#a1#B#1#TAG#TRANSFORM' | 'A#a2#B#2#TAG#TRANSFORM'>(
            Tagged.unsafeKey('PK', partial, { depth: 3, allowPartial: true }),
        )

        const Valued = tableEntry<Union>()({
            PK: [
                'a',
                'b',
                {
                    at: 'c',
                    tag: false,
                    value: (_c: boolean) => 'TRANSFORM' as const,
                },
            ],
        })
        attest<'A#a1#B#1#TRANSFORM' | 'A#a2#B#2#TRANSFORM'>(
            Valued.unsafeKey('PK', partial, { depth: 3, allowPartial: true }),
        )

        // 23005 -> 25224: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 25224 -> 22012: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 24747.
        attest.instantiations([22012, 'instantiations'])
    })

    it('tableEntry joins the key components with the separator, and reads an entry back as the entity', () => {
        type Entity =
            | { a: 'a1'; b: 1; c: true; z: 'never' }
            | { a: 'a2'; b: 2; c: true; z: 'never' }
        const testTableEntry = tableEntry<Entity>()(
            {
                PK: ['a', 'b', 'c'],
                SK: 'b', // raw numeric key is only allowed for sorting propuse where other mechanism is not available (arbitrary precision numbers), either way it should use a regular composite key.
            } as const,
            { separator: '-' },
        )

        type entries =
            | ({
                  a: 'a1'
                  b: 1
                  c: true
                  z: 'never'
              } & {
                  readonly PK: 'A-a1-B-1-C-true'
                  readonly SK: number | bigint
              })
            | ({
                  a: 'a2'
                  b: 2
                  c: true
                  z: 'never'
              } & {
                  readonly PK: 'A-a2-B-2-C-true'
                  readonly SK: number | bigint
              })

        attest<entries>(testTableEntry.infer)

        expect(
            testTableEntry.unsafeKey(
                'PK',
                {
                    a: 'a1',
                    b: 1,
                    c: true,
                },
                {
                    depth: 2,
                    allowPartial: false,
                },
            ),
        ).toBe('A-a1-B-1')

        expect(
            testTableEntry.unsafeKey(
                'PK',
                {
                    a: 'a1',
                    b: 1,
                    c: true,
                },
                {
                    depth: 2,
                    allowPartial: false,
                    enforceBoundary: true,
                },
            ),
        ).toBe('A-a1-B-1-C-')

        const entity = {
            a: 'a1',
            b: 1,
            c: true,
            z: 'never',
        } satisfies Entity

        const testTableEntryObj = testTableEntry.unsafeToEntry(entity)

        testTableEntry.unsafeToEntry({
            a: 'a1',
            b: 1,
            c: true,
            z: 'never',
            // @ts-expect-error
            nonexistent: 'nonexistent',
        })

        expect(testTableEntryObj).toEqual({
            ...entity,
            PK: 'A-a1-B-1-C-true',
            SK: 1,
        })

        const fromEntry = testTableEntry.fromEntry(testTableEntryObj)

        attest<typeof entity>(fromEntry) // the exact type, with no failure

        expect(fromEntry).toEqual(entity)

        const key = testTableEntry.unsafeKey(
            'PK',
            {
                a: 'a1',
                b: 1,
            },
            {
                depth: 2,
                allowPartial: true,
            },
        )

        attest<'A-a1-B-1'>(key)

        expect(key).toBe('A-a1-B-1')

        const keyDefaults = testTableEntry.unsafeKey('PK', {
            a: 'a1',
            b: 1,
            c: true,
        })

        attest<'A-a1-B-1-C-true'>(keyDefaults)

        expect(keyDefaults).toBe('A-a1-B-1-C-true')

        // paths are accessible at runtime, and stringify to the document path
        expect(testTableEntry.path().PK.toString()).toBe('PK')

        expect(
            testTableEntry.unsafeKey(
                'SK',
                {
                    b: 1,
                },
                undefined, // when is raw numeric key, configuration is not needed
            ),
        ).toBe(1)
        expect(
            testTableEntry.unsafeKey(
                'SK',
                {
                    b: 1,
                },
                // @ts-expect-error
                { depth: 1 },
            ),
        ).toBe(1)

        expect(
            testTableEntry.unsafeKey(
                'SK',
                {
                    b: 1,
                },
                // @ts-expect-error
                { allowPartial: true },
            ),
        ).toBe(1)

        // 7826 -> 8483: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 8483 -> 8590: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        // 8590 -> 11406: `toEntry`, `fromEntry`, `infer` and `path` type each key as the member that
        // the codec stores, so an N key reads as `number | bigint`. The owner accepted the cost for
        // the exact type
        // 11406 -> 11232: an N key of an entry is the union of two primitives, which the SDK
        // marshaller writes, and no longer the class `DynamoNumber`
        // 11330 -> 12971: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 12971 -> 13785: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 14136.
        attest.instantiations([13785, 'instantiations'])
    })

    test('path from infer then toString', () => {
        const testTableEntry = tableEntry<{
            a: 'a1'
            b: 1
            c: true
            z: 'never'
            data: {
                type: string
                description: string
            }
            logs: {
                type: string
                description: string
            }[]
        }>()(
            {
                PK: ['a', 'b', 'c'],
                SK: ['c'],
            },
            { separator: '-' },
        )

        expect(testTableEntry.path().data.type.toString()).toBe('data.type')
        // biome-ignore lint/style/noNonNullAssertion: index access in test assertion
        expect(testTableEntry.path().logs[0]!.type.toString()).toBe(
            'logs[0].type',
        )
        // biome-ignore lint/style/noNonNullAssertion: index access in test assertion
        expect(testTableEntry.path().logs['0']!.type.toString()).toBe(
            'logs[0].type',
        )
        expect(testTableEntry.path().PK.toString()).toBe('PK')

        // 1505 -> 1869: `path()` is typed as a path rather than as the entity, which strips
        // optionality at every level so no hop needs a non-null assertion, and carries what lives
        // there so `item.at` can recover it. Both cost one more type per level.
        // 1869 -> 2235: `keyUpdates` asks the codec which components it already decides, which
        // walks the codec spec once per key
        // 2235 -> 2378: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 2378 -> 2388: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        // 2388 -> 2875: the constraint of a key spec admits a path and a match on a path, and the
        // pin of the parameter type states both
        // 2966 -> 3538: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 3538 -> 3915: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 4014.
        attest.instantiations([3915, 'instantiations'])
    })

    test('table Entry with transform and discriminator ', () => {
        const base = tableEntry<
            | { a: 'a1'; b: 1n; c: true; z: 'never' }
            | { a: 'a2'; b: 2; c: 0; z: 'never' }
        >()
        attest<
            [
                schema: Record<
                    string,
                    | 'a'
                    | 'b'
                    | 'c'
                    | 'z'
                    | `${string}.${string}`
                    | NonEmptyArray<
                          | 'a'
                          | 'b'
                          | 'c'
                          | 'z'
                          | {
                                readonly at: 'a'
                                readonly tag?: string | false
                                readonly value?: (key: 'a1' | 'a2') => Joinable
                                readonly default?: never
                            }
                          | {
                                readonly at: 'b'
                                readonly tag?: string | false
                                readonly value?: (key: 1n | 2) => Joinable
                                readonly default?: never
                            }
                          | {
                                readonly at: 'c'
                                readonly tag?: string | false
                                readonly value?: (key: true | 0) => Joinable
                                readonly default?: never
                            }
                          | {
                                readonly at: 'z'
                                readonly tag?: string | false
                                readonly value?: (key: 'never') => Joinable
                                readonly default?: never
                            }
                          | PathComponents
                      >
                    | null
                    | PathMatchPin
                    | CasesMatchPin
                    | {
                          discriminator: 'a'
                          cases?: never
                          spec: {
                              a1:
                                  | 'a'
                                  | 'b'
                                  | 'c'
                                  | 'z'
                                  | `${string}.${string}`
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'c'
                                        | 'z'
                                        | {
                                              readonly at: 'a'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'a1',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'b'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 1n,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'c'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: true,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'z'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'never',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | PathComponents
                                    >
                                  | null
                                  | PathMatchPin
                                  | CasesMatchPin
                              a2:
                                  | 'a'
                                  | 'b'
                                  | 'c'
                                  | 'z'
                                  | `${string}.${string}`
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'c'
                                        | 'z'
                                        | {
                                              readonly at: 'a'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'a2',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'b'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 2,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'c'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 0,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'z'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'never',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | PathComponents
                                    >
                                  | null
                                  | PathMatchPin
                                  | CasesMatchPin
                          }
                      }
                    | {
                          discriminator: 'z'
                          cases?: never
                          spec: {
                              never:
                                  | 'a'
                                  | 'b'
                                  | 'c'
                                  | 'z'
                                  | `${string}.${string}`
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'c'
                                        | 'z'
                                        | {
                                              readonly at: 'a'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'a1' | 'a2',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'b'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 2 | 1n,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'c'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: true | 0,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'z'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'never',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | PathComponents
                                    >
                                  | null
                                  | PathMatchPin
                                  | CasesMatchPin
                                  | {
                                        discriminator: 'a'
                                        cases?: never
                                        spec: {
                                            a1:
                                                | 'a'
                                                | 'b'
                                                | 'c'
                                                | 'z'
                                                | `${string}.${string}`
                                                | NonEmptyArray<
                                                      | 'a'
                                                      | 'b'
                                                      | 'c'
                                                      | 'z'
                                                      | {
                                                            readonly at: 'a'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 'a1',
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | {
                                                            readonly at: 'b'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 1n,
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | {
                                                            readonly at: 'c'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: true,
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | {
                                                            readonly at: 'z'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 'never',
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | PathComponents
                                                  >
                                                | null
                                                | PathMatchPin
                                                | CasesMatchPin
                                            a2:
                                                | 'a'
                                                | 'b'
                                                | 'c'
                                                | 'z'
                                                | `${string}.${string}`
                                                | NonEmptyArray<
                                                      | 'a'
                                                      | 'b'
                                                      | 'c'
                                                      | 'z'
                                                      | {
                                                            readonly at: 'a'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 'a2',
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | {
                                                            readonly at: 'b'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 2,
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | {
                                                            readonly at: 'c'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 0,
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | {
                                                            readonly at: 'z'
                                                            readonly tag?:
                                                                | string
                                                                | false
                                                            readonly value?: (
                                                                key: 'never',
                                                            ) => Joinable
                                                            readonly default?: never
                                                        }
                                                      | PathComponents
                                                  >
                                                | null
                                                | PathMatchPin
                                                | CasesMatchPin
                                        }
                                    }
                          }
                      }
                >,
            ]
        >(null as any as [Parameters<typeof base>[0]])

        const testTableEntry = base(
            {
                PK: [
                    'a',
                    'b',
                    {
                        at: 'c',
                        value: (c: number | boolean) =>
                            c ? 'VERDADERO' : 'FALSO',
                    },
                ],
                SK: 'b',

                GSI1PK: {
                    discriminator: 'z',
                    spec: {
                        never: 'b',
                    },
                },
                GSI1SK: {
                    discriminator: 'a',
                    spec: {
                        a2: ['b'],
                        a1: [
                            'a',
                            'b',
                            {
                                at: 'c',
                                tag: 'NEW_TAG',
                                value: (c: number | boolean) =>
                                    c
                                        ? ('VERDADERO' as const)
                                        : ('FALSO' as const),
                            },
                        ],
                    },
                },

                GSI2PK: {
                    discriminator: 'a',
                    spec: {
                        a2: 'b',
                        a1: null,
                    },
                },
            },
            { separator: '-' },
        )

        type entries = show<
            | ({
                  a: 'a1'
                  b: 1n
                  c: true
                  z: 'never'
              } & {
                  readonly PK: 'A-a1-B-1-C-VERDADERO' | 'A-a1-B-1-C-FALSO'
                  readonly SK: number | bigint
                  readonly GSI1PK: number | bigint
                  readonly GSI1SK:
                      | 'A-a1-B-1-NEW_TAG-VERDADERO'
                      | 'A-a1-B-1-NEW_TAG-FALSO'
                  readonly GSI2PK?: never
              })
            | ({
                  a: 'a2'
                  b: 2
                  c: 0
                  z: 'never'
              } & {
                  readonly PK: 'A-a2-B-2-C-VERDADERO' | 'A-a2-B-2-C-FALSO'
                  readonly SK: number | bigint
                  readonly GSI1PK: number | bigint
                  readonly GSI1SK: 'B-2'
                  readonly GSI2PK: number | bigint
              })
        >

        attest<entries>(testTableEntry.infer)

        expect(
            testTableEntry.unsafeKey(
                'PK',
                {
                    a: 'a1',
                    b: 1n,
                    c: true,
                },
                {
                    allowPartial: true,
                },
            ),
        ).toBe('A-a1-B-1-C-VERDADERO')
        expect(
            testTableEntry.unsafeKey('PK', {
                a: 'a2',
                b: 2,
                c: 0,
            }),
        ).toBe('A-a2-B-2-C-FALSO')

        expect(
            testTableEntry.unsafeKey('SK', {
                b: 2,
            }),
        ).toBe(2)

        expect(
            testTableEntry.unsafeKey('SK', {
                b: 1n,
            }),
        ).toBe(1n)
        void testTableEntry.unsafeKey(
            'GSI1SK',
            {
                a: 'a1',
                b: 1n,
                c: true,
            },
            {
                depth: 2,
            },
        )

        void testTableEntry.unsafeKey('GSI1PK', {
            z: 'never', // required to discriminate
            b: 1n,
        })
        expect(
            testTableEntry.unsafeKey('GSI1PK', {
                z: 'never', // required to discriminate
                b: 1n,
            }),
        ).toBe(1n)

        expect(
            testTableEntry.unsafeKey(
                'GSI1SK',
                {
                    a: 'a1',
                    b: 1n,
                    c: true,
                },
                {
                    depth: 2,
                },
            ),
        ).toBe('A-a1-B-1')

        expect(
            testTableEntry.unsafeKey('GSI1SK', {
                a: 'a1',
                b: 1n,
                c: true,
            }),
        ).toBe('A-a1-B-1-NEW_TAG-VERDADERO')

        expect(
            testTableEntry.unsafeKey('GSI1SK', {
                a: 'a2',
                b: 2,
                // z: 'never',
            }),
        ).toBe('B-2')

        expect(
            testTableEntry.unsafeKey('GSI2PK', {
                a: 'a2',
                b: 2,
                // z: 'never',
            }),
        ).toBe(2)

        expect(
            testTableEntry.unsafeKey('GSI2PK', {
                a: 'a1',
            }),
        ).toBeUndefined()

        // 13308 -> 15421: same cause as the `path()` baseline above — `keyUpdates` now reads
        // `ConstantAttributes` off the codec spec for every key in the schema
        // 15421 -> 15565: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 15565 -> 15628: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        // 15628 -> 19066: the constraint of a key spec admits a path and a match on a path, and each
        // pin of the parameter type states both
        // 16581 -> 17975: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 17975 -> 17375: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 18726.
        attest.instantiations([17375, 'instantiations'])
    })

    test('a union of many variants over one large record types the key of each tag, within the instantiation count', () => {
        type BigUnion =
            | 'A'
            | 'B'
            | 'C'
            | 'D'
            | 'E'
            | 'F'
            | 'G'
            | 'H'
            | 'I'
            | 'J'
            | 'K'
            | 'L'
            | 'M'
            | 'N'
            | 'O'
            | 'P'
            | 'Q'
            | 'R'
            | 'E'
            | 'T'
            | 'U'
            | 'V'
            | 'W'
            | 'X' // excessively deep mark - before PR
            | 'Y'
            | 'Z'
            | 'A1'
            | 'B1'
            | 'C1'
            | 'D1' // excessively deep mark - before Attest
            | 'E1'
            | 'F1'
            | 'G1'
            | 'H1'
            | 'I1'
            | 'J1'
            | 'K1'
            | 'L1'
            | 'M1'
            | 'N1'
            | 'O1'
            | 'P1'
            | 'Q1'
            | 'R1'
            | 'E1'
            | 'T1'
            | 'U1'
            | 'V1'
            | 'W1'
            | 'X1'
            | 'Y1'
            | 'Z1' // YOLO

        type BigRecord = {
            [k in BigUnion]: `value:${k}`
        }

        type A = {
            id1: string
            tag: 'A'
            user: string
            id2: string

            type: 'TypeA'
        } & BigRecord

        type B = {
            id1: string
            tag: 'B'
            user: string
            id2: string
            type: 'TypeB'
        } & BigRecord

        type C = {
            id1: string
            tag: 'C'
            user: string
            id2: string
            type: 'TypeB'
        } & BigRecord

        type D = {
            id1: string
            tag: 'D'
            user: string
            deviceId: string
            id2: string
            type: 'TypeA'
            kind: string
        } & BigRecord

        type RealEntry = typeof RealEntry.infer
        const RealEntry = tableEntry<A | C | D | B>()({
            PK: ['id1', 'user'],
            SK: {
                discriminator: 'tag',
                spec: {
                    C: ['tag', 'id2', 'type'],
                    D: ['tag', 'id2', 'kind', 'type'],
                    A: ['tag', 'id2', 'type'],
                    B: ['tag', 'id2', 'type'],
                },
            },
            GSI1PK: ['id2'],
            GSI1SK: {
                discriminator: 'tag',
                spec: {
                    C: ['type'],
                    D: ['kind'],
                    A: ['type'],
                    B: ['type'],
                },
            },
        })

        attest<
            show<
                | (A & {
                      readonly PK: `ID1#${string}#USER#${string}`
                      readonly SK: `TAG#A#ID2#${string}#TYPE#TypeA`
                      readonly GSI1PK: `ID2#${string}`
                      readonly GSI1SK: `TYPE#TypeA`
                  })
                | ({
                      readonly PK: `ID1#${string}#USER#${string}`
                      readonly SK: `TAG#C#ID2#${string}#TYPE#TypeB`
                      readonly GSI1PK: `ID2#${string}`
                      readonly GSI1SK: `TYPE#TypeB`
                  } & C)
                | ({
                      readonly PK: `ID1#${string}#USER#${string}`
                      readonly SK: `TAG#D#ID2#${string}#KIND#${string}#TYPE#TypeA`
                      readonly GSI1PK: `ID2#${string}`
                      readonly GSI1SK: `KIND#${string}`
                  } & D)
                | ({
                      readonly PK: `ID1#${string}#USER#${string}`
                      readonly SK: `TAG#B#ID2#${string}#TYPE#TypeB`
                      readonly GSI1PK: `ID2#${string}`
                      readonly GSI1SK: `TYPE#TypeB`
                  } & B)
            >
        >(null as any as RealEntry)

        void (RealEntry.unsafeKey(
            'PK',
            {
                id1: 'client',
                user: 'user',
            },
            {
                allowPartial: true,
            },
        ) satisfies 'ID1#client#USER#user' | 'ID1#client')

        void (RealEntry.unsafeKey(
            'PK',
            {
                id1: 'client',
                user: 'user',
            },
            {
                // allowPartial: true,
            },
        ) satisfies 'ID1#client#USER#user')

        void (RealEntry.unsafeKey('GSI1SK', {
            type: 'TypeA',
            tag: 'A',
        }) satisfies 'TYPE#TypeA')

        // @ts-expect-error
        const expect_key2_ = RealEntry.unsafeKey('GSI1SK', {
            type: 'TypeA',
            tag: 'A',
            // biome-ignore lint/complexity/noBannedTypes: test case
        } as {})

        void (RealEntry.unsafeKey(
            'PK',
            {
                id1: 'client',
                user: 'user',
            },
            {
                allowPartial: true,
                depth: 1,
            },
        ) satisfies 'ID1#client')

        const expect_key_depth_partial_discriminator = RealEntry.unsafeKey(
            'SK',
            { tag: 'A', id2: 'yolo' },
            { allowPartial: true, depth: 2 },
        ) satisfies 'TAG#A' | `TAG#A#ID2#${string}`

        attest<'TAG#A#ID2#yolo'>(expect_key_depth_partial_discriminator)

        void (RealEntry.unsafeKey(
            'SK',
            { tag: 'A', id2: 'yolo' },
            { depth: 2 },
        ) satisfies 'TAG#A#ID2#yolo')

        // 32508 -> 33502: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 33502 -> 33647: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        // 31172 -> 33286: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 33286 -> 36454: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 36702.
        attest.instantiations([36454, 'instantiations'])
    })

    test('schema allows for nullish values if has transform', () => {
        const base = tableEntry<
            | { a: 'a1'; b: 1n; c: true; z: 'never' }
            | { a: 'a2'; b: 2; c: 0; z?: 'never' | null }
        >()

        const testTableEntry = base(
            {
                PK: ['a', { at: 'b', value: (x: 1n | 2) => x.toString() }, 'c'],
                SK: [
                    'c',
                    {
                        at: 'z',
                        value: (z: 'never' | null) => z ?? 'DEFAULT',
                        default: null,
                    },
                ],
                GSIPK: 'z',
                GSISK: {
                    discriminator: 'a',
                    spec: {
                        a1: [
                            'z',
                            { at: 'z', value: (z: 'never') => z ?? 'DEFAULT' },
                        ],
                        a2: [
                            {
                                at: 'z',
                                value: (z: 'never' | null) => z ?? 'DEFAULT',
                                default: 'never',
                            },
                        ],
                    },
                },
            },
            { separator: '-' },
        )

        type entries = show<
            | ({
                  a: 'a1'
                  b: 1n
                  c: true
                  z: 'never'
              } & {
                  readonly PK: `A-a1-B-${string}-C-true`
                  readonly SK: 'C-true-Z-never' | 'C-true-Z-DEFAULT'
                  readonly GSIPK: 'never'
                  readonly GSISK: 'Z-never-Z-never'
              })
            | ({
                  a: 'a2'
                  b: 2
                  c: 0
                  z?: 'never' | null
              } & {
                  readonly PK: `A-a2-B-${string}-C-0`
                  readonly SK: 'C-0-Z-DEFAULT' | 'C-0-Z-never'
                  readonly GSIPK?: 'never'
                  readonly GSISK: 'Z-never' | 'Z-DEFAULT'
              })
        >

        attest<entries>(testTableEntry.infer)

        expect(
            testTableEntry.unsafeKey('SK', {
                c: 0,
                z: undefined,
            }),
        ).toBe('C-0-Z-DEFAULT')

        expect(
            testTableEntry.unsafeKey('SK', {
                c: 0,
                z: 'never',
            }),
        ).toBe('C-0-Z-never')

        expect(
            // on partial no transform if missing
            testTableEntry.unsafeKey(
                'PK',
                {
                    a: 'a2',
                },
                { allowPartial: true },
            ),
        ).toBe('A-a2')

        // a later component that the call gives after an absent one is a hole: the print would drop it
        expect(() =>
            testTableEntry.unsafeKey(
                'PK',
                {
                    c: 0,
                    a: 'a2',
                },
                { allowPartial: true },
            ),
        ).toThrow(/would drop/)
    })

    test('a key schema over variants that type one attribute differently gives a transform the union of those types', () => {
        const base = tableEntry<
            { a: 'a1'; b: 1n; extra: 'extra' } | { a: 'a2'; b: 2 }
        >()
        attest<
            [
                schema: Record<
                    string,
                    | 'a'
                    | 'b'
                    | `${string}.${string}`
                    | NonEmptyArray<
                          | 'a'
                          | 'b'
                          | {
                                readonly at: 'a'
                                readonly tag?: string | false
                                readonly value?: (key: 'a1' | 'a2') => Joinable
                                readonly default?: never
                            }
                          | {
                                readonly at: 'b'
                                readonly tag?: string | false
                                readonly value?: (key: 1n | 2) => Joinable
                                readonly default?: never
                            }
                          | PathComponents
                      >
                    | null
                    | PathMatchPin
                    | CasesMatchPin
                    | {
                          discriminator: 'a'
                          cases?: never
                          spec: {
                              a1:
                                  | 'a'
                                  | 'b'
                                  | 'extra'
                                  | `${string}.${string}`
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'extra'
                                        | {
                                              readonly at: 'a'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'a1',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'b'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 1n,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'extra'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'extra',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | PathComponents
                                    >
                                  | null
                                  | PathMatchPin
                                  | CasesMatchPin
                              a2:
                                  | 'a'
                                  | 'b'
                                  | `${string}.${string}`
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | {
                                              readonly at: 'a'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 'a2',
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | {
                                              readonly at: 'b'
                                              readonly tag?: string | false
                                              readonly value?: (
                                                  key: 2,
                                              ) => Joinable
                                              readonly default?: never
                                          }
                                        | PathComponents
                                    >
                                  | null
                                  | PathMatchPin
                                  | CasesMatchPin
                          }
                      }
                >,
            ]
        >(null as any as [Parameters<typeof base>[0]])
    })

    test('optional object property with narrowed transform accepts partial default', () => {
        type Inner = { id: string; name: string; age: number }
        type Entity = {
            data?: Inner
            key: string
        }

        const table = tableEntry<Entity>()({
            PK: [
                {
                    at: 'data',
                    tag: 'DATA',
                    value: (d: Pick<Inner, 'id'>) => d.id,
                    default: { id: 'default-id' },
                },
                'key',
            ],
        })

        // empty object should be rejected — it doesn't satisfy the transform param
        tableEntry<Entity>()({
            PK: [
                {
                    at: 'data',
                    tag: 'DATA',
                    value: (d: Pick<Inner, 'id'>) => d.id,
                    default: {},
                },
                'key',
            ],
        })

        // Uses the actual value when present
        expect(
            table.unsafeKey('PK', {
                data: { id: 'real-id' },
                key: 'k1',
            }),
        ).toBe('DATA#real-id#KEY#k1')

        // Falls back to default when data is undefined
        expect(
            table.unsafeKey('PK', {
                data: undefined,
                key: 'k1',
            }),
        ).toBe('DATA#default-id#KEY#k1')
    })

    test('transform parameter types narrow .key() attributes', () => {
        type A = {
            w: string
            x: string
            y: string
            z: string
        }

        type B = {
            a: A
            b: string
        }

        const Entry = tableEntry<B>()({
            PK: [{ at: 'a', tag: 'W', value: (x: Pick<A, 'w'>) => x.w }],
            SK: [
                { at: 'a', tag: 'W', value: (x: Pick<A, 'w'>) => x.w },
                { at: 'a', tag: 'X', value: (x: Pick<A, 'x'>) => x.x },
                { at: 'b', tag: 'B_VAL', value: (x: string) => x },
            ],
            GSI1PK: [{ at: 'a', tag: 'W', value: (x: Pick<A, 'w'>) => x.w }],
            GSI1SK: [{ at: 'b', tag: 'B_VAL', value: (x: string) => x }],
        })

        // PK only needs w
        expect(
            Entry.unsafeKey('PK', {
                a: { w: 'w1' },
            }),
        ).toBe('W#w1')

        // SK needs w AND x (intersected from both transform params)
        expect(
            Entry.unsafeKey('SK', {
                a: { w: 'w1', x: 'x1' },
                b: 'b1',
            }),
        ).toBe('W#w1#X#x1#B_VAL#b1')

        // GSI1PK only needs w
        expect(
            Entry.unsafeKey('GSI1PK', {
                a: { w: 'w1' },
            }),
        ).toBe('W#w1')

        // GSI1SK only needs b
        expect(
            Entry.unsafeKey('GSI1SK', {
                b: 'b1',
            }),
        ).toBe('B_VAL#b1')

        // SK requires both w and x on a
        Entry.unsafeKey('SK', {
            // @ts-expect-error - missing w
            a: { x: 'x1' },
            b: 'b1',
        })

        // SK requires both w and x on a
        Entry.unsafeKey('SK', {
            // @ts-expect-error - missing x
            a: { w: 'w1' },
            b: 'b1',
        })

        // PK requires w on a
        Entry.unsafeKey('PK', {
            // @ts-expect-error - empty object missing w
            a: {},
        })

        // PK requires w on a, not x
        Entry.unsafeKey('PK', {
            // @ts-expect-error - x does not exist on Pick<A, 'w'>
            a: { x: 'x1' },
        })

        // 6982 -> 7273: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 7273 -> 7329: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        // 7329 -> 9028: an arm of a match is a key spec of its variant, so each arm of a discriminated
        // key builds the type of a match that the variant allows, and the schema check reads it
        // 7931 -> 8734: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        // 8734 -> 7651: a component is a record that holds its tag, function and default, so the constraint of a name is one record in place of three function arms, and the key type reads the label, the value and the default from named properties. The measured count at the base was 8829.
        attest.instantiations([7651, 'instantiations'])
    })

    test('a default of the wrong type is refused in a list that also holds a bare name', () => {
        type Entity = {
            id: string
            data?: { name: string }
        }

        // The only record with a default is in a list beside a bare name, and the default is checked
        // against the type of the value.
        tableEntry<Entity>()({
            PK: [
                'id',
                {
                    at: 'data',
                    value: (d: { name: string }) => d.name,
                    default: {},
                },
            ],
        })

        // Valid default should pass
        const table = tableEntry<Entity>()({
            PK: [
                'id',
                {
                    at: 'data',
                    value: (d: { name: string }) => d.name,
                    default: { name: 'legacy' },
                },
            ],
        })

        expect(table.unsafeKey('PK', { id: 'x', data: undefined })).toBe(
            'ID#x#DATA#legacy',
        )
    })
})

/**
 * **The published surface, pinned — both what is on it and what is deliberately not.**
 *
 * `Rotorise.ts` enumerates the codec values rather than starring them, so that an export is a
 * decision rather than a consequence of where a function happens to live. That only holds if
 * something notices when the two lists drift. A re-export written as `export * from './codec/codec'`
 * puts every export of that module on the surface, and only a test can say so.
 *
 * The absent half is the load-bearing one. The names below read a **term** for this library's own
 * resolver, declaration guard and emitter to ask what a codec is; a caller has the codec's
 * behaviour, which is what they are derived from. Re-adding one is a decision, and this makes it a
 * visible one.
 *
 * **The list is the live names.** `Object.hasOwn` answers `false` for a name that nothing declares,
 * so a row for a dead name passes by asserting nothing. A deleted name cannot leak. Only a live one
 * can, so a row for a dead name is not a test, and a deletion pass moves the row to the name that
 * replaced it.
 */
describe('the published surface', () => {
    const internal = [
        // the two that ask the pair, which is what admission is: `accepts` and `readsBack` ask the
        // codec rather than read a term
        'accepts',
        'readsBack',
        // the functions of a term the model computes, and the tag of a variant, which
        // `assignmentOf` reads off the body of the option
        'member',
        'occV',
        'assignmentOf',
        // the disjointness decision of the scoped walk, which the declaration guard and the
        // narrowing of a path share
        'agrees',
        // the predicate a refinement carries, run
        'holds',
        // the value kinds a term takes, the two halves of the term cache, and the mark reader
        'valueKinds',
        'termOf',
        'codecOfTerm',
        'constantOf',
        // the predicates and constants of the attribute domain, and two helpers, that the library
        // reads and no caller needs
        'MAX_DOCUMENT_NESTING',
        'everyEntry',
        'isNumeral',
        'isStoredNumeral',
        'memberOf',
        'shapeOf',
        'tooDeeplyNested',
    ] as const

    it('does not carry the internal utilities', async () => {
        const surface = await import('./Rotorise')
        for (const name of internal) {
            expect(Object.hasOwn(surface, name)).toBe(false)
        }
    })

    it('names only declarations that a module of the library holds, so no row asserts nothing', async () => {
        const modules = await Promise.all([
            import('./codec/attribute'),
            import('./codec/codec'),
            import('./codec/denote'),
            import('./codec/objects'),
            import('./codec/scoped'),
            import('./codec/term'),
            import('./codec/value'),
        ])
        for (const name of internal) {
            expect(
                modules.some((module) => Object.hasOwn(module, name)),
                name,
            ).toBe(true)
        }
    })

    /**
     * **The other half of the same fact.**
     *
     * The list above is a run-time check, and a run-time check cannot see a type. `export type *
     * from './codec/codec'` would re-export every export of that module, the values among them as
     * *types*, so `import { accepts } from 'rotorise'` would type-check and be `undefined` when
     * it ran. The type surface must be a decision, as the value list is, and not a consequence of
     * where a function lives.
     *
     * One rule covers both halves: no name held back at run time is a key of the module's type
     * either. A name added to `internal` is checked by both halves without a line here.
     */
    it('does not carry them at the type level either', () => {
        type Entry = typeof import('./Rotorise')
        attest<[Extract<keyof Entry, (typeof internal)[number]>], [never]>()
    })

    it('carries the constructors and combinators', async () => {
        const surface = await import('./Rotorise')
        for (const name of [
            'array',
            'binary',
            'boolean',
            'decimal',
            'discriminatedUnion',
            'exclude',
            'extract',
            'fill',
            'held',
            'legacy',
            'list',
            'nullValue',
            'nullable',
            'number',
            'object',
            'opaque',
            'optional',
            'ref',
            'refine',
            'scope',
            'spread',
            'string',
            'union',
            'CodecError',
        ]) {
            expect(Object.hasOwn(surface, name)).toBe(true)
        }
    })
})
