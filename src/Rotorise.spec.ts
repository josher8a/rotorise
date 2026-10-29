import { attest } from '@ark/attest'
import { describe, expect, it, test } from 'vitest'
import {
    type CodecError,
    type CompositeKeyBuilder,
    type CompositeKeyParams,
    failed,
    type TransformShape,
    tableEntry,
} from './Rotorise'
import type { ErrorMessage, Exact, NonEmptyArray, show } from './utils'

// The constraint of a key spec admits any path and any match on a path, whatever the entity holds,
// and `ValidatePaths` reads the paths that a spec holds. The pins below state the two shapes.
type AnyPathPin = `${string}.${string}`
type PathComponents =
    | AnyPathPin
    | [AnyPathPin, { readonly tag: string }]
    // biome-ignore lint/suspicious/noExplicitAny: the constraint types the parameter of a path transform as any
    | [AnyPathPin, (key: any) => TransformShape, unknown?]
type LooseArmPin =
    | (string | unknown[])[]
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

        const entryA = table.toEntry({ base: 'x', a: 'A', type: 'A' })
        attest(entryA.PK).equals('BASE#x')
        attest(entryA.SK).equals('A#A')

        const entryB = table.toEntry({
            base: 'y',
            b: 'B',
            type: 'B',
            extra: 'E',
        })
        attest(entryB.PK).equals('BASE#y')
        attest(entryB.SK).equals('B#B')

        // excess property still rejected
        table.toEntry({
            base: 'z',
            a: 'A',
            type: 'A',
            // @ts-expect-error - 'unknown' not in any variant
            unknown: 'bad',
        })
    })
})

describe('DynamoDB Utils', () => {
    it('CompositeKeyParams', () => {
        attest<{ a: string; b?: number; c?: boolean }>(
            null as any as CompositeKeyParams<
                { a: string; b: number; c: boolean },
                ['a', 'b', 'c']
            >,
        )
        attest<{ a: string; b?: number; c?: boolean }>(
            null as any as CompositeKeyParams<
                { a: string; b: number; c: boolean },
                ['a', 'b', ['c', (c: boolean) => 'TRANSFORM']]
            >,
        )
        attest<{ a: string; b: number; c?: boolean }>(
            null as any as CompositeKeyParams<
                { a: string; b: number; c: boolean },
                ['a', 'b', ['c', (c: boolean) => 'TRANSFORM']],
                2
            >,
        )
        attest<{ a: string; b?: number; c?: boolean }>(
            null as any as CompositeKeyParams<
                { a: string; b: number; c: boolean },
                ['a', 'b', ['c', (c: boolean) => 'TRANSFORM']],
                number
            >,
        )

        attest.instantiations([2010, 'instantiations'])
    })

    it('CompositeKeyBuilder', () => {
        attest<`A#${string}#B#${number}#C#${boolean}`>(
            null as any as CompositeKeyBuilder<
                { a: string; b: number; c: boolean },
                ['a', 'b', 'c']
            >,
        )
        attest<`A#${'a1'}#B#${1}` | `A#${'a2'}#B#${2}`>(
            null as any as CompositeKeyBuilder<
                | { a: 'a1'; b: 1; c: true; z: never }
                | { a: 'a2'; b: 2; c: true; z: never },
                ['a', 'b']
            >,
        )
        attest<`A-${string}-B-${number}-C-${boolean}`>(
            null as any as CompositeKeyBuilder<
                { a: string; b: number; c: boolean },
                ['a', 'b', 'c'],
                '-'
            >,
        )
        attest<`A-${string}-B-${number}`>(
            null as any as CompositeKeyBuilder<
                { a: string; b: number; c: boolean },
                ['a', 'b', 'c'],
                '-',
                2
            >,
        )
        attest<
            | `A-${string}`
            | `A-${string}-B-${number}`
            | `A-${string}-B-${number}-C-${boolean}`
        >(
            null as any as CompositeKeyBuilder<
                { a: string; b: number; c: boolean },
                ['a', 'b', 'c'],
                '-',
                3,
                true
            >,
        )
        attest<
            | 'A#a1'
            | 'A#a1#B#1'
            | 'A#a1#B#1#C#true'
            | 'A#a2'
            | 'A#a2#B#2'
            | 'A#a2#B#2#C#false'
        >(
            null as any as CompositeKeyBuilder<
                | { a: 'a1'; b: 1; c: true; z: never }
                | { a: 'a2'; b: 2; c: false; z: never },
                ['a', 'b', 'c'],
                '#',
                3,
                true
            >,
        )
        attest<
            | 'A#a1'
            | 'A#a1#B#1'
            | 'A#a2'
            | 'A#a2#B#2'
            | 'A#a1#B#1#C#TRANSFORM'
            | 'A#a2#B#2#C#TRANSFORM'
        >(
            null as any as CompositeKeyBuilder<
                | { a: 'a1'; b: 1; c: true; z: never }
                | { a: 'a2'; b: 2; c: false; z: never },
                ['a', 'b', ['c', (c: boolean) => 'TRANSFORM']],
                '#',
                3,
                true
            >,
        )
        attest<
            | 'A#a1'
            | 'A#a1#B#1'
            | 'A#a2'
            | 'A#a2#B#2'
            | 'A#a1#B#1#TAG#TRANSFORM'
            | 'A#a2#B#2#TAG#TRANSFORM'
        >(
            null as any as CompositeKeyBuilder<
                | { a: 'a1'; b: 1; c: true; z: never }
                | { a: 'a2'; b: 2; c: false; z: never },
                [
                    'a',
                    'b',
                    [
                        'c',
                        (c: boolean) => {
                            tag: 'TAG'
                            value: 'TRANSFORM'
                        },
                    ],
                ],
                '#',
                3,
                true
            >,
        )
        attest<
            | 'A#a1'
            | 'A#a1#B#1'
            | 'A#a2'
            | 'A#a2#B#2'
            | 'A#a1#B#1#TRANSFORM'
            | 'A#a2#B#2#TRANSFORM'
        >(
            null as any as CompositeKeyBuilder<
                | { a: 'a1'; b: 1; c: true; z: never }
                | { a: 'a2'; b: 2; c: false; z: never },
                [
                    'a',
                    'b',
                    [
                        'c',
                        (c: boolean) => {
                            value: 'TRANSFORM'
                        },
                    ],
                ],
                '#',
                3,
                true
            >,
        )

        // 5662 -> 5746: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        attest.instantiations([5746, 'instantiations'])
    })

    it('tableEntry', () => {
        type Entity =
            | { a: 'a1'; b: 1; c: true; z: 'never' }
            | { a: 'a2'; b: 2; c: true; z: 'never' }
        const testTableEntry = tableEntry<Entity>()(
            {
                PK: ['a', 'b', 'c'],
                SK: 'b', // raw numeric key is only allowed for sorting propuse where other mechanism is not available (arbitrary precision numbers), either way it should use a regular composite key.
            } as const,
            '-',
        )

        expect(testTableEntry.fromEntry).toBeDefined()
        expect(testTableEntry.toEntry).toBeDefined()
        expect(testTableEntry.key).toBeDefined()
        expect(testTableEntry.infer).toBeDefined()

        type entries =
            | ({
                  a: 'a1'
                  b: 1
                  c: true
                  z: 'never'
              } & {
                  readonly PK: 'A-a1-B-1-C-true'
                  readonly SK: 1
              })
            | ({
                  a: 'a2'
                  b: 2
                  c: true
                  z: 'never'
              } & {
                  readonly PK: 'A-a2-B-2-C-true'
                  readonly SK: 2
              })

        attest<entries>(testTableEntry.infer)

        expect(
            testTableEntry.key(
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
            testTableEntry.key(
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
        ).toBe('A-a1-B-1-')

        const entity = {
            a: 'a1',
            b: 1,
            c: true,
            z: 'never',
        } satisfies Entity

        const testTableEntryObj = testTableEntry.toEntry(entity)

        testTableEntry.toEntry({
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

        attest<Entity | CodecError>(
            null as any as ReturnType<typeof testTableEntry.fromEntry>,
        )
        if (failed(fromEntry)) throw fromEntry
        attest<typeof entity>(fromEntry) // narrow down to the exact type

        expect(fromEntry).toEqual(entity)

        const key = testTableEntry.key(
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

        attest<'A-a1-B-1' | 'A-a1'>(key)

        expect(key).toBe('A-a1-B-1')

        const keyDefaults = testTableEntry.key('PK', {
            a: 'a1',
            b: 1,
            c: true,
        })

        attest<'A-a1-B-1-C-true'>(keyDefaults)

        expect(keyDefaults).toBe('A-a1-B-1-C-true')

        // paths are accessible at runtime, and stringify to the document path
        expect(testTableEntry.path().PK.toString()).toBe('PK')

        expect(
            testTableEntry.key(
                'SK',
                {
                    b: 1,
                },
                undefined, // when is raw numeric key, configuration is not needed
            ),
        ).toBe(1)
        expect(
            testTableEntry.key(
                'SK',
                {
                    b: 1,
                },
                // @ts-expect-error
                { depth: 1 },
            ),
        ).toBe(1)

        expect(
            testTableEntry.key(
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
        attest.instantiations([8590, 'instantiations'])
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
            '-',
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
        attest.instantiations([2875, 'instantiations'])
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
                    | NonEmptyArray<
                          | 'a'
                          | 'b'
                          | 'c'
                          | 'z'
                          | ['a', (key: 'a1' | 'a2') => TransformShape]
                          | ['b', (key: 1n | 2) => TransformShape]
                          | ['c', (key: true | 0) => TransformShape]
                          | ['z', (key: 'never') => TransformShape]
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
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'c'
                                        | 'z'
                                        | ['a', (key: 'a1') => TransformShape]
                                        | ['b', (key: 1n) => TransformShape]
                                        | ['c', (key: true) => TransformShape]
                                        | [
                                              'z',
                                              (key: 'never') => TransformShape,
                                          ]
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
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'c'
                                        | 'z'
                                        | ['a', (key: 'a2') => TransformShape]
                                        | ['b', (key: 2) => TransformShape]
                                        | ['c', (key: 0) => TransformShape]
                                        | [
                                              'z',
                                              (key: 'never') => TransformShape,
                                          ]
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
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'c'
                                        | 'z'
                                        | [
                                              'a',
                                              (
                                                  key: 'a1' | 'a2',
                                              ) => TransformShape,
                                          ]
                                        | ['b', (key: 2 | 1n) => TransformShape]
                                        | [
                                              'c',
                                              (key: true | 0) => TransformShape,
                                          ]
                                        | [
                                              'z',
                                              (key: 'never') => TransformShape,
                                          ]
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
                                                | NonEmptyArray<
                                                      | 'a'
                                                      | 'b'
                                                      | 'c'
                                                      | 'z'
                                                      | [
                                                            'a',
                                                            (
                                                                key: 'a1',
                                                            ) => TransformShape,
                                                        ]
                                                      | [
                                                            'b',
                                                            (
                                                                key: 1n,
                                                            ) => TransformShape,
                                                        ]
                                                      | [
                                                            'c',
                                                            (
                                                                key: true,
                                                            ) => TransformShape,
                                                        ]
                                                      | [
                                                            'z',
                                                            (
                                                                key: 'never',
                                                            ) => TransformShape,
                                                        ]
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
                                                | NonEmptyArray<
                                                      | 'a'
                                                      | 'b'
                                                      | 'c'
                                                      | 'z'
                                                      | [
                                                            'a',
                                                            (
                                                                key: 'a2',
                                                            ) => TransformShape,
                                                        ]
                                                      | [
                                                            'b',
                                                            (
                                                                key: 2,
                                                            ) => TransformShape,
                                                        ]
                                                      | [
                                                            'c',
                                                            (
                                                                key: 0,
                                                            ) => TransformShape,
                                                        ]
                                                      | [
                                                            'z',
                                                            (
                                                                key: 'never',
                                                            ) => TransformShape,
                                                        ]
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
                    ['c', (c: number | boolean) => (c ? 'VERDADERO' : 'FALSO')],
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
                        a2: 'b',
                        a1: [
                            'a',
                            'b',
                            [
                                'c',
                                (c: number | boolean) => ({
                                    tag: 'NEW_TAG' as const,
                                    value: c
                                        ? ('VERDADERO' as const)
                                        : ('FALSO' as const),
                                }),
                            ],
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
            '-',
        )

        type entries = show<
            | ({
                  a: 'a1'
                  b: 1n
                  c: true
                  z: 'never'
              } & {
                  readonly PK: 'A-a1-B-1-C-VERDADERO' | 'A-a1-B-1-C-FALSO'
                  readonly SK: 1n
                  readonly GSI1PK: 1n
                  readonly GSI1SK:
                      | 'A-a1-B-1-NEW_TAG-VERDADERO'
                      | 'A-a1-B-1-NEW_TAG-FALSO'
                  readonly GSI2PK: never
              })
            | ({
                  a: 'a2'
                  b: 2
                  c: 0
                  z: 'never'
              } & {
                  readonly PK: 'A-a2-B-2-C-VERDADERO' | 'A-a2-B-2-C-FALSO'
                  readonly SK: 2
                  readonly GSI1PK: 2
                  readonly GSI1SK: 2
                  readonly GSI2PK: 2
              })
        >

        attest<entries>(testTableEntry.infer)

        expect(
            testTableEntry.key(
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
            testTableEntry.key('PK', {
                a: 'a2',
                b: 2,
                c: 0,
            }),
        ).toBe('A-a2-B-2-C-FALSO')

        expect(
            testTableEntry.key('SK', {
                b: 2,
            }),
        ).toBe(2)

        expect(
            testTableEntry.key('SK', {
                b: 1n,
            }),
        ).toBe(1n)
        void testTableEntry.key(
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

        void testTableEntry.key('GSI1PK', {
            z: 'never', // required to discriminate
            b: 1n,
        })
        expect(
            testTableEntry.key('GSI1PK', {
                z: 'never', // required to discriminate
                b: 1n,
            }),
        ).toBe(1n)

        expect(
            testTableEntry.key(
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
            testTableEntry.key('GSI1SK', {
                a: 'a1',
                b: 1n,
                c: true,
            }),
        ).toBe('A-a1-B-1-NEW_TAG-VERDADERO')

        expect(
            testTableEntry.key('GSI1SK', {
                a: 'a2',
                b: 2,
                // z: 'never',
            }),
        ).toBe(2)

        expect(
            testTableEntry.key('GSI2PK', {
                a: 'a2',
                b: 2,
                // z: 'never',
            }),
        ).toBe(2)

        expect(
            testTableEntry.key('GSI2PK', {
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
        attest.instantiations([19066, 'instantiations'])
    })

    test('real world example', () => {
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

        void (RealEntry.key(
            'PK',
            {
                id1: 'client',
                user: 'user',
            },
            {
                allowPartial: true,
            },
        ) satisfies 'ID1#client#USER#user' | 'ID1#client')

        void (RealEntry.key(
            'PK',
            {
                id1: 'client',
                user: 'user',
            },
            {
                // allowPartial: true,
            },
        ) satisfies 'ID1#client#USER#user')

        void (RealEntry.key('GSI1SK', {
            type: 'TypeA',
            tag: 'A',
        }) satisfies 'TYPE#TypeA')

        // @ts-expect-error
        const expect_key2_ = RealEntry.key('GSI1SK', {
            type: 'TypeA',
            tag: 'A',
            // biome-ignore lint/complexity/noBannedTypes: test case
        } as {})

        void (RealEntry.key(
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

        const expect_key_depth_partial_discriminator = RealEntry.key(
            'SK',
            { tag: 'A', id2: 'yolo' },
            { allowPartial: true, depth: 2 },
        ) satisfies 'TAG#A' | `TAG#A#ID2#${string}`

        attest<'TAG#A' | `TAG#A#ID2#yolo`>(
            expect_key_depth_partial_discriminator,
        )

        void (RealEntry.key(
            'SK',
            { tag: 'A', id2: 'yolo' },
            { depth: 2 },
        ) satisfies 'TAG#A#ID2#yolo')

        // 32508 -> 33502: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 33502 -> 33647: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        attest.instantiations([33647, 'instantiations'])
    })

    test('schema allows for nullish values if has transform', () => {
        const base = tableEntry<
            | { a: 'a1'; b: 1n; c: true; z: 'never' }
            | { a: 'a2'; b: 2; c: 0; z?: 'never' | null }
        >()

        const testTableEntry = base(
            {
                PK: ['a', ['b', (x: 1n | 2) => x.toString()], 'c'],
                SK: ['c', ['z', (z: 'never' | null) => z ?? 'DEFAULT', null]],
                GSIPK: 'z',
                GSISK: {
                    discriminator: 'a',
                    spec: {
                        a1: ['z', ['z', (z: 'never') => z ?? 'DEFAULT']],
                        a2: [
                            [
                                'z',
                                (z: 'never' | null) => z ?? 'DEFAULT',
                                'never',
                            ],
                        ],
                    },
                },
            },
            '-',
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
                  readonly GSIPK: 'never' | undefined
                  readonly GSISK: 'Z-never' | 'Z-DEFAULT'
              })
        >

        attest<entries>(testTableEntry.infer)

        expect(
            testTableEntry.key('SK', {
                c: 0,
                z: undefined,
            }),
        ).toBe('C-0-Z-DEFAULT')

        expect(
            testTableEntry.key('SK', {
                c: 0,
                z: 'never',
            }),
        ).toBe('C-0-Z-never')

        expect(
            // on partial no transform if missing
            testTableEntry.key(
                'PK',
                {
                    c: 0,
                    a: 'a2',
                },
                { allowPartial: true },
            ),
        ).toBe('A-a2')
    })

    test('heterogenous keys schema', () => {
        const base = tableEntry<
            { a: 'a1'; b: 1n; extra: 'extra' } | { a: 'a2'; b: 2 }
        >()

        attest<
            [
                schema: Record<
                    string,
                    | 'a'
                    | 'b'
                    | NonEmptyArray<
                          | 'a'
                          | 'b'
                          | ['a', (key: 'a1' | 'a2') => TransformShape]
                          | ['b', (key: 1n | 2) => TransformShape]
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
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | 'extra'
                                        | ['a', (key: 'a1') => TransformShape]
                                        | ['b', (key: 1n) => TransformShape]
                                        | [
                                              'extra',
                                              (key: 'extra') => TransformShape,
                                          ]
                                        | PathComponents
                                    >
                                  | null
                                  | PathMatchPin
                                  | CasesMatchPin
                              a2:
                                  | 'a'
                                  | 'b'
                                  | NonEmptyArray<
                                        | 'a'
                                        | 'b'
                                        | ['a', (key: 'a2') => TransformShape]
                                        | ['b', (key: 2) => TransformShape]
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
                [
                    'data',
                    (d: Pick<Inner, 'id'>) => ({
                        tag: 'DATA' as const,
                        value: d.id,
                    }),
                    { id: 'default-id' },
                ],
                'key',
            ],
        })

        // empty object should be rejected — it doesn't satisfy the transform param
        tableEntry<Entity>()({
            PK: [
                [
                    'data',
                    (d: Pick<Inner, 'id'>) => ({
                        tag: 'DATA' as const,
                        value: d.id,
                    }),
                    // @ts-expect-error - {} does not satisfy Pick<Inner, 'id'>
                    {},
                ],
                'key',
            ],
        })

        // Uses the actual value when present
        expect(
            table.key('PK', {
                data: { id: 'real-id' },
                key: 'k1',
            }),
        ).toBe('DATA#real-id#KEY#k1')

        // Falls back to default when data is undefined
        expect(
            table.key('PK', {
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
            PK: [
                [
                    'a',
                    (x: Pick<A, 'w'>) => ({
                        tag: 'W' as const,
                        value: x.w,
                    }),
                ],
            ],
            SK: [
                [
                    /// ERROR FOUND - adding other sub attribute to the same key structure
                    'a',
                    (x: Pick<A, 'w'>) => ({
                        tag: 'W' as const,
                        value: x.w,
                    }),
                ],
                [
                    'a',
                    (x: Pick<A, 'x'>) => ({
                        tag: 'X' as const,
                        value: x.x,
                    }),
                ],
                [
                    'b',
                    (x: string) => ({
                        tag: 'B_VAL' as const,
                        value: x,
                    }),
                ],
            ],
            GSI1PK: [
                [
                    'a',
                    (x: Pick<A, 'w'>) => ({
                        tag: 'W' as const,
                        value: x.w,
                    }),
                ],
            ],
            GSI1SK: [
                [
                    'b',
                    (x: string) => ({
                        tag: 'B_VAL' as const,
                        value: x,
                    }),
                ],
            ],
        })

        // PK only needs w
        expect(
            Entry.key('PK', {
                a: { w: 'w1' },
            }),
        ).toBe('W#w1')

        // SK needs w AND x (intersected from both transform params)
        expect(
            Entry.key('SK', {
                a: { w: 'w1', x: 'x1' },
                b: 'b1',
            }),
        ).toBe('W#w1#X#x1#B_VAL#b1')

        // GSI1PK only needs w
        expect(
            Entry.key('GSI1PK', {
                a: { w: 'w1' },
            }),
        ).toBe('W#w1')

        // GSI1SK only needs b
        expect(
            Entry.key('GSI1SK', {
                b: 'b1',
            }),
        ).toBe('B_VAL#b1')

        // SK requires both w and x on a
        Entry.key('SK', {
            // @ts-expect-error - missing w
            a: { x: 'x1' },
            b: 'b1',
        })

        // SK requires both w and x on a
        Entry.key('SK', {
            // @ts-expect-error - missing x
            a: { w: 'w1' },
            b: 'b1',
        })

        // PK requires w on a
        Entry.key('PK', {
            // @ts-expect-error - empty object missing w
            a: {},
        })

        // PK requires w on a, not x
        Entry.key('PK', {
            // @ts-expect-error - x does not exist on Pick<A, 'w'>
            a: { x: 'x1' },
        })

        // 6982 -> 7273: the codec types grew over the passes since the last refresh, each move
        // inside the tolerance, so no single change moved the pin out of it
        // 7273 -> 7329: the type of a key reads `enforceBoundary`, so the builder of the key type
        // carries one more parameter and each prefix of a partial key one more template
        // 7329 -> 9028: an arm of a match is a key spec of its variant, so each arm of a discriminated
        // key builds the type of a match that the variant allows, and the schema check reads it
        attest.instantiations([9028, 'instantiations'])
    })

    test('NeedsValidation detects 3-tuples in mixed arrays', () => {
        type Entity = {
            id: string
            data?: { name: string }
        }

        // Schema where the ONLY 3-tuple is in a mixed array (alongside a bare key).
        // NeedsValidation uses `V[number] extends Tuple3` which checks ALL elements,
        // so if it misses mixed arrays, {} would incorrectly pass.
        tableEntry<Entity>()({
            PK: [
                'id',
                [
                    'data',
                    (d: { name: string }) => d.name,
                    // @ts-expect-error - {} does not satisfy { name: string }
                    {},
                ],
            ],
        })

        // Valid default should pass
        const table = tableEntry<Entity>()({
            PK: [
                'id',
                [
                    'data',
                    (d: { name: string }) => d.name,
                    { name: 'withLegacyRead' },
                ],
            ],
        })

        expect(table.key('PK', { id: 'x', data: undefined })).toBe(
            'ID#x#DATA#withLegacyRead',
        )
    })
})

/**
 * **The published surface, pinned — both what is on it and what is deliberately not.**
 *
 * `Rotorise.ts` enumerates the codec values rather than starring them, so that an export is a
 * decision rather than a consequence of where a function happens to live. That only holds if
 * something notices when the two lists drift, and nothing did: the reader then called `admits`
 * reached the surface in `46cb950` because the re-export was `export * from './codec/codec'`, and no test
 * could have said so.
 *
 * The absent half is the load-bearing one. The names below read a **term** for this library's own
 * resolver, declaration guard and emitter to ask what a codec is; a caller has the codec's
 * behaviour, which is what they are derived from. Re-adding one is a decision, and this makes it a
 * visible one.
 *
 * **The list is the live names, and that is a rule this test learned the hard way.** It held eight
 * names that had been deleted — `admits`, `writes`, `decides`, `setBase`, `deeper`, `occupies`,
 * `reads`, `admitsAttribute` — and `Object.hasOwn` answers `false` for a name nothing declares, so
 * eight of its twelve rows passed by asserting nothing while their replacements went unguarded. A
 * deleted name cannot leak. Only a live one can, so a row for a dead name is a row that has stopped
 * being a test, and a deletion pass moves the row to the name that replaced it.
 */
describe('the published surface', () => {
    const internal = [
        // the two that ask the pair, which is what admission is: `accepts` replaced `admits` and
        // `readsBack` replaced `admitsAttribute`, both asking the codec rather than reading a term
        'accepts',
        'readsBack',
        // deleted public names remain absent from the value and type surfaces
        'Slot',
        'fallback',
        'legacy',
        'drop',
        'RestPolicy',
        'RestDeclaration',
        // a cycle is a `scope`, and the thunk under a `ref` is internal
        'lazy',
        // the five functions of a term the model computes, which `writes` and `decides` became
        'member',
        'occV',
        'occA',
        'specOf',
        'tagsOf',
        // the declaration guard and what it reads, which `identifying` and `deeper` became
        'compatible',
        // the predicate a refinement carries, run
        'holds',
        // the value kinds a term takes, the two halves of the term cache, and the mark reader
        'valueKinds',
        'termOf',
        'codecOfTerm',
        'constantOf',
    ] as const

    it('does not carry the internal utilities', async () => {
        const surface = await import('./Rotorise')
        for (const name of internal) {
            expect(Object.hasOwn(surface, name)).toBe(false)
        }
    })

    /**
     * **The other half of the same fact, and it was unpinned while twelve names leaked.**
     *
     * The list above is a run-time check, and a run-time check cannot see a type. `export type *
     * from './codec/codec'` re-exported every one of that module's exports — the values among them as
     * *types* — so `import { decides } from 'rotorise'` type-checked and was `undefined` when it
     * ran. The value list was a decision and the type surface was still a consequence of where a
     * function lived, which is the thing `46cb950` was supposed to have ended.
     *
     * Written as one rule rather than as twelve suppressions: no name held back at run time is a
     * key of the module's type either. A thirteenth added to `internal` is checked by both halves
     * without a line here.
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
            'withLegacyRead',
            'held',
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
