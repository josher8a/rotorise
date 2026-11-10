/**
 * A tag has one stored literal, and one reader finds it through the wrappers of the field.
 *
 * The reader is the model's `pinOfG` with the `ref` indirection: it passes each `refine`, then one
 * `held`, and the term under that `held` pins the stored literal. The variant lookup, the decision
 * of a constant and the type of the tag table each read the tag by it.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import { DynamoNumber } from '../../attribute'
import {
    CodecError,
    constantOf,
    discriminatedUnion,
    held,
    item,
    mdunion,
    number,
    object,
    ref,
    refine,
    scope,
    string,
    union,
} from '../../codec'
import { dynamoNumber } from '../../prisms'
import { orThrow } from '../../result'

const DogTag = held(string('D'), string('dog'), {
    encode: (_: 'dog') => 'D' as const,
    decode: (_: 'D') => 'dog' as const,
})
const isDog = (v: 'dog'): v is 'dog' => v === 'dog'

type Store = {
    decode: (row: unknown) => unknown
    encode: (value: unknown) => unknown
}
const row = { kind: { S: 'D' }, bark: { S: 'woof' } }

describe('a tag read through a ref and a refine', () => {
    it('writes back the row that it read, where the tag is a ref to an adapter of a caller', () => {
        const { Pets } = scope({
            Pets: discriminatedUnion('kind', [
                object({ kind: ref('DogTag'), bark: string }),
                object({ kind: string('cat'), lives: number }),
            ] as never),
            DogTag,
        } as never) as { Pets: never }
        const Pet = item(Pets) as unknown as Store
        const read = Pet.decode(row)
        expect(read).toEqual({ kind: 'dog', bark: 'woof' })
        expect(Pet.encode(read)).toEqual(row)
    })

    it('writes back the row that it read, where the tag is a refine over a ref to an adapter', () => {
        const { Pets } = scope({
            Pets: discriminatedUnion('kind', [
                object({
                    kind: refine(ref('DogTag') as never, isDog as never),
                    bark: string,
                }),
                object({ kind: string('cat'), lives: number }),
            ] as never),
            DogTag,
        } as never) as { Pets: never }
        const Pet = item(Pets) as unknown as Store
        const read = Pet.decode(row)
        expect(read).toEqual({ kind: 'dog', bark: 'woof' })
        expect(Pet.encode(read)).toEqual(row)
    })

    it('keys a refined tag by the stored literal, in the type and at run time', () => {
        const Pets = item(
            discriminatedUnion('kind', [
                object({ kind: refine(DogTag, isDog), bark: string }),
                object({ kind: string('cat'), lives: number }),
            ]),
        )
        expect(Object.keys(Pets.spec).sort()).toEqual(['D', 'cat'])
        expectTypeOf(Pets.spec).toHaveProperty('D')
        // @ts-expect-error the caller's value is no key of the spec
        void Pets.spec.dog
    })
})

describe('a tag whose adapter pins no literal', () => {
    it('is refused in the type and at construction, where the adapter holds the tag over another adapter', () => {
        const Twice = held(DogTag, string('dd'), {
            encode: (_: 'dd') => 'dog' as const,
            decode: (_: 'dog') => 'dd' as const,
        })
        expect(() =>
            item(
                // @ts-expect-error the adapter holds the tag over another adapter, and names no literal
                discriminatedUnion('kind', [
                    object({ kind: Twice, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ]),
            ),
        ).toThrow(/every option must name 'kind' with a literal/)
    })

    it('is refused in the type and at construction, where the inner term is no literal', () => {
        const Loose = held(string, string('dog'), {
            encode: (v: 'dog') => v,
            decode: () => 'dog' as const,
        })
        expect(() =>
            item(
                // @ts-expect-error the inner term is no literal
                discriminatedUnion('kind', [
                    object({ kind: Loose, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ]),
            ),
        ).toThrow(/every option must name 'kind' with a literal/)
    })
})

describe('two members that decode their tag to one value', () => {
    const refusal =
        /two options decode to 'kind' = 'dog', and a write of that value gives '(D|dog)', the text of option 0, so option 1 is never written/

    it('are refused in the type and at construction, where a caller adapter and a plain literal meet', () => {
        expect(() =>
            item(
                // @ts-expect-error two options decode 'kind' to 'dog'
                discriminatedUnion('kind', [
                    object({ kind: DogTag, bark: string }),
                    object({ kind: string('dog'), lives: number }),
                ]),
            ),
        ).toThrow(refusal)
        expect(() =>
            item(
                // @ts-expect-error two options decode 'kind' to 'dog'
                discriminatedUnion('kind', [
                    object({ kind: string('dog'), lives: number }),
                    object({ kind: DogTag, bark: string }),
                ]),
            ),
        ).toThrow(refusal)
    })

    it('are refused where the two differ only by a refine over the caller tag', () => {
        const Other = held(string('O'), string('dog'), {
            encode: (_: 'dog') => 'O' as const,
            decode: (_: 'O') => 'dog' as const,
        })
        expect(() =>
            item(
                // @ts-expect-error two options decode 'kind' to 'dog'
                discriminatedUnion('kind', [
                    object({ kind: refine(DogTag, isDog), bark: string }),
                    object({ kind: Other, lives: number }),
                ]),
            ),
        ).toThrow(refusal)
    })

    it('are refused with the error of the adapter as the cause, where the adapter throws', () => {
        const bug = new TypeError('a bug in the adapter')
        const Kind = held(string('D'), string('dog'), {
            encode: (_: 'dog') => 'D' as const,
            decode: (_: 'D'): 'dog' => {
                throw bug
            },
        })
        let thrown: unknown
        try {
            item(
                discriminatedUnion('kind', [
                    object({ kind: Kind, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ]),
            )
        } catch (error) {
            thrown = error
        }
        expect(thrown).toBeInstanceOf(CodecError)
        expect((thrown as CodecError).cause).toBe(bug)
    })

    it('are two members when each decodes its tag to its own value', () => {
        expect(() =>
            item(
                discriminatedUnion('kind', [
                    object({ kind: DogTag, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ]),
            ),
        ).not.toThrow()
    })

    it('are refused where the two differ at another key, because the write reads each key alone', () => {
        expect(() =>
            item(
                mdunion(
                    ['kind', 'size'],
                    // @ts-expect-error two options decode 'kind' to 'dog', and store two texts
                    [
                        object({
                            kind: DogTag,
                            size: string('small'),
                            bark: string,
                        }),
                        object({
                            kind: string('dog'),
                            size: string('large'),
                            pen: string,
                        }),
                    ],
                ),
            ),
        ).toThrow(refusal)
    })

    it('are two members in either order, where a plain tag is the text of the number that a caller tag decodes to', () => {
        const OneTag = held(string('D'), number(1), {
            encode: (_: 1) => 'D' as const,
            decode: (_: 'D') => 1 as const,
        })
        const caller = object({ kind: OneTag, bark: string })
        const plain = object({ kind: string('1'), lives: number })
        // the type accepts both orders, because `1` and `'1'` are two values
        for (const Pets of [
            item(discriminatedUnion('kind', [caller, plain])),
            item(discriminatedUnion('kind', [plain, caller])),
        ] as unknown as Store[]) {
            const read = Pets.decode({ kind: { S: 'D' }, bark: { S: 'woof' } })
            expect(read).toEqual({ kind: 1, bark: 'woof' })
            for (const stored of [
                { kind: { S: 'D' }, bark: { S: 'woof' } },
                { kind: { S: '1' }, lives: { N: '9' } },
            ])
                expect(Pets.encode(Pets.decode(stored))).toEqual(stored)
        }
    })

    it('are refused where the adapter does not write its own value as its own literal', () => {
        const Broken = held(string('D'), string('dog'), {
            encode: (_: 'dog') =>
                new CodecError('the adapter refuses its own value'),
            decode: (_: 'D') => 'dog' as const,
        })
        // the type accepts the pair: it states the overlap of the decoded tags and no lookup law
        expect(() =>
            item(
                discriminatedUnion('kind', [
                    object({ kind: Broken, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ]),
            ),
        ).toThrow(
            /option 0 decodes 'kind' = 'dog', and the write of that value refuses: the adapter refuses its own value/,
        )
    })

    it('are refused in either order where a plain number tag meets a caller tag that decodes to the same number', () => {
        const one = orThrow(DynamoNumber.from('1'))
        const XTag = held(string('X'), dynamoNumber(one), {
            encode: (_: DynamoNumber) => 'X' as const,
            decode: (_: 'X') => orThrow(DynamoNumber.from('1')),
        })
        const plain = object({ kind: dynamoNumber(one), lives: number })
        const caller = object({ kind: XTag, bark: string })
        // the model has no reference identity: a number is its digits, so one answer for both orders
        for (const options of [
            [plain, caller],
            [caller, plain],
        ])
            expect(() =>
                item(discriminatedUnion('kind', options as never)),
            ).toThrow(/two options decode to 'kind' = '1'/)
    })

    it('are refused where a tag that is a union of one literal decodes to the value of the other tag', () => {
        expect(() =>
            item(
                mdunion(['kind', 'size'], [
                    object({
                        kind: DogTag,
                        size: string('small'),
                        bark: string,
                    }),
                    object({
                        kind: union([string('dog')]),
                        size: string('large'),
                        pen: string,
                    }),
                ] as never) as never,
            ),
        ).toThrow(/two options decode to 'kind' = 'dog'/)
    })

    it('write back the row that each reads, where the write gives each member its own text', () => {
        const Pets = item(
            mdunion(['kind', 'size'], [
                object({ kind: DogTag, size: string('small'), bark: string }),
                object({
                    kind: string('cat'),
                    size: string('large'),
                    pen: string,
                }),
                object({
                    kind: string('cat'),
                    size: string('small'),
                    pen: string,
                }),
            ] as never) as never,
        ) as unknown as Store
        for (const stored of [
            { kind: { S: 'D' }, size: { S: 'small' }, bark: { S: 'woof' } },
            { kind: { S: 'cat' }, size: { S: 'large' }, pen: { S: 'north' } },
            { kind: { S: 'cat' }, size: { S: 'small' }, pen: { S: 'south' } },
        ])
            expect(Pets.encode(Pets.decode(stored))).toEqual(stored)
    })
})

describe('the constant that a field decides', () => {
    it('is read through a ref, and not through a refine, which can reject the value', () => {
        const { Row } = scope({
            Row: object({
                kind: ref('DogTag'),
                label: ref('Label'),
                guarded: refine(
                    ref('Label') as never,
                    ((v: 'PET') => v === 'PET') as never,
                ),
            } as never),
            DogTag,
            Label: string('PET'),
        } as never) as unknown as {
            Row: { spec: Record<'kind' | 'label' | 'guarded', never> }
        }
        expect(constantOf(Row.spec.kind)).toBe('dog')
        expect(constantOf(Row.spec.label)).toBe('PET')
        expect(constantOf(Row.spec.guarded)).toBeUndefined()
    })
})

describe('a key component whose adapter throws', () => {
    it('is refused at construction, with the component and the error of the adapter as the cause', () => {
        const bug = new TypeError('a bug in the adapter')
        const Kind = held(string('D'), string('dog'), {
            encode: (_: 'dog') => 'D' as const,
            decode: (_: 'D'): 'dog' => {
                throw bug
            },
        })
        let thrown: unknown
        try {
            tableEntry<{ kind: 'dog'; petId: string }>()(
                { PK: ['kind', 'petId'] },
                { codec: { kind: Kind, petId: string } },
            )
        } catch (error) {
            thrown = error
        }
        expect(thrown).toBeInstanceOf(RotoriseError)
        expect((thrown as RotoriseError).message).toContain(
            "'kind' is a key component under the adapter of a caller",
        )
        expect((thrown as RotoriseError).cause).toBe(bug)
    })

    it('decides no constant where the adapter returns a refusal of its own literal', () => {
        const Kind = held(string('D'), string('dog'), {
            encode: (_: 'dog') => 'D' as const,
            decode: (_: 'D'): 'dog' | CodecError => new CodecError('no dog'),
        })
        expect(constantOf(object({ kind: Kind }).spec.kind)).toBeUndefined()
    })
})

describe('the write of a tag that refuses', () => {
    const refusing = (v: 'dog'): v is 'dog' => v !== 'dog'

    it('names the write and not the adapter where a refinement over the tag refuses the decoded tag', () => {
        const refused = () =>
            item(
                discriminatedUnion('kind', [
                    object({ kind: refine(DogTag, refusing), bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ] as never),
            )
        expect(refused).toThrow(CodecError)
        expect(refused).toThrow(/and the write of that value refuses: /)
        expect(refused).not.toThrow(/its adapter refuses/)
    })

    it('names no adapter at a key that holds no adapter', () => {
        const none = (v: 'small'): v is 'small' => v !== 'small'
        const refused = () =>
            item(
                mdunion(['kind', 'size'], [
                    object({
                        kind: DogTag,
                        size: refine(string('small'), none),
                        bark: string,
                    }),
                    object({
                        kind: string('cat'),
                        size: string('large'),
                        lives: number,
                    }),
                ] as never) as never,
            )
        expect(refused).toThrow(/at size: .*the write of that value refuses/)
        expect(refused).not.toThrow(/adapter/)
    })

    it('keeps the reason of the one member that refuses the value at encode, and lists no stored text', () => {
        const DogOnly = held(string('D'), string, {
            encode: (v: string) =>
                v === 'dog'
                    ? ('D' as const)
                    : new CodecError('only dog is a dog'),
            decode: (_: 'D') => 'dog',
        })
        const Pets = item(
            discriminatedUnion('kind', [
                object({ kind: DogOnly, bark: string }),
                object({ kind: string('cat'), lives: number }),
            ] as never),
        ) as unknown as { encode: (value: unknown) => unknown }
        const refused = Pets.encode({ kind: 'dgo', bark: 'woof' })
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).message).toMatch(/only dog is a dog/)
        expect((refused as CodecError).message).not.toMatch(/expected 'D'/)
    })

    it('gives the reason of each member that refuses the value at encode', () => {
        const DogOnly = held(string('D'), string, {
            encode: (v: string) =>
                v === 'dog'
                    ? ('D' as const)
                    : new CodecError('only dog is a dog'),
            decode: (_: 'D') => 'dog',
        })
        const CatOnly = held(string('C'), string, {
            encode: (v: string) =>
                v === 'cat'
                    ? ('C' as const)
                    : new CodecError('only cat is a cat'),
            decode: (_: 'C') => 'cat',
        })
        const Pets = item(
            discriminatedUnion('kind', [
                object({ kind: DogOnly, bark: string }),
                object({ kind: CatOnly, lives: number }),
            ] as never),
        ) as unknown as { encode: (value: unknown) => unknown }
        const refused = Pets.encode({ kind: 'dgo', bark: 'woof' })
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).message).toMatch(/only dog is a dog/)
        expect((refused as CodecError).message).toMatch(/only cat is a cat/)
    })
})

describe('a tag whose adapter breaks the pair that it owes', () => {
    it('keeps the path and the cause of the refusal of the own write, as the own write gives them', () => {
        const cause = new Error('the cause of the adapter')
        const Broken = held(string('D'), string('dog'), {
            encode: (_: 'dog') =>
                new CodecError('the adapter refuses its own value', 'refused', {
                    cause,
                }),
            decode: (_: 'D') => 'dog' as const,
        })
        let thrown: unknown
        try {
            item(
                discriminatedUnion('kind', [
                    object({ kind: Broken, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ] as never),
            )
        } catch (error) {
            thrown = error
        }
        expect(thrown).toBeInstanceOf(CodecError)
        expect((thrown as CodecError).path).toEqual(['kind'])
        expect((thrown as CodecError).cause).toBe(cause)
    })

    it('is refused where the adapter refuses to read its own stored literal, as it is where the adapter throws', () => {
        const Unread = held(string('D'), string('dog'), {
            encode: (_: 'dog') => 'D' as const,
            decode: (_: 'D') =>
                new CodecError('the adapter refuses its own literal'),
        })
        expect(() =>
            item(
                discriminatedUnion('kind', [
                    object({ kind: Unread, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ] as never),
            ),
        ).toThrow(/the adapter refuses its own literal/)
    })

    it('is refused at construction where a later write of the adapter refuses the value', () => {
        let calls = 0
        const Flaky = held(string('D'), string('dog'), {
            encode: (_: 'dog') =>
                ++calls === 1
                    ? ('D' as const)
                    : new CodecError('the second write refuses'),
            decode: (_: 'D') => 'dog' as const,
        })
        expect(() =>
            item(
                discriminatedUnion('kind', [
                    object({ kind: Flaky, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ] as never),
            ),
        ).toThrow(
            /a later write of that value refuses: .*the second write refuses/,
        )
    })

    it('is refused at construction where a later write of the adapter gives a text that the tag does not hold', () => {
        let calls = 0
        const Moves = held(string('D'), string('dog'), {
            encode: (_: 'dog') =>
                ++calls === 1 ? ('D' as const) : ('E' as never),
            decode: (_: 'D') => 'dog' as const,
        })
        expect(() =>
            item(
                discriminatedUnion('kind', [
                    object({ kind: Moves, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ] as never),
            ),
        ).toThrow(/a later write of that value refuses: .*'E'/)
    })
})

describe('a discriminator is read at its own name', () => {
    it('refuses a row that lacks a discriminator that the prototype also names', () => {
        const Ctor = item(
            discriminatedUnion('constructor', [
                object({ constructor: string('a'), x: string }),
                object({ constructor: string('b'), y: string }),
            ] as never),
        ) as unknown as { decode: (row: unknown) => unknown }
        const refused = Ctor.decode({}) as CodecError
        expect(refused).toBeInstanceOf(CodecError)
        expect(refused.message).toMatch(/has no such attribute/)
    })
})
