/**
 * A tag has one stored literal, and one reader finds it through the wrappers of the field.
 *
 * The reader is the model's `pinOfG` with the `ref` indirection: it passes each `refine`, then one
 * `held`, and the term under that `held` pins the stored literal. The variant lookup, the decision
 * of a constant and the type of the tag table each read the tag by it.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import {
    CodecError,
    constantOf,
    discriminatedUnion,
    held,
    item,
    number,
    object,
    ref,
    refine,
    scope,
    string,
} from '../../codec'

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
        const named: (typeof Pets.spec)['dog'] = undefined as never
        expect(named).toBeUndefined()
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

    it('decides nothing where the adapter returns a refusal', () => {
        const Kind = held(string('D'), string('dog'), {
            encode: (_: 'dog') => 'D' as const,
            decode: (_: 'D') => new CodecError('no dog') as unknown as 'dog',
        })
        expect(() =>
            tableEntry<{ kind: 'dog'; petId: string }>()(
                { PK: ['kind', 'petId'] },
                { codec: { kind: Kind, petId: string } },
            ),
        ).not.toThrow()
    })
})
