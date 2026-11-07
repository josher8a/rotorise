/**
 * A tag is the stored literal on both sides.
 *
 * A caller's adapter over a tag field writes the caller's value as the stored literal. The variant
 * lookup keys on the stored literal, in the type and at run time, so a row that carries `'D'` reads
 * as the variant that the caller names `'dog'`, and the value that the read returns writes back to
 * the same row.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError } from '../../../Rotorise'
import {
    type Decoded,
    discriminatedUnion,
    exclude,
    held,
    item,
    number,
    object,
    string,
} from '../../codec'

const Dog = held(string('D'), string('dog'), {
    encode: (_: 'dog') => 'D' as const,
    decode: (_: 'D') => 'dog' as const,
})
const PetUnion = discriminatedUnion('kind', [
    object({ kind: Dog, bark: string }),
    object({ kind: string('cat'), lives: number }),
])
const Pets = item(PetUnion)

describe('a tag under a caller adapter', () => {
    it('keys the variant by the stored literal in the type', () => {
        void Pets.spec.D
        // @ts-expect-error the caller's value is no key of the spec
        void Pets.spec.dog
        expect(Object.keys(Pets.spec).sort()).toEqual(['D', 'cat'])
    })

    it('reads the stored row as the variant, and writes the read back to the row', () => {
        const row = { kind: { S: 'D' }, bark: { S: 'woof' } }
        const read = Pets.unsafeDecode(row)
        expect(read).toEqual({ kind: 'dog', bark: 'woof' })
        expect(Pets.unsafeEncode(read)).toEqual(row)
        expect(Pets.unsafeEncodePartial({ kind: 'dog' })).toEqual({
            kind: { S: 'D' },
        })
    })

    it('picks the variant of a plain tag beside it', () => {
        const cat = { kind: 'cat', lives: 9 } as const
        const row = Pets.unsafeEncode(cat)
        expect(row).toEqual({ kind: { S: 'cat' }, lives: { N: '9' } })
        expect(Pets.unsafeDecode(row)).toEqual(cat)
    })

    it('refuses a tag that no variant writes, and names the stored literals', () => {
        const refused = Pets.encode({ kind: 'bird' } as never)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).message).toContain("expected 'D', 'cat'")
    })
})

describe('a number tag under a caller adapter', () => {
    it('is refused at construction, because a number is an adapter and a tag is read through one', () => {
        const One = held(number(1), string('one'), {
            encode: (_: 'one') => 1 as const,
            decode: (_: 1) => 'one' as const,
        })
        expect(() =>
            item(
                // @ts-expect-error the tag is a number under the adapter of a caller, which names no key
                discriminatedUnion('size', [
                    object({ size: One, pups: string }),
                    object({ size: number(2), pups: string, extra: number }),
                ]),
            ),
        ).toThrow(/every option must name 'size' with a literal/)
    })
})

describe('a slice of a tag under a caller adapter', () => {
    const NotCats = exclude(PetUnion, object({ kind: string('cat') }))

    it('keeps the variant that the stored literal selects, in the type and at run time', () => {
        expectTypeOf<Decoded<typeof NotCats>>().toEqualTypeOf<{
            readonly kind: 'dog'
            readonly bark: string
        }>()
        const row = { M: { kind: { S: 'D' }, bark: { S: 'woof' } } }
        expect(NotCats.unsafeDecode(row)).toEqual({ kind: 'dog', bark: 'woof' })
        expect(NotCats.unsafeEncode({ kind: 'dog', bark: 'woof' })).toEqual(row)
    })
})
