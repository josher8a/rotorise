/**
 * Failures as values, with the throwing pair behind an `unsafe` prefix.
 *
 * Reading a row is not exceptional. A table holds every shape it has ever held, and a row that no
 * longer matches the schema is an ordinary outcome — so `decode` returns the failure and
 * `unsafeDecode` throws it, rather than the other way round. Naming the throwing one is what makes
 * choosing it deliberate.
 *
 * `Result<T> = T | CodecError` is a bare union, which is the same shape `flow`'s `Result<T, E>`
 * has: nothing to unwrap, nothing allocated, and `instanceof Error` tells the two apart.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import type { Attribute } from '../../attribute'
import type { AttributeCodec } from '../../codec'
import {
    array,
    CodecError,
    custom,
    discriminatedUnion,
    lazy,
    legacy,
    list,
    nullable,
    object,
    opaque,
    optional,
    record,
    refine,
    string,
    union,
} from '../../codec'

type Pet = { TAG: 'PET'; id: string; name: string }

const Pet = object({ TAG: string('PET'), id: string, name: string }).item
const pet: Pet = { TAG: 'PET', id: 'p1', name: 'Rex' }

type Tree = { name: string; children?: readonly Tree[] }
const Tree: AttributeCodec<Tree, Attribute<'M'>> = lazy(() =>
    object({ name: string, children: optional(array(Tree)) }),
)

const Visits = discriminatedUnion('type', [
    object({ type: string('CHECKUP'), petId: string }),
]).item

const Lines = union([
    object({ petId: string }),
    object({ petIds: array(string) }),
]).item

/** What a consumer writes — the same narrowing `flow`'s `isError` does. */
const isError = (value: unknown): value is CodecError => value instanceof Error

describe('the safe pair returns the failure', () => {
    it('gives the value when it works', () => {
        const encoded = Pet.encode(pet)
        expect(isError(encoded)).toBe(false)
        if (isError(encoded)) return
        expect(encoded.id).toEqual({ S: 'p1' })
    })

    it('gives the error when it does not, and does not throw', () => {
        const decoded = Pet.decode({ TAG: { S: 'PET' }, id: { N: '1' } })
        expect(isError(decoded)).toBe(true)
        if (!isError(decoded)) return
        expect(decoded).toBeInstanceOf(CodecError)
        expect(decoded.path).toEqual(['id'])
    })

    it('narrows to the entity once the error is ruled out', () => {
        const decoded = Pet.decode(Pet.unsafeEncode(pet))
        if (isError(decoded)) return expect.unreachable()
        // `decoded` is Pet here, with no cast and no unwrapping
        expect(decoded.name).toBe('Rex')
    })

    // PINS A FACT NO LAW HAS, deliberately: that the safe pair reports the *same* assembled
    // message as the throwing one is the claim, so the string is the subject here too. It stays.
    it('carries the path through nesting, as the thrown one does', () => {
        const Order = object({
            lines: array(object({ note: string })),
        }).item
        const decoded = Order.decode({
            lines: { L: [{ M: { note: { N: '7' } } }] },
        })
        if (!isError(decoded)) return expect.unreachable()
        expect(decoded.message).toBe(
            "at lines[0].note: expected attribute member 'S', found 'N'",
        )
    })
})

describe('the unsafe pair throws, and is the one composition uses', () => {
    it('throws where the safe one returns', () => {
        expect(() => Pet.unsafeDecode({ id: { N: '1' } })).toThrow(CodecError)
    })

    it('agrees with the safe one on success', () => {
        expect(Pet.encode(pet)).toEqual(Pet.unsafeEncode(pet))
    })

    /**
     * The reason composition throws: a nested decode returning a union would have to be unwrapped
     * at every point one codec reaches into the next, and the unwrapping is the part that gets
     * forgotten. Here the nested codec's failure still arrives intact.
     */
    it('lets a nested failure reach the boundary unchanged', () => {
        const Outer = object({
            inner: object({ note: string }),
        }).item
        const decoded = Outer.decode({ inner: { M: { note: { N: '1' } } } })
        if (!isError(decoded)) return expect.unreachable()
        expect(decoded.path).toEqual(['inner', 'note'])
    })
})

describe('anything that is not a decoding failure still throws', () => {
    it('does not swallow a bug in a caller-supplied codec', () => {
        const broken = custom<string>({
            encode: () => {
                throw new TypeError('a bug, not a bad row')
            },
            decode: () => '',
        })
        expect(() => broken.encode('x')).toThrow(TypeError)
    })
})

describe('tableEntry has the same pair', () => {
    const Pets = tableEntry<Pet>()(
        { PK: ['TAG', 'id'] },
        {
            codec: { TAG: string('PET'), id: string, name: string },
        },
    )

    it('returns the item, or why it could not be written', () => {
        const written = Pets.toItem(pet)
        if (isError(written)) return expect.unreachable()
        expect(written.PK).toEqual({ S: 'TAG#PET#ID#p1' })

        const read = Pets.fromItem(written)
        if (isError(read)) return expect.unreachable()
        expect(read).toEqual(pet)
    })

    it('reports a bad row rather than throwing', () => {
        const read = Pets.fromItem({
            PK: { S: 'x' },
            TAG: { S: 'PET' },
            id: { S: 'p1' },
            name: { N: '7' },
        })
        expect(isError(read)).toBe(true)
        expect(Pets.unsafeToItem(pet).PK).toEqual({ S: 'TAG#PET#ID#p1' })
    })
})

/**
 * The property that makes "errors as values" mean anything.
 *
 * A codec whose implementation throws somewhere inside still *compiles* as one that returns a
 * failure — the union is in the type either way. Two did: `lazy` called the throwing pair, so a bad
 * row in a recursive entity escaped past the layers that add path segments, and `opaque` threw
 * through `encode` while claiming to return. Neither was caught by a test that only asked what the
 * value was.
 *
 * So this asks the other question: that nothing below `orThrow` throws at all.
 */
describe('the safe pair never throws, whatever is thrown at it', () => {
    const badly: readonly (readonly [string, () => unknown])[] = [
        ['string', () => string.decode({ N: '1' })],
        ['literal', () => string('A').decode({ N: '1' })],
        ['literal encode', () => string('A').encode('B' as 'A')],
        ['opaque encode', () => opaque.encode(1n)],
        ['opaque decode', () => opaque.decode({ N: '1' })],
        ['opaque nested', () => opaque.encode({ a: [{ b: 1n }] })],
        ['set', () => string.set().encode(new Set())],
        ['array', () => array(string).decode({ L: [{ N: '1' }] })],
        ['tuple', () => list(string).decode({ L: [] })],
        ['record', () => record(string).decode({ M: { k: { N: '1' } } })],
        ['map', () => object({ a: string }).decode({ M: {} })],
        ['item missing', () => object({ a: string }).encode({} as never)],
        [
            'item nested',
            () => Pet.decode({ TAG: { S: 'PET' }, id: { N: '1' } }),
        ],
        ['nullable', () => nullable(string).decode({ N: '1' })],
        [
            'refine',
            () => refine(string, (v): v is 't' => v === 't').decode({ N: '1' }),
        ],
        [
            'legacy',
            () =>
                legacy({ current: string, older: string }).decode({
                    BOOL: true,
                }),
        ],
        ['lazy', () => Tree.decode({ M: { name: { N: '1' } } })],
        [
            'lazy nested',
            () =>
                Tree.decode({
                    M: {
                        name: { S: 'a' },
                        children: { L: [{ M: { name: { N: '1' } } }] },
                    },
                }),
        ],
        ['tagged', () => Visits.decode({ type: { S: 'NOPE' } })],
        ['untagged', () => Lines.decode({ nothing: { S: 'x' } })],
    ]

    it.each(badly.map(([kind, run]) => ({ kind, run })))(
        '$kind returns the failure instead of throwing',
        ({ run }) => {
            let outcome: unknown
            expect(() => {
                outcome = run()
            }).not.toThrow()
            expect(outcome).toBeInstanceOf(CodecError)
        },
    )
})
