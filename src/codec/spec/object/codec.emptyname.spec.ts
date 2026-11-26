/**
 * An attribute name has a character.
 *
 * DynamoDB refuses an item that holds an attribute name of no character, at the top of the item
 * and inside a map, and refuses a document path that holds one. A field of `object` is declared in
 * the code, so the declaration is refused. An open key is data, so `encode` gives a refusal at the
 * key. `decode` reads the stored names as they are, because DynamoDB never stores an empty one.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    at,
    CodecError,
    item,
    object,
    opaque,
    optional,
    string,
} from '../../codec'
import { parsePath } from '../../documentPath'
import { native } from '../../native'
import { failed } from '../../result'

const Vaccines = item(object({ petId: string }, [string, optional(string)]))
const Litter = item(object({ petId: string, litter: array(string) }))
const Kennel = item(
    object({ petId: string, vaccines: object({}, [string, optional(string)]) }),
)

describe('a field of an object has a character in its name', () => {
    it('refuses the field at construction, and names the field', () => {
        expect(() => object({ petId: string, '': string })).toThrow(CodecError)
        expect(() => object({ petId: string, '': string })).toThrow(
            /declares the field ''/,
        )
    })

    it('refuses a field of no name inside an object', () => {
        expect(() =>
            object({ petId: string, owner: object({ '': string }) }),
        ).toThrow(/declares the field ''/)
    })

    it('refuses a field of no name that an entry of a literal key declares', () => {
        expect(() => object([string(''), string])).toThrow(
            /declares the field ''/,
        )
    })

    it('admits a field with one character in its name', () => {
        expect(() => object({ petId: string, a: string })).not.toThrow()
    })
})

describe('an open key has a character in its name', () => {
    it('refuses the key at the top of the item, with the key as the place of the refusal', () => {
        const written = Vaccines.encode({ petId: 'p1', '': '2024-01-01' })
        expect(failed(written)).toBe(true)
        if (!failed(written)) return
        expect(written.path).toEqual([''])
        expect(written.reason).toMatch(/open key has no character/)
    })

    it('refuses the key inside a map, with the whole path of the refusal', () => {
        const written = Kennel.encode({
            petId: 'p1',
            vaccines: { '': '2024-01-01' },
        })
        expect(failed(written)).toBe(true)
        if (!failed(written)) return
        expect(written.path).toEqual(['vaccines', ''])
    })

    it('throws the refusal from unsafeEncode', () => {
        expect(() =>
            Vaccines.unsafeEncode({ petId: 'p1', '': '2024-01-01' }),
        ).toThrow(CodecError)
    })

    it('writes a key with one character', () => {
        expect(Vaccines.unsafeEncode({ petId: 'p1', r: '2024-01-01' })).toEqual(
            {
                petId: { S: 'p1' },
                r: { S: '2024-01-01' },
            },
        )
    })
})

describe('a document path has a character in each name', () => {
    it.each(['vaccines..rabies', 'vaccines.', '.vaccines'])(
        'refuses %s, because DynamoDB refuses an empty name in a path',
        (text) => {
            expect(() => parsePath(text)).toThrow(CodecError)
            expect(() => parsePath(text)).toThrow(/a name has a character/)
        },
    )

    it('reads the empty path as the root, and a position after a name', () => {
        expect(parsePath('')).toEqual([])
        expect(parsePath('vaccines[0]')).toEqual(['vaccines', 0])
    })

    it('refuses an empty segment of a path at an open key in the type, and at run time', () => {
        const trailing: 'vaccines.' = 'vaccines.'
        // @ts-expect-error a name has a character, so the open key does not offer the empty name
        const closing = () => at(Kennel, trailing)
        expect(closing).toThrow(/a name has a character/)
        const doubled: 'vaccines..rabies' = 'vaccines..rabies'
        // @ts-expect-error a name has a character
        const between = () => at(Kennel, doubled)
        expect(between).toThrow(/a name has a character/)
        const leading: '.vaccines' = '.vaccines'
        // @ts-expect-error a name has a character
        const opening = () => at(Kennel, leading)
        expect(opening).toThrow(/a name has a character/)
    })

    it('refuses a position that has no name after a dot, because DynamoDB refuses it', () => {
        expect(() => parsePath('litter.[0]')).toThrow(/a name has a character/)
        expect(() => parsePath('owner.litter.[0]')).toThrow(
            /a name has a character/,
        )
        const dotted: 'litter.[0]' = 'litter.[0]'
        // @ts-expect-error a part behind a dot starts with a name
        const run = () => at(Litter, dotted)
        expect(run).toThrow(/a name has a character/)
    })

    it('reads a position with no name at the start of a path, where the codec is a list', () => {
        expect(parsePath('[0]')).toEqual([0])
        expect(parsePath('litter[0]')).toEqual(['litter', 0])
        expect(() => at(array(string), '[0]')).not.toThrow()
    })

    it('admits a path at an open key with a name of one character', () => {
        expect(() => at(Kennel, 'vaccines.r')).not.toThrow()
    })
})

describe('native and opaque write a map key with a character in its name', () => {
    it.each([
        ['native', native],
        ['opaque', opaque],
    ])(
        '%s refuses the key at the top of a map, with the key as the place of the refusal',
        (_name, codec) => {
            const written = codec.encode({ petId: 'p1', '': 'v' })
            expect(failed(written)).toBe(true)
            if (!failed(written)) return
            expect(written.path).toEqual([''])
            expect(written.reason).toMatch(/no character/)
        },
    )

    it.each([
        ['native', native],
        ['opaque', opaque],
    ])(
        '%s refuses the key inside a nested map, with the whole path of the refusal',
        (_name, codec) => {
            const written = codec.encode({ vaccines: { '': '2024-01-01' } })
            expect(failed(written)).toBe(true)
            if (!failed(written)) return
            expect(written.path).toEqual(['vaccines', ''])
        },
    )

    it.each([
        ['native', native],
        ['opaque', opaque],
    ])('%s throws the refusal from unsafeEncode', (_name, codec) => {
        expect(() => codec.unsafeEncode({ '': 'v' })).toThrow(CodecError)
    })

    it.each([
        ['native', native],
        ['opaque', opaque],
    ])('%s writes a key with one character', (_name, codec) => {
        expect(codec.unsafeEncode({ r: 'v' })).toEqual({ M: { r: { S: 'v' } } })
    })

    it('native refuses the key of a Map that it writes as a map', () => {
        const written = native.encode(new Map([['', 'v']]))
        expect(failed(written)).toBe(true)
    })
})

describe('the tuple form of at has a character in each name', () => {
    it('refuses an empty name at an open key at run time, and names the segment', () => {
        // @ts-expect-error a name has a character
        const run = () => at(Kennel, ['vaccines', ''])
        expect(run).toThrow(CodecError)
        expect(run).toThrow(/segment 1 of the path is no name/)
    })

    it('refuses an empty name at the first segment', () => {
        // @ts-expect-error a name has a character
        const run = () => at(Kennel, [''])
        expect(run).toThrow(/a name has a character/)
    })

    it('admits a name of one character and a position', () => {
        expect(() => at(Kennel, ['vaccines', 'r'])).not.toThrow()
        expect(() => at(Litter, ['litter', 0])).not.toThrow()
    })
})
