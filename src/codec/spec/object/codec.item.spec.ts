/**
 * **`item` is the one reader of the whole-item reading of a codec.** An object codec, a union of
 * objects, a tagged union and a dissection each keep the reading, and `item` gives the reading
 * back. Each reading carries `itemMark`, and no codec carries it.
 */
import { describe, expect, it } from 'vitest'
import {
    discriminatedUnion,
    item,
    itemMark,
    mdunion,
    number,
    object,
    string,
    union,
} from '../../codec'

const cat = object({ kind: string('cat'), lives: number })
const dog = object({ kind: string('dog'), good: number })
const sized = [
    object({ kind: string('cat'), size: string('S'), lives: number }),
    object({ kind: string('cat'), size: string('L'), lives: number }),
] as const

const readings = {
    object: item(cat),
    union: item(union([cat, dog])),
    tagged: item(discriminatedUnion('kind', [cat, dog])),
    dissection: item(mdunion(['kind', 'size'], sized)),
} as const

describe('the marker of a whole-item reading', () => {
    it.each(Object.entries(readings))(
        'marks the reading of %s, so a root is told from a codec by the marker and not by `spec`',
        (_, reading) => {
            expect(itemMark in reading).toBe(true)
        },
    )

    it('is carried by no codec, although an object codec declares a `spec` too', () => {
        for (const codec of [
            cat,
            union([cat, dog]),
            discriminatedUnion('kind', [cat, dog]),
            mdunion(['kind', 'size'], sized),
        ]) {
            expect(itemMark in codec).toBe(false)
        }
        expect('spec' in cat).toBe(true)
    })
})

describe('the reading of a union', () => {
    it('is the reading that the union kept, and a spread copy keeps it', () => {
        const tagged = discriminatedUnion('kind', [cat, dog])
        expect(item({ ...tagged })).toBe(item(tagged))
        const either = union([cat, dog])
        expect(item({ ...either })).toBe(item(either))
    })

    it('writes the item of the option that the value selects, without the top-level map', () => {
        expect(readings.tagged.unsafeEncode({ kind: 'dog', good: 2 })).toEqual({
            kind: { S: 'dog' },
            good: { N: '2' },
        })
    })

    it('keeps the tag as the discriminator, and the specs of the options as a list', () => {
        expect(readings.tagged.discriminator).toBe('kind')
        expect(readings.dissection.keys).toEqual(['kind', 'size'])
        expect(readings.union.spec).toHaveLength(2)
    })

    it('has a message for a type and no members where the union can hold an attribute that is not a map', () => {
        const either = union([cat, string])
        // @ts-expect-error the union can hold an `S`, so there is no item to read
        const write = item(either).unsafeEncode
        expect(write).toBeDefined()
    })
})
