/**
 * A refusal is a value: `decode` of a stored row that no codec writes returns a value or a
 * `CodecError`, and never throws another error.
 *
 * `checkDecodesAreWritable` rewrites each row of the codec's own write at each position, and feeds
 * the result to `decode`: a null-prototype payload, a `null` or `undefined` list entry, `{ NULL: false }`
 * and the row itself `undefined` or `null` among them. A `CodecError` is the right answer. Any other
 * throw is a reader that used a payload before it checked it, which is the class of defect that
 * `codec.boundary.spec.ts` holds one by one.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from '../../attribute'
import {
    array,
    CodecError,
    discriminatedUnion,
    held,
    item,
    nullValue,
    number,
    object,
    opaque,
    string,
} from '../../codec'
import { checkDecodesAreWritable } from '../../testing'

describe('decode returns a value or a CodecError for every mutated row', () => {
    const rows = {
        'a tag read through its payload': item(
            discriminatedUnion('species', [
                object({ species: string('cat'), name: string }),
                object({ species: string('dog'), name: string }),
            ]),
        ),
        'a literal key read through its payload': item(
            object({ species: string('cat', 'dog'), name: string }),
        ),
        'the null codec': item(object({ nothing: nullValue })),
        'a list entry that is no attribute': item(
            object({ tags: array(string) }),
        ),
        'an untyped list entry': item(object({ anything: opaque })),
        'a set of numbers': item(object({ amounts: number.set() })),
        'a row that is no map': item(object({ name: string, age: number })),
        'a conversion of a held that throws at decode': item(
            object({
                name: held(string, string, {
                    encode: (text: string) => text,
                    decode: () => {
                        throw Object.create(null)
                    },
                    // a drawn value does not go through `decode`, which throws
                    arbitrary: () => 'Rex',
                }),
            }),
        ),
    }

    for (const [name, codec] of Object.entries(rows)) {
        it(`holds for ${name}`, () => {
            expect(() =>
                checkDecodesAreWritable(codec as never, {
                    count: 60,
                    seed: 11,
                }),
            ).not.toThrow()
        })
    }
})

describe('a decode that throws another error is reported, with the mutation that made it throw', () => {
    const Pet = item(object({ name: string, age: number }))

    it('reports a TypeError at a row that is undefined', () => {
        const careless = {
            ...Pet,
            unsafeDecode: (row: AttributeMap) => {
                if (row === undefined)
                    throw new TypeError('reading a member of undefined')
                return Pet.unsafeDecode(row)
            },
        }
        expect(() => checkDecodesAreWritable(careless, { seed: 11 })).toThrow(
            /a refusal is not a value.*\n  mutation = the row is undefined\n.*\n.*\n  threw    = TypeError: reading a member of undefined/,
        )
    })

    it('accepts a CodecError at the same row', () => {
        const careful = {
            ...Pet,
            unsafeDecode: (row: AttributeMap) => {
                if (row === undefined) throw new CodecError('no row')
                return Pet.unsafeDecode(row)
            },
        }
        expect(() =>
            checkDecodesAreWritable(careful, { seed: 11 }),
        ).not.toThrow()
    })
})
