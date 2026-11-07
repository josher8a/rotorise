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
    decimal,
    discriminatedUnion,
    fill,
    held,
    item,
    legacy,
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

describe('a read keeps the shape of the row, in the members, the sizes and the names', () => {
    const Amounts = item(object({ amounts: number.set() }))

    it('holds for a set of numbers, whose read refuses two numerals that read to one value', () => {
        expect(() =>
            checkDecodesAreWritable(Amounts, { count: 40, seed: 11 }),
        ).not.toThrow()
    })

    /**
     * The read of a set that maps two stored members to one is no injective image, as the model's
     * `setImage` states: `{ NS: ['0.1', '0.10000000000000001'] }` is two members, and the set that it
     * reads to holds one, so the row that the set writes is another row.
     */
    it('reports a read that merges two members of a set into one', () => {
        const merging = {
            ...Amounts,
            unsafeDecode: (row: AttributeMap) => {
                // a row that is no map reaches this double too, and `decode` refuses it as a value
                const numerals = row?.amounts?.NS
                const merged =
                    numerals === undefined
                        ? row
                        : {
                              ...row,
                              amounts: {
                                  NS: numerals.filter(
                                      (one, at) =>
                                          numerals.findIndex(
                                              (other) =>
                                                  Number(other) === Number(one),
                                          ) === at,
                                  ),
                              },
                          }
                return Amounts.unsafeDecode(merged)
            },
        }
        expect(() =>
            checkDecodesAreWritable(merging, { count: 40, seed: 11 }),
        ).toThrow(
            /a read keeps the shape of the row.*\n  mutation = a duplicate member in two numeral forms, at 'amounts'\n[^]*'amounts' was \["NS",2\] and is \["NS",1\]/,
        )
    })
})

describe('the shape of a read is held at every depth, and relaxed where the term says', () => {
    it('holds for a fill below the top level, where the row lacks the name', () => {
        const Pet = item(
            object({
                petId: string,
                home: object({ city: fill(string, 'Lima') }),
            }),
        )
        expect(() =>
            checkDecodesAreWritable(Pet, { count: 60, seed: 3 }),
        ).not.toThrow()
    })

    it('holds for a fill in an object that is the element of a list', () => {
        const Pet = item(
            object({
                petId: string,
                visits: array(object({ city: fill(string, 'Lima') })),
            }),
        )
        expect(() =>
            checkDecodesAreWritable(Pet, { count: 60, seed: 3 }),
        ).not.toThrow()
    })

    /**
     * A `legacy` below an object reads the older form and writes the current form, so the member at
     * that position changes by design. The row is built by hand: the codec writes the older form of
     * `rate` for a value that it did not read, and the current form for a value that it did.
     */
    it('holds for a legacy below an object, at a row that holds the older form', () => {
        const Real = item(
            object({
                petId: string,
                home: object({
                    rate: legacy({ current: decimal, older: string }),
                }),
            }),
        )
        const read = new WeakSet<object>()
        const double = {
            ...Real,
            unsafeEncode: (value: { readonly petId: string }) =>
                read.has(value)
                    ? Real.unsafeEncode(value as never)
                    : {
                          petId: { S: value.petId },
                          home: { M: { rate: { S: '1.5' } } },
                      },
            unsafeDecode: (row: AttributeMap) => {
                const value = Real.unsafeDecode(row)
                read.add(value)
                return value
            },
        }
        expect(() =>
            checkDecodesAreWritable(double as never, { count: 20, seed: 3 }),
        ).not.toThrow()
    })
})
