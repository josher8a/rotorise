/**
 * `discriminatedUnion(d, options)` and `mdunion([d], options)` are one codec.
 *
 * **The delegation is the first half of this and the stronger half.** `discriminatedUnion` is
 * `mdunion` at a one-element key set and holds no code of its own, so every one-key assertion in
 * every other spec already runs through `mdunion`'s builder: there is one implementation rather
 * than two that agree.
 *
 * What that leaves is the caller's own half — that writing the other spelling changes nothing a
 * caller can observe. That is what this file pins: the same term, the same reading on both halves,
 * the same `spec`, `discriminator` and patch, and the same *type* in both directions.
 */
import { describe, expect, it } from 'vitest'
import type { Itemable } from '../../codec'
import {
    decimal,
    discriminatedUnion,
    item,
    mdunion,
    number,
    object,
    optional,
    string,
} from '../../codec'
import type { Term } from '../../term'

/** One declaration per shape the one-key specs use: strings, a numeral, and an optional field. */
const cases = [
    {
        name: 'string tags',
        d: 'type',
        options: [
            object({ type: string('CHECKUP'), petId: string, vetId: string }),
            object({ type: string('SHOT'), petId: string, vaccine: string }),
        ],
        values: [
            { type: 'CHECKUP', petId: 'p1', vetId: 'v1' },
            { type: 'SHOT', petId: 'p1', vaccine: 'rabies' },
        ],
    },
    {
        name: 'a decimal tag',
        d: 'code',
        options: [
            object({ code: decimal('1'), a: string }),
            object({ code: decimal('2'), b: string }),
        ],
        values: [
            { code: '1', a: 'x' },
            { code: '2', b: 'y' },
        ],
    },
    {
        name: 'a numeric tag',
        d: 'code',
        options: [
            object({ code: number(1), a: string }),
            object({ code: number(2), b: string }),
        ],
        values: [
            { code: 1, a: 'x' },
            { code: 2, b: 'y' },
        ],
    },
    {
        name: 'an optional field inside a variant',
        d: 'type',
        options: [
            object({ type: string('A'), a: string, note: optional(string) }),
            object({ type: string('B'), b: string }),
        ],
        values: [
            { type: 'A', a: 'x' },
            { type: 'A', a: 'x', note: 'n' },
            { type: 'B', b: 'y' },
        ],
    },
] as const

/**
 * The table's declarations differ in shape, so the loop reads both codecs through one structural
 * type. The *precise* type identity is the claim of the last test in this file, where the two calls
 * are written out and `tsc` checks each against the other.
 */
type Swappable = {
    readonly def: Term
    readonly encode: (value: never) => unknown
    readonly decode: (attribute: never) => unknown
    readonly unsafeEncode: (value: never) => never
} & Itemable<{
    readonly encode: (item: never) => unknown
    readonly encodePartial: (patch: never) => unknown
    readonly discriminator: string
    readonly spec: Record<string, unknown>
}>

describe.each(cases)('$name', ({ d, options, values }) => {
    const one = discriminatedUnion(
        d as never,
        options as never,
    ) as unknown as Swappable
    const many = mdunion([d] as never, options as never) as unknown as Swappable

    /** The term is what every other stratum reads, so two spellings of one term is the claim. */
    it('builds the same term', () => {
        expect(many.def).toEqual(one.def)
    })

    it('writes and reads every value the same way, on both halves', () => {
        for (const value of values) {
            expect(many.encode(value as never)).toEqual(
                one.encode(value as never),
            )
            const written = one.unsafeEncode(value as never)
            expect(many.decode(written)).toEqual(one.decode(written))
            expect(item(many).encode(value as never)).toEqual(
                item(one).encode(value as never),
            )
        }
    })

    it('answers the same for a value no variant carries', () => {
        const stray = { [d]: 'nothing at all' }
        expect(String(item(many).encode(stray as never))).toBe(
            String(item(one).encode(stray as never)),
        )
    })

    it('carries the same discriminator, and the same spec of each variant at each tag', () => {
        expect(item(many).discriminator).toBe(item(one).discriminator)
        expect(Object.keys(item(many).spec)).toEqual(
            Object.keys(item(one).spec),
        )
        expect(item(many).spec).toEqual(item(one).spec)
    })

    it('encodes a patch the same way', () => {
        for (const value of values) {
            const patch = { [d]: (value as Record<string, unknown>)[d] }
            expect(item(many).encodePartial(patch as never)).toEqual(
                item(one).encodePartial(patch as never),
            )
        }
    })
})

/**
 * **The swap is a type fact, not only a runtime one.**
 *
 * `mdunion` at a one-element key set resolves to the type `discriminatedUnion` returns, so each is
 * assignable to the other. A caller replacing one call with the other rewrites no annotation, and
 * `tsc` is what checks this: the two bindings below are the assertion.
 */
describe('the two spellings have one type', () => {
    it('is assignable in both directions', () => {
        const options = [
            object({ type: string('CHECKUP'), petId: string }),
            object({ type: string('SHOT'), vaccine: string }),
        ] as const
        const one = discriminatedUnion('type', options)
        const many = mdunion(['type'], options)

        const there: typeof one = many
        const back: typeof many = one
        expect(there.def).toEqual(back.def)
    })
})
