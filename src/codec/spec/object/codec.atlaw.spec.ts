/**
 * **A located codec is a codec again, and `at` continues the path of the codec.** The law:
 * `at(at(c, p), q)` is `at(c, p ++ q)`. The segments join, and the preconditions conjoin, so a
 * caller can hoist the codec at a prefix and select below it.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import {
    type AnyCodec,
    array,
    at,
    CodecError,
    discriminatedUnion,
    item,
    narrow,
    number,
    object,
    optional,
    path,
    preconditions,
    string,
} from '../../codec'
import { parsePath } from '../../scopePath'

const Leg = object({ id: string, deliveredAt: optional(string) })
const Adoption = item(
    object({
        id: string,
        shipment: object({ carrier: string, legs: array(Leg) }),
        pay: discriminatedUnion('tender', [
            object({ tender: string('CARD'), card: object({ last4: string }) }),
            object({ tender: string('CASH'), drawer: number }),
        ]),
    }),
)

/** The facts of a located codec that the law compares. */
const factsOf = (codec: AnyCodec) => ({
    path: path(codec),
    preconditions: preconditions(codec),
    written: codec.encode('x' as never),
})

describe('at continues the path of a located codec: at(at(c, p), q) is at(c, p ++ q)', () => {
    it('joins the segments of a name below a name', () => {
        const composed = at(at(Adoption, ['shipment']), ['carrier'])
        const direct = at(Adoption, ['shipment', 'carrier'])
        expect(path(composed)).toBe('shipment.carrier')
        expect(path(composed)).toBe(path(direct))
        expect(factsOf(composed)).toEqual(factsOf(direct))
        expectTypeOf(composed).toEqualTypeOf(direct)
    })

    it('joins the segments of a position and a name below a list', () => {
        const composed = at(at(Adoption, ['shipment', 'legs']), [
            1,
            'deliveredAt',
        ])
        const direct = at(Adoption, ['shipment', 'legs', 1, 'deliveredAt'])
        expect(path(composed)).toBe('shipment.legs[1].deliveredAt')
        expect(path(composed)).toBe(path(direct))
        expect(factsOf(composed)).toEqual(factsOf(direct))
        expectTypeOf(composed).toEqualTypeOf(direct)
    })

    it('conjoins the preconditions of a narrow in the prefix with the path below it', () => {
        const composed = at(
            narrow(at(Adoption, ['pay']), object({ tender: string('CARD') })),
            ['card', 'last4'],
        )
        const direct = at(
            narrow(at(Adoption, ['pay']), object({ tender: string('CARD') })),
            ['card', 'last4'],
        )
        expect(path(composed)).toBe('pay.card.last4')
        expect(path(composed)).toBe(path(direct))
        expect(factsOf(composed)).toEqual(factsOf(direct))
        expect(preconditions(composed)).toEqual([
            { segments: ['pay', 'tender'], in: [{ S: 'CARD' }] },
        ])
        expectTypeOf(composed).toEqualTypeOf(direct)
    })

    /**
     * **A spread copy of a located codec keeps its location.** The copy gives the path of the
     * original, and `at` continues the path of the original, so no copy reads as a root.
     */
    it('gives a spread copy the same path and the same composition as the original', () => {
        const located = at(Adoption, ['shipment'])
        const copy = { ...located }
        expect(path(copy)).toBe(path(located))
        const composed = at(copy, ['carrier'])
        const direct = at(Adoption, ['shipment', 'carrier'])
        expect(path(composed)).toBe('shipment.carrier')
        expect(factsOf(composed)).toEqual(factsOf(direct))
    })

    /**
     * **A spread copy of an object codec keeps its item.** The reading sits at a symbol slot, and a
     * spread copies own symbol keys, so `item` of the copy is the item of the original.
     */
    it('gives a spread copy of an object codec the item of the original', () => {
        const Whole = object({ id: string })
        const copy = { ...Whole }
        expect(item(copy)).toBe(item(Whole))
        expect(item(copy).unsafeEncode({ id: 'a' })).toEqual({ id: { S: 'a' } })
    })
})

/**
 * **A path string addresses the place that the segments address, or no string exists.** An
 * expression reads one name where the name is a letter, then letters, digits and `_`, and has no
 * escape for a name. So `parsePath` of the string equals the segments for such a name, and `path`
 * throws a `CodecError` for each other name. The tuple form of `at` still builds the place.
 */
describe('the string of a path addresses the place of its segments', () => {
    const names = {
        plain: ['name', 'owner', 'a_b', 'a1', 'Z'],
        // an expression reads a separator, a position, or the end of a path
        dot: ['owner.name', 'a.'],
        bracket: ['a[0]', 'a[', ']'],
        comma: ['a,b'],
        // an expression drops a space at an end of a name
        space: [' a', 'a '],
        // DynamoDB refuses the expression
        store: ['0', '12', '1a', '_a', 'a-b', 'a b', 'é', 'aé'],
        empty: [''],
    } as const
    const attributes = Object.fromEntries(
        Object.values(names)
            .flat()
            .map((name) => [name, string]),
    )
    const Pool = item(
        object({ ...attributes, holder: object({ ...attributes }) }),
    )
    // the pool names are data, so the segments are wide for the type of `at`
    const located = at as unknown as (
        codec: unknown,
        segments: readonly string[],
    ) => AnyCodec
    // the root is an item, so `path` gives a string
    const textOf = (codec: AnyCodec): string => {
        const text = path(codec)
        if (typeof text !== 'string') throw new Error('the root is no item')
        return text
    }

    it('gives a string whose parse is the segments, or throws a CodecError, for each class of name', () => {
        const none = {
            plain: 0,
            dot: 0,
            bracket: 0,
            comma: 0,
            space: 0,
            store: 0,
            empty: 0,
        }
        const drawn = { ...none }
        const refused = { ...none }
        for (const [kind, ofKind] of Object.entries(names)) {
            for (const name of ofKind) {
                for (const segments of [[name], ['holder', name]]) {
                    const codec = located(Pool, segments)
                    // the place is built whatever the string does
                    expect(codec.unsafeEncode('x' as never)).toEqual({
                        S: 'x',
                    })
                    const k = kind as keyof typeof drawn
                    drawn[k] += 1
                    // only `path` may refuse: a string that `parsePath` cannot read is a failure
                    let text: string | undefined
                    try {
                        text = textOf(codec)
                    } catch (cause) {
                        if (!(cause instanceof CodecError)) throw cause
                        refused[k] += 1
                    }
                    if (text !== undefined) {
                        expect(parsePath(text)).toEqual(segments)
                    }
                }
            }
        }
        for (const count of Object.values(drawn))
            expect(count).toBeGreaterThan(0)
        // a plain name has a string, and each other name has none
        expect(refused).toEqual({ ...drawn, plain: 0 })
    })

    it('refuses the string at path, and builds the place at at, for a name that holds a dot', () => {
        const flat = located(Pool, ['owner.name'])
        expect(flat.unsafeEncode('x' as never)).toEqual({ S: 'x' })
        expect(() => textOf(flat)).toThrow(CodecError)
        expect(() => textOf(flat)).toThrow(/ExpressionAttributeNames/)
        // the message gives the position of the segment, and not the name
        expect(() => textOf(flat)).not.toThrow(/owner\.name/)
    })
})
