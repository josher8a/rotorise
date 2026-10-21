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
            narrow(at(Adoption, ['pay']), { tender: string('CARD') }),
            ['card', 'last4'],
        )
        const direct = at(
            narrow(at(Adoption, ['pay']), { tender: string('CARD') }),
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
