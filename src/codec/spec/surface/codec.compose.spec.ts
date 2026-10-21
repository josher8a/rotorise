/**
 * Composing codecs without naming every piece.
 *
 * There is one kind of codec and it writes an attribute, so a codec goes wherever an attribute codec
 * is expected and nothing has to be converted on the way in. There used to be three kinds that each
 * *were* one `M` attribute and had to say so — `fulfilment: Fulfilment.attribute` at every nesting
 * point, which also forced a `const` for every sub-shape whether or not it was worth naming.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    at,
    discriminatedUnion,
    item as itemOf,
    list,
    number,
    object,
    optional,
    path,
    string,
    union,
} from '../../codec'

type Tender = { kind: 'CASH'; code: string } | { kind: 'PET'; coat: string }
type Leg = { n: number }
type Adoption = {
    id: string
    tender: Tender
    items: readonly Leg[]
    legs: readonly [Leg, Leg]
    tags: Readonly<Record<string, Leg>>
    maybe?: { m: string }
    untagged: { a: string } | { b: number }
}

/** Every piece built where it is used. */
const Adoption = itemOf(
    object({
        id: string,
        tender: discriminatedUnion('kind', [
            object({ kind: string('CASH'), code: string }),
            object({ kind: string('PET'), coat: string }),
        ]),
        items: array(object({ n: number })),
        legs: list(object({ n: number }), object({ n: number })),
        tags: object([string, optional(object({ n: number }))]),
        maybe: optional(object({ m: string })),
        untagged: union([object({ a: string }), object({ b: number })]),
    }),
)

const adoption: Adoption = {
    id: 'q1',
    tender: { kind: 'CASH', code: 'AKC' },
    items: [{ n: 1 }],
    legs: [{ n: 1 }, { n: 2 }],
    tags: { first: { n: 3 } },
    untagged: { b: 7 },
}

describe('a codec used where an attribute codec is expected', () => {
    it('nests with nothing said about nesting', () => {
        const item = Adoption.unsafeEncode(adoption)
        expect(item.tender).toEqual({
            M: { kind: { S: 'CASH' }, code: { S: 'AKC' } },
        })
        expect(item.items).toEqual({ L: [{ M: { n: { N: '1' } } }] })
        expect(item.legs).toEqual({
            L: [{ M: { n: { N: '1' } } }, { M: { n: { N: '2' } } }],
        })
        expect(item.tags).toEqual({ M: { first: { M: { n: { N: '3' } } } } })
        expect(item.untagged).toEqual({ M: { b: { N: '7' } } })
    })

    it('round-trips, so nesting is not the only thing that survives', () => {
        expect(Adoption.unsafeDecode(Adoption.unsafeEncode(adoption))).toEqual(
            adoption,
        )
    })

    it('reaches a path through a piece that was never named', () => {
        expect(path(Adoption).tender.code.toString()).toBe('tender.code')
        expect(path(Adoption).legs.at(1).n.toString()).toBe('legs[1].n')
        expect(at(Adoption, (p) => p.legs.at(0).n).unsafeEncode(4)).toEqual({
            N: '4',
        })
    })

    it('still accepts the explicit form, which is the same codec', () => {
        const Leg = object({ n: number })
        const A = itemOf(object({ leg: Leg }))
        const B = itemOf(object({ leg: Leg }))
        expect(A.unsafeEncode({ leg: { n: 1 } })).toEqual(
            B.unsafeEncode({ leg: { n: 1 } }),
        )
    })

    it('nests inside a map, which takes them too', () => {
        const Wrapped = object({ inner: object({ n: number }) })
        expect(Wrapped.unsafeEncode({ inner: { n: 9 } })).toEqual({
            M: { inner: { M: { n: { N: '9' } } } },
        })
    })
})
