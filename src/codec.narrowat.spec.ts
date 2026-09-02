/**
 * An attribute two variants store differently, and where narrowing does and does not reach.
 *
 * An entity whose `from` is an `OwnerParty` in one variant and a `StaffParty` in another puts two
 * codecs at one attribute name. Where variants disagree about how an attribute is stored, the name
 * alone does not say which codec to encode with, and `at` reports that rather than guessing.
 *
 * `when` does not settle it, and cannot: a filter is a type, and types are gone by the time anything
 * runs. It narrows what the path *is*, not which codec the path resolves to. Reaching for the
 * variant's own codec is what settles it — at the cost of a path relative to that variant.
 */
import { describe, expect, it } from 'vitest'
import {
    CodecError,
    decimal,
    discriminatedUnion,
    number,
    object,
    string,
    writes,
} from './codec'

type Op =
    | { type: 'SHIPMENT'; amount: string; note: string }
    | { type: 'COUNTER'; amount: string; note: string }

const OpCodec = discriminatedUnion('type', [
    object({ type: string('SHIPMENT'), amount: decimal, note: string }),
    object({ type: string('COUNTER'), amount: string, note: string }),
])

const Entity = object({ op: OpCodec }).item

describe('where the variants disagree', () => {
    it('is reported rather than guessed', () => {
        const ambiguous = Entity.at((p) => p.op.amount)
        expect(() => ambiguous.unsafeEncode('1.5')).toThrow(CodecError)
    })

    it('says where to go instead', () => {
        expect(() => Entity.at((p) => p.op.amount).unsafeEncode('1.5')).toThrow(
            /Reach for the variant you mean — `variant\(\.\.\.\)` is an item codec with its own `at`/,
        )
    })

    it('is settled by the variant codec, with a path relative to it', () => {
        const asNumber = OpCodec.item.variant('SHIPMENT').at((p) => p.amount)
        const asString = OpCodec.item.variant('COUNTER').at((p) => p.amount)

        expect(asNumber.unsafeEncode('1.5')).toEqual({ N: '1.5' })
        expect(asString.unsafeEncode('1.5')).toEqual({ S: '1.5' })
        // relative, because the variant codec does not know where it was reached from
        expect(asNumber.path()).toBe('amount')
    })

    /**
     * And it says nothing about *what* is there, because there is no single thing. This used to be
     * a `CodecDef` kind — a definition, in a language of codec definitions, for something that was
     * not a codec — so every reader of a definition had to carry a case for it.
     */
    it('carries no definition, because there is no one codec to describe', () => {
        const ambiguous = Entity.at((p) => p.op.amount)
        expect(ambiguous.def).toBeUndefined()
        expect(writes(ambiguous)).toBeUndefined()
        // the path half is untouched, which is what `at` is most often for
        expect(ambiguous.path()).toBe('op.amount')
    })

    it('is not settled by narrowing the path, and does not pretend to be', () => {
        // the filter narrows the type; the codec walker never sees it
        const narrowed = Entity.at(
            (p) => p.op.when<{ type: 'COUNTER' }>().amount,
        )
        expect(narrowed.path()).toBe('op.amount')
        expect(() => narrowed.unsafeEncode('1.5')).toThrow(CodecError)
    })
})

describe('where they agree, or only one declares it', () => {
    it('resolves an attribute the variants store the same way', () => {
        expect(Entity.at((p) => p.op.note).unsafeEncode('hello')).toEqual({
            S: 'hello',
        })
    })

    it('resolves an attribute only one variant has', () => {
        type Mixed = { tag: 'A'; only: number } | { tag: 'B'; shared: string }
        const M = object({
            m: discriminatedUnion('tag', [
                object({ tag: string('A'), only: number }),
                object({ tag: string('B'), shared: string }),
            ]),
        }).item
        expect(M.at((p) => p.m.only).unsafeEncode(7)).toEqual({ N: '7' })
    })
})
