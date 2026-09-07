/**
 * A custom marshaller, described in both directions.
 *
 * Two marshallers over one table, agreeing on every byte and disagreeing on how to read one of
 * them. A store that sells things keeps `N` as the digits it stored, because a price that becomes a
 * JS number stops being the price; the SDK's reads it as a `number`, widening to `bigint`. Same
 * rows, two entities — and nothing about the bytes says which reading was meant.
 *
 * Calling `native` is that difference as one branch rather than a fork, and `native.Decode` is that
 * difference as a type — so it can be written down, diffed, and tested rather than discovered.
 */
import { describe, expect, it } from 'vitest'
import type { M, N, S } from '../../attribute'
import { CodecError, failed } from '../../codec'
import { native } from '../../native'
import { checkAgainst } from '../../testing'

/** The deviation, in one line: the digits as stored, not a number. */
const exact = native({}, { readNumber: (digits) => digits })

type Sale = {
    id: string
    price: string
    tags: ReadonlySet<string>
    fee: { price: string }
}

/** What the table holds — the same for both marshallers, because they write the same bytes. */
type SaleItem = native.ItemEncode<{
    id: string
    price: number
    tags: ReadonlySet<string>
    fee: { price: number }
}>

describe('the two marshallers write the same bytes', () => {
    const stored = {
        id: 'o1',
        price: 1.5,
        tags: new Set(['a']),
        fee: { price: 0.5 },
    }

    it('byte for byte', () => {
        expect(exact.encode(stored)).toEqual(native.encode(stored))
    })

    it('and the shape they write is the one written down', () => {
        const shape: SaleItem = {
            id: { S: 'o1' },
            price: { N: '1.5' },
            tags: { SS: ['a'] },
            fee: { M: { price: { N: '0.5' } } },
        }
        expect(exact.unsafeEncode(stored)).toEqual({ M: shape })
    })
})

describe('and read them differently, which is the whole point', () => {
    const row = { M: { price: { N: '1.50' }, id: { S: 'o1' } } } as never

    it('the SDK rounds the digits into a number', () => {
        expect(native.decode(row)).toEqual({ price: 1.5, id: 'o1' })
    })

    it('the exact marshaller keeps them', () => {
        expect(exact.decode(row)).toEqual({ price: '1.50', id: 'o1' })
    })

    /** The reason: past the safe range a number is no longer the price that was stored. */
    it('and keeps them where a number could not', () => {
        const wide = { M: { price: { N: '9007199254740993' } } } as never
        expect(exact.decode(wide)).toEqual({ price: '9007199254740993' })
        expect(native.decode(wide)).toEqual({ price: 9007199254740993n })
    })
})

describe('both readings are types you can diff', () => {
    it('the SDK reads N as a number, widening past the safe range', () => {
        type Theirs = native.Decode<M<{ price: N; id: S }>>
        const read: Theirs = { price: 1.5, id: 'o1' }
        const wide: Theirs = { price: 9007199254740993n, id: 'o1' }
        expect([read, wide]).toHaveLength(2)
    })

    it('the exact marshaller reads it as the digits', () => {
        type Ours = native.Decode<M<{ price: N; id: S }>, string>
        const read: Ours = { price: '1.50', id: 'o1' }
        // @ts-expect-error a number is not what this marshaller hands back
        const wrong: Ours = { price: 1.5, id: 'o1' }
        expect([read, wrong]).toHaveLength(2)
    })

    it('descends, so a nested price is described too', () => {
        type Ours = native.ItemDecode<SaleItem, string>
        const read: Ours = {
            id: 'o1',
            price: '1.50',
            tags: new Set(['a']),
            fee: { price: '0.50' },
        }
        // the entity a repository actually works with
        const asEntity: Sale = read
        expect(asEntity.fee.price).toBe('0.50')
    })
})

describe('and the pair is testable against the marshaller in the repo', () => {
    /** Whatever a team already has, expressed as the two functions `checkAgainst` asks for. */
    const theirs = {
        marshall: (value: unknown) => ({
            v: exact.unsafeEncode(value),
        }),
        unmarshall: (item: { readonly [k: string]: unknown }) =>
            exact.unsafeDecode(item.v as never),
    }

    const holder = {
        unsafeEncode: (value: unknown) => ({ v: exact.unsafeEncode(value) }),
        unsafeDecode: (item: { readonly [k: string]: unknown }) =>
            exact.unsafeDecode(item.v as never),
        def: exact.def,
    }

    it('agrees over generated values, both directions', () => {
        expect(() =>
            checkAgainst(holder as never, theirs as never, {
                count: 200,
                seed: 20260827,
                // only what this marshaller accepts: a number past the safe range is refused by
                // both, and a sweep is about where they *differ*, not where they agree to refuse
                filter: (value) => !failed(exact.encode(value)),
            }),
        ).not.toThrow()
    })

    it('and reports where a marshaller that drifted would differ', () => {
        const drifted = {
            ...theirs,
            unmarshall: (item: { readonly [k: string]: unknown }) => {
                const read = exact.unsafeDecode(item.v as never)
                return typeof read === 'string' ? Number(read) : read
            },
        }
        expect(() =>
            checkAgainst(holder as never, drifted as never, {
                count: 200,
                seed: 1,
                filter: (value) =>
                    typeof value === 'number' && !failed(exact.encode(value)),
            }),
        ).toThrow(CodecError)
    })
})
