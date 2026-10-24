/**
 * A union decodes by the literals that its options pin.
 *
 * Two options that pin distinct required string literals at the same key paths never admit one
 * attribute, so the literals name the option that reads it. Every result must equal the result of
 * attempting each option in turn, and a union that pins no such paths must still decode.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import type { Option } from '../../codec'
import {
    boolean,
    decimal,
    meet,
    number,
    object,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import { altSem, optionOfTerm } from '../../denote'
import { failed } from '../../result'

type Row = { readonly M: Record<string, AttributeValue> }

const optionsOf = (codec: { readonly def: unknown }): Option[] =>
    (
        codec.def as { options: Parameters<typeof optionOfTerm>[0][] }
    ).options.map(optionOfTerm)

/** The decode of each option, counted: the count says which options a decode touched. */
const counted = (all: readonly Option[]) => {
    const calls = { n: 0 }
    const wrapped = all.map(
        (option): Option => ({
            ...option,
            codec: {
                ...option.codec,
                decode: (attribute: AttributeValue) => {
                    calls.n++
                    return option.codec.decode(attribute)
                },
            } as Option['codec'],
        }),
    )
    return { wrapped, calls }
}

/** Each valid row, each row damaged at every attribute, and each pair of rows mixed. */
const pool = (valid: readonly Row[]): Row[] => {
    const out: Row[] = [...valid]
    for (const row of valid) {
        for (const name of Object.keys(row.M)) {
            const { [name]: _dropped, ...rest } = row.M
            out.push({ M: rest }, { M: { ...row.M, [name]: { S: 'zz' } } })
        }
        out.push({ M: { ...row.M, extra: { S: 'x' } } })
    }
    for (const a of valid)
        for (const b of valid) out.push({ M: { ...a.M, ...b.M } })
    return out
}

const agreeOn = (all: readonly Option[], rows: readonly Row[]) => {
    const fast = altSem(all).pair.decode
    const slow = altSem(all, false).pair.decode
    let decoded = 0
    for (const row of rows) {
        const a = fast(row as AttributeValue)
        const b = slow(row as AttributeValue)
        if (failed(b)) {
            expect(failed(a), JSON.stringify(row)).toBe(true)
            expect((a as { message: string }).message).toBe(
                (b as { message: string }).message,
            )
        } else {
            decoded++
            expect(a, JSON.stringify(row)).toEqual(b)
        }
    }
    return decoded
}

const categories = union([
    object({ category: string('DOG'), breed: string }),
    object({ category: string('CAT'), coat: string }),
])
const listings = union([
    object({ listing: string('SALE'), price: decimal }),
    object({ listing: string('AUCTION'), startBid: decimal }),
    object({ listing: string('RENTAL'), daily: decimal }),
])
const statuses = union([
    object({ status: string('AVAILABLE') }),
    object({ status: string('ADOPTED'), adopterId: string }),
])
const cross = meet(categories, listings, statuses)

const cell = (a: number, k: number, s: number): Row => ({
    M: {
        category: { S: ['DOG', 'CAT'][a] as string },
        ...(a === 0 ? { breed: { S: 'beagle' } } : { coat: { S: 'tabby' } }),
        listing: {
            S: ['SALE', 'AUCTION', 'RENTAL'][k] as string,
        },
        ...{ [['price', 'startBid', 'daily'][k] as string]: { N: '5' } },
        status: { S: ['AVAILABLE', 'ADOPTED'][s] as string },
        ...(s === 1 ? { adopterId: { S: 'owner-1' } } : {}),
    },
})
const crossRows = [0, 1].flatMap((a) =>
    [0, 1, 2].flatMap((k) => [0, 1].map((s) => cell(a, k, s))),
)

describe('a union of options that pin distinct literals decodes by the literals', () => {
    it('gives the result and the message of attempting, on valid and damaged rows', () => {
        const rows = pool(crossRows)
        const decoded = agreeOn(optionsOf(cross), rows)
        expect(decoded).toBeGreaterThanOrEqual(crossRows.length)
        expect(rows.length).toBeGreaterThan(decoded)
    })

    it('reads only the option that the literals name', () => {
        const { wrapped, calls } = counted(optionsOf(cross))
        const last = crossRows[crossRows.length - 1] as Row
        expect(
            failed(altSem(wrapped).pair.decode(last as AttributeValue)),
        ).toBe(false)
        expect(calls.n).toBe(1)
        calls.n = 0
        altSem(wrapped, false).pair.decode(last as AttributeValue)
        expect(calls.n).toBe(crossRows.length)
    })

    it('answers a row that the named option refuses as attempting does', () => {
        const row = cell(1, 2, 1)
        const damaged: Row = { M: { ...row.M, daily: { S: 'not a number' } } }
        const fast = altSem(optionsOf(cross)).pair.decode(
            damaged as AttributeValue,
        )
        const slow = altSem(optionsOf(cross), false).pair.decode(
            damaged as AttributeValue,
        )
        expect(failed(fast)).toBe(true)
        expect((fast as { message: string }).message).toBe(
            (slow as { message: string }).message,
        )
    })
})

describe('a union whose options pin no distinct literals still decodes', () => {
    it('attempts each option where two options pin one literal', () => {
        const shared = union([
            object({ kind: string('A'), n: number }),
            object({ kind: string('A'), s: string }),
        ])
        const rows: Row[] = [
            { M: { kind: { S: 'A' }, n: { N: '1' } } },
            { M: { kind: { S: 'A' }, s: { S: 'x' } } },
        ]
        const all = optionsOf(shared)
        expect(agreeOn(all, pool(rows))).toBeGreaterThanOrEqual(2)
        const { wrapped, calls } = counted(all)
        altSem(wrapped).pair.decode(rows[1] as AttributeValue)
        expect(calls.n).toBe(2)
    })

    it('attempts each option where an option is no object', () => {
        const mixed = union([string, number])
        const all = optionsOf(mixed)
        const decode = altSem(all).pair.decode
        expect(decode({ S: 'a' })).toBe('a')
        expect(decode({ N: '1' })).toBe(1)
    })
})

describe('a union of objects that differ only under a key decodes by the path', () => {
    const makePet = (category: string, listing: string, extra: string) =>
        object({
            category: string(category),
            listing: string(listing),
            [extra]: decimal,
        } as never)
    const orders = union([
        object({ id: string, pet: makePet('DOG', 'SALE', 'price') }),
        object({ id: string, pet: makePet('DOG', 'AUCTION', 'startBid') }),
        object({
            id: string,
            pet: makePet('CAT', 'SALE', 'price'),
        }),
        object({
            id: string,
            pet: makePet('CAT', 'AUCTION', 'startBid'),
        }),
    ])
    const order = (category: string, listing: string, extra: string): Row => ({
        M: {
            id: { S: 'i' },
            pet: {
                M: {
                    category: { S: category },
                    listing: { S: listing },
                    [extra]: { N: '5' },
                },
            },
        },
    })
    const valid = [
        order('DOG', 'SALE', 'price'),
        order('DOG', 'AUCTION', 'startBid'),
        order('CAT', 'SALE', 'price'),
        order('CAT', 'AUCTION', 'startBid'),
    ]

    it('gives the result and the message of attempting', () => {
        const damaged: Row[] = valid.flatMap((row): Row[] => [
            { M: { ...row.M, pet: { S: 'oops' } } },
            { M: { ...row.M, pet: { M: { category: { S: 'DOG' } } } } },
            { M: { id: { S: 'i' } } },
        ])
        expect(
            agreeOn(optionsOf(orders), pool(valid).concat(damaged)),
        ).toBeGreaterThanOrEqual(4)
    })

    it('reads only the option that the literals under the key name', () => {
        const { wrapped, calls } = counted(optionsOf(orders))
        const last = valid[3] as Row
        expect(
            failed(altSem(wrapped).pair.decode(last as AttributeValue)),
        ).toBe(false)
        expect(calls.n).toBe(1)
    })
})

describe('a union of options that pin distinct literals of any base decodes by the literals', () => {
    const decodesAsAttempting = (
        options: readonly Parameters<typeof union>[0][number][],
        valid: readonly Row[],
    ) => {
        const all = optionsOf(union(options as never))
        expect(agreeOn(all, pool(valid))).toBeGreaterThanOrEqual(valid.length)
        const { wrapped, calls } = counted(all)
        const last = valid[valid.length - 1] as Row
        expect(
            failed(altSem(wrapped).pair.decode(last as AttributeValue)),
        ).toBe(false)
        expect(calls.n).toBe(1)
    }

    it('reads one option where the tags are numbers under an adapter', () => {
        decodesAsAttempting(
            [
                object({ v: number(1), a: string }),
                object({ v: number(2), b: string }),
                object({ v: number(3), c: string }),
            ],
            [
                { M: { v: { N: '1' }, a: { S: 'x' } } },
                { M: { v: { N: '2' }, b: { S: 'x' } } },
                { M: { v: { N: '3' }, c: { S: 'x' } } },
            ],
        )
    })

    it('reads one option where the tags are decimals', () => {
        decodesAsAttempting(
            [
                object({ v: decimal('1.5'), a: string }),
                object({ v: decimal('2'), b: string }),
            ],
            [
                { M: { v: { N: '1.5' }, a: { S: 'x' } } },
                { M: { v: { N: '2' }, b: { S: 'x' } } },
            ],
        )
    })

    it('reads one option where the tags are booleans', () => {
        decodesAsAttempting(
            [
                object({ flag: boolean(true), a: string }),
                object({ flag: boolean(false), b: string }),
            ],
            [
                { M: { flag: { BOOL: true }, a: { S: 'x' } } },
                { M: { flag: { BOOL: false }, b: { S: 'x' } } },
            ],
        )
    })

    it('keeps a string tag and a number tag of one text apart', () => {
        decodesAsAttempting(
            [
                object({ k: string('1'), a: string }),
                object({ k: number(1), b: string }),
            ],
            [
                { M: { k: { S: '1' }, a: { S: 'x' } } },
                { M: { k: { N: '1' }, b: { S: 'x' } } },
            ],
        )
    })

    it('answers a number that is no stored numeral as attempting does', () => {
        const all = optionsOf(
            union([
                object({ v: number(1), a: string }),
                object({ v: number(2), b: string }),
            ]),
        )
        const row = { M: { v: { N: '2.0' }, b: { S: 'x' } } } as Row
        const fast = altSem(all).pair.decode(row as AttributeValue)
        const slow = altSem(all, false).pair.decode(row as AttributeValue)
        expect(failed(fast)).toBe(failed(slow))
        if (failed(fast) && failed(slow))
            expect(fast.message).toBe(slow.message)
    })
})

describe('a union whose tag sits under a fallback field decodes as attempting does', () => {
    // A row that lacks the tag reads as the stand-in, so the tag is no required literal of the stored
    // view. The row must still reach the option that the stand-in names.
    const tagged = union([
        object({
            kind: withLegacyRead({ current: string('A'), whenMissing: 'A' }),
            a: string,
        }),
        object({ kind: string('B'), b: string }),
    ])
    const valid: Row[] = [
        { M: { kind: { S: 'A' }, a: { S: 'x' } } },
        { M: { kind: { S: 'B' }, b: { S: 'x' } } },
    ]

    it('gives the result and the message of attempting, on valid and damaged rows', () => {
        expect(agreeOn(optionsOf(tagged), pool(valid))).toBeGreaterThanOrEqual(
            valid.length,
        )
    })

    it('reads a row that lacks the tag as the option that the stand-in names', () => {
        const row: Row = { M: { a: { S: 'x' } } }
        expect(tagged.decode(row as AttributeValue)).toEqual({
            kind: 'A',
            a: 'x',
        })
    })
})
