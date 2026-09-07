/**
 * Reading what a table already holds.
 *
 * A table holds every shape it has ever held. The hand-written reconciliation is
 * `holding: item.holding ?? 'STORE_V1'` at every read site, which is once per place to forget. Two
 * things are going on there and they are worth keeping apart: an attribute that is *absent*, and
 * an attribute written in an encoding that is no longer the current one.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap, AttributeValue } from '../../attribute'
import {
    andThen,
    binary,
    CodecError,
    custom,
    decimal,
    fallback,
    legacy,
    object,
    string,
} from '../../codec'
import { checkMembersStable, checkRoundTrip } from '../../testing'

type Listing = {
    id: string
    /** added later; older rows have no such attribute */
    holding: 'STORE_V1' | 'STORE_V2'
    /** added later too */
    vendorId: 'PICKUP' | 'ACME'
    /** was written as a number for a while, and is a decimal string now */
    rate: string
}

const Listing = object({
    id: string,
    holding: fallback(string('STORE_V1', 'STORE_V2'), 'STORE_V1' as const),
    vendorId: fallback(string('PICKUP', 'ACME'), 'PICKUP' as const),
    rate: legacy({ current: decimal, older: string }),
}).item

/**
 * An older encoding whose *held* type is not the current one, and a table that has held three.
 *
 * Two things at once. `older` asks for a reader and not a codec, because digits stored as `B` by a
 * migration nobody finished read back as a `Uint8Array` rather than the `string` `decimal` holds — and
 * converting that with `held` would mean writing an encode path `legacy` never calls, since it writes
 * `current` and only `current`.
 *
 * And it takes *one* older encoding, so three encodings are two of these nested — `legacy` is itself
 * a reader. Not a union: a union needs its options to read back as different types so a value says
 * which it is, and every encoding of one attribute reads back as the same type by definition.
 */
describe('an older encoding held as something else', () => {
    const decoder = new TextDecoder()
    const Priced = object({
        id: string,
        price: legacy({
            current: decimal,
            older: legacy({
                current: string,
                older: {
                    decode: (at: AttributeValue) =>
                        andThen(binary.decode(at), (bytes) =>
                            decoder.decode(bytes),
                        ),
                },
            }),
        }),
    }).item

    it('reads the current encoding', () => {
        expect(
            Priced.unsafeDecode({ id: { S: 'p' }, price: { N: '1.5' } }).price,
        ).toBe('1.5')
    })

    it('reads an older one of the same held type', () => {
        expect(
            Priced.unsafeDecode({ id: { S: 'p' }, price: { S: '1.5' } }).price,
        ).toBe('1.5')
    })

    it('and one that had to be converted to reach it', () => {
        expect(
            Priced.unsafeDecode({
                id: { S: 'p' },
                price: { B: new TextEncoder().encode('1.5') },
            }).price,
        ).toBe('1.5')
    })

    it('writes only the current encoding, whichever it read', () => {
        const fromBytes = Priced.unsafeDecode({
            id: { S: 'p' },
            price: { B: new TextEncoder().encode('1.5') },
        })
        expect(Priced.unsafeEncode(fromBytes).price).toEqual({ N: '1.5' })
    })

    it('and still refuses an attribute no encoding reads', () => {
        expect(() =>
            Priced.unsafeDecode({ id: { S: 'p' }, price: { BOOL: true } }),
        ).toThrow(CodecError)
    })
})

describe('an attribute the row does not have', () => {
    it('reads as the value the entity says it has', () => {
        const old: AttributeMap = { id: { S: 'o1' }, rate: { N: '1.5' } }
        expect(Listing.unsafeDecode(old)).toEqual({
            id: 'o1',
            holding: 'STORE_V1',
            vendorId: 'PICKUP',
            rate: '1.5',
        })
    })

    it('does not stand in for one that is there', () => {
        const stored: AttributeMap = {
            id: { S: 'o1' },
            holding: { S: 'STORE_V2' },
            vendorId: { S: 'ACME' },
            rate: { N: '1.5' },
        }
        expect(Listing.unsafeDecode(stored).holding).toBe('STORE_V2')
        expect(Listing.unsafeDecode(stored).vendorId).toBe('ACME')
    })

    it('is written every time, so a row read once stops being old', () => {
        const old: AttributeMap = { id: { S: 'o1' }, rate: { N: '1.5' } }
        expect(Listing.unsafeEncode(Listing.unsafeDecode(old)).holding).toEqual(
            {
                S: 'STORE_V1',
            },
        )
    })

    it('is not the same as optional, which says the entity may lack it', () => {
        // the entity type says `holding` is always there; only the data may not have it
        const back: Listing = Listing.unsafeDecode({
            id: { S: 'o1' },
            rate: { N: '1' },
        })
        expect(back.holding).toBeDefined()
    })

    /**
     * **A copy per read, so a mutable stand-in cannot be shared between entities.**
     *
     * The declaration holds one value — that is what makes §3 `(fallback)`'s premise checkable
     * where the declaration is, rather than on whichever read reaches it first — and each read
     * that needs one gets a `structuredClone`. Both halves matter and this asserts both: the
     * value is right, and it is not the *same* value twice.
     *
     * The failure this pins is a caller mutating what they decoded. It shipped once as the
     * opposite behaviour and the two assertions below were `toEqual(['x'])` and `toBe(a.tags)`.
     */
    it('is a copy per read, not one shared value', () => {
        const C = object({
            id: string,
            tags: fallback({ ...listOfStrings }, []),
        }).item
        const a = C.unsafeDecode({ id: { S: 'a' } })
        const b = C.unsafeDecode({ id: { S: 'b' } })
        a.tags.push('x')
        expect(b.tags).toEqual([])
        expect(b.tags).not.toBe(a.tags)
    })

    /** A primitive is handed over as it is: there is nothing to copy and nothing to leak. */
    it('does not copy a primitive stand-in', () => {
        const C = object({ id: string, tier: fallback(string, 'FREE') }).item
        expect(C.unsafeDecode({ id: { S: 'a' } }).tier).toBe('FREE')
    })

    /**
     * **And the one value that cannot be copied is shared, rather than throwing on a read.**
     *
     * `structuredClone` refuses anything holding a function. No declared codec admits such a
     * value — a stand-in comes from the value language, and all of that clones — but `custom`'s
     * admission asks the caller's own pair, so a hand-written codec can admit one. The
     * cloneability is settled at the declaration, so this is a shared stand-in and not a
     * `DataCloneError` arriving out of a `decode` months later.
     */
    it('shares a stand-in structuredClone refuses, rather than failing the read', () => {
        type Holder = { tag: string; run: () => number }
        const holding = custom<Holder>({
            encode: (value) => ({ S: value.tag }) as never,
            decode: () => ({ tag: 'x', run: () => 1 }),
        })
        const stand: Holder = { tag: 'x', run: () => 1 }
        expect(() => structuredClone(stand)).toThrow()

        const C = object({ id: string, h: fallback(holding, stand) }).item
        const a = C.unsafeDecode({ id: { S: 'a' } })
        const b = C.unsafeDecode({ id: { S: 'b' } })
        expect(a.h).toBe(b.h)
    })
})

describe('an attribute written in an older encoding', () => {
    it('reads the current one', () => {
        expect(
            Listing.unsafeDecode(listingWith({ rate: { N: '1.5' } })).rate,
        ).toBe('1.5')
    })

    it('reads the older one too', () => {
        expect(
            Listing.unsafeDecode(listingWith({ rate: { S: '1.5' } })).rate,
        ).toBe('1.5')
    })

    it('writes only the current one', () => {
        const fromOld = Listing.unsafeDecode(
            listingWith({ rate: { S: '1.5' } }),
        )
        expect(Listing.unsafeEncode(fromOld).rate).toEqual({ N: '1.5' })
    })

    /**
     * **Pins wording no law has, deliberately.** The refusal is asserted as a `CodecError` beside
     * it; what the regex adds is the diagnostic, which is this test's subject. Here it is that the refusal
     * says *how many* encodings were tried, which is what tells a caller the migration ran at all
     * rather than the current reader having failed alone.
     */
    it('reports when no encoding can read it', () => {
        expect(() =>
            Listing.unsafeDecode(listingWith({ rate: { BOOL: true } })),
        ).toThrow(CodecError)
        expect(() =>
            Listing.unsafeDecode(listingWith({ rate: { BOOL: true } })),
        ).toThrow(
            /no encoding could read this attribute; tried the current one and one older/,
        )
    })

    it('keeps the round-trip law, because it only ever writes one shape', () => {
        checkRoundTrip(Listing, { count: 200, seed: 20260826 })
    })

    it('cannot be got backwards, because the roles are named', () => {
        // the whole point of the shape: `current` is the encoding the entity is in now
        const toNumber = legacy({ current: decimal, older: string })
        const toString = legacy({ current: string, older: decimal })

        expect(toNumber.unsafeDecode({ S: '1.5' })).toBe('1.5')
        expect(toNumber.unsafeEncode('1.5')).toEqual({ N: '1.5' })

        expect(toString.unsafeDecode({ N: '1.5' })).toBe('1.5')
        expect(toString.unsafeEncode('1.5')).toEqual({ S: '1.5' })
    })

    it('deliberately does not keep the member stable — that is the migration', () => {
        expect(() =>
            checkMembersStable(Listing, [listingWith({ rate: { S: '1.5' } })]),
        ).toThrow(CodecError)
    })
})

/** A hand-built codec — `custom` derives the safe pair from the throwing one. */
const listOfStrings = custom<string[]>({
    encode: (value) => ({ L: value.map((v) => ({ S: v })) }) as never,
    decode: () => [] as string[],
})

function listingWith(extra: AttributeMap): AttributeMap {
    return {
        id: { S: 'o1' },
        holding: { S: 'STORE_V1' },
        vendorId: { S: 'PICKUP' },
        ...extra,
    }
}
