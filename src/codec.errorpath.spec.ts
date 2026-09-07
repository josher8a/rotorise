/**
 * Where a failure happened, not only what it was.
 *
 * A row is data somebody else wrote, possibly years ago. "expected attribute member 'S', found 'N'"
 * is true and useless on a thirty-attribute entity — it names the disagreement and not the place.
 * Each composite knows only its own segment, which is exactly the one the level beneath cannot
 * know, so the path is assembled as the error unwinds.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeMap } from './attribute'
import {
    array,
    CodecError,
    decimal,
    number,
    object,
    record,
    string,
    tuple,
} from './codec'

const pathOf = (run: () => unknown): readonly (string | number)[] => {
    try {
        run()
    } catch (thrown) {
        if (thrown instanceof CodecError) return thrown.path
        throw thrown
    }
    throw new Error('expected a CodecError')
}

describe('a failure carries the path it took', () => {
    it('names the attribute, at the top level', () => {
        const Pet = object({
            id: string,
            age: number,
        }).item
        expect(
            pathOf(() => Pet.unsafeDecode({ id: { S: 'p' }, age: { S: '3' } })),
        ).toEqual(['age'])
    })

    it('names the index, inside a list', () => {
        const Tags = object({ tags: array(string) }).item
        expect(
            pathOf(() =>
                Tags.unsafeDecode({ tags: { L: [{ S: 'a' }, { N: '2' }] } }),
            ),
        ).toEqual(['tags', 1])
    })

    it('names the key, inside a record', () => {
        const Prices = object({
            prices: record(decimal),
        }).item
        expect(
            pathOf(() =>
                Prices.unsafeDecode({
                    prices: { M: { dog: { N: '1' }, cat: { S: 'x' } } },
                }),
            ),
        ).toEqual(['prices', 'cat'])
    })

    it('names the position, inside a tuple', () => {
        const Pair = object({
            pair: tuple(string, number),
        }).item
        expect(
            pathOf(() =>
                Pair.unsafeDecode({ pair: { L: [{ S: 'a' }, { S: 'b' }] } }),
            ),
        ).toEqual(['pair', 1])
    })

    it('reads as a document path, which is what you paste into a query', () => {
        const Order = object({
            lines: array(object({ tender: object({ note: string }) })),
        }).item
        const broken: AttributeMap = {
            lines: {
                L: [{ M: { tender: { M: { note: { N: '7' } } } } }],
            },
        }
        // PINS A FACT NO LAW HAS, deliberately: the assembled path *is* what this file is for,
        // so the exact string is the subject rather than a stand-in for a refusal. A rewrite that
        // changed it would be changing the thing under test. It stays as it is.
        try {
            Order.unsafeDecode(broken)
            expect.unreachable()
        } catch (thrown) {
            const error = thrown as CodecError
            expect(error.message).toBe(
                "at lines[0].tender.note: expected attribute member 'S', found 'N'",
            )
            // the failure itself is still available without the path spliced in
            expect(error.reason).toBe(
                "expected attribute member 'S', found 'N'",
            )
        }
    })

    /** Encoding fails too — `literal` checks on the way out, and says where. */
    it('says where on the way out, not only on the way in', () => {
        const Row = object({
            kind: string('A'),
            id: string,
        }).item
        expect(
            pathOf(() => Row.unsafeEncode({ kind: 'B' as 'A', id: 'x' })),
        ).toEqual(['kind'])
    })

    it('is empty when the failure is the item itself', () => {
        const Pet = object({ id: string }).item
        expect(pathOf(() => Pet.unsafeDecode({}))).toEqual([])
    })
})
