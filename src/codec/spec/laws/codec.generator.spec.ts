/**
 * The generator draws what a codec carries, and a failure of a law is reported as a failure of the law.
 *
 * `arbitraryOf` derives a value from the term. A `held` is read through the pair, a list stops at the
 * size bound, and a shrink goes only where the pair maps both ways.
 */
import { describe, expect, it } from 'vitest'
import { DynamoNumber } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    CodecError,
    held,
    item,
    object,
    ref,
    scope,
    string,
} from '../../codec'
import { native } from '../../native'
import {
    arbitraryOf,
    checkDecodesAreWritable,
    checkRoundTrip,
    rngFrom,
} from '../../testing'

/** A string adapter whose write refuses a long string. */
const shortOnly = () =>
    held(string, string, {
        encode: (value: string) =>
            value.length > 1 ? new CodecError('long') : value,
        decode: (value: string) => value,
    })

describe('a native marshaller of any configuration generates what it reads', () => {
    it('passes the round trip where the read gives back a DynamoNumber', () => {
        const exact = native(
            {},
            { readNumber: (digits) => DynamoNumber.from(digits) },
        )
        expect(() =>
            checkRoundTrip(item(object({ x: exact })) as never, { count: 100 }),
        ).not.toThrow()
    })

    it('passes the round trip of the default marshaller', () => {
        expect(() =>
            checkRoundTrip(item(object({ x: native })) as never, {
                count: 100,
            }),
        ).not.toThrow()
    })
})

describe('a held shrinks only through a pair that maps both ways', () => {
    it('reports the counterexample as a failure of the codec, where the write refuses the draw', () => {
        const run = () =>
            checkRoundTrip(item(object({ x: shortOnly() })) as never)
        expect(run).toThrow(CodecError)
        expect(run).toThrow(/unsafeDecode\(unsafeEncode\(x\)\) threw/)
    })
})

describe('a list stops at the size bound, so a recursion through a list ends', () => {
    const { Tree } = scope({ Tree: array(ref('Tree')) }) as unknown as {
        Tree: AnyCodec
    }
    const depth = (value: unknown): number =>
        Array.isArray(value) ? 1 + Math.max(0, ...value.map(depth)) : 0

    it('keeps the nesting of a draw within the bound, for a thousand seeds', () => {
        let deepest = 0
        for (let seed = 0; seed < 1000; seed++)
            deepest = Math.max(
                deepest,
                depth(arbitraryOf(Tree, rngFrom(seed), 4)),
            )
        expect(deepest).toBeLessThanOrEqual(5)
    })

    it('passes the round trip of an item that holds the recursion', () => {
        expect(() =>
            checkRoundTrip(item(object({ t: Tree })) as never),
        ).not.toThrow()
    })
})

describe('a value is attributed to the read of the pair by one condition', () => {
    it('reports (C) where the codec refuses a value that refine handed back as it was', () => {
        expect(() =>
            checkDecodesAreWritable(
                item(object({ x: shortOnly() })) as never,
                { refine: (value: unknown) => value } as never,
            ),
        ).toThrow(/\(C\) fails/)
    })

    it('does not report (C) where refine repaired the value into another one', () => {
        expect(() =>
            checkDecodesAreWritable(
                item(object({ x: shortOnly() })) as never,
                {
                    refine: (value: { x: string }) => ({ x: `${value.x}!` }),
                } as never,
            ),
        ).not.toThrow()
    })
})
