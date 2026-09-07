/**
 * **The nesting bound, at the two codecs that walk data nobody declared.**
 *
 * `docs/dynamo-datatypes.md:130` allows document types nested up to 32 levels. Nothing in this
 * library checked it, so `opaque` and `native` would encode a 100-level document without complaint
 * and DynamoDB would reject the row on write — a C1 violation of the same shape as the
 * `⟨N, "5e-324"⟩` one that `number`, `literal` and `opaque` were each gated for. §12.3 of
 * `docs/codec-audit.md` is where it was found; the model over-approximates `𝔸` in depth and only in
 * depth, so this is the host checking what the model has not yet said.
 *
 * Two limits in that reference are deliberately *not* checked here, and the reasons differ.
 * Element count is unbounded — the reference says so twice — so a wide attribute is exact rather
 * than lucky. Item size (400 KB) sums over every attribute of a row, so it is checkable where an
 * item is assembled and nowhere inside one attribute's codec.
 */
import { describe, expect, it } from 'vitest'
import { MAX_DOCUMENT_NESTING } from '../../attribute'
import { CodecError, opaque } from '../../codec'
import { native } from '../../native'

/** `n` nested arrays around a string: `n` document levels, the string not being one. */
const nestL = (n: number): unknown => {
    let v: unknown = 'leaf'
    for (let i = 0; i < n; i++) v = [v]
    return v
}

/** The same in maps. */
const nestM = (n: number): unknown => {
    let v: unknown = 'leaf'
    for (let i = 0; i < n; i++) v = { k: v }
    return v
}

describe('the document nesting bound', () => {
    /**
     * The boundary is the one thing the reference does not settle — its sentence does not say
     * whether a scalar inside 32 lists is the 32nd level or the 33rd. These two cases pin the
     * reading actually implemented, so a disagreement with a live table shows up here as a failing
     * test naming the off-by-one rather than as a rejected write in production.
     */
    it('accepts exactly MAX_DOCUMENT_NESTING levels', () => {
        expect(opaque.encode(nestL(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
        expect(opaque.encode(nestM(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
    })

    it('refuses one more, and says which limit and by how much', () => {
        const result = opaque.encode(nestL(MAX_DOCUMENT_NESTING + 1))
        expect(result).toBeInstanceOf(CodecError)
        expect((result as CodecError).reason).toMatch(
            /nesting reaches 33 levels of list and map, and DynamoDB stores at most 32/,
        )
    })

    it('refuses in maps as well as lists', () => {
        expect(opaque.encode(nestM(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
    })

    /**
     * `native` mirrors the SDK's shape, not its willingness to write what the store refuses — the
     * same deliberate divergence as the `N` gate, and the spec asserts both sides of it.
     */
    it('applies to native, which the SDK does not check at all', () => {
        expect(native.encode(nestL(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
        expect(native.encode(nestL(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
        expect(native.encode(nestM(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
    })

    /**
     * Asked before recursing, not after. A depth that would blow the call stack has to come back as
     * a `CodecError` like every other refusal — measuring the finished attribute would crash first,
     * which is how this was found.
     */
    it('refuses a pathological depth instead of exhausting the stack', () => {
        expect(opaque.encode(nestL(20_000))).toBeInstanceOf(CodecError)
        expect(native.encode(nestL(20_000))).toBeInstanceOf(CodecError)
    })

    /** Depth is not breadth: the reference puts no limit on how many values a document holds. */
    it('leaves a wide attribute alone', () => {
        const wide = Array.from({ length: 5_000 }, (_, i) => `v${i}`)
        expect(opaque.encode(wide)).not.toBeInstanceOf(CodecError)
    })
})
