/**
 * The one place a codec is constructed.
 *
 * Its own module for one reason: it must be reachable from `native.ts`, which builds the SDK's
 * marshaller, and it must *not* be reachable from the package's public surface, which re-exports
 * `./codec` wholesale. A separate module is the only thing that gives both — an explicit export list
 * on the barrel would give it too, at the cost of naming all eighty-odd exports twice and silently
 * dropping whichever one is forgotten next.
 *
 * The types come from `./codec` and the values from `./result`, so the type-level circularity is
 * erased at build time and there is no import cycle at runtime.
 */
import type { AttributeValue } from './attribute'
import type { AttributeCodec, Rng } from './codec'
import type { Result } from './result'
import { orThrow } from './result'
import type { Term } from './term'

/**
 * What has to be said to build a codec; the rest of {@link CodecShape} follows from it.
 *
 * Spelled out rather than `Pick`ed from {@link AttributeCodec}. It is the argument type of the one
 * construction site, so it is instantiated once per codec *written*, and a `Pick & Partial<Pick>`
 * instantiates the record it selects from twice over to answer the same five fields.
 */
export type Codec<T, A extends AttributeValue> = {
    readonly encode: (value: T) => Result<A>
    readonly decode: (attribute: AttributeValue) => Result<T>
    /**
     * **A projection of the term, and not a second fact.**
     *
     * `denote` writes these two onto the codec object at `custom` and nowhere else, copying what
     * the term already carries — `custom` being the one term whose generation is the caller's to
     * state. `refine`'s lives in its `Refinement` and rides in the term the same way.
     *
     * **No library code reads them.** `arbitraryOf` and `shrinkOf` dispatch on the term alone, so
     * the fact has one path rather than two and a stray codec object cannot answer differently
     * from the term it was built from. They stay because they are on the published codec object
     * and a caller may read one — building a second `custom` from the first's generator is what
     * `codec.shrink.spec.ts` does. Removing them from the surface is a decision for the owner.
     */
    readonly arbitrary?: (rng: Rng, size: number) => T
    readonly shrink?: (value: T) => readonly T[]
    readonly def: Term
}

/**
 * A codec from the two directions that can fail, with the throwing pair derived.
 *
 * The one construction site. Every codec in this file is this shape, so the {@link orThrow} pairing
 * is written once and no constructor can end up with `unsafeEncode` disagreeing with `encode` —
 * which is a divergence nothing else would catch, since both round-trip perfectly on their own.
 */
export const codec = <T, A extends AttributeValue>({
    encode,
    decode,
    arbitrary,
    shrink,
    def,
}: Codec<T, A>): AttributeCodec<T, A> => ({
    encode,
    decode,
    unsafeEncode: (value) => orThrow(encode(value)),
    unsafeDecode: (attribute) => orThrow(decode(attribute)),
    arbitrary,
    shrink,
    def,
})
