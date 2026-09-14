/**
 * The product of two objects: the founding operation of the Cartesian product over codecs.
 *
 * `Body.merge` is the model's, and `typed_merge` is the corollary that makes the result derivable
 * from the two factors' own judgements. Every distribution law above this one reduces to this
 * merge, so what this file pins is the merge alone: no distribution, no variadic form, no slice.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec } from '../../codec'
import {
    boolean,
    CodecError,
    decimal,
    object,
    optional,
    product,
    string,
} from '../../codec'
import { checkRoundTrip } from '../../testing'

const Pet = object({ petId: string, name: string })
const Price = object({ price: decimal, gift: optional(boolean) })

describe('the product of two closed objects', () => {
    /**
     * **The law.** The field tables are a disjoint union and the rest policies merge, so the term
     * the product denotes is the term the merged spec denotes. Asserted against a body written by
     * hand rather than against another `product`, which would compare the operation with itself.
     */
    it('is the object of the merged spec', () => {
        expect(product(Pet, Price).def).toEqual(
            object({
                petId: string,
                name: string,
                price: decimal,
                gift: optional(boolean),
            }).def,
        )
    })

    /** `Rest.merge`: `refuse` wins, and two `drop`s give `drop`. */
    it('merges the rest policies, and refuse wins', () => {
        const dropDrop = product(object({ a: string }), object({ b: string }))
        const dropRefuse = product(
            object({ a: string }),
            object({ b: string }, 'refuse'),
        )
        const refuseRefuse = product(
            object({ a: string }, 'refuse'),
            object({ b: string }, 'refuse'),
        )
        expect(dropDrop.def).toEqual(object({ a: string, b: string }).def)
        expect(dropRefuse.def).toEqual(
            object({ a: string, b: string }, 'refuse').def,
        )
        expect(refuseRefuse.def).toEqual(
            object({ a: string, b: string }, 'refuse').def,
        )
    })

    /** The two directions agree with the merged object, which is what the term equality buys. */
    it('encodes and decodes what the merged object does', () => {
        const merged = object({
            petId: string,
            name: string,
            price: decimal,
            gift: optional(boolean),
        })
        const entity = {
            petId: 'o1',
            name: 'Rex',
            price: '10',
            gift: true,
        } as const
        expect(product(Pet, Price).item.unsafeEncode(entity)).toEqual(
            merged.item.unsafeEncode(entity),
        )
        expect(
            product(Pet, Price).item.unsafeDecode(
                merged.item.unsafeEncode(entity),
            ),
        ).toEqual(entity)
    })

    it('round-trips over generated values', () => {
        checkRoundTrip(product(Pet, Price).item, {
            count: 200,
            seed: 20260914,
        })
    })
})

describe('the declarations a product refuses', () => {
    /** A name both factors declare has no product: the merge needs the tables disjoint. */
    it('refuses a name both factors declare', () => {
        expect(() =>
            // @ts-expect-error the type refuses the pair; this asserts the runtime half
            product(object({ a: string }), object({ a: string })),
        ).toThrow(CodecError)
        // the message names the name, because that is what a caller has to change
        expect(() =>
            // @ts-expect-error the same type-level refusal
            product(object({ a: string, b: string }), object({ b: decimal })),
        ).toThrow(/'b'/)
    })

    /**
     * An open factor holds an undeclared name through a codec of its own, so the product would
     * have to hold it through both. `Rest.merge` answers `none` there and this is that refusal.
     */
    it('refuses a factor left open by a rest codec', () => {
        expect(() =>
            // @ts-expect-error the type refuses an open factor too
            product(object({ a: string }, string), object({ b: string })),
        ).toThrow(CodecError)
        expect(() =>
            // @ts-expect-error either side, and the order does not matter
            product(object({ a: string }), object({ b: string }, string)),
        ).toThrow(CodecError)
    })

    /**
     * Only an object declares a name, so only an object is a factor.
     *
     * Declared through a cast of `product` itself, as the union spec casts `union`: the type
     * refuses a non-object factor by a different clause, and what is under test here is the
     * runtime a cast or a JavaScript caller reaches.
     */
    it('refuses a factor that is not an object', () => {
        const take = product as unknown as (
            first: AnyCodec,
            second: AnyCodec,
        ) => unknown
        expect(() => take(string, object({ b: string }))).toThrow(CodecError)
        expect(() => take(object({ a: string }), string)).toThrow(CodecError)
        // and the message says what a factor has to be
        expect(() => take(string, object({ b: string }))).toThrow(
            /two object codecs/,
        )
    })
})
