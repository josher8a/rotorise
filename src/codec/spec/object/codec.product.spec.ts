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
    array,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    fallback,
    never,
    nullable,
    object,
    optional,
    product,
    rest,
    string,
    tuple,
    undefinable,
    union,
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
            /an object codec or a `union` of object codecs/,
        )
    })
})

describe('the product distributes over a union', () => {
    const Kind = union([object({ a: string }), object({ b: boolean })])
    const Tail = object({ n: decimal })

    /**
     * **The distribution law.** A product over a union of objects is the union of the merges,
     * and nothing is nested: the result is one flat `union`, built through `union` itself so
     * `Collides` and `separable` run over the products rather than over the factors.
     */
    it('is the union of the merges, flat', () => {
        expect(product(Kind, Tail).def).toEqual(
            union([
                object({ a: string, n: decimal }),
                object({ b: boolean, n: decimal }),
            ]).def,
        )
    })

    /**
     * **The order is the model's `flatMap` order**: outer over the first factor's options, inner
     * over the second. Asserted as a term against a union written out in that order, which is
     * what pins it — a different order is a different term.
     */
    it('takes n·m merges in flatMap order, outer first', () => {
        const Other = union([object({ n: decimal }), object({ m: boolean })])
        expect(product(Kind, Other).def).toEqual(
            union([
                object({ a: string, n: decimal }),
                object({ a: string, m: boolean }),
                object({ b: boolean, n: decimal }),
                object({ b: boolean, m: boolean }),
            ]).def,
        )
    })

    it('round-trips through whichever merge the names choose', () => {
        const P = product(Kind, Tail)
        expect(P.unsafeDecode(P.unsafeEncode({ a: 'x', n: '1' }))).toEqual({
            a: 'x',
            n: '1',
        })
        expect(P.unsafeDecode(P.unsafeEncode({ b: true, n: '2' }))).toEqual({
            b: true,
            n: '2',
        })
    })

    /**
     * **(D) is inherited, and it is a theorem rather than a check.**
     *
     * A collision between two merges reduces to a collision inside one factor. Names are disjoint
     * across factors, so `req(Aᵢ ∪ Cⱼ) ⊆ decl(Aₖ ∪ C_l)` splits into `req(Aᵢ) ⊆ decl(Aₖ)` and
     * `req(Cⱼ) ⊆ decl(C_l)` — and both directions of that are exactly `Collides` at one factor,
     * which that factor's own `union` already refused.
     *
     * So the collision check `product` hands to {@link union} never fires on valid factors. It is
     * kept because the products go through `union` rather than around it, which is what makes the
     * claim checkable at all; this test is the claim.
     */
    it('never produces two merges that collide, whatever the factors are', () => {
        const lefts = [
            union([object({ a: string }), object({ b: boolean })]),
            union([
                object({ a: string, p: optional(string) }),
                object({ b: boolean }),
            ]),
            union([object({ a: string }), object({ b: boolean, q: decimal })]),
        ]
        const rights = [
            union([object({ n: decimal }), object({ m: boolean })]),
            union([
                object({ n: decimal, r: optional(string) }),
                object({ m: boolean }),
            ]),
        ]
        for (const left of lefts) {
            for (const right of rights) {
                expect(() => product(left, right)).not.toThrow()
            }
        }
    })
})

describe('the variadic product', () => {
    /** The fold is left, and `merge_assoc` on `fields` and `rest` is why the other nesting agrees. */
    it('folds left, and both nestings give the same term', () => {
        const a = object({ a: string })
        const b = object({ b: boolean })
        const c = object({ c: decimal })
        expect(product(a, b, c).def).toEqual(product(product(a, b), c).def)
        expect(product(a, b, c).def).toEqual(product(a, product(b, c)).def)
        expect(product(a, b, c).def).toEqual(
            object({ a: string, b: boolean, c: decimal }).def,
        )
    })

    it('refuses fewer than two factors', () => {
        const take = product as unknown as (...f: readonly unknown[]) => unknown
        expect(() => take(object({ a: string }))).toThrow(CodecError)
    })
})

describe('the factors a product refuses until the owner rules', () => {
    /**
     * **A slot nothing fills makes the term hold no value**, and the constructor refuses it.
     *
     * A slot is a position a value must fill: a fixed element of a tuple, and a `req` or
     * `fallback` field. `never` already names the term that holds nothing, so a second spelling
     * for it is a declaration that looks like a schema and refuses every entity.
     */
    it('refuses a slot declared at never, at the constructor that holds it', () => {
        // @ts-expect-error the type refuses it too; this asserts the runtime half
        expect(() => object({ a: string, dead: never })).toThrow(
            /holds no value/,
        )
        // @ts-expect-error a fixed position of a tuple is a slot
        expect(() => tuple(never, string)).toThrow(/nothing fills it/)
        // …and a `never` tail is a tail that admits nothing past the fixed part. The runtime
        // alone refuses this one: `RestCodec.rest` is typed `AttributeCodec<T, A>`, which erases
        // the narrowed `def` that the fixed positions are matched on
        expect(() => tuple(string, rest(never))).toThrow(/nothing fills it/)
    })

    /**
     * **A mark that lets the value be absent makes the name a non-slot**, so the object still
     * holds something and the declaration stands.
     *
     * `optional` and `undefinable` declare a key that can never be present, which is a redundant
     * declaration rather than an impossible one. `nullable(never)` is different and is `null`
     * alone: the field stays `req`, and the one value it holds is the null.
     */
    it('declares a name at never under a mark that admits absence', () => {
        const Opt = object({ a: string, gone: optional(never) }).item
        expect(Opt.unsafeEncode({ a: 'q' })).toEqual({ a: { S: 'q' } })

        // `undefinable` keeps the key in the entity and lets the value be `undefined`, so over
        // `never` the key is required and `undefined` is the only value it can take
        const Und = object({ a: string, gone: undefinable(never) }).item
        expect(Und.unsafeEncode({ a: 'q', gone: undefined })).toEqual({
            a: { S: 'q' },
        })

        // `nullable` holds the null and nothing else, and the name stays required
        const Nul = object({ a: string, gone: nullable(never) }).item
        expect(Nul.unsafeEncode({ a: 'q', gone: null })).toEqual({
            a: { S: 'q' },
            gone: { NULL: true },
        })
        expect(() => Nul.unsafeEncode({ a: 'q' } as never)).toThrow(CodecError)
    })

    /**
     * **`fallback` at `never` is refused twice, by two different rules.**
     *
     * The type reaches it through the slot gate: a `fallback` name is always written. The runtime
     * never gets that far, because `fallback`'s own older rule refuses a stand-in that the codec
     * it stands in for cannot write, and `never` writes nothing.
     */
    it('refuses a fallback at never, at the type by the slot and at the runtime by the stand-in', () => {
        expect(() =>
            // @ts-expect-error the slot gate refuses it at the type
            object({ a: string, gone: fallback(never as never, 'v') }),
        ).toThrow(/stand-in must be a value/)
    })

    /** `array` and `record` are not slots: both admit their empty case, and that is a value. */
    it('declares an array of never, which holds the empty list', () => {
        const Empty = array(never)
        expect(Empty.unsafeDecode(Empty.unsafeEncode([]))).toEqual([])
    })

    /**
     * **(D) fails at a product against a factor that holds nothing.** Every merge would hold
     * nothing too, and two empty held sets are comparable in both directions, so no value could
     * select between the results. `not_subset_prodOn` carries that hypothesis.
     */
    it('refuses never as a factor', () => {
        // the type refuses it by a clause of its own: without one the open-factor clause fired
        // and told the caller to close a rest policy `never` does not have
        // @ts-expect-error the clause under test
        expect(() => product(never, object({ n: decimal }))).toThrow(
            /holds no value/,
        )
        // @ts-expect-error and either position
        expect(() => product(object({ n: decimal }), never)).toThrow(
            /holds no value/,
        )
    })

    /**
     * A `dunion` chooses a variant by a tag and a `union` by names, so one product of the two
     * would need a term carrying both selection rules. The owner has not ruled on that
     * constructor, and the message says so rather than guessing.
     */
    it('refuses a discriminatedUnion factor, naming the pending ruling', () => {
        const Tagged = discriminatedUnion('kind', [
            object({ kind: string('a'), x: string }),
            object({ kind: string('b'), y: boolean }),
        ]) as never
        expect(() => product(Tagged, object({ n: decimal }))).toThrow(
            CodecError,
        )
        expect(() => product(Tagged, object({ n: decimal }))).toThrow(
            /the owner has not made/,
        )
    })
})
