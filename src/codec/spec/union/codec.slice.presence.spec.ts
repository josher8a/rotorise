/**
 * A field that may be absent, against a pattern that requires its key.
 *
 * A value that omits the field lies outside the pattern, and a value that holds the field may lie
 * inside it. So the option splits into a present part and an absent part. The extraction keeps the
 * present part, with the key required, and the exclusion keeps the absent part. Each value of the
 * original decodes in exactly one of the two slices, and the decoded type of each slice admits what
 * the run time keeps.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import {
    type AnyCodec,
    type Decoded,
    discriminatedUnion,
    object,
    optional,
    product,
    string,
    undefinable,
    union,
} from '../../codec'
import { failed } from '../../result'
import { arbitraryOf, rngFrom } from '../../testing'

type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends <T>() => T extends B
    ? 1
    : 2
    ? true
    : false

/** Each value of the pool decodes in exactly one of the two slices, as the original decodes it. */
const complement = (
    original: AnyCodec,
    kept: AnyCodec,
    rejected: AnyCodec,
    n = 2000,
) => {
    let inKept = 0
    let inRejected = 0
    for (let seed = 1; seed <= n; seed++) {
        const value = arbitraryOf(original, rngFrom(seed), 3)
        const row = original.encode(value as never)
        const whole = original.decode(row as never)
        expect(failed(whole)).toBe(false)
        const a = kept.decode(row as never)
        const b = rejected.decode(row as never)
        const okA = !failed(a)
        const okB = !failed(b)
        expect([okA, okB, seed]).toSatisfy(
            ([x, y]: [boolean, boolean]) => x !== y,
        )
        if (okA) {
            inKept++
            expect(a).toEqual(whole)
        }
        if (okB) {
            inRejected++
            expect(b).toEqual(whole)
        }
    }
    return { inKept, inRejected }
}

const single = union([object({ k: string('A'), a: optional(string) })])
const wantA = object({ a: string })

describe('the extraction keeps the present part with the key required, and the exclusion keeps the absent part', () => {
    const kept = single.extract(wantA)
    const rejected = single.exclude(wantA)
    it('types each slice by what the run time keeps', () => {
        expectTypeOf<
            Equal<Decoded<typeof kept>, { readonly k: 'A'; readonly a: string }>
        >().toEqualTypeOf<true>()
        expectTypeOf<
            Equal<
                Decoded<typeof rejected>,
                { readonly k: 'A'; readonly a?: undefined }
            >
        >().toEqualTypeOf<true>()
    })
    it('decodes a row with the field into the extraction and a row without it into the exclusion', () => {
        expect(
            kept.decode({ M: { k: { S: 'A' }, a: { S: 'x' } } } as never),
        ).toEqual({
            k: 'A',
            a: 'x',
        })
        expect(failed(kept.decode({ M: { k: { S: 'A' } } } as never))).toBe(
            true,
        )
        expect(rejected.decode({ M: { k: { S: 'A' } } } as never)).toEqual({
            k: 'A',
        })
        expect(
            failed(
                rejected.decode({
                    M: { k: { S: 'A' }, a: { S: 'x' } },
                } as never),
            ),
        ).toBe(true)
    })
    it('decodes each value of the original in exactly one slice', () => {
        const got = complement(single, kept, rejected)
        expect(got.inKept).toBeGreaterThan(0)
        expect(got.inRejected).toBeGreaterThan(0)
    })
})

const mixed = union([
    object({ k: string('A'), a: optional(string) }),
    object({ k: string('B') }),
    object({ k: string('C'), a: string }),
    object({ k: string('D'), a: undefinable(string) }),
])

describe('an option without the key, an option that requires it, and an option that may hold undefined', () => {
    const kept = mixed.extract(wantA)
    const rejected = mixed.exclude(wantA)
    it('types each slice by what the run time keeps', () => {
        expectTypeOf<
            Equal<
                Decoded<typeof kept>,
                | { readonly k: 'A'; readonly a: string }
                | { readonly k: 'C'; readonly a: string }
                | { readonly k: 'D'; readonly a: string }
            >
        >().toEqualTypeOf<true>()
        expectTypeOf<
            Equal<
                Decoded<typeof rejected>,
                | { readonly k: 'A'; readonly a?: undefined }
                | { readonly k: 'B' }
                | { readonly k: 'D'; readonly a: undefined }
            >
        >().toEqualTypeOf<true>()
    })
    it('decodes each value of the original in exactly one slice', () => {
        const got = complement(mixed, kept, rejected)
        expect(got.inKept).toBeGreaterThan(0)
        expect(got.inRejected).toBeGreaterThan(0)
    })
    it('refuses a key that no option declares', () => {
        expect(() => mixed.extract(object({ zz: string }) as never)).toThrow(
            /'zz' is not a key any member declares/,
        )
        expect(() => single.extract(object({ zz: string }) as never)).toThrow(
            /'zz' is not a key any member declares/,
        )
    })
})

const dog = object({ kind: string('dog'), bark: string })
const cat = object({ kind: string('cat'), meow: string })
const nest = union([
    object({
        k: string('A'),
        pet: optional(union([dog, cat])),
        b: optional(string),
    }),
])

describe('the present part is sliced again, and two keys that may be absent split', () => {
    const p = object({ pet: object({ kind: string('dog') }), b: string })
    const kept = nest.extract(p)
    const rejected = nest.exclude(p)
    it('types each slice by what the run time keeps', () => {
        expectTypeOf<
            Equal<
                Decoded<typeof kept>,
                {
                    readonly k: 'A'
                    readonly pet: {
                        readonly kind: 'dog'
                        readonly bark: string
                    }
                    readonly b: string
                }
            >
        >().toEqualTypeOf<true>()
    })
    it('decodes each value of the original in exactly one slice', () => {
        const got = complement(nest, kept, rejected)
        expect(got.inKept).toBeGreaterThan(0)
        expect(got.inRejected).toBeGreaterThan(0)
    })
})

// a product of a supply family and a price family
const TOY = string('TOY')
const KIBBLE = string('KIBBLE')
const supplies = discriminatedUnion('supplyType', [
    object({ supplyType: KIBBLE, brand: string('ACME') }),
    object({
        supplyType: TOY,
        brand: string('ROPE', 'BALL'),
        warrantyId: optional(string),
    }),
])
const kinds = discriminatedUnion('priceType', [
    object({ priceType: string('FIXED'), value: string }),
    object({ priceType: string('BID'), expected: string }),
])
const offers = product(supplies, kinds)

describe('a product of a supply family and a price family, where one supply option may omit a key', () => {
    const p = object({ supplyType: TOY, warrantyId: string })
    it('extract and exclude', () => {
        const kept = offers.extract(p)
        const rejected = offers.exclude(p)
        expectTypeOf<
            Equal<
                Decoded<typeof kept>,
                | {
                      readonly supplyType: 'TOY'
                      readonly brand: 'ROPE' | 'BALL'
                      readonly warrantyId: string
                      readonly priceType: 'FIXED'
                      readonly value: string
                  }
                | {
                      readonly supplyType: 'TOY'
                      readonly brand: 'ROPE' | 'BALL'
                      readonly warrantyId: string
                      readonly priceType: 'BID'
                      readonly expected: string
                  }
            >
        >().toEqualTypeOf<true>()
        const got = complement(offers, kept, rejected)
        expect(got.inKept).toBeGreaterThan(0)
    })
})

describe('a union pattern splits an option at a field that may be absent', () => {
    const p = union([
        object({ supplyType: KIBBLE }),
        object({ supplyType: TOY, warrantyId: string }),
    ])
    const kept = offers.extract(p)
    const rejected = offers.exclude(p)
    it('types each slice by what the run time keeps', () => {
        type Committed =
            | {
                  readonly supplyType: 'KIBBLE'
                  readonly brand: 'ACME'
                  readonly priceType: 'FIXED'
                  readonly value: string
              }
            | {
                  readonly supplyType: 'KIBBLE'
                  readonly brand: 'ACME'
                  readonly priceType: 'BID'
                  readonly expected: string
              }
            | {
                  readonly supplyType: 'TOY'
                  readonly brand: 'ROPE' | 'BALL'
                  readonly warrantyId: string
                  readonly priceType: 'FIXED'
                  readonly value: string
              }
            | {
                  readonly supplyType: 'TOY'
                  readonly brand: 'ROPE' | 'BALL'
                  readonly warrantyId: string
                  readonly priceType: 'BID'
                  readonly expected: string
              }
        expectTypeOf<
            Equal<Decoded<typeof kept>, Committed>
        >().toEqualTypeOf<true>()
        type Absent =
            | {
                  readonly supplyType: 'TOY'
                  readonly brand: 'ROPE' | 'BALL'
                  readonly warrantyId?: undefined
                  readonly priceType: 'FIXED'
                  readonly value: string
              }
            | {
                  readonly supplyType: 'TOY'
                  readonly brand: 'ROPE' | 'BALL'
                  readonly warrantyId?: undefined
                  readonly priceType: 'BID'
                  readonly expected: string
              }
        expectTypeOf<
            Equal<Decoded<typeof rejected>, Absent>
        >().toEqualTypeOf<true>()
    })
    it('decodes each value of the original in exactly one slice', () => {
        const got = complement(offers, kept, rejected)
        expect(got.inKept).toBeGreaterThan(0)
        expect(got.inRejected).toBeGreaterThan(0)
    })
})

describe('a dissection keeps its members whole, so no member splits at presence', () => {
    const rows = {
        withId: {
            M: {
                supplyType: { S: 'TOY' },
                brand: { S: 'ROPE' },
                warrantyId: { S: 'x' },
            },
        },
        withoutId: { M: { supplyType: { S: 'TOY' }, brand: { S: 'ROPE' } } },
        kibble: {
            M: { supplyType: { S: 'KIBBLE' }, brand: { S: 'ACME' } },
        },
    }
    const decoded = (codec: AnyCodec) =>
        Object.values(rows).map((row) => !failed(codec.decode(row as never)))
    const pattern = object({ supplyType: TOY, warrantyId: string })

    it('keeps in the extraction no member that does not fit whole', () => {
        expect(decoded(supplies.extract(pattern))).toEqual([
            false,
            false,
            false,
        ])
    })
    it('keeps in the exclusion each member whole', () => {
        expect(decoded(supplies.exclude(pattern))).toEqual([true, true, true])
    })
})

describe('a pattern key that no option declares is refused in the type', () => {
    it('refuses it at the top and at depth, and accepts a key that one option declares as optional', () => {
        expect(() =>
            // @ts-expect-error no option declares 'zz'
            mixed.extract(object({ zz: string })),
        ).toThrow()
        expect(() =>
            // @ts-expect-error no option declares 'zz', at depth
            nest.extract(object({ pet: object({ zz: string }) })),
        ).toThrow()
        expect(() => single.extract(object({ a: string }))).not.toThrow()
    })
})
