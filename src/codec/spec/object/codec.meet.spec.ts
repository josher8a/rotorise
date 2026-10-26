/**
 * The meet of two objects: the founding operation of the lattice over codecs.
 *
 * Every distribution law above this one reduces to this merge, so what this file pins is the merge
 * alone: no distribution, no variadic form, no slice.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AnyCodec, Decoded } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    decimal,
    held,
    item,
    list,
    meet,
    never,
    nullable,
    number,
    object,
    opaque,
    optional,
    ref,
    refine,
    scope,
    spread,
    string,
    undefinable,
    union,
    withLegacyRead,
} from '../../codec'
import { failed } from '../../result'
import {
    arbitraryOf,
    checkDecodesAreWritable,
    checkRoundTrip,
    rngFrom,
} from '../../testing'

/** The definition of a codec, read through `AnyCodec` because a meet at `never` has the type `never`. */
const defOf = (codec: AnyCodec) => codec.def

const Pet = object({ petId: string, name: string })
const Price = object({ price: decimal, gift: optional(boolean) })

describe('the meet of two closed objects', () => {
    /**
     * **The law.** The field tables are a disjoint union and the rest policies merge, so the term
     * the meet denotes is the term the merged spec denotes. Asserted against a body written by
     * hand rather than against another `meet`, which would compare the operation with itself.
     */
    it('is the object of the merged spec', () => {
        expect(meet(Pet, Price).def).toEqual(
            object({
                petId: string,
                name: string,
                price: decimal,
                gift: optional(boolean),
            }).def,
        )
    })

    /** Strict objects remain strict when meet merges their bodies. */
    it('merges strict object bodies', () => {
        const leftThenRight = meet(object({ a: string }), object({ b: string }))
        const rightThenLeft = meet(object({ a: string }), object({ b: string }))
        expect(leftThenRight.def).toEqual(object({ a: string, b: string }).def)
        expect(rightThenLeft.def).toEqual(object({ a: string, b: string }).def)
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
        expect(item(meet(Pet, Price)).unsafeEncode(entity)).toEqual(
            item(merged).unsafeEncode(entity),
        )
        expect(
            item(meet(Pet, Price)).unsafeDecode(
                item(merged).unsafeEncode(entity),
            ),
        ).toEqual(entity)
    })

    it('round-trips over generated values', () => {
        checkRoundTrip(item(meet(Pet, Price)), {
            count: 200,
            seed: 20260914,
        })
    })
})

describe('the meet of two objects at a shared name', () => {
    /**
     * **A shared name holds the meet of its two fields**, as `A & B` reads it: the values that both
     * factors admit at that name. Asserted against an object written by hand.
     */
    it('meets the two fields of a name that both factors declare', () => {
        expect(
            meet(
                object({ a: string('x', 'y'), b: string }),
                object({ a: string('y', 'z'), c: boolean }),
            ).def,
        ).toEqual(object({ a: string('y'), b: string, c: boolean }).def)
        expect(meet(object({ a: string }), object({ a: string })).def).toEqual(
            object({ a: string }).def,
        )
    })

    /** A name that one factor requires is required in the meet, because the meet admits fewer values. */
    it('requires a name that one factor requires and the other leaves optional', () => {
        const expected = object({ a: string }).def
        expect(
            meet(object({ a: string }), object({ a: optional(string) })).def,
        ).toEqual(expected)
        expect(
            meet(object({ a: optional(string) }), object({ a: string })).def,
        ).toEqual(expected)
    })

    /** A shared name whose fields hold no common value leaves the object no value, so the meet is `never`. */
    it('meets at never where the fields of a shared name meet at never', () => {
        expect(
            defOf(meet(object({ a: string('x') }), object({ a: string('y') }))),
        ).toEqual(never.def)
        expect(
            defOf(
                meet(object({ a: string, b: string }), object({ b: boolean })),
            ),
        ).toEqual(never.def)
    })

    /**
     * **`optional` and `undefinable` share the absent row.** `optional` reads `{}` and
     * `{ a: undefined }` as one value, and `undefinable` reads the absent row to `{ a: undefined }`,
     * so the meet keeps the key at `undefined`, as TypeScript reads `{ a?: X } & { a: X | undefined }`.
     */
    it('meets an optional field and an undefinable field of one name at undefinable', () => {
        const expected = object({ a: undefinable(string('y')) }).def
        expect(
            meet(
                object({ a: optional(string('x', 'y')) }),
                object({ a: undefinable(string('y', 'z')) }),
            ).def,
        ).toEqual(expected)
        expect(
            meet(
                object({ a: undefinable(string('y', 'z')) }),
                object({ a: optional(string('x', 'y')) }),
            ).def,
        ).toEqual(expected)
        const both = meet(
            object({ a: optional(string) }),
            object({ a: undefinable(string) }),
        )
        expectTypeOf<Decoded<typeof both>>().toEqualTypeOf<{
            readonly a: string | undefined
        }>()
        const other = meet(
            object({ a: undefinable(string) }),
            object({ a: optional(string) }),
        )
        expectTypeOf<Decoded<typeof other>>().toEqualTypeOf<{
            readonly a: string | undefined
        }>()
        expect(both.decode({ M: {} })).toEqual({ a: undefined })
    })

    /**
     * **A `withLegacyRead` side shares no absent row with a side that admits absence.** The stand-in
     * side decodes the absent row to the stand-in, and the other side to no value, so the meet drops
     * the row and the name is required. A required side holds no absent row either.
     */
    it('requires a name that one factor reads through withLegacyRead', () => {
        const fill = object({
            a: withLegacyRead({ current: string('x', 'y'), whenMissing: 'x' }),
        })
        const expected = object({ a: string('y') }).def
        for (const other of [
            object({ a: optional(string('y', 'z')) }),
            object({ a: undefinable(string('y', 'z')) }),
            object({ a: string('y', 'z') }),
        ]) {
            expect(meet(fill, other).def).toEqual(expected)
            expect(meet(other, fill).def).toEqual(expected)
        }
        const plain = object({
            a: withLegacyRead({ current: string, whenMissing: 'x' }),
        })
        const required = meet(plain, object({ a: optional(string) }))
        expectTypeOf<Decoded<typeof required>>().toEqualTypeOf<{
            readonly a: string
        }>()
        const reversed = meet(object({ a: optional(string) }), plain)
        expectTypeOf<Decoded<typeof reversed>>().toEqualTypeOf<{
            readonly a: string
        }>()
        expect(failed(required.decode({ M: {} }))).toBe(true)
    })

    /**
     * **An open block that narrows a `withLegacyRead` field makes the field required**: the open key
     * entry is an optional slot at the block, and the absent row has no pair on both sides.
     */
    it('requires a withLegacyRead name that the open block of the other factor narrows', () => {
        const both: AnyCodec = meet(
            // @ts-expect-error the type refuses an open factor
            object({}, [string, optional(string('x', 'y'))]),
            object({
                a: withLegacyRead({ current: string, whenMissing: 'x' }),
            }),
        )
        expect(failed(both.decode({ M: { a: { S: 'y' } } }))).toBe(false)
        expect(failed(both.decode({ M: { a: { S: 'z' } } }))).toBe(true)
        expect(failed(both.decode({ M: {} }))).toBe(true)
    })

    /**
     * Two stand-ins share the absent row only where they are one value, and the host compares no
     * two stand-ins, as the model compares no two fills. The refusal names the name.
     */
    it('refuses a shared name that both factors read through withLegacyRead', () => {
        expect(() =>
            meet(
                object({
                    a: withLegacyRead({
                        current: string('x', 'y'),
                        whenMissing: 'x',
                    }),
                }),
                object({
                    a: withLegacyRead({
                        current: string('x', 'z'),
                        whenMissing: 'x',
                    }),
                }),
            ),
        ).toThrow(/'a'.*withLegacyRead.*stand-ins/)
    })

    /**
     * **An open factor meets on the alignment.** A name that one factor declares meets the open
     * block of the other factor, and the two open blocks meet. The type of `meet` still refuses an
     * open factor, because the type reads no open block.
     */
    it('meets a declared name against the open block of the other factor', () => {
        const both: AnyCodec = meet(
            // @ts-expect-error the type refuses an open factor
            object({ a: string }, [string, optional(string)]),
            object({ b: string }),
        )
        expect(
            failed(
                both.decode({
                    M: { a: { S: 'x' }, b: { S: 'y' }, c: { S: 'z' } },
                }),
            ),
        ).toBe(false)
        expect(
            failed(both.decode({ M: { a: { S: 'x' }, b: { N: '1' } } })),
        ).toBe(true)
        expect(
            failed(
                both.decode({
                    M: { a: { S: 'x' }, b: { S: 'y' }, c: { N: '1' } },
                }),
            ),
        ).toBe(true)
    })

    /**
     * **A required name that the open block of the other factor refuses empties the meet.** The
     * meet held such a name before as the other factor declared it, and the open factor refused the
     * result.
     */
    it('meets at never where a required name meets the open block of the other factor at never', () => {
        const kept: AnyCodec = meet(
            // @ts-expect-error the type refuses an open factor
            object({}, [string, optional(object({ k: string('p') }))]),
            object({ b: string('a') }),
        )
        expect(defOf(kept)).toEqual(never.def)
    })

    /**
     * **A factor of another kind meets at `never`.** No value is both an object and a string, so the
     * meet holds nothing, and a `never` codec refuses when it is used.
     */
    it('meets at never a factor that is not an object', () => {
        expect(defOf(meet(string, object({ b: string })))).toEqual(never.def)
        expect(defOf(meet(object({ a: string }), string))).toEqual(never.def)
        expect(() => item(meet(string, object({ b: string })))).toThrow(
            CodecError,
        )
    })
})

describe('the meet distributes over a union', () => {
    const Kind = union([object({ a: string }), object({ b: boolean })])
    const Tail = object({ n: decimal })

    /**
     * **The distribution law.** A meet over a union of objects is the union of the merges,
     * and nothing is nested: the result is one flat `union`, built through `union` itself so
     * `agrees` runs over the meets rather than over the factors.
     */
    it('is the union of the merges, flat', () => {
        expect(meet(Kind, Tail).def).toEqual(
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
        expect(meet(Kind, Other).def).toEqual(
            union([
                object({ a: string, n: decimal }),
                object({ a: string, m: boolean }),
                object({ b: boolean, n: decimal }),
                object({ b: boolean, m: boolean }),
            ]).def,
        )
    })

    it('round-trips through whichever merge the names choose', () => {
        const P = meet(Kind, Tail)
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
     * **(D) is inherited on disjoint names, and it is a theorem rather than a check.**
     *
     * A collision between two merges reduces to a collision inside one factor. Where the names are
     * disjoint across factors, `req(Aᵢ ∪ Cⱼ) ⊆ decl(Aₖ ∪ C_l)` splits into `req(Aᵢ) ⊆ decl(Aₖ)` and
     * `req(Cⱼ) ⊆ decl(C_l)` — and both directions of that are a collision of name intervals at one factor,
     * which that factor's own `union` already refused.
     *
     * So the collision check `meet` hands to {@link union} never fires on valid factors of disjoint
     * names. It is kept because the meets go through `union` rather than around it, which is what
     * makes the claim checkable at all; this test is the claim.
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
                expect(() => meet(left, right)).not.toThrow()
            }
        }
    })
})

describe('a factor that lies below the other is the meet', () => {
    /**
     * **The walk distributes a union only where neither factor lies below the other.** Each option
     * here meets the object at the object itself, read open, and no union holds two overlapping
     * options, so a distribution refused the pair.
     */
    it('meets an object below a union of objects at the object, with no distribution', () => {
        const all = object({ a: string, b: string, c: string })
        const either = union([object({ a: string }), object({ c: string })])
        expect(defOf(meet(all, either))).toEqual(all.def)
        expect(defOf(meet(either, all))).toEqual(all.def)
    })
})

describe('two lists meet on their aligned rows', () => {
    /**
     * **Below the tail, each common length is one fixed row. From the tail up, the ends meet and the
     * spreads meet.** Here the tail starts at two positions, so the one-position row meets alone.
     */
    it('meets a prefix against a suffix at the fixed rows and the tail', () => {
        const both: AnyCodec = meet(
            list(string('a', 'b'), spread(string)),
            list(spread(string), string('b', 'c')),
        )
        const decodes = (...xs: string[]) =>
            !failed(both.decode({ L: xs.map((x) => ({ S: x })) }))
        expect(decodes('b')).toBe(true)
        expect(decodes('a')).toBe(false)
        expect(decodes('a', 'c')).toBe(true)
        expect(decodes('a', 'x', 'c')).toBe(true)
        expect(decodes('c', 'c')).toBe(false)
        expect(decodes('a', 'x')).toBe(false)
    })

    /** A row with a position at `never` holds no value, and a meet with no row is `never`. */
    it('drops a row with a position at never, and meets at never with no row', () => {
        expect(
            defOf(
                meet(
                    list(string('a'), spread(string)),
                    list(string('b'), spread(string)),
                ),
            ),
        ).toEqual(never.def)
    })
})

describe('the variadic meet', () => {
    /**
     * The fold is left. No declaration of the model proves the term of the other nesting equal.
     */
    it('folds left, and both nestings give the same term', () => {
        const a = object({ a: string })
        const b = object({ b: boolean })
        const c = object({ c: decimal })
        expect(meet(a, b, c).def).toEqual(meet(meet(a, b), c).def)
        expect(meet(a, b, c).def).toEqual(meet(a, meet(b, c)).def)
        expect(meet(a, b, c).def).toEqual(
            object({ a: string, b: boolean, c: decimal }).def,
        )
    })

    it('refuses fewer than two factors', () => {
        const take = meet as unknown as (...f: readonly unknown[]) => unknown
        expect(() => take(object({ a: string }))).toThrow(CodecError)
    })
})

describe('the slots that the constructors refuse at never', () => {
    /**
     * **A slot nothing fills makes the term hold no value**, and the constructor refuses it.
     *
     * A slot is a position a value must fill: a fixed element of a tuple, and a `req` or
     * `withLegacyRead` field. `never` already names the term that holds nothing, so a second spelling
     * for it is a declaration that looks like a schema and refuses every entity.
     */
    it('refuses a slot declared at never, at the constructor that holds it', () => {
        // @ts-expect-error the type refuses it too; this asserts the runtime half
        expect(() => object({ a: string, dead: never })).toThrow(
            /holds no value/,
        )
        // @ts-expect-error a declared position of a list is a slot
        expect(() => list(never, string)).toThrow(/nothing fills it/)
        // …and the spread is NOT one, so it is admitted: a value of exactly the declared length
        // omits every spread position, so this is `list(string)` and that holds a value
        expect(() => list(string, spread(never))).not.toThrow()
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
        const Opt = item(object({ a: string, gone: optional(never) }))
        expect(Opt.unsafeEncode({ a: 'q' })).toEqual({ a: { S: 'q' } })

        // `undefinable` keeps the key in the entity and lets the value be `undefined`, so over
        // `never` the key is required and `undefined` is the only value it can take
        const Und = item(object({ a: string, gone: undefinable(never) }))
        expect(Und.unsafeEncode({ a: 'q', gone: undefined })).toEqual({
            a: { S: 'q' },
        })

        // `nullable` holds the null and nothing else, and the name stays required
        const Nul = item(object({ a: string, gone: nullable(never) }))
        expect(Nul.unsafeEncode({ a: 'q', gone: null })).toEqual({
            a: { S: 'q' },
            gone: { NULL: true },
        })
        expect(() => Nul.unsafeEncode({ a: 'q' } as never)).toThrow(CodecError)
    })

    /**
     * A name at `never` under a mark that admits absence holds no value, so the generator has
     * nothing to draw for it. `optional` leaves the key out, and `undefinable` keeps the key at
     * `undefined`, which is the one value that the key can take.
     */
    it('generates a name at never as absent under optional, and as undefined under undefinable', () => {
        const Opt = object({ a: string, gone: optional(never) })
        const Und = object({ a: string, gone: undefinable(never) })
        const rng = rngFrom(7)
        for (let i = 0; i < 100; i++) {
            const opt = arbitraryOf(Opt, rng, 4) as Record<string, unknown>
            expect('gone' in opt).toBe(false)
            const und = arbitraryOf(Und, rng, 4) as Record<string, unknown>
            expect('gone' in und).toBe(true)
            expect(und.gone).toBeUndefined()
        }
        checkRoundTrip(item(Opt))
        checkRoundTrip(item(Und))
    })

    /**
     * **`withLegacyRead` at `never` is refused twice, by two different rules.**
     *
     * The type reaches it through the slot gate: a `withLegacyRead` name is always written. The runtime
     * never gets that far, because `withLegacyRead`'s own older rule refuses a stand-in that the codec
     * it stands in for cannot write, and `never` writes nothing.
     */
    it('refuses a withLegacyRead at never, at the type by the slot and at the runtime by the stand-in', () => {
        expect(() =>
            object({
                a: string,
                gone: withLegacyRead({
                    current: never as never,
                    // @ts-expect-error the slot gate refuses it at the type
                    whenMissing: 'v',
                }),
            }),
        ).toThrow(/stand-in must be a value/)
    })

    /** `array` and an open object are not slots: both admit their empty case, and that is a value. */
    it('declares an array of never, which holds the empty list', () => {
        const Empty = array(never)
        expect(Empty.unsafeDecode(Empty.unsafeEncode([]))).toEqual([])
    })

    /**
     * **`never` absorbs.** The meet of a codec with the term that holds no value holds no value, in
     * either position. The result is `never`, and a `never` codec refuses when it is used.
     */
    it('meets at never a factor at never, in either position', () => {
        expect(defOf(meet(never, object({ n: decimal })))).toEqual(never.def)
        expect(defOf(meet(object({ n: decimal }), never))).toEqual(never.def)
    })
})

describe('a meet of lawful factors is lawful', () => {
    // each factor is lawful, and the meet's field tables are a disjoint union, so the meet
    // reads back what it wrote and writes back what it read
    const meets = [
        ['two closed objects', item(meet(Pet, Price))],
        [
            'literals, sets and lists',
            item(
                meet(
                    object({ tag: string('a', 'b'), n: number }),
                    object({ tags: string.set(), steps: array(decimal) }),
                ),
            ),
        ],
        [
            'nullable and optional fields',
            item(
                meet(
                    object({ note: nullable(string) }),
                    object({
                        gift: optional(boolean),
                        count: optional(number),
                    }),
                ),
            ),
        ],
        [
            'three factors',
            item(
                meet(
                    object({ a: string }),
                    object({ b: decimal }),
                    object({ c: boolean }),
                ),
            ),
        ],
    ] as const

    for (const [name, codec] of meets) {
        it(`decodes what it encodes, for ${name}`, () => {
            checkRoundTrip(codec as never, {
                count: 60,
                seed: 20260924,
            })
        })
        it(`encodes what it decodes, for ${name}`, () => {
            checkDecodesAreWritable(codec as never, {
                count: 40,
                seed: 20260924,
            })
        })
    }
})

describe('the composition reads each factor open', () => {
    /**
     * **The composition reads both factors open**, as `A & B` reads it. A closed factor holds each
     * undeclared name at `opaque`, so a name that only the other factor declares keeps the slot that
     * the other factor declares. The result closes again where both factors are closed. The type
     * reads two object slots on the union of their names, as the run time does.
     */
    it('keeps an optional name that only the other factor declares, at every depth', () => {
        const met = meet(
            object({ c: string }),
            object({ c: string, v: optional(number) }),
        )
        expect(met.def).toEqual(object({ c: string, v: optional(number) }).def)
        expectTypeOf<Decoded<typeof met>>().toEqualTypeOf<{
            readonly c: string
            readonly v?: number
        }>()
        const nested = meet(
            object({ n: object({ c: string }) }),
            object({ n: object({ c: string, v: optional(number) }) }),
        )
        expect(nested.def).toEqual(
            object({ n: object({ c: string, v: optional(number) }) }).def,
        )
        expectTypeOf<Decoded<typeof nested>>().toEqualTypeOf<{
            readonly n: { readonly c: string; readonly v?: number }
        }>()
    })

    /**
     * **The meet of two recursive factors that differ is recursive.** The walk meets a pair of nodes
     * again below itself, and a `ref` to the meet of the pair closes the cycle. The `ref` names the
     * meet of the two unions, so the option that declares `k` stands below `m` as at the top.
     */
    it('closes the meet of two recursive factors with a ref to the meet', () => {
        const { self: left } = scope({
            self: union([string.set(), object({ m: optional(ref('self')) })]),
        })
        const { self: right } = scope({
            self: union([
                object({ k: string('p') }),
                object({ m: optional(ref('self')) }),
            ]),
        })
        const one: AnyCodec = left
        const other: AnyCodec = right
        const both: AnyCodec = meet(one, other)
        expect(failed(both.decode({ M: { k: { S: 'p' } } }))).toBe(false)
        expect(
            failed(both.decode({ M: { m: { M: { k: { S: 'p' } } } } })),
        ).toBe(false)
        expect(failed(both.decode({ M: { m: { M: { m: { M: {} } } } } }))).toBe(
            false,
        )
        expect(
            failed(both.decode({ M: { m: { M: { k: { S: 'q' } } } } })),
        ).toBe(true)
        expect(failed(both.decode({ SS: ['a'] }))).toBe(true)
    })
})

describe('a thunk changes no verdict of the order', () => {
    /** The codec `codec` behind a `ref`: the model reads the term behind the thunk. */
    const thunked = (codec: AnyCodec): AnyCodec =>
        scope({ At: ref('It'), It: codec }).At

    /**
     * **`opaque` is the unit of the meet, written plain or behind a `ref`.** A union that meets the
     * unit is the union itself. Read at the written node, the thunked unit distributes the union, and
     * the two meets overlap, which no union holds.
     */
    it('returns the other factor when one factor is opaque behind a ref', () => {
        const kind: AnyCodec = union([
            object({ a: string }),
            object({ b: number }),
        ])
        for (const top of [opaque, thunked(opaque)]) {
            expect(meet(kind, top)).toBe(kind)
            expect(meet(top, kind)).toBe(kind)
        }
    })

    /**
     * **A name that the pattern leaves to an `opaque` block is the top, written plain or behind a
     * `ref`.** The stand-in of a `withLegacyRead` slot pairs the absent row with a value, and only
     * the top holds that pair, so the order reads the block at the node behind the thunk.
     */
    it('reads an opaque block behind a ref as the top of a stand-in slot', () => {
        const kind: AnyCodec = union([
            object({
                a: withLegacyRead({ current: string, whenMissing: 'x' }),
            }),
            object({ b: number }),
        ])
        for (const top of [opaque, thunked(opaque)]) {
            const open: AnyCodec = object([string, optional(top)])
            expect(meet(kind, open)).toBe(kind)
            expect(meet(open, kind)).toBe(kind)
        }
    })
})

describe('the type of a meet reads the values that the run time keeps', () => {
    /** A base meets its literal at the literal, in the type and in the term. */
    it('meets a base and its literal at the literal', () => {
        const one = meet(string, string('q'))
        expectTypeOf<Decoded<typeof one>>().toEqualTypeOf<'q'>()
        expect(one.def).toEqual(string('q').def)
        const field = meet(object({ a: string }), object({ a: string('q') }))
        expectTypeOf<Decoded<typeof field>>().toEqualTypeOf<{
            readonly a: 'q'
        }>()
        expect(field.def).toEqual(object({ a: string('q') }).def)
    })

    it('meets two lists and two sets by element', () => {
        const lists = meet(
            object({ a: array(string) }),
            object({ a: array(string('q')) }),
        )
        expectTypeOf<Decoded<typeof lists>>().toEqualTypeOf<{
            readonly a: readonly 'q'[]
        }>()
        expect(lists.def).toEqual(object({ a: array(string('q')) }).def)
        const fixed = meet(
            object({ a: list(string, boolean) }),
            object({ a: list(string('q'), boolean) }),
        )
        expectTypeOf<Decoded<typeof fixed>>().toEqualTypeOf<{
            readonly a: readonly ['q', boolean]
        }>()
        expect(fixed.def).toEqual(object({ a: list(string('q'), boolean) }).def)
        const sets = meet(
            object({ a: string.set() }),
            object({ a: string.set() }),
        )
        expectTypeOf<Decoded<typeof sets>>().toEqualTypeOf<{
            readonly a: ReadonlySet<string>
        }>()
        expect(sets.def).toEqual(object({ a: string.set() }).def)
    })

    /** Two bases of different members hold no common value, so the type is `never` as the term is. */
    it('meets two bases of different members at never', () => {
        const field = meet(object({ a: string }), object({ a: boolean }))
        expectTypeOf(field).toBeNever()
        expect(defOf(field)).toEqual(never.def)
        const bare = meet(string, boolean)
        expectTypeOf(bare).toBeNever()
        expect(defOf(bare)).toEqual(never.def)
    })

    /**
     * **The type stays coarser at two literal sets that share a literal.** The type cannot build the
     * codec of the common literals, so the decoded type is that of one side and holds `'z'`, which the
     * term drops. A caller reads the term for the exact values.
     */
    it('keeps the decoded type of one side at two overlapping literal sets', () => {
        const both = meet(string('x', 'y'), string('y', 'z'))
        expectTypeOf<Decoded<typeof both>>().toEqualTypeOf<'y' | 'z'>()
        expect(both.def).toEqual(string('y').def)
    })

    /**
     * **Two codecs whose stored members cannot meet have the bottom as their meet**, whatever adapter
     * sits over them: no attribute is stored by both, so no value is held by both.
     */
    it('meets string and number at never', () => {
        const bare = meet(string, number)
        expectTypeOf(bare).toBeNever()
        expect(defOf(bare)).toEqual(never.def)
        const named = meet(object({ a: string }), object({ a: number }))
        expectTypeOf(named).toBeNever()
        expect(defOf(named)).toEqual(never.def)
    })

    it('meets decimal and string at never, because decimal stores a number', () => {
        const bare = meet(decimal, string)
        expectTypeOf(bare).toBeNever()
        expect(defOf(bare)).toEqual(never.def)
        expect(defOf(meet(string, decimal))).toEqual(never.def)
    })

    /**
     * **A refinement reads through**: the meet refines the meet of the inner term by the same
     * predicate, and each pair of that meet is a pair of the inner term.
     */
    it('refines the meet of the inner term by the predicate of the refinement', () => {
        const isA = (value: string): value is string => value.startsWith('a')
        const both: AnyCodec = meet(refine(string, isA), string('a1', 'b'))
        expect(failed(both.decode({ S: 'a1' }))).toBe(false)
        expect(failed(both.decode({ S: 'b' }))).toBe(true)
        expect(failed(both.decode({ S: 'a2' }))).toBe(true)
        const reversed: AnyCodec = meet(string('a1', 'b'), refine(string, isA))
        expect(failed(reversed.decode({ S: 'a1' }))).toBe(false)
        expect(failed(reversed.decode({ S: 'b' }))).toBe(true)
        expect(defOf(meet(refine(string, isA), boolean))).toEqual(never.def)
    })

    /**
     * **A refinement meets through an adapter.** A pair of the meet is one row and one value that
     * both sides relate, so the predicate reads that value on either side. The meet refines the
     * other side by the predicate.
     */
    it('refines the other side by the predicate where the other side holds an adapter', () => {
        const notOne = (value: unknown): value is unknown => value !== '1'
        const both: AnyCodec = meet(refine(opaque, notOne), decimal)
        expect(failed(both.decode({ N: '2.5' }))).toBe(false)
        expect(failed(both.decode({ N: '1' }))).toBe(true)
        expect(failed(both.decode({ S: '2.5' }))).toBe(true)
        const positive = (value: string): value is string =>
            !value.startsWith('-')
        const listed: AnyCodec = meet(
            refine(decimal, positive),
            decimal('1', '-2.5'),
        )
        expect(failed(listed.decode({ N: '1' }))).toBe(false)
        expect(failed(listed.decode({ N: '-2.5' }))).toBe(true)
        expect(failed(listed.decode({ N: '3' }))).toBe(true)
    })

    /**
     * **Two parts whose caller views share no value meet at the bottom**, in both orders. `decimal`
     * and `number` store one member, so the stored views share each attribute. `decimal` decodes a
     * text and `number` decodes a number, so no row relates one value on both sides.
     */
    it('meets decimal and number at never, because their caller views share no value', () => {
        const bare = meet(decimal, number)
        expectTypeOf(bare).toBeNever()
        expect(defOf(bare)).toEqual(never.def)
        const reversed = meet(number, decimal)
        expectTypeOf(reversed).toBeNever()
        expect(defOf(reversed)).toEqual(never.def)
    })

    /**
     * **A `held` part that neither side fits, apart in neither view, is refused.** The adapter of
     * the part is an opaque function, and the function decides which common rows relate one value.
     */
    it('refuses a held part that neither side fits where the views overlap', () => {
        const shifted = held(number, number, {
            encode: (value: number) => value + 1,
            decode: (value: number) => value - 1,
        })
        expect(() => meet(shifted, number(1, 2))).toThrow(
            /`held` part that fits neither side.*opaque function/,
        )
        expect(() => meet(number(1, 2), shifted)).toThrow(
            /`held` part that fits neither side.*opaque function/,
        )
    })

    /**
     * **An older reading holds each pair of its current form**, so a side below the current form is
     * the meet.
     */
    it('meets a side below the current form of an older reading at that side', () => {
        const widened = withLegacyRead({ current: string, older: decimal })
        expect(meet(widened, string('q')).def).toEqual(string('q').def)
        expect(meet(string('q'), widened).def).toEqual(string('q').def)
    })
})
