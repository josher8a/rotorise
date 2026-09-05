/**
 * Every kind of codec can be generated from its definition alone.
 *
 * The codecs no longer carry generators; `arbitraryOf` and `shrinkOf` build from {@link Def}
 * instead, which is what keeps a property-testing harness out of the production bundle. That is 19
 * branches of dispatch, and a kind nobody covers here is one that throws the first time somebody
 * property-tests it.
 *
 * This replaced an equivalence test: while both implementations existed, it asserted they produced
 * the same values from the same seed. They agreed, the baked-in ones were deleted, and what is
 * worth keeping is coverage and determinism.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec, Def } from './codec'
import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    legacy,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    refine,
    string,
    tuple,
    union,
} from './codec'
import { arbitraryOf, rngFrom, shrinkOf } from './testing'

const isTag = (v: string): v is `t-${string}` => v.startsWith('t-')

type Pet = { TAG: 'PET'; id: string; name?: string }
type Visit =
    | { type: 'CHECKUP'; petId: string }
    | { type: 'SHOT'; petId: string; vaccine: string }
type Line = { petId: string; price: string } | { petIds: readonly string[] }

const codecs: readonly (readonly [string, AnyCodec])[] = [
    ['string', string],
    ['literal', string('A', 'B', 'C')],
    ['literal(one)', string('ONLY')],
    ['decimal', decimal],
    ['number', number],
    ['literal(N)', number(0, 1, 2)],
    ['boolean', boolean],
    ['null', nullValue],
    ['binary', binary],
    ['opaque', opaque],
    ['set', string.set()],
    ['array', array(string)],
    ['tuple', tuple(string, number)],
    ['record', record(decimal)],
    ['map', object({ a: string, b: number })],
    ['nullable', nullable(string)],
    ['legacy', legacy({ current: decimal, older: string })],
    ['refine', refine(string, isTag, { arbitrary: () => 't-x' as const })],
    [
        'item',
        object({
            TAG: string('PET'),
            id: string,
            name: optional(string),
        }),
    ],
    [
        'tagged',
        discriminatedUnion('type', [
            object({ type: string('CHECKUP'), petId: string }),
            object({
                type: string('SHOT'),
                petId: string,
                vaccine: string,
            }),
        ]),
    ],
    [
        'untagged',
        union([
            object({ petId: string, price: decimal }),
            object({ petIds: array(string) }),
        ]),
    ],
]

describe('a definition generates what the codec generated', () => {
    it.each(codecs.map(([kind, codec]) => ({ kind, codec })))(
        '$kind generates, and the same seed generates the same value',
        ({ codec }) => {
            for (const seed of [1, 7, 0x5eed, 12345]) {
                const once = arbitraryOf(codec, rngFrom(seed), 4)
                const twice = arbitraryOf(codec, rngFrom(seed), 4)
                expect(twice).toEqual(once)
                // and what it generates is something the codec can actually carry
                expect(() => codec.unsafeEncode(once as never)).not.toThrow()
            }
        },
    )

    it.each(codecs.map(([kind, codec]) => ({ kind, codec })))(
        '$kind shrinks to values it can still carry, and never to itself',
        ({ codec }) => {
            for (const seed of [1, 7, 0x5eed]) {
                const value = arbitraryOf(codec, rngFrom(seed), 4)
                for (const smaller of shrinkOf(codec, value)) {
                    // shrinking to the value itself is how a search fails to terminate
                    expect(smaller).not.toEqual(value)
                    expect(() =>
                        codec.unsafeEncode(smaller as never),
                    ).not.toThrow()
                }
            }
        },
    )

    // 19: `numeric` was removed (it was `number` with an unchecked cast, and its two call sites
    // here are now `number` and `number(0, 1, 2)`, whose kinds were already covered), and
    // `nullValue` was added, giving the `NULL` point a codec for the first time
    //
    // PINS A FACT NO LAW HAS, deliberately: the *number* of kinds is a property of this
    // library's inventory, not of the calculus, so adding a constructor is meant to fail here
    // and be looked at. It stays as it is.
    it('covers every kind a codec can be', () => {
        const kinds = new Set(codecs.map(([, c]) => c.def?.kind))
        expect(kinds.size).toBe(18)
        expect([...kinds].every(Boolean)).toBe(true)
    })
})
