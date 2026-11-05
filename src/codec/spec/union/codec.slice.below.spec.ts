/**
 * The fit of a codec at a pattern is the order of the run time, rule for rule.
 *
 * The run time decides with `below` on the terms. The type decides with the same rules on the same
 * terms, so a result type holds every option that the run time keeps. Each test below is a pair
 * that a fit by decoded type reads wrongly: the slot differs in presence, in adapter or in layout,
 * and the decoded types lie inside each other. Each test assigns a value that the run time keeps to
 * the decoded type, and decodes it.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { Decoded } from '../../codec'
import {
    decimal,
    exclude,
    extract,
    legacy,
    list,
    object,
    opaque,
    optional,
    spread,
    string,
    undefinable,
    union,
} from '../../codec'
import { failed } from '../../result'

const dog = object({ kind: string('dog') })
const dogStored = { M: { kind: { S: 'dog' } } }

describe('the fit reads the order of the run time at each slot of an object', () => {
    it('keeps in the exclusion the absent part of an optional slot that meets an undefinable slot', () => {
        const cat = object({ kind: string('cat'), nickname: optional(string) })
        const rest = exclude(
            union([dog, cat]),
            object({ nickname: undefinable(string) }),
        )
        expectTypeOf<Decoded<typeof dog>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expectTypeOf<{ readonly kind: 'cat' }>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(rest.decode(dogStored)).toEqual({ kind: 'dog' })
        expect(rest.decode({ M: { kind: { S: 'cat' } } })).toEqual({
            kind: 'cat',
        })
        expect(
            failed(
                rest.decode({
                    M: { kind: { S: 'cat' }, nickname: { S: 'tom' } },
                }),
            ),
        ).toBe(true)
    })

    it('keeps in the exclusion a member whose slot meets a held pattern slot', () => {
        const named = object({ kind: string('dog'), name: string })
        const cat = object({ kind: string('cat') })
        const rest = exclude(
            union([named, cat]),
            object({ name: opaque('lossy') }),
        )
        expectTypeOf<Decoded<typeof named>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expectTypeOf<Decoded<typeof cat>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(
            rest.decode({ M: { kind: { S: 'dog' }, name: { S: 'rex' } } }),
        ).toEqual({ kind: 'dog', name: 'rex' })
    })

    it('keeps in the exclusion a member whose slot reads an older encoding', () => {
        const aged = object({
            kind: string('cat'),
            name: legacy({ current: string, older: decimal }),
        })
        const rest = exclude(union([aged, dog]), object({ name: string }))
        expectTypeOf<Decoded<typeof aged>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expectTypeOf<Decoded<typeof dog>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(
            rest.decode({ M: { kind: { S: 'cat' }, name: { S: 'tom' } } }),
        ).toEqual({ kind: 'cat', name: 'tom' })
    })
})

describe('the fit reads the layout of a list as the run time does', () => {
    it('keeps in the exclusion a member whose list has no spread against a pattern with a prefix and a spread', () => {
        const owner = object({ kind: string('owner'), petIds: list(string) })
        const rest = exclude(
            union([owner, dog]),
            object({ petIds: list(string, spread(string)) }),
        )
        expectTypeOf<Decoded<typeof owner>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expectTypeOf<Decoded<typeof dog>>().toMatchTypeOf<
            Decoded<typeof rest>
        >()
        expect(
            rest.decode({
                M: { kind: { S: 'owner' }, petIds: { L: [{ S: 'p1' }] } },
            }),
        ).toEqual({ kind: 'owner', petIds: ['p1'] })
    })
})

describe('the fit reads the literals of a union as the run time does', () => {
    it('keeps in the extraction the member whose decimal union lies inside the decimal literal set', () => {
        const priced = object({
            price: union([decimal('1'), decimal('2')]),
        })
        const free = object({ price: string('free') })
        const kept = extract(
            union([priced, free]),
            object({ price: decimal('1', '2') }),
        )
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof priced>
        >()
        expect(kept.decode({ M: { price: { N: '1' } } })).toEqual({
            price: '1',
        })
        expect(failed(kept.decode({ M: { price: { S: 'free' } } }))).toBe(true)
    })
})
