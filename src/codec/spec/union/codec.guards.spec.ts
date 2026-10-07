/**
 * **A write at a narrowed path is safe only under the guards of the path.**
 *
 * `when` drops each option that the stored view of the clause separates, and the store can still
 * hold an item of a dropped option. The guards state the stored admission of each clause as data:
 * `in`, `type` and `exists` at a path. A condition expression built from the guards refuses the
 * write on an item of a dropped option. A clause key that no exact guard states is a refusal,
 * because a weaker condition admits such an item.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import {
    CodecError,
    decimal,
    discriminatedUnion,
    type Guard,
    number,
    object,
    opaque,
    string,
    union,
} from '../../codec'

describe('the guards of a path are the stored admission of each clause', () => {
    it('a path with no clause has no guard', () => {
        const Plain = object({ a: object({ b: string }) }).item
        expect(Plain.at((p) => p.a.b).guards).toEqual([])
    })

    it('a string tag pins the stored text', () => {
        const M = object({
            m: discriminatedUnion('tag', [
                object({ tag: string('A'), only: number }),
                object({ tag: string('B'), shared: string }),
            ]),
        }).item
        expect(M.at((p) => p.m.when({ tag: string('A') }).only).guards).toEqual(
            [{ segments: ['m', 'tag'], in: [{ S: 'A' }] }],
        )
    })

    const Numeric = object({
        u: union([
            object({ k: number(1), a: string }),
            object({ k: number(2), b: string }),
        ]),
    }).item

    it('a numeric tag pins the stored numeral, not the number', () => {
        expect(Numeric.at((p) => p.u.when({ k: number(1) }).a).guards).toEqual([
            { segments: ['u', 'k'], in: [{ N: '1' }] },
        ])
    })

    it('a decimal tag pins the stored numeral, which a number tag stores too', () => {
        expect(
            Numeric.at((p) => p.u.when({ k: decimal('1') }).a).guards,
        ).toEqual([{ segments: ['u', 'k'], in: [{ N: '1' }] }])
    })

    it('a presence clause states that the attribute exists', () => {
        const Untagged = object({
            u: union([object({ a: string }), object({ b: number })]),
        }).item
        expect(Untagged.at((p) => p.u.when({ a: opaque }).a).guards).toEqual([
            { segments: ['u', 'a'], exists: true },
        ])
    })

    it('a base clause states the stored member', () => {
        const ByMember = object({
            u: union([
                object({ tag: string('A'), v: decimal }),
                object({ tag: string('B'), v: string }),
            ]),
        }).item
        expect(ByMember.at((p) => p.u.when({ v: number }).tag).guards).toEqual([
            { segments: ['u', 'v'], type: 'N' },
        ])
    })

    it('a clause on a nested union guards at the path of that union', () => {
        const Nested = object({
            u: discriminatedUnion('tag', [
                object({
                    tag: string('OUTER'),
                    inner: discriminatedUnion('kind', [
                        object({ kind: string('x'), x: number }),
                        object({ kind: string('y'), y: string }),
                    ]),
                }),
                object({ tag: string('FLAT'), flat: string }),
            ]),
        }).item
        expect(
            Nested.at(
                (p) =>
                    p.u
                        .when({ tag: string('OUTER') })
                        .inner.when({ kind: string('x') }).x,
            ).guards,
        ).toEqual([
            { segments: ['u', 'tag'], in: [{ S: 'OUTER' }] },
            { segments: ['u', 'inner', 'kind'], in: [{ S: 'x' }] },
        ])
    })

    it('two clauses on one path are a conjunction of their guards', () => {
        const Two = object({
            u: union([
                object({
                    kind: string('pet'),
                    size: string('large'),
                    pen: number,
                }),
                object({
                    kind: string('pet'),
                    size: string('small'),
                    cage: string,
                }),
                object({
                    kind: string('food'),
                    size: string('large'),
                    bag: string,
                }),
            ]),
        }).item
        expect(
            Two.at(
                (p) =>
                    p.u.when({ kind: string('pet') }).when({
                        size: string('large'),
                    }).pen,
            ).guards,
        ).toEqual([
            { segments: ['u', 'kind'], in: [{ S: 'pet' }] },
            { segments: ['u', 'size'], in: [{ S: 'large' }] },
        ])
    })

    it('a closed-object clause is a refusal that names the key, because no condition is exact', () => {
        const Closed = object({
            u: union([
                object({ data: object({ n: number }), tag: string }),
                object({ data: string, tag: string }),
            ]),
        }).item
        const guards = Closed.at(
            (p) => p.u.when({ data: object({ n: number }) }).tag,
        ).guards
        expect(guards).toBeInstanceOf(CodecError)
        expect(String(guards)).toMatch(
            /'u\.data' gives no exact guard: the clause stores a closed object/,
        )
    })
})

/**
 * **What a condition expression answers on a stored item**: each guard holds at its path. The
 * store compares an `N` as a number, and each `N` in these items is already normal.
 */
const holds = (
    item: Readonly<Record<string, AttributeValue>>,
    guards: readonly Guard[],
): boolean =>
    guards.every((guard) => {
        let at: AttributeValue | undefined
        for (const segment of guard.segments) {
            at =
                at === undefined
                    ? item[segment]
                    : 'M' in at && at.M !== undefined
                      ? at.M[segment]
                      : 'L' in at &&
                          at.L !== undefined &&
                          typeof segment === 'number'
                        ? at.L[segment]
                        : undefined
            if (at === undefined) return false
        }
        if ('in' in guard) {
            return guard.in.some(
                (one) => JSON.stringify(one) === JSON.stringify(at),
            )
        }
        if ('type' in guard) return at !== undefined && guard.type in at
        return at !== undefined
    })

describe('a write at a narrowed path is safe only under its guards', () => {
    const M = object({
        m: discriminatedUnion('tag', [
            object({ tag: string('A'), only: number }),
            object({ tag: string('B'), shared: string }),
        ]),
    }).item
    const itemA = M.unsafeEncode({ m: { tag: 'A', only: 1 } })
    const itemB = M.unsafeEncode({ m: { tag: 'B', shared: 's' } })

    it('refuses the write on an item of the dropped option, which the write would leave unreadable', () => {
        const only = M.at((p) => p.m.when({ tag: string('A') }).only)
        const guards = only.guards
        if (guards instanceof CodecError) throw guards
        const wrote = only.unsafeEncode(7)
        // the write at the path, as `UpdateItem` sets `m.only`
        const written = (item: typeof itemA) => ({
            ...item,
            m: { M: { ...(item.m as { M: object }).M, only: wrote } },
        })
        // without the guards, the write leaves the item of `B` unreadable
        expect(M.decode(written(itemB) as never)).toBeInstanceOf(CodecError)
        // under the guards, the store refuses that write and accepts the write on `A`
        expect(holds(itemB, guards)).toBe(false)
        expect(holds(itemA, guards)).toBe(true)
        expect(M.decode(written(itemA) as never)).not.toBeInstanceOf(CodecError)
    })
})
