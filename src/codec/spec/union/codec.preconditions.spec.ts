/**
 * **A write at a narrowed path is safe only under the preconditions of the path.**
 *
 * `narrow` drops each option that the stored view of the clause separates, and the store can
 * still hold an item of a dropped option. The preconditions state the stored admission of each
 * clause as data: `in`, `type` and `exists` at a path. A condition expression built from the
 * preconditions refuses the write on an item of a dropped option. A clause key that no exact
 * precondition states is a refusal, because a weaker condition admits such an item.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import {
    array,
    at as atOf,
    CodecError,
    decimal,
    discriminatedUnion,
    item as itemOf,
    narrow,
    number,
    object,
    opaque,
    type Precondition,
    preconditions as preconditionsOf,
    ref,
    refine,
    scope,
    string,
    union,
    withLegacyRead,
} from '../../codec'

describe('the preconditions of a path are the stored admission of each clause', () => {
    it('a path with no clause has no precondition', () => {
        const Plain = itemOf(object({ a: object({ b: string }) }))
        expect(preconditionsOf(atOf(Plain, ['a', 'b']))).toEqual([])
    })

    it('a string tag pins the stored text', () => {
        const M = itemOf(
            object({
                m: discriminatedUnion('tag', [
                    object({ tag: string('A'), only: number }),
                    object({ tag: string('B'), shared: string }),
                ]),
            }),
        )
        expect(
            preconditionsOf(
                atOf(narrow(atOf(M, ['m']), object({ tag: string('A') })), [
                    'only',
                ]),
            ),
        ).toEqual([{ segments: ['m', 'tag'], in: [{ S: 'A' }] }])
    })

    const Numeric = itemOf(
        object({
            u: union([
                object({ k: number(1), a: string }),
                object({ k: number(2), b: string }),
            ]),
        }),
    )

    it('a numeric tag pins the stored numeral, not the number', () => {
        expect(
            preconditionsOf(
                atOf(narrow(atOf(Numeric, ['u']), object({ k: number(1) })), [
                    'a',
                ]),
            ),
        ).toEqual([{ segments: ['u', 'k'], in: [{ N: '1' }] }])
    })

    it('a decimal tag pins the stored numeral, which a number tag stores too', () => {
        expect(
            preconditionsOf(
                atOf(
                    narrow(atOf(Numeric, ['u']), object({ k: decimal('1') })),
                    ['a'],
                ),
            ),
        ).toEqual([{ segments: ['u', 'k'], in: [{ N: '1' }] }])
    })

    it('a presence clause states that the attribute exists', () => {
        const Untagged = itemOf(
            object({
                u: union([object({ a: string }), object({ b: number })]),
            }),
        )
        expect(
            preconditionsOf(
                atOf(narrow(atOf(Untagged, ['u']), object({ a: opaque })), [
                    'a',
                ]),
            ),
        ).toEqual([{ segments: ['u', 'a'], exists: true }])
    })

    /**
     * **A clause key over an older reader states that the attribute exists**, as the model's
     * `termPreAt` does at `legacy`: the older reader reads every attribute, so the stored view of
     * the key is `opaque`. A refusal here states a rule that the model does not state.
     */
    it('a clause key over withLegacyRead states that the attribute exists, as an opaque key does', () => {
        const Untagged = itemOf(
            object({
                u: union([object({ a: string }), object({ b: number })]),
            }),
        )
        const older = withLegacyRead({ current: string, older: string })
        expect(
            preconditionsOf(
                atOf(narrow(atOf(Untagged, ['u']), object({ a: older })), [
                    'a',
                ]),
            ),
        ).toEqual([{ segments: ['u', 'a'], exists: true }])
    })

    it('a base clause states the stored member', () => {
        const ByMember = itemOf(
            object({
                u: union([
                    object({ tag: string('A'), v: decimal }),
                    object({ tag: string('B'), v: string }),
                ]),
            }),
        )
        expect(
            preconditionsOf(
                atOf(narrow(atOf(ByMember, ['u']), object({ v: number })), [
                    'tag',
                ]),
            ),
        ).toEqual([{ segments: ['u', 'v'], type: 'N' }])
    })

    it('a clause on a nested union states its precondition at the path of that union', () => {
        const Nested = itemOf(
            object({
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
            }),
        )
        expect(
            preconditionsOf(
                atOf(
                    narrow(
                        atOf(
                            narrow(
                                atOf(Nested, ['u']),
                                object({
                                    tag: string('OUTER'),
                                }),
                            ),
                            ['inner'],
                        ),
                        object({ kind: string('x') }),
                    ),
                    ['x'],
                ),
            ),
        ).toEqual([
            { segments: ['u', 'tag'], in: [{ S: 'OUTER' }] },
            { segments: ['u', 'inner', 'kind'], in: [{ S: 'x' }] },
        ])
    })

    it('two clauses on one path are a conjunction of their preconditions', () => {
        const Two = itemOf(
            object({
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
            }),
        )
        expect(
            preconditionsOf(
                atOf(
                    narrow(
                        narrow(
                            atOf(Two, ['u']),
                            object({ kind: string('pet') }),
                        ),
                        object({
                            size: string('large'),
                        }),
                    ),
                    ['pen'],
                ),
            ),
        ).toEqual([
            { segments: ['u', 'kind'], in: [{ S: 'pet' }] },
            { segments: ['u', 'size'], in: [{ S: 'large' }] },
        ])
    })

    it('a nested clause is open at each level, so it gives a type precondition at each level', () => {
        const Nested = itemOf(
            object({
                u: union([
                    object({ data: object({ n: number }), tag: string }),
                    object({ data: string, tag: string }),
                ]),
            }),
        )
        expect(
            preconditionsOf(
                atOf(
                    narrow(
                        atOf(Nested, ['u']),
                        object({ data: object({ n: number }) }),
                    ),
                    ['tag'],
                ),
            ),
        ).toEqual([
            { segments: ['u', 'data'], type: 'M' },
            { segments: ['u', 'data', 'n'], type: 'N' },
        ])
    })

    /**
     * **A recursion holds no adapter, so a refinement of a recursion keeps its predicate in the
     * stored view.** The walk of the stored view reads each term of the cycle once. A refinement
     * that the view drops would leave the list below it, and the refusal would name a list.
     */
    it('a refinement of a recursion below the top keeps its predicate, so the clause stores a refinement', () => {
        type Nest = readonly Nest[]
        const { Nest } = scope({ Nest: array(ref('Nest')) })
        const Filled = refine(Nest, (v): v is Nest => v.length > 0)
        const Drawing = itemOf(
            object({
                u: union([
                    object({ shape: Nest, tag: string }),
                    object({ shape: string, tag: string }),
                ]),
            }),
        )
        const preconditions = preconditionsOf(
            atOf(narrow(atOf(Drawing, ['u']), object({ shape: Filled })), [
                'tag',
            ]),
        )
        expect(preconditions).toBeInstanceOf(CodecError)
        expect(String(preconditions)).toMatch(
            /'u\.shape' gives no exact precondition: the clause stores a refinement/,
        )
    })
})

/**
 * **What a condition expression answers on a stored item**: each precondition holds at its path. The
 * store compares an `N` as a number, and each `N` in these items is already normal.
 */
const holds = (
    item: Readonly<Record<string, AttributeValue>>,
    preconditions: readonly Precondition[],
): boolean =>
    preconditions.every((precondition) => {
        let at: AttributeValue | undefined
        for (const segment of precondition.segments) {
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
        if ('in' in precondition) {
            return precondition.in.some(
                (one) => JSON.stringify(one) === JSON.stringify(at),
            )
        }
        if ('type' in precondition)
            return at !== undefined && precondition.type in at
        return at !== undefined
    })

describe('a write at a narrowed path is safe only under its preconditions', () => {
    const M = itemOf(
        object({
            m: discriminatedUnion('tag', [
                object({ tag: string('A'), only: number }),
                object({ tag: string('B'), shared: string }),
            ]),
        }),
    )
    const itemA = M.unsafeEncode({ m: { tag: 'A', only: 1 } })
    const itemB = M.unsafeEncode({ m: { tag: 'B', shared: 's' } })

    it('refuses the write on an item of the dropped option, which the write would leave unreadable', () => {
        const only = atOf(
            narrow(atOf(M, ['m']), object({ tag: string('A') })),
            ['only'],
        )
        const preconditions = preconditionsOf(only)
        if (preconditions instanceof CodecError) throw preconditions
        const wrote = only.unsafeEncode(7)
        // the write at the path, as `UpdateItem` sets `m.only`
        const written = (item: typeof itemA) => ({
            ...item,
            m: { M: { ...(item.m as { M: object }).M, only: wrote } },
        })
        // without the preconditions, the write leaves the item of `B` unreadable
        expect(M.decode(written(itemB) as never)).toBeInstanceOf(CodecError)
        // under the preconditions, the store refuses that write and accepts the write on `A`
        expect(holds(itemB, preconditions)).toBe(false)
        expect(holds(itemA, preconditions)).toBe(true)
        expect(M.decode(written(itemA) as never)).not.toBeInstanceOf(CodecError)
    })
})
