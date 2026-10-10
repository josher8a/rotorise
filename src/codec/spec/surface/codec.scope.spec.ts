/**
 * Codecs that name each other, declared in one `scope`.
 *
 * A `ref` names an entry of its scope, and the decoded type of each entry follows from the
 * definitions. No caller states the type of a cycle, as the annotation of a recursive `lazy` does.
 * The run time builds the term graph that `lazy` builds for the same codecs.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import {
    type AttributeCodec,
    array,
    CodecError,
    type Decoded,
    lazy,
    nullValue,
    number,
    object,
    optional,
    ref,
    scope,
    string,
    union,
} from '../../codec'
import { recursionUse, sameTerm } from '../../term'

type TA = { readonly v: string; readonly b?: TB }
type TB = { readonly a?: TA; readonly n: null }

const S = scope({
    A: object({ v: string, b: optional(ref('B')) }),
    B: object({ a: optional(ref('A')), n: nullValue }),
})

describe('a scope', () => {
    it('round-trips a mutual recursion at any depth, with no annotation', () => {
        const v: Decoded<typeof S.A> = {
            v: 'x',
            b: { n: null, a: { v: 'y', b: { n: null, a: { v: 'z' } } } },
        }
        // the decoded type of an entry is the type of the cycle, in both directions
        const typed: TA = v
        const back: Decoded<typeof S.A> = typed
        expect(S.A.decode(S.A.unsafeEncode(back))).toEqual(v)
    })

    it('reaches a path through two refs', () => {
        const W = object({ r: optional(S.A) }).item
        expect(W.at((p) => p.r.b.a.b.a.v).path()).toBe('r.b.a.b.a.v')
    })

    it('builds the term graph that lazy builds for the same codecs', () => {
        const B: AttributeCodec<TB> = lazy(() =>
            object({ a: optional(A), n: nullValue }),
        )
        const A: AttributeCodec<TA> = lazy(() =>
            object({ v: string, b: optional(B) }),
        )
        expect(sameTerm(S.A.def, A.def)).toBe(true)
        expect(sameTerm(S.B.def, B.def)).toBe(true)
        // the control: another shape is another graph
        expect(sameTerm(S.A.def, B.def)).toBe(false)
    })

    it('refuses a ref to a name that the scope does not declare, in the type and at construction', () => {
        expect(() =>
            // @ts-expect-error the scope declares no 'Z'
            scope({ A: object({ b: optional(ref('Z')) }) }),
        ).toThrow(/a ref names 'Z', which this scope does not declare/)
    })

    it('refuses a recursion with no list or object on its path, at construction', () => {
        expect(() => scope({ C: ref('D'), D: ref('C') })).toThrow(CodecError)
        expect(() => scope({ U: union([string, ref('U')]) })).toThrow(
            CodecError,
        )
        expect(() =>
            scope({
                U: union([object({ a: string }), ref('V')]),
                V: ref('U'),
            }),
        ).toThrow(CodecError)
    })
})

/**
 * **A `ref` as a union option.** The union reads each option where the union is declared, and a
 * `ref` resolves only where its scope binds it. So the union waits for the scope, and decides with
 * every name bound. The same union through `lazy` decides where each name that it reads is declared
 * first, and the two decisions agree.
 */
describe('a ref as a union option', () => {
    /**
     * The answers of a codec: the attribute that it writes for each value, and what it reads from
     * each stored attribute. A refusal answers with its message.
     */
    const answers = <T>(
        codec: AttributeCodec<T>,
        values: readonly T[],
        stored: readonly AttributeValue[],
    ) =>
        [
            ...values.map((value) => codec.encode(value)),
            ...stored.map((attribute) => codec.decode(attribute)),
        ].map((answer) =>
            answer instanceof CodecError ? String(answer) : answer,
        )

    it('decides as the same union through lazy, where an option is an object', () => {
        const Scoped = scope({
            U: union([object({ a: string }), ref('V')]),
            V: object({ u: ref('U') }),
        })
        type TU = { readonly a: string } | TV
        type TV = { readonly u: TU }
        const V: AttributeCodec<TV> = object({
            u: lazy((): AttributeCodec<TU> => U),
        })
        const U = union([object({ a: string }), lazy(() => V)])

        expect(sameTerm(Scoped.U.def, U.def)).toBe(true)
        expect(recursionUse(Scoped.U.def)).toBe(recursionUse(U.def))
        const values: readonly TU[] = [
            { a: 'x' },
            { u: { a: 'y' } },
            { u: { u: { a: 'z' } } },
        ]
        const stored: readonly AttributeValue[] = [
            { M: { u: { M: { a: { S: 'y' } } } } },
            { M: { b: { S: 'no option' } } },
            { M: { u: { M: { b: { S: 'no option' } } } } },
            { S: 'a string' },
        ]
        expect(answers(Scoped.U, values, stored)).toEqual(
            answers(U, values, stored),
        )
        const typed: Decoded<typeof Scoped.U> = { u: { u: { a: 'z' } } }
        expect(Scoped.U.decode(Scoped.U.unsafeEncode(typed))).toEqual(typed)
    })

    it('decides as the same union through lazy, where an option is a list', () => {
        const Scoped = scope({
            T: union([string, ref('L')]),
            L: array(ref('T')),
        })
        type TT = string | readonly TT[]
        const L: AttributeCodec<readonly TT[]> = array(
            lazy((): AttributeCodec<TT> => T),
        )
        const T = union([string, lazy(() => L)])

        expect(sameTerm(Scoped.T.def, T.def)).toBe(true)
        expect(recursionUse(Scoped.T.def)).toBe(recursionUse(T.def))
        const values: readonly TT[] = ['a', ['b', ['c']], []]
        const stored: readonly AttributeValue[] = [
            { L: [{ S: 'b' }, { L: [{ S: 'c' }] }] },
            { L: [{ N: '1' }] },
            { M: { not: { S: 'a list' } } },
            { N: '7' },
        ]
        expect(answers(Scoped.T, values, stored)).toEqual(
            answers(T, values, stored),
        )
    })
})

/**
 * **An entry keeps the methods of its body.** An object keeps its item, and a union of objects
 * keeps its item and its slices. Each method reads the decoded type of the entry, so a path
 * crosses a `ref` as a field of an object does.
 */
describe('an entry of a scope', () => {
    it('keeps the item of an object, with a path through the refs', () => {
        const located = S.A.item.at((p) => p.b.a.v)
        expect(located.path()).toBe('b.a.v')
        const v: Decoded<typeof located> = 'leaf'
        expect(located.encode(v)).toEqual({ S: 'leaf' })
        const row: TA = { v: 'x', b: { n: null } }
        expect(S.A.item.decode(S.A.item.unsafeEncode(row))).toEqual(row)
    })

    it('keeps the item and the slices of a union of objects', () => {
        const P = scope({
            P: union([
                object({ k: string('a'), next: optional(ref('P')) }),
                object({ k: string('b') }),
            ]),
        }).P
        type TP = { readonly k: 'a'; readonly next?: TP } | { readonly k: 'b' }
        const row: TP = { k: 'a', next: { k: 'b' } }
        expect(P.item.decode(P.item.unsafeEncode(row))).toEqual(row)
        const kept = P.extract({ k: string('a') })
        const one: Decoded<typeof kept> = { k: 'a', next: { k: 'a' } }
        expect(kept.decode(kept.unsafeEncode(one))).toEqual(one)
        expect(kept.decode({ M: { k: { S: 'b' } } })).toBeInstanceOf(CodecError)
        expect(P.exclude({ k: string('a') }).unsafeEncode({ k: 'b' })).toEqual({
            M: { k: { S: 'b' } },
        })
    })
})

describe('an open name of a path', () => {
    it('is selected by entry, as the codec of the open entry', () => {
        const Open = object({ id: string }, [string, optional(number)]).item
        const located = Open.at((p) => p.entry('size'))
        expect(located.path()).toBe('size')
        expect(located.encode(3)).toEqual({ N: '3' })
        // the codec of the open entry, with no `| undefined` that a property step adds
        const read: number = located.unsafeDecode({ N: '3' })
        expect(read).toBe(3)
    })
})
