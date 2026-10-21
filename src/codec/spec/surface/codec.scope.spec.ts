/**
 * Codecs that name each other, declared in one `scope`.
 *
 * A `ref` names an entry of its scope, and the decoded type of each entry follows from the
 * definitions. No caller states the type of a cycle. At run time, each `ref` is a thunk, so each
 * cycle of the term graph passes through a thunk.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import type { AttributeValue } from '../../attribute'
import {
    type AttributeCodec,
    array,
    CodecError,
    type Decoded,
    discriminatedUnion,
    exclude,
    extract,
    type FreeOf,
    held,
    list,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    ref,
    refine,
    scope,
    spread,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import type { RefSlot, Term } from '../../term'
import { freeNamesOf, recursionUse, sameTerm } from '../../term'

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

    it('builds a term graph whose cycle passes through a ref node at each ref', () => {
        const toA: RefSlot = { name: 'A', waiting: [] }
        const toB: RefSlot = { name: 'B', waiting: [] }
        const A: Term = {
            kind: 'object',
            body: {
                fields: {
                    v: { mark: 'req', t: { kind: 'string' } },
                    b: { mark: 'optional', t: { kind: 'ref', slot: toB } },
                },
            },
        }
        const B: Term = {
            kind: 'object',
            body: {
                fields: {
                    a: { mark: 'optional', t: { kind: 'ref', slot: toA } },
                    n: { mark: 'req', t: { kind: 'null' } },
                },
            },
        }
        toA.bound = toB.bound = { A, B }
        expect(sameTerm(S.A.def, A)).toBe(true)
        expect(sameTerm(S.B.def, B)).toBe(true)
        // the control: another shape is another graph
        expect(sameTerm(S.A.def, B)).toBe(false)
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
 * every name bound.
 */
describe('a ref as a union option', () => {
    /**
     * The answers of a codec: the attribute that it writes for each value, and what it reads from
     * each stored attribute. A refusal answers `'refused'`.
     */
    const answers = <T>(
        codec: AttributeCodec<T>,
        values: readonly T[],
        stored: readonly AttributeValue[],
    ) =>
        [
            ...values.map((value) => codec.encode(value)),
            ...stored.map((attribute) => codec.decode(attribute)),
        ].map((answer) => (answer instanceof CodecError ? 'refused' : answer))

    it('decides with every name bound, where an option is an object', () => {
        const Scoped = scope({
            U: union([object({ a: string }), ref('V')]),
            V: object({ u: ref('U') }),
        })
        type TU = { readonly a: string } | TV
        type TV = { readonly u: TU }

        // the recursion is guarded: an object is on its path
        expect(recursionUse(Scoped.U.def)).toBe(1)
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
        expect(answers(Scoped.U, values, stored)).toEqual([
            { M: { a: { S: 'x' } } },
            { M: { u: { M: { a: { S: 'y' } } } } },
            { M: { u: { M: { u: { M: { a: { S: 'z' } } } } } } },
            { u: { a: 'y' } },
            'refused',
            'refused',
            'refused',
        ])
        const typed: Decoded<typeof Scoped.U> = { u: { u: { a: 'z' } } }
        expect(Scoped.U.decode(Scoped.U.unsafeEncode(typed))).toEqual(typed)
    })

    it('decides with every name bound, where an option is a list', () => {
        const Scoped = scope({
            T: union([string, ref('L')]),
            L: array(ref('T')),
        })
        type TT = string | readonly TT[]

        // the recursion is guarded: a list is on its path
        expect(recursionUse(Scoped.T.def)).toBe(1)
        const values: readonly TT[] = ['a', ['b', ['c']], []]
        const stored: readonly AttributeValue[] = [
            { L: [{ S: 'b' }, { L: [{ S: 'c' }] }] },
            { L: [{ N: '1' }] },
            { M: { not: { S: 'a list' } } },
            { N: '7' },
        ]
        expect(answers(Scoped.T, values, stored)).toEqual([
            { S: 'a' },
            { L: [{ S: 'b' }, { L: [{ S: 'c' }] }] },
            { L: [] },
            ['b', ['c']],
            'refused',
            'refused',
            'refused',
        ])
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
        const kept = extract(P, object({ k: string('a') }))
        const one: Decoded<typeof kept> = { k: 'a', next: { k: 'a' } }
        expect(kept.decode(kept.unsafeEncode(one))).toEqual(one)
        expect(kept.decode({ M: { k: { S: 'b' } } })).toBeInstanceOf(CodecError)
        expect(
            exclude(P, object({ k: string('a') })).unsafeEncode({ k: 'b' }),
        ).toEqual({
            M: { k: { S: 'b' } },
        })
    })

    it('refuses a member read across an entry on a cycle, in the type and at run time', () => {
        // `B` returns to `A`, so `B` is an entry of the cycle, and an entry stores no member that
        // a path can read: the path cannot pass the `refine` over `B`
        const C = scope({
            A: object({
                s: union([
                    object({ x: string }),
                    refine(ref('B'), (v: unknown): v is unknown => v !== null),
                ]),
            }),
            B: array(ref('A')),
        })
        expect(() =>
            // @ts-expect-error the path reads a member across the entry `B` of a cycle
            C.A.item.at((p) => p.s.x),
        ).toThrow(/a path cannot go into `refine` at 'x'/)
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

type Same<T, U> = [T] extends [U] ? ([U] extends [T] ? true : false) : false

/**
 * **A use needs a closed codec.** Each codec carries in its type the names that its term reads
 * through a `ref` and that no scope binds. An open fragment builds outside a scope, a scope binds
 * the names, and each use of an open fragment refuses, in the type and at run time, by name.
 */
describe('the free names of a codec', () => {
    const older = { decode: () => 'o' as never }
    const fragments = {
        base: string,
        ref: ref('a'),
        array: array(ref('a')),
        object: object({ x: ref('a'), y: optional(ref('b')) }),
        union: union([string, array(ref('a'))]),
        list: list(string, spread(ref('b'))),
        held: held(ref('a'), string, {
            encode: (v: string) => v,
            decode: (v: unknown) => String(v),
        }),
        refine: refine(ref('a'), (v: unknown): v is string => v !== ''),
        legacy: withLegacyRead({ current: ref('a'), older }),
        fill: object({
            f: withLegacyRead({ current: ref('b'), whenMissing: 'x' }),
        }),
        nullable: nullable(ref('a')),
        dunion: discriminatedUnion('k', [
            object({ k: string('x'), v: ref('a') }),
            object({ k: string('y') }),
        ]),
        entry: scope({ a: string, U: union([string, array(ref('a'))]) }).U,
    }

    it('carries in the type the free names that the term reads at run time', () => {
        const typed: {
            readonly [K in keyof typeof fragments]: Same<
                FreeOf<(typeof fragments)[K]>,
                {
                    base: never
                    ref: 'a'
                    array: 'a'
                    object: 'a' | 'b'
                    union: 'a'
                    list: 'b'
                    held: 'a'
                    refine: 'a'
                    legacy: 'a'
                    fill: 'b'
                    nullable: 'a'
                    dunion: 'a'
                    entry: never
                }[K]
            >
        } = {
            base: true,
            ref: true,
            array: true,
            object: true,
            union: true,
            list: true,
            held: true,
            refine: true,
            legacy: true,
            fill: true,
            nullable: true,
            dunion: true,
            entry: true,
        }
        expect(Object.values(typed).every(Boolean)).toBe(true)
        const atRunTime = Object.fromEntries(
            Object.entries(fragments).map(([name, codec]) => [
                name,
                [...freeNamesOf(codec.def)].sort(),
            ]),
        )
        expect(atRunTime).toEqual({
            base: [],
            ref: ['a'],
            array: ['a'],
            object: ['a', 'b'],
            union: ['a'],
            list: ['b'],
            held: ['a'],
            refine: ['a'],
            legacy: ['a'],
            fill: ['b'],
            nullable: ['a'],
            dunion: ['a'],
            entry: [],
        })
    })

    it('refuses each use of an open fragment, in the type and at run time, by name', () => {
        const open = object({ k: array(ref('k')), v: string })
        const free = /this codec reads 'k' through a `ref` that no scope binds/
        // @ts-expect-error a use needs a closed codec
        expect(String(open.encode({ k: [], v: 'x' }))).toMatch(free)
        // @ts-expect-error a use needs a closed codec
        expect(String(open.decode({ M: { v: { S: 'x' } } }))).toMatch(free)
        // @ts-expect-error a use needs a closed codec
        expect(String(open.item.encode({ k: [], v: 'x' }))).toMatch(free)
        // @ts-expect-error a use needs a closed codec
        const located = open.item.at((p) => p.v)
        expect(String(located.encode('x'))).toMatch(free)
        const options = union([
            object({ t: string('a'), k: ref('k') }),
            object({ t: string('b') }),
        ])
        // @ts-expect-error a use needs a closed codec
        expect(() => extract(options, object({ t: string('a') }))).toThrow(free)
    })

    it('closes a fragment that a scope binds, and the entry is the codec to use', () => {
        const open = object({ k: array(ref('k')), v: string })
        const { K } = scope({ k: object({ v: string }), K: open })
        const value = { k: [{ v: 'a' }], v: 'x' }
        expect(K.unsafeDecode(K.unsafeEncode(value))).toEqual(value)
    })

    it('refuses a table entry over an open item, in the type', () => {
        type Row = { id: string; next: unknown }
        const closed = object({ id: string, next: opaque })
        const open = object({ id: string, next: ref('Row') })
        tableEntry<Row>()({ PK: ['id'] }, { codec: closed.item })
        // @ts-expect-error a table entry needs a closed codec
        tableEntry<Row>()({ PK: ['id'] }, { codec: open.item })
    })
})

describe('a refusal inside a nested scope', () => {
    const same = { encode: (v: unknown) => v, decode: (v: unknown) => v }

    /**
     * A scope that refuses keeps its definitions in the slot of each `ref`, so a later scope that
     * reads the fragment sees the cycle that the inner scope refused. The guard of the later scope
     * reads that cycle, and refuses the whole codec.
     */
    it('is the refusal of the whole codec, for an unguarded cycle', () => {
        const fragment = union([string, ref('A')])
        expect(() => scope({ A: fragment as never })).toThrow(
            /'A' reaches a recursion with no list or object on its path/,
        )
        // @ts-expect-error a use needs a closed codec, and the ref reads 'A'
        expect(() => fragment.unsafeEncode('x')).toThrow(
            /through a `ref` that no scope binds/,
        )
        expect(() =>
            scope({
                O: object({ x: ref('A') }) as never,
                A: fragment as never,
            }),
        ).toThrow(/'O' reaches a recursion with no list or object on its path/)
    })

    it('is the refusal of the whole codec, for a cycle through a wall', () => {
        const fragment = held(ref('W') as never, string as never, same as never)
        expect(() => scope({ W: fragment as never })).toThrow(
            /'W' reaches a recursion with an adapter/,
        )
        expect(() =>
            scope({
                O: object({ x: ref('W') }) as never,
                W: fragment as never,
            }),
        ).toThrow(/'O' reaches a recursion with an adapter/)
        expect(() =>
            scope({ O: object({ x: array(fragment as never) }) as never }),
        ).toThrow(/holds an adapter/)
    })
})

/**
 * **A wall reaches no cycle.** A `held` or a `withLegacyRead` with an older reader reads its
 * argument through caller code at any depth. A wall over an entry on a cycle makes the flat system
 * non-contractive, so the host refuses the wall. A wall over an acyclic entry stays legal. The type
 * reads the cycle from the term of the entry, so each spelling below refuses in the type and at
 * run time.
 */
describe('a wall reaches no cycle', () => {
    const same = { encode: (v: string) => v, decode: (v: unknown) => String(v) }
    const older = { decode: () => 'o' as never }
    const { Json } = scope({ Json: union([string, array(ref('Json'))]) })

    it('refuses a wall over an entry on a cycle, in the type and at construction', () => {
        // @ts-expect-error a wall reaches no cycle, and 'Json' is on a cycle
        expect(() => held(Json, string, same)).toThrow(
            /`held` reads 'Json', an entry on a cycle/,
        )
        // @ts-expect-error a wall reaches no cycle, and 'Json' is on a cycle
        expect(() => withLegacyRead({ current: Json, older })).toThrow(
            /`withLegacyRead` reads 'Json', an entry on a cycle/,
        )
    })

    it('refuses a wall over an entry on a cycle of its own scope, in the type and where the scope closes', () => {
        expect(() =>
            scope({
                T: object({ kids: array(ref('T')) }),
                // @ts-expect-error a wall reaches no cycle, and 'T' is on a cycle
                W: held(ref('T'), string, same),
            }),
        ).toThrow(/`held` reads 'T', an entry on a cycle/)
    })

    it('keeps a wall over an acyclic entry', () => {
        const { Text, When } = scope({
            Text: string,
            When: held(ref('Text'), string, same),
        })
        expect(When.unsafeEncode('x')).toEqual({ S: 'x' })
        expect(held(Text, string, same).unsafeEncode('x')).toEqual({ S: 'x' })
        expect(
            withLegacyRead({ current: Text, older }).unsafeEncode('x'),
        ).toEqual({ S: 'x' })
    })
})
