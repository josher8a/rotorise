/**
 * **A former reads the node that a `ref` names**, and not the spelling of its argument.
 *
 * A `ref` and its target are one node of the term graph, so a former gives the two spellings one
 * verdict. Each case below states one rule twice: once with the argument written directly, and once
 * with the argument written as an entry of a scope that names the argument through a `ref`. The
 * type and the run time each give the same verdict to both spellings.
 */
import { describe, expect, it } from 'vitest'
import {
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    exclude,
    extract,
    list,
    never,
    nullable,
    nullValue,
    object,
    opaque,
    optional,
    product,
    ref,
    refine,
    scope,
    string,
    union,
} from '../../codec'
import { RecursionRefused } from '../../term'

/** `It`, named through the `ref` of the entry `At`. */
const NeverAt = scope({ At: ref('It'), It: never }).At
const ObjectAt = scope({ At: ref('It'), It: object({ a: string }) }).At
const KeysAt = scope({ K: ref('L'), L: string('a', 'b') }).K
const OptionAt = scope({
    X: ref('Y'),
    Y: object({ t: string('a'), x: string }),
}).X
const StringAt = scope({ At: ref('It'), It: string }).At
const EmptyAt = scope({ At: ref('It'), It: union([]) }).At
const DissectionAt = scope({
    At: ref('It'),
    It: discriminatedUnion('kind', [
        object({ kind: string('a'), x: string }),
        object({ kind: string('b'), y: boolean }),
    ]),
}).At

describe('a slot at never is refused through a ref', () => {
    it('refuses a declared list position at never, direct and through a ref', () => {
        const row = object({ a: opaque, b: boolean })
        // @ts-expect-error the type refuses the position
        expect(() => list(row, never)).toThrow(/nothing fills it/)
        // @ts-expect-error the type reads the node that the entry names
        expect(() => list(row, NeverAt)).toThrow(/nothing fills it/)
    })

    /**
     * The list is built before the scope binds the name, so the type of `list` reads a free name.
     * The run time refuses at the scope, where the name is bound.
     */
    it('refuses a list position at a ref that the scope binds to never, at the scope', () => {
        expect(() => scope({ L: list(string, ref('N')), N: never })).toThrow(
            /position 1 of the declared positions is `never`/,
        )
    })

    it('refuses a field that the row always writes at never, direct and through a ref', () => {
        // @ts-expect-error the type refuses the field
        expect(() => object({ a: never })).toThrow(/declared at `never`/)
        // @ts-expect-error the type reads the node that the entry names
        expect(() => object({ a: NeverAt })).toThrow(/declared at `never`/)
        expect(() => object({ a: optional(NeverAt) })).not.toThrow()
    })
})

describe('a product reads the node that each factor names', () => {
    it('refuses a factor at never with the never reason, direct and through a ref', () => {
        // @ts-expect-error the type refuses the factor
        expect(() => product(never, object({ b: string }))).toThrow(
            /holds no value/,
        )
        // @ts-expect-error the type gives the never reason through a ref
        expect(() => product(NeverAt, object({ b: string }))).toThrow(
            /holds no value/,
        )
    })

    it('merges an object that a ref names as the object itself', () => {
        const direct = product(object({ a: string }), object({ b: decimal }))
        const named = product(ObjectAt, object({ b: decimal }))
        expect(named.def).toEqual(direct.def)
        expect(named.item.encode({ a: 'x', b: '1' })).toEqual({
            a: { S: 'x' },
            b: { N: '1' },
        })
    })

    /** A dissection is a union of objects in the term, so the product distributes over its variants. */
    it('merges each variant of a discriminatedUnion factor, in declared order', () => {
        const Tagged = discriminatedUnion('kind', [
            object({ kind: string('a'), x: string }),
            object({ kind: string('b'), y: boolean }),
        ])
        const merged = product(Tagged, object({ n: decimal }))
        const plain = product(
            union([
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), y: boolean }),
            ]),
            object({ n: decimal }),
        )
        expect(merged.def).toEqual(plain.def)
        const written: {
            readonly kind: 'b'
            readonly y: boolean
            readonly n: string
        } = { kind: 'b', y: true, n: '1' }
        expect(merged.item.encode(written)).toEqual({
            kind: { S: 'b' },
            y: { BOOL: true },
            n: { N: '1' },
        })
    })

    it('refuses a factor that names a ref that no scope binds, because the merge is built at the declaration', () => {
        expect(() =>
            product(ref('Free') as never, object({ b: decimal })),
        ).toThrow(CodecError)
    })
})

describe('an entry key and a variant read the node that a ref names', () => {
    it('declares the names of a key set that a ref names', () => {
        const direct = object([string('a', 'b'), optional(string)])
        const named = object([KeysAt, optional(string)])
        expect(named.def).toEqual(direct.def)
    })

    it('selects a variant that a ref names by its tag', () => {
        const Visit = discriminatedUnion('t', [
            OptionAt,
            object({ t: string('b'), y: boolean }),
        ])
        expect(Visit.item.encode({ t: 'a', x: 'q' })).toEqual({
            t: { S: 'a' },
            x: { S: 'q' },
        })
        expect(Visit.item.decode({ t: { S: 'b' }, y: { BOOL: true } })).toEqual(
            { t: 'b', y: true },
        )
    })
})

describe('a set element and a slice read the node that a ref names', () => {
    /** The type offers `.set()` on the attribute that the entry names, so the run time builds it. */
    it('stores a set of a refined element that a ref names', () => {
        const Tags = refine(
            StringAt,
            (v: string): v is string => v !== '',
        ).set()
        expect(Tags.encode(new Set(['x']))).toEqual({ SS: ['x'] })
    })

    it('slices a union whose option is a ref, in the type and at run time', () => {
        const h = object({
            a: union([string.set('a', 'b'), nullValue]),
            b: decimal('1', '2.5'),
        })
        const { U } = scope({
            O: object({ m: string }),
            U: union([h, ref('O')]),
        })
        expect(() => extract(U, object({ b: decimal('1') }))).not.toThrow()
        expect(() => exclude(U, object({ b: decimal('2.5') }))).not.toThrow()
    })
})

describe('the judgment decides the obligation of a union', () => {
    /**
     * Agreement reads the meaning of two options, which no type computes, so the run time alone
     * refuses the pair. The refusal through a `ref` lands at the scope that binds the name.
     */
    it('refuses two options that are not shown compatible, direct and through a ref', () => {
        expect(() => union([decimal('1', '2'), string('1', '2')])).toThrow(
            "decimal('1', '2') and string('1', '2') are not shown compatible",
        )
        expect(() =>
            scope({
                U: union([ref('D'), string('1', '2')]),
                D: decimal('1', '2'),
            }),
        ).toThrow(/are not shown compatible/)
    })

    it('admits two compatible options, direct and through a ref', () => {
        expect(() => union([string('A'), string])).not.toThrow()
        expect(() => union([StringAt, string('A')])).not.toThrow()
    })
})

describe('one guard refuses a recursion with no container', () => {
    /**
     * The scope guards each entry, and a term declared over the names of a refused scope reads the
     * cycle that the scope refused. One guard gives both refusals, each with the model's term. The
     * type reads no cycle of the guard, so the run time alone refuses.
     */
    it('refuses the entry at the scope, and a term over the refused names where it is declared', () => {
        const self = ref('A')
        expect(() => scope({ A: self })).toThrow(
            /\[scope\] 'A' reaches a recursion with no list or object on its path/,
        )
        expect(() => list(self)).toThrow(RecursionRefused)
        expect(() => list(self)).toThrow(
            /this `list` term reaches a recursive `ref` with no list or object between/,
        )
    })
})

describe('a term that holds no value is refused where never is', () => {
    it('refuses a declared list position at union([]), direct and through a ref', () => {
        // @ts-expect-error the type reads the empty union
        expect(() => list(string, union([]))).toThrow(/nothing fills it/)
        // @ts-expect-error the type reads the node that the entry names
        expect(() => list(string, EmptyAt)).toThrow(/nothing fills it/)
    })

    it('refuses a field that the row always writes at a union of empty options, direct and through a ref', () => {
        // @ts-expect-error the type reads each option
        expect(() => object({ a: union([never, union([])]) })).toThrow(
            /declared at `never`/,
        )
        // @ts-expect-error the type reads the node that the entry names
        expect(() => object({ a: EmptyAt })).toThrow(/declared at `never`/)
        expect(() => object({ a: optional(EmptyAt) })).not.toThrow()
    })

    it('refuses a product factor at union([]) with the never reason, direct and through a ref', () => {
        // @ts-expect-error the type gives the never reason
        expect(() => product(union([]), object({ b: string }))).toThrow(
            /holds no value/,
        )
        // @ts-expect-error the type gives the never reason through a ref
        expect(() => product(EmptyAt, object({ b: string }))).toThrow(
            /holds no value/,
        )
    })

    /** No function decides that a closure admits nothing, so a refinement is not read as empty. */
    it('admits a position at a refinement whose predicate admits nothing', () => {
        const none = refine(string, (_: string): _ is string => false)
        expect(() => list(string, none)).not.toThrow()
    })

    /**
     * A term that holds no value adds no option, so the codec is `NULL` itself. The type keeps the
     * union with the null point that it states for `never`.
     */
    it('reads nullable over a term that holds no value as the null point, direct and through a ref', () => {
        expect(nullable(union([])).def).toEqual({ kind: 'null' })
        expect(nullable(EmptyAt).def).toEqual({ kind: 'null' })
        expect(nullable(NeverAt).def).toEqual({ kind: 'null' })
        expect(nullable(EmptyAt).encode(null)).toEqual({ NULL: true })
    })
})

describe('a chain of names holds no value when its last entry holds none, at any length', () => {
    it('refuses a field that the row always writes at the end of a chain of 6 to 16 names, as the run time does', () => {
        const c6 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 6 names
        expect(() => object({ a: c6 })).toThrow(/declared at `never`/)
        const c7 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 7 names
        expect(() => object({ a: c7 })).toThrow(/declared at `never`/)
        const c8 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 8 names
        expect(() => object({ a: c8 })).toThrow(/declared at `never`/)
        const c9 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 9 names
        expect(() => object({ a: c9 })).toThrow(/declared at `never`/)
        const c10 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 10 names
        expect(() => object({ a: c10 })).toThrow(/declared at `never`/)
        const c11 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 11 names
        expect(() => object({ a: c11 })).toThrow(/declared at `never`/)
        const c12 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: ref('A11'),
            A11: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 12 names
        expect(() => object({ a: c12 })).toThrow(/declared at `never`/)
        const c13 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: ref('A11'),
            A11: ref('A12'),
            A12: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 13 names
        expect(() => object({ a: c13 })).toThrow(/declared at `never`/)
        const c14 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: ref('A11'),
            A11: ref('A12'),
            A12: ref('A13'),
            A13: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 14 names
        expect(() => object({ a: c14 })).toThrow(/declared at `never`/)
        const c15 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: ref('A11'),
            A11: ref('A12'),
            A12: ref('A13'),
            A13: ref('A14'),
            A14: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 15 names
        expect(() => object({ a: c15 })).toThrow(/declared at `never`/)
        const c16 = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: ref('A11'),
            A11: ref('A12'),
            A12: ref('A13'),
            A13: ref('A14'),
            A14: ref('A15'),
            A15: never,
        }).A0
        // @ts-expect-error the type reads the end of a chain of 16 names
        expect(() => object({ a: c16 })).toThrow(/declared at `never`/)
    })

    it('admits a field at the end of a chain of names that holds a value', () => {
        const chain = scope({
            A0: ref('A1'),
            A1: ref('A2'),
            A2: ref('A3'),
            A3: ref('A4'),
            A4: ref('A5'),
            A5: ref('A6'),
            A6: ref('A7'),
            A7: ref('A8'),
            A8: ref('A9'),
            A9: ref('A10'),
            A10: ref('A11'),
            A11: string,
        }).A0
        expect(() => object({ a: chain })).not.toThrow()
    })
})

describe('an entry carries the capabilities of the node that its ref chain names', () => {
    it('offers the set of an entry whose node writes S, N or B, direct and through a ref', () => {
        const { S, A, L } = scope({ S: string, A: ref('S'), L: string('a') })
        expect(S.set().encode(new Set(['x']))).toEqual({ SS: ['x'] })
        expect(A.set().encode(new Set(['x']))).toEqual({ SS: ['x'] })
        expect(L.set().encode(new Set(['a'] as const))).toEqual({ SS: ['a'] })
    })

    it('offers no set where the node writes another member', () => {
        const { O, B } = scope({
            O: object({ a: string }),
            B: ref('T'),
            T: boolean,
        })
        // @ts-expect-error an object writes M
        expect(() => O.set()).toThrow(TypeError)
        // @ts-expect-error a boolean writes BOOL, and DynamoDB has no set of it
        expect(() => B.set()).toThrow(/a set holds strings, numbers or binary/)
    })

    it('merges each variant of a discriminatedUnion factor that a ref names, in declared order', () => {
        const direct = scope({
            D: discriminatedUnion('kind', [
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), y: boolean }),
            ]),
        }).D
        const named = product(DissectionAt, object({ n: decimal }))
        expect(named.def).toEqual(product(direct, object({ n: decimal })).def)
        expect(named.item.encode({ kind: 'a', x: 'q', n: '1' })).toEqual({
            kind: { S: 'a' },
            x: { S: 'q' },
            n: { N: '1' },
        })
    })
})
