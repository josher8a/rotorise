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
    list,
    never,
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

/** `It`, named through the `ref` of the entry `At`. */
const NeverAt = scope({ At: ref('It'), It: never }).At
const ObjectAt = scope({ At: ref('It'), It: object({ a: string }) }).At
const KeysAt = scope({ K: ref('L'), L: string('a', 'b') }).K
const OptionAt = scope({
    X: ref('Y'),
    Y: object({ t: string('a'), x: string }),
}).X
const StringAt = scope({ At: ref('It'), It: string }).At

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
        expect(() => U.extract({ b: decimal('1') })).not.toThrow()
        expect(() => U.exclude({ b: decimal('2.5') })).not.toThrow()
    })
})
