/**
 * An entity that contains itself.
 *
 * `object()` evaluates its spec eagerly, so before `lazy` a recursive entity could not be declared at
 * all — the constant is not initialised when the spec that names it is built. This is the shape a
 * category tree, a comment thread and a nested menu all have.
 */
import { describe, expect, it } from 'vitest'
import type { Attribute } from '../../attribute'
import {
    type AnyCodec,
    type AttributeCodec,
    array,
    CodecError,
    decimal,
    lazy,
    nullable,
    object,
    optional,
    string,
    union,
} from '../../codec'
import { leanTermOf } from '../../lean'
import { arbitraryOf, checkRoundTrip, rngFrom, shrinkOf } from '../../testing'

type Category = {
    name: string
    children?: readonly Category[]
}

const Category: AttributeCodec<Category, Attribute<'M'>> = lazy(() =>
    object({
        name: string,
        children: optional(array(Category)),
    }),
)

const tree: Category = {
    name: 'pets',
    children: [
        { name: 'dogs', children: [{ name: 'beagle' }] },
        { name: 'cats' },
    ],
}

describe('a recursive entity', () => {
    it('round-trips at depth', () => {
        expect(Category.unsafeDecode(Category.unsafeEncode(tree))).toEqual(tree)
    })

    it('nests as M all the way down', () => {
        const encoded = Category.unsafeEncode(tree) as {
            M: { children: { L: { M: { name: { S: string } } }[] } }
        }
        expect(encoded.M.children.L[0]?.M.name).toEqual({ S: 'dogs' })
    })

    it('reports where in the tree a bad row went wrong', () => {
        const broken = structuredClone(
            Category.unsafeEncode(tree),
        ) as never as {
            M: { children: { L: { M: { name: unknown } }[] } }
        }
        broken.M.children.L[1]!.M.name = { N: '7' }

        try {
            Category.unsafeDecode(broken as never)
            expect.unreachable()
        } catch (thrown) {
            expect(thrown).toBeInstanceOf(CodecError)
            const error = thrown as CodecError
            expect(error.path).toEqual(['children', 1, 'name'])
            expect(error.message).toContain('children[1].name')
        }
    })

    /** `size` bounds the recursion: the optional attribute is dropped once the budget runs out. */
    it('generates trees that terminate', () => {
        for (const seed of [1, 7, 0x5eed]) {
            const generated = arbitraryOf(Category, rngFrom(seed), 3)
            expect(() =>
                Category.unsafeEncode(generated as Category),
            ).not.toThrow()
        }
    })

    it('shrinks toward the shallower tree', () => {
        const smaller = shrinkOf(Category, tree)
        expect(smaller.length).toBeGreaterThan(0)
        for (const value of smaller) expect(value).not.toEqual(tree)
    })

    it('holds the round-trip law over generated trees', () => {
        checkRoundTrip(Category as never, {
            count: 50,
            seed: 20260827,
            size: 3,
        })
    })

    it('resolves once, not once per call', () => {
        let built = 0
        const Counted: AttributeCodec<{ n: string }> = lazy(() => {
            built++
            return object({ n: string })
        })
        Counted.unsafeEncode({ n: 'a' })
        Counted.unsafeEncode({ n: 'b' })
        Counted.unsafeDecode(Counted.unsafeEncode({ n: 'c' }))
        expect(built).toBe(1)
    })
})

type Tree = string | readonly Tree[]

/** The verdict of a union of `codec` beside `other`: whether the declaration accepts. */
const accepts = (codec: AnyCodec, other: AnyCodec): boolean => {
    try {
        union([codec, other])
        return true
    } catch {
        return false
    }
}

describe('a union that names itself', () => {
    /**
     * The union checks its options at the declaration, and the check forces the thunk that is
     * being resolved. The forced thunk names the codec being declared, and the declaration ends.
     */
    it(
        'declares when the thunk encloses the whole union, and round-trips a value',
        {
            timeout: 5000,
        },
        () => {
            const Self: AttributeCodec<Tree> = lazy(() =>
                union([string, array(Self)]),
            )
            const value: Tree = ['x', ['y']]
            expect(Self.unsafeEncode(value)).toEqual({
                L: [{ S: 'x' }, { L: [{ S: 'y' }] }],
            })
            expect(Self.unsafeDecode(Self.unsafeEncode(value))).toEqual(value)
        },
    )

    /** Where the thunk sits is a spelling. The term and each verdict are the same. */
    it(
        'gives one term and one verdict wherever the thunk sits',
        {
            timeout: 5000,
        },
        () => {
            const Self: AttributeCodec<Tree> = lazy(() =>
                union([string, array(Self)]),
            )
            const Json: AttributeCodec<Tree> = union([
                string,
                array(lazy(() => Json)),
            ])
            expect(leanTermOf(Self)).toBe(leanTermOf(Json))
            for (const other of [string, decimal])
                expect(accepts(Self, other)).toBe(accepts(Json, other))
        },
    )

    /**
     * A thunk forced before its constant exists names a codec not yet declared. The thunk
     * resolves once the constant exists.
     */
    it('resolves a thunk that was forced before its constant existed', () => {
        const Early: AttributeCodec<string> = lazy(() => Late)
        expect(() => Early.unsafeEncode('x')).toThrow(ReferenceError)
        const Late = string
        expect(Early.unsafeEncode('x')).toEqual({ S: 'x' })
    })

    /** A throw that names no undeclared codec is a defect of the caller, and reaches the caller. */
    it('surfaces a thunk that fails for any other reason', () => {
        const Broken: AttributeCodec<string> = lazy(() => {
            throw new TypeError('the caller code is wrong')
        })
        expect(() => union([decimal, array(Broken)])).toThrow(TypeError)
    })

    /**
     * **A thunk that names a codec not yet declared is a free variable, and the term of a free
     * variable does not say whether the variable reaches null.** So `nullable` refuses at
     * construction, as for any inner term that decides the null point by a function.
     */
    it('refuses a nullable of a codec not yet declared, because the null point is unknown', () => {
        const declare = () => {
            const Self: AttributeCodec<string | null> = nullable(
                lazy(() => Self),
            )
            return Self
        }
        expect(declare).toThrow(CodecError)
    })

    /**
     * The same refusal holds for a thunk that its own resolution forces again. The refusal reaches
     * the caller at each use, as a `CodecError` that names `nullable`.
     */
    it('refuses a nullable of the thunk under resolution at each use', () => {
        type Node = { v: string; next: Node | null }
        const List: AttributeCodec<Node> = lazy(() =>
            object({ v: string, next: nullable(List) }),
        )
        for (let use = 0; use < 2; use++)
            expect(() => List.unsafeEncode({ v: 'a', next: null })).toThrow(
                /^nullable:/,
            )
    })
})
