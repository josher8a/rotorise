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
    type AttributeCodec,
    array,
    CodecError,
    lazy,
    object,
    optional,
    string,
} from '../../codec'
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
