/**
 * **The nesting bound, at every codec that writes a list or a map.**
 *
 * `docs/dynamo-datatypes.md:130` allows document types nested up to 32 levels. Nothing in this
 * library checked it, so `opaque` and `native` would encode a 100-level document without complaint
 * and DynamoDB would reject the row on write — a C1 violation of the same shape as the
 * `⟨N, "5e-324"⟩` one that `number`, `literal` and `opaque` were each gated for. The model
 * over-approximates `𝔸` in depth and only in depth, so this is the host checking what the model
 * has not yet said.
 *
 * Two limits in that reference are deliberately *not* checked here, and the reasons differ.
 * Element count is unbounded — the reference says so twice — so a wide attribute is exact rather
 * than lucky. Item size (400 KB) sums over every attribute of a row, so it is checkable where an
 * item is assembled and nowhere inside one attribute's codec.
 */
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import { MAX_DOCUMENT_NESTING } from '../../attribute'
import {
    type AnyCodec,
    array,
    at as atOf,
    CodecError,
    discriminatedUnion,
    held,
    item as itemOf,
    list,
    narrow,
    nullable,
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
import { native } from '../../native'

/** `n` nested arrays around a string: `n` document levels, the string not being one. */
const nestL = (n: number): unknown => {
    let v: unknown = 'leaf'
    for (let i = 0; i < n; i++) v = [v]
    return v
}

/** The same in maps. */
const nestM = (n: number): unknown => {
    let v: unknown = 'leaf'
    for (let i = 0; i < n; i++) v = { k: v }
    return v
}

describe('the document nesting bound', () => {
    /**
     * The boundary is the one thing the reference does not settle — its sentence does not say
     * whether a scalar inside 32 lists is the 32nd level or the 33rd. These two cases pin the
     * reading actually implemented, so a disagreement with a live table shows up here as a failing
     * test naming the off-by-one rather than as a rejected write in production.
     */
    it('accepts exactly MAX_DOCUMENT_NESTING levels', () => {
        expect(opaque.encode(nestL(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
        expect(opaque.encode(nestM(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
    })

    it('refuses one more, and says which limit and by how much', () => {
        const result = opaque.encode(nestL(MAX_DOCUMENT_NESTING + 1))
        expect(result).toBeInstanceOf(CodecError)
        expect((result as CodecError).reason).toMatch(
            /nesting reaches 33 levels of list and map, and DynamoDB stores at most 32/,
        )
    })

    it('refuses in maps as well as lists', () => {
        expect(opaque.encode(nestM(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
    })

    /**
     * `native` mirrors the SDK's shape, not its willingness to write what the store refuses — the
     * same deliberate divergence as the `N` gate, and the spec asserts both sides of it.
     */
    it('applies to native, which the SDK does not check at all', () => {
        expect(native.encode(nestL(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
        expect(native.encode(nestL(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
        expect(native.encode(nestM(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
    })

    /**
     * Asked before recursing, not after. A depth that would blow the call stack has to come back as
     * a `CodecError` like every other refusal — measuring the finished attribute would crash first,
     * which is how this was found.
     */
    it('refuses a pathological depth instead of exhausting the stack', () => {
        expect(opaque.encode(nestL(20_000))).toBeInstanceOf(CodecError)
        expect(native.encode(nestL(20_000))).toBeInstanceOf(CodecError)
    })

    /** Depth is not breadth: the reference puts no limit on how many values a document holds. */
    it('leaves a wide attribute alone', () => {
        const wide = Array.from({ length: 5_000 }, (_, i) => `v${i}`)
        expect(opaque.encode(wide)).not.toBeInstanceOf(CodecError)
    })
})

/**
 * **The bound holds at every position, not only below `opaque`.** Each typed container adds one
 * level, so the store refuses what `array(array(opaque))` writes at 33 levels as much as what
 * `opaque` writes. Each row wraps `opaque` in one former. A value at 32 levels is written, and a
 * value at 33 is refused.
 */
describe('the nesting bound around a typed container', () => {
    const one = (v: unknown) => [v]
    const formers: readonly (readonly [
        string,
        AnyCodec,
        number,
        (inner: unknown) => unknown,
    ])[] = [
        ['an array', array(opaque), 1, one],
        ['an array of arrays', array(array(opaque)), 2, (v) => [[v]]],
        ['a list with a spread', list(opaque, spread(opaque)), 1, one],
        ['a list with a suffix', list(spread(string), opaque), 1, one],
        ['a tuple', list(opaque), 1, one],
        ['a record', object([string, optional(opaque)]), 1, (v) => ({ k: v })],
        ['an object', object({ a: opaque }), 1, (v) => ({ a: v })],
        [
            'an object with an optional field',
            object({ a: optional(opaque) }),
            1,
            (v) => ({ a: v }),
        ],
        ['a union', union([array(opaque), string]), 1, one],
        ['a ref', scope({ At: ref('Arr'), Arr: array(opaque) }).At, 1, one],
        [
            'a refine',
            refine(
                array(opaque),
                (x: readonly unknown[]): x is readonly unknown[] =>
                    x.length >= 0,
                {},
            ),
            1,
            one,
        ],
        [
            'a held',
            held(array(opaque), array(opaque), {
                encode: (x) => x,
                decode: (x) => x,
            }),
            1,
            one,
        ],
        [
            'a withLegacyRead with an older reader',
            withLegacyRead({ current: array(opaque), older: array(string) }),
            1,
            one,
        ],
        [
            'a withLegacyRead with a stand-in',
            object({
                a: withLegacyRead({ current: array(opaque), whenMissing: [] }),
            }),
            2,
            (v) => ({ a: [v] }),
        ],
        ['a nullable', nullable(array(opaque)), 1, one],
    ]

    it.each(formers)(
        'writes %s at exactly MAX_DOCUMENT_NESTING levels',
        (_, codec, levels, wrap) => {
            const value = wrap(nestL(MAX_DOCUMENT_NESTING - levels))
            expect(codec.encode(value as never)).not.toBeInstanceOf(CodecError)
        },
    )

    it.each(formers)(
        'refuses %s that would store more than 32 levels around opaque',
        (_, codec, levels, wrap) => {
            const value = wrap(nestL(MAX_DOCUMENT_NESTING + 1 - levels))
            expect(codec.encode(value as never)).toBeInstanceOf(CodecError)
        },
    )

    /** No codec walks the data here, so only the containers can count the levels. */
    it('refuses a typed spec of 33 nested arrays with no opaque in it', () => {
        let codec: AnyCodec = string
        for (let i = 0; i < MAX_DOCUMENT_NESTING; i++) codec = array(codec)
        expect(
            codec.encode(nestL(MAX_DOCUMENT_NESTING) as never),
        ).not.toBeInstanceOf(CodecError)
        const deeper: AnyCodec = array(codec)
        expect(
            deeper.encode(nestL(MAX_DOCUMENT_NESTING + 1) as never),
        ).toBeInstanceOf(CodecError)
    })

    /** An item attribute sits inside no list and no map, so the item map adds no level. */
    it('counts an item attribute from zero, as the store does', () => {
        const entity = itemOf(object({ a: opaque }))
        expect(
            entity.encode({ a: nestL(MAX_DOCUMENT_NESTING) }),
        ).not.toBeInstanceOf(CodecError)
        expect(
            entity.encode({ a: nestL(MAX_DOCUMENT_NESTING + 1) }),
        ).toBeInstanceOf(CodecError)
    })
})

/**
 * **A recursive entity takes its depth from the value**, so no declaration bounds it. The
 * container that would write the 33rd level refuses, and the refusal names its position.
 */
describe('the nesting bound in a recursive entity', () => {
    type Tree = readonly Tree[]
    const { Tree } = scope({ Tree: array(ref('Tree')) })

    /** `n` levels of list, the innermost one empty. */
    const nestTree = (n: number): Tree => {
        let v: Tree = []
        for (let i = 1; i < n; i++) v = [v]
        return v
    }

    it('writes a recursive entity at exactly MAX_DOCUMENT_NESTING levels', () => {
        expect(
            Tree.encode(nestTree(MAX_DOCUMENT_NESTING) as never),
        ).not.toBeInstanceOf(CodecError)
    })

    it('refuses a recursive entity at the 33rd level, and names the position', () => {
        const result = Tree.encode(nestTree(MAX_DOCUMENT_NESTING + 1) as never)
        expect(result).toBeInstanceOf(CodecError)
        expect((result as CodecError).reason).toMatch(
            /nesting reaches 33 levels of list and map, and DynamoDB stores at most 32/,
        )
        expect((result as CodecError).path).toEqual(
            Array.from({ length: MAX_DOCUMENT_NESTING }, () => 0),
        )
    })

    /** A self-nesting object costs two levels a turn, and the bound counts both. */
    it('refuses a self-nesting object at the 33rd level', () => {
        type Category = { name: string; children?: readonly Category[] }
        const { Category } = scope({
            Category: object({
                name: string,
                children: optional(array(ref('Category'))),
            }),
        })
        // the leaf is one map, and each turn adds a list and a map
        const nest = (turns: number): Category => {
            let v: Category = { name: 'leaf' }
            for (let i = 0; i < turns; i++) v = { name: 'node', children: [v] }
            return v
        }
        expect(Category.encode(nest(15) as never)).not.toBeInstanceOf(
            CodecError,
        )
        expect(Category.encode(nest(16) as never)).toBeInstanceOf(CodecError)
    })

    it('refuses a pathological recursive depth instead of exhausting the stack', () => {
        expect(Tree.encode(nestTree(20_000) as never)).toBeInstanceOf(
            CodecError,
        )
    })
})

/**
 * **A write at a path counts the levels the path crosses.** `at` encodes below the item root, so
 * the value it writes sits inside the maps and lists of the path. The item root is no level, and
 * each segment past the first crosses one `M` or `L`. Each row names the levels its path crosses.
 */
describe('the nesting bound at a path', () => {
    type Node = { next?: Node }
    const { Node } = scope({ Node: object({ next: optional(ref('Node')) }) })

    const anObject = itemOf(object({ a: object({ b: opaque }) }))
    const aList = itemOf(object({ xs: array(array(opaque)) }))
    const aRecursive = itemOf(object({ root: Node }))
    const aUnion = itemOf(
        object({
            u: union([object({ x: opaque }), object({ w: string })]),
        }),
    )
    const aDiscriminated = itemOf(
        object({
            d: discriminatedUnion('t', [
                object({ t: string('A'), x: opaque }),
                object({ t: string('B'), x: opaque }),
            ]),
        }),
    )
    const anOpenRest = itemOf(object([string, optional(object({ y: opaque }))]))
    const aTuple = itemOf(
        object({
            tup: list(object({ w: string }), object({ z: opaque })),
        }),
    )

    /** `n` levels of map, the innermost one empty. */
    const nestNode = (n: number): Node => {
        let v: Node = {}
        for (let i = 1; i < n; i++) v = { next: v }
        return v
    }

    const paths: readonly (readonly [
        string,
        { readonly encode: (value: never) => unknown },
        { readonly encode: (item: never) => unknown },
        number,
        (levels: number) => unknown,
        (value: unknown) => unknown,
    ])[] = [
        [
            'an object path',
            atOf(anObject, ['a', 'b']),
            anObject,
            1,
            nestL,
            (v) => ({ a: { b: v } }),
        ],
        [
            'a list path',
            atOf(aList, ['xs', 0, 0]),
            aList,
            2,
            nestL,
            (v) => ({ xs: [[v]] }),
        ],
        [
            'a recursive path',
            atOf(aRecursive, ['root', 'next', 'next', 'next']),
            aRecursive,
            3,
            nestNode,
            (v) => ({ root: { next: { next: { next: v } } } }),
        ],
        [
            'a union path',
            atOf(narrow(atOf(aUnion, ['u']), { x: opaque }), ['x']),
            aUnion,
            1,
            nestL,
            (v) => ({ u: { x: v } }),
        ],
        [
            'a discriminated union path',
            atOf(aDiscriminated, ['d', 'x']),
            aDiscriminated,
            1,
            nestL,
            (v) => ({ d: { t: 'A', x: v } }),
        ],
        [
            'an open rest path',
            atOf(anOpenRest, ['k', 'y']),
            anOpenRest,
            1,
            nestL,
            (v) => ({ k: { y: v } }),
        ],
        [
            'a tuple path',
            atOf(aTuple, ['tup', 1, 'z']),
            aTuple,
            2,
            nestL,
            (v) => ({ tup: [{ w: 's' }, { z: v }] }),
        ],
    ]

    it.each(paths)(
        'writes at %s the value that fills the last level',
        (_, at, __, crossed, nest) => {
            const value = nest(MAX_DOCUMENT_NESTING - crossed)
            expect(at.encode(value as never)).not.toBeInstanceOf(CodecError)
        },
    )

    it.each(paths)(
        'refuses at %s the value that reaches the 33rd level, and names the reason',
        (_, at, __, crossed, nest) => {
            const result = at.encode(
                nest(MAX_DOCUMENT_NESTING + 1 - crossed) as never,
            )
            expect(result).toBeInstanceOf(CodecError)
            expect((result as CodecError).reason).toMatch(
                /nesting reaches 33 levels of list and map, and DynamoDB stores at most 32/,
            )
        },
    )

    it.each(paths)(
        'a write at %s agrees with the write of the whole item',
        (_, at, item, crossed, nest, wrap) => {
            for (const levels of [
                MAX_DOCUMENT_NESTING - crossed,
                MAX_DOCUMENT_NESTING + 1 - crossed,
            ]) {
                const value = nest(levels)
                expect(at.encode(value as never) instanceof CodecError).toBe(
                    item.encode(wrap(value) as never) instanceof CodecError,
                )
            }
        },
    )

    /** A path of one segment names an item attribute, which sits inside no list and no map. */
    it('counts a path of one segment from zero, as the item does', () => {
        const at = atOf(itemOf(object({ a: opaque })), ['a'])
        expect(at.encode(nestL(MAX_DOCUMENT_NESTING))).not.toBeInstanceOf(
            CodecError,
        )
        expect(at.encode(nestL(MAX_DOCUMENT_NESTING + 1))).toBeInstanceOf(
            CodecError,
        )
    })
})

/**
 * **The read side of the bound.** A decode returns a value that the encode writes back, and the
 * encode refuses past the bound. So a stored attribute past the bound is refused on the read, at
 * the same level, and not read into a value that no write accepts.
 */
describe('the nesting bound on a read', () => {
    /** The stored form of `n` nested lists around a string. */
    const storedL = (n: number): AttributeValue => {
        let v: AttributeValue = { S: 'leaf' }
        for (let i = 0; i < n; i++) v = { L: [v] }
        return v
    }

    /** The same in maps. */
    const storedM = (n: number): AttributeValue => {
        let v: AttributeValue = { S: 'leaf' }
        for (let i = 0; i < n; i++) v = { M: { k: v } }
        return v
    }

    /** `n` levels of stored list, the innermost one empty. */
    const storedTree = (n: number): AttributeValue => {
        let v: AttributeValue = { L: [] }
        for (let i = 1; i < n; i++) v = { L: [v] }
        return v
    }

    const refusesPastTheStore = (result: unknown) => {
        expect(result).toBeInstanceOf(CodecError)
        expect((result as CodecError).reason).toMatch(
            /nesting reaches 33 levels of list and map, and DynamoDB stores at most 32/,
        )
    }

    it('a decode refuses an attribute that the store could not hold, so every decode encodes back', () => {
        refusesPastTheStore(opaque.decode(storedL(MAX_DOCUMENT_NESTING + 1)))
        refusesPastTheStore(opaque.decode(storedM(MAX_DOCUMENT_NESTING + 1)))
        refusesPastTheStore(native.decode(storedL(MAX_DOCUMENT_NESTING + 1)))

        type Tree = readonly Tree[]
        const { Tree } = scope({ Tree: array(ref('Tree')) })
        refusesPastTheStore(Tree.decode(storedTree(MAX_DOCUMENT_NESTING + 1)))

        const item = itemOf(object({ a: opaque }))
        const tooDeep = item.decode({ a: storedL(MAX_DOCUMENT_NESTING + 1) })
        refusesPastTheStore(tooDeep)
        expect((tooDeep as CodecError).path).toEqual([
            'a',
            ...Array.from({ length: MAX_DOCUMENT_NESTING }, () => 0),
        ])

        const either = union([object({ a: opaque }), object({ b: string })])
        refusesPastTheStore(
            itemOf(either).decode({ a: storedL(MAX_DOCUMENT_NESTING + 1) }),
        )

        // at the bound, each read encodes back
        const read = opaque.decode(storedL(MAX_DOCUMENT_NESTING))
        expect(read).not.toBeInstanceOf(CodecError)
        expect(opaque.encode(read)).toEqual(storedL(MAX_DOCUMENT_NESTING))
        const readTree = Tree.decode(storedTree(MAX_DOCUMENT_NESTING))
        expect(readTree).not.toBeInstanceOf(CodecError)
        expect(Tree.encode(readTree as Tree)).toEqual(
            storedTree(MAX_DOCUMENT_NESTING),
        )
    })

    /** A path of two segments reads an attribute that sits inside one map. */
    it('counts the level of a path on a read, as on a write', () => {
        const at = atOf(itemOf(object({ a: object({ b: opaque }) })), [
            'a',
            'b',
        ])
        expect(at.decode(storedL(MAX_DOCUMENT_NESTING - 1))).not.toBeInstanceOf(
            CodecError,
        )
        refusesPastTheStore(at.decode(storedL(MAX_DOCUMENT_NESTING)))
    })

    /** The walk stops at the bound, so a pathological attribute is a refusal and not a crash. */
    it('refuses a read far past the bound without exhausting the call stack', () => {
        refusesPastTheStore(opaque.decode(storedL(100_000)))
    })
})
