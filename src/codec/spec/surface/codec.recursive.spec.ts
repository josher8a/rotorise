/**
 * An entity that contains itself.
 *
 * `object()` evaluates its spec eagerly, so a recursive entity names itself with a `ref` in a
 * `scope`, and the scope binds the name. This is the shape a category tree, a comment thread and a
 * nested menu all have.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    at,
    boolean,
    CodecError,
    discriminatedUnion,
    held,
    list,
    mdunion,
    nullable,
    object,
    opaque,
    optional,
    path,
    ref,
    refine,
    scope,
    string,
    union,
    withLegacyRead,
} from '../../codec'
import { arbitraryOf, checkRoundTrip, rngFrom, shrinkOf } from '../../testing'

type Category = {
    name: string
    children?: readonly Category[]
}

const { Category } = scope({
    Category: object({
        name: string,
        children: optional(array(ref('Category'))),
    }),
})

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
        expect(Category.unsafeEncode(tree)).toMatchObject({
            M: {
                children: {
                    L: [
                        { M: { name: { S: 'dogs' } } },
                        { M: { name: { S: 'cats' } } },
                    ],
                },
            },
        })
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
})

type Tree = string | readonly Tree[]

describe('a union that names itself', () => {
    /**
     * The union waits for the scope, and the scope binds the name before the union checks its
     * options. The list on the path guards the recursion, and the declaration ends.
     */
    it(
        'declares a union that names itself through a ref, and round-trips a value',
        {
            timeout: 5000,
        },
        () => {
            const { Self } = scope({
                Self: union([string, array(ref('Self'))]),
            })
            const value: Tree = ['x', ['y']]
            expect(Self.unsafeEncode(value)).toEqual({
                L: [{ S: 'x' }, { L: [{ S: 'y' }] }],
            })
            expect(Self.unsafeDecode(Self.unsafeEncode(value))).toEqual(value)
        },
    )

    /**
     * **A use needs a closed codec.** A `ref` that no scope binds yet is an open fragment: the type
     * refuses a use, and the run time refuses a use with the free name. The scope that binds the
     * name closes the fragment, and the entry is the codec to use.
     */
    it('refuses a use of a ref that no scope binds, by name, and resolves the entry once a scope binds it', () => {
        const Early = ref('Late')
        // @ts-expect-error a use needs a closed codec, and the ref reads 'Late'
        expect(() => Early.unsafeEncode('x')).toThrow(
            /this codec reads 'Late' through a `ref` that no scope binds/,
        )
        const bound = scope({ Early, Late: string })
        expect(bound.Early.unsafeEncode('x')).toEqual({ S: 'x' })
    })

    /**
     * **A refusal is a value inside the boundary.** A use of an open fragment refuses, so the safe
     * pair returns the refusal, and only the unsafe pair throws.
     */
    it('returns the refusal of an open fragment that a decode reads, and does not throw', () => {
        const List = object({ v: string, next: nullable(ref('List')) })
        // @ts-expect-error a use needs a closed codec
        const read = List.decode({ M: { v: { S: 'a' }, next: { NULL: true } } })
        expect(read).toBeInstanceOf(CodecError)
        expect(String(read)).toMatch(/reads 'List' through a `ref`/)
        // @ts-expect-error a use needs a closed codec
        expect(List.encode({ v: 'a', next: null })).toBeInstanceOf(CodecError)
        // @ts-expect-error a use needs a closed codec
        expect(() => List.unsafeEncode({ v: 'a', next: null })).toThrow(
            /reads 'List' through a `ref`/,
        )
    })

    /**
     * **A refusal is a value on the path that `at` returns.** The walk of `at` over an open
     * fragment returns a codec that refuses, and keeps the path, because the path needs no codec.
     */
    it('returns the refusal of an open fragment that the walk of at reads, and does not throw', () => {
        const List = object({ v: string, next: nullable(ref('List')) })
        const Doc = object({ head: List }).item
        // @ts-expect-error a use needs a closed codec
        const located = at(Doc, (p) => p.head.v)
        expect(path(located)).toBe('head.v')
        const written = located.encode('a')
        expect(written).toBeInstanceOf(CodecError)
        expect(String(written)).toMatch(/reads 'List' through a `ref`/)
        expect(located.decode({ S: 'a' })).toBeInstanceOf(CodecError)
        expect(() => located.unsafeEncode('a')).toThrow(/reads 'List'/)
    })

    /**
     * **A `nullable` over a `ref` that names its own entry, with no container between, reads its own
     * input.** The `nullable` waits for the scope, and the scope refuses the recursion.
     */
    it('refuses a nullable that names its own entry with no container between, at the scope', () => {
        const unguarded =
            /\[scope\] 'Self' reaches a recursion with no list or object on its path/
        expect(() => scope({ Self: nullable(ref('Self')) })).toThrow(unguarded)
        expect(() => scope({ Self: nullable(nullable(ref('Self'))) })).toThrow(
            unguarded,
        )
    })

    /**
     * **The null point of a `ref` is known once the scope binds the name.** A `nullable` over a
     * `ref` waits for the scope, and asks the question there, so a nullable recursive field needs
     * no other spelling.
     */
    it('declares a nullable recursive field, because nullable waits for the scope', () => {
        type Node = { v: string; next: Node | null }
        const { List } = scope({
            List: object({ v: string, next: nullable(ref('List')) }),
        })
        const chain: Node = { v: 'a', next: { v: 'b', next: null } }
        expect(List.unsafeEncode(chain)).toEqual({
            M: {
                v: { S: 'a' },
                next: { M: { v: { S: 'b' }, next: { NULL: true } } },
            },
        })
        expect(List.unsafeDecode(List.unsafeEncode(chain))).toEqual(chain)
        expect(
            List.decode({ M: { v: { S: 'a' }, next: { S: 'b' } } }),
        ).toBeInstanceOf(CodecError)
    })

    /**
     * **A `nullable` over a `ref` refuses at the scope where the term does not decide the null
     * point.** The adapter decides the null point by running a function that the term cannot read.
     * The scope runs the check of the `nullable`, so the refusal lands at the declaration and not at
     * a later use.
     */
    it('refuses at the scope a nullable whose ref names an adapter, because the null point is unknown', () => {
        const declare = () =>
            scope({
                Node: object({ v: string, next: nullable(ref('Held')) }),
                Held: held(nullable(string), string, {
                    encode: (v: string) => v,
                    decode: (v: string | null) => v ?? '',
                }),
            })
        expect(declare).toThrow(/^ref and null are not shown compatible/)
    })

    /**
     * **The walk of `at` crosses a `nullable` over a `ref`.** The walk forces the thunk that the
     * path crosses, and the scope already resolved it, so the located codec writes the leaf.
     */
    it('walks at through a nullable ref, because nullable waits for the scope', () => {
        const { List } = scope({
            List: object({ v: string, next: nullable(ref('List')) }),
        })
        const Doc = object({ head: List }).item
        const located = at(Doc, (p) => p.head.next.v)
        expect(path(located)).toBe('head.next.v')
        expect(located.encode('a')).toEqual({ S: 'a' })
        expect(located.decode({ S: 'a' })).toBe('a')
    })
})

/**
 * **The model's guard refuses a recursion that reads the input of its own binder.** With no list or
 * object on the path, each stage reads the same input, and encode overflows the stack. The scope
 * refuses such a cycle where it binds the names, as `union` refuses such an option.
 */
describe('a recursion is refused or accepted where it is declared, as the model guards each binder', () => {
    it('a recursion that reads its own input with no list or object between is refused where it is declared', () => {
        const between = /reaches a recursion with no list or object on its path/
        expect(() => scope({ X: ref('X') })).toThrow(between)
        expect(() => scope({ P: ref('Q'), Q: ref('P') })).toThrow(between)
    })

    it('a union accepts a guarded recursion that it reaches through options and refs with no container', () => {
        const { Tree, Twice, Self } = scope({
            Tree: object({ kids: array(ref('Tree')) }),
            Twice: ref('Once'),
            Once: ref('Tree'),
            Self: union([string, array(ref('Self'))]),
        })
        const options = union([string, Tree])
        expect(options.unsafeEncode({ kids: [{ kids: [] }] })).toEqual({
            M: { kids: { L: [{ M: { kids: { L: [] } } }] } },
        })
        expect(() => union([string, Twice])).not.toThrow()
        expect(Self.unsafeEncode(['x'])).toEqual({ L: [{ S: 'x' }] })
    })

    it('a ref that two positions share without a cycle is no recursion', () => {
        const shared = scope({ At: ref('S'), S: string }).At
        const Pair = object({ a: shared, b: optional(shared) })
        expect(Pair.unsafeEncode({ a: 'x', b: 'y' })).toEqual({
            M: { a: { S: 'x' }, b: { S: 'y' } },
        })
        expect(() => array(object({ a: shared, b: shared }))).not.toThrow()
    })
})

/**
 * **A `ref` that closes no cycle is the codec of its entry.** Each former reads the `ref` as a free
 * variable, so the former builds an open fragment, and the scope runs the guard and each waiting
 * check with the name bound. So a former directly over a `ref` gives the verdict that the codec of
 * the entry gives in its place, where the model's guard accepts the term.
 */
describe('a former directly over a ref', () => {
    it('accepts a held directly over a ref, and converts through the entry', () => {
        const { When } = scope({
            When: held(ref('Text'), string, {
                encode: (v: string) => v.toLowerCase(),
                decode: (v: unknown) => String(v).toUpperCase(),
            }),
            Text: string,
        })
        expect(When.unsafeEncode('AB')).toEqual({ S: 'ab' })
        expect(When.unsafeDecode({ S: 'ab' })).toBe('AB')
    })

    it('accepts a refine directly over a ref, and refuses what the predicate refuses', () => {
        const { Named } = scope({
            Named: refine(ref('Text'), (v: unknown): v is string => v !== '', {
                describe: 'a name that is not empty',
            }),
            Text: string,
        })
        expect(Named.unsafeEncode('a')).toEqual({ S: 'a' })
        expect(Named.encode('')).toBeInstanceOf(CodecError)
    })

    it('accepts an older reader directly over a ref, and reads the older encoding', () => {
        const { Rate } = scope({
            Rate: withLegacyRead({
                current: ref('Text'),
                older: {
                    decode: (attribute) =>
                        attribute.N === undefined
                            ? new CodecError('no older rate')
                            : attribute.N,
                },
            }),
            Text: string,
        })
        expect(Rate.unsafeDecode({ S: '1.5' })).toBe('1.5')
        expect(Rate.unsafeDecode({ N: '1.5' })).toBe('1.5')
    })

    /**
     * **A tag that a `ref` names is read when the scope binds the name.** The index of the
     * dissection reads the literal of each tag through the `ref`, so the index waits for the scope.
     * The type of a `ref` is its name alone, and carries no literal, so the type refuses the tag.
     */
    it('keys a variant by a tag that a ref names, once the scope binds the name', () => {
        const { Visit } = scope({
            Checkup: string('CHECKUP'),
            // @ts-expect-error the type of a ref carries no literal for the tag
            Visit: discriminatedUnion('type', [
                object({ type: ref('Checkup'), petId: string }),
                object({ type: string('SHOT'), vaccine: string }),
            ]),
        })
        const read = Visit.decode({
            M: { type: { S: 'CHECKUP' }, petId: { S: 'p' } },
        })
        expect(read).toEqual({ type: 'CHECKUP', petId: 'p' })
        const { Byway } = scope({
            Pet: string('pet'),
            Byway: mdunion(
                ['kind'],
                // @ts-expect-error the type of a ref carries no literal for the tag
                [
                    object({ kind: ref('Pet'), toy: string }),
                    object({ kind: string('food'), gram: string }),
                ],
            ),
        })
        expect(
            Byway.decode({ M: { kind: { S: 'pet' }, toy: { S: 't' } } }),
        ).toEqual({ kind: 'pet', toy: 't' })
    })
})

/**
 * **A spelling through a ref draws the same values.** A `ref` that closes no cycle spells its
 * target in place, so the arbitrary reads the target with no draw of its own and no step of the
 * budget. A pool that spells a leaf behind a `ref` then draws the same codecs as the plain pool.
 */
describe('a spelling through a ref draws the same values', () => {
    it('draws one value sequence for a term and for the same term behind a ref', () => {
        const behind = <C>(codec: C): C =>
            scope({ At: ref('It'), It: codec as never }).At as never
        const plain = list(boolean, opaque)
        const spelled = list(behind(boolean), behind(opaque))
        for (const seed of [1, 2, 3, 4, 5, 6, 7, 8]) {
            const counted = () => {
                const base = rngFrom(seed)
                const rng = { draws: 0, next: () => 0 }
                rng.next = () => {
                    rng.draws++
                    return base()
                }
                return rng
            }
            const a = counted()
            const b = counted()
            expect(arbitraryOf(spelled, b.next, 2)).toEqual(
                arbitraryOf(plain, a.next, 2),
            )
            expect(b.draws).toBe(a.draws)
        }
    })
})
