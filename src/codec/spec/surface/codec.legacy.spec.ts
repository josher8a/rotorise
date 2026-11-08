/**
 * Reading what a table already holds.
 *
 * A table holds every shape it has ever held. The hand-written reconciliation is
 * `holding: item.holding ?? 'STORE_V1'` at every read site, which is once per place to forget. Two
 * things are going on there and they are worth keeping apart: an attribute that is *absent*, and
 * an attribute written in an encoding that is no longer the current one.
 */
import { describe, expect, it, vi } from 'vitest'
import type { AttributeMap, AttributeValue } from '../../attribute'
import { DynamoNumber } from '../../attribute'
import {
    andThen,
    array,
    binary,
    CodecError,
    decimal,
    dynamoNumber,
    fill,
    held,
    item,
    legacy,
    object,
    optional,
    ref,
    refine,
    scope,
    string,
    union,
} from '../../codec'
import { orThrow } from '../../result'
import type { StandardSchemaV1 } from '../../standard'
import { checkMembersStable, checkRoundTrip } from '../../testing'

/** A Standard Schema v1 written by hand, that admits every value: the held side is not the subject. */
const anything = <T>(): StandardSchemaV1<T> => ({
    '~standard': {
        version: 1,
        vendor: 'handwritten',
        validate: (value) => ({ value: value as T }),
    },
})

type Listing = {
    id: string
    /** added later; older rows have no such attribute */
    holding: 'STORE_V1' | 'STORE_V2'
    /** added later too */
    vendorId: 'PICKUP' | 'ACME'
    /** was written as a number for a while, and is a decimal string now */
    rate: string
}

const Listing = item(
    object({
        id: string,
        holding: fill(string('STORE_V1', 'STORE_V2'), 'STORE_V1' as const),
        vendorId: fill(string('PICKUP', 'ACME'), 'PICKUP' as const),
        rate: legacy({ current: decimal, older: string }),
    }),
)

/**
 * An older encoding whose *held* type is not the current one, and a table that has held three.
 *
 * Two things at once. `older` asks for a reader and not a codec, because digits stored as `B` by a
 * migration nobody finished read back as a `Uint8Array` rather than the `string` `decimal` holds — and
 * converting that with `held` would mean writing an encode path `legacy` never calls, since it writes
 * `current` and only `current`.
 *
 * And it takes *one* older encoding, so three encodings are two of these nested — `legacy` is itself
 * a reader. Not a union: a union needs its options to read back as different types so a value says
 * which it is, and every encoding of one attribute reads back as the same type by definition.
 */
describe('an older encoding held as something else', () => {
    const decoder = new TextDecoder()
    const Priced = item(
        object({
            id: string,
            price: legacy({
                current: decimal,
                older: legacy({
                    current: string,
                    older: {
                        decode: (at: AttributeValue) =>
                            andThen(binary.decode(at), (bytes) =>
                                decoder.decode(bytes),
                            ),
                    },
                }),
            }),
        }),
    )

    it('reads the current encoding', () => {
        expect(
            Priced.unsafeDecode({ id: { S: 'p' }, price: { N: '1.5' } }).price,
        ).toBe('1.5')
    })

    it('reads an older one of the same held type', () => {
        expect(
            Priced.unsafeDecode({ id: { S: 'p' }, price: { S: '1.5' } }).price,
        ).toBe('1.5')
    })

    it('and one that had to be converted to reach it', () => {
        expect(
            Priced.unsafeDecode({
                id: { S: 'p' },
                price: { B: new TextEncoder().encode('1.5') },
            }).price,
        ).toBe('1.5')
    })

    it('writes only the current encoding, whichever it read', () => {
        const fromBytes = Priced.unsafeDecode({
            id: { S: 'p' },
            price: { B: new TextEncoder().encode('1.5') },
        })
        expect(Priced.unsafeEncode(fromBytes).price).toEqual({ N: '1.5' })
    })

    it('and still refuses an attribute no encoding reads', () => {
        expect(() =>
            Priced.unsafeDecode({ id: { S: 'p' }, price: { BOOL: true } }),
        ).toThrow(CodecError)
    })
})

describe('an attribute the row does not have', () => {
    it('reads as the value the entity says it has', () => {
        const old: AttributeMap = { id: { S: 'o1' }, rate: { N: '1.5' } }
        expect(Listing.unsafeDecode(old)).toEqual({
            id: 'o1',
            holding: 'STORE_V1',
            vendorId: 'PICKUP',
            rate: '1.5',
        })
    })

    it('does not stand in for one that is there', () => {
        const stored: AttributeMap = {
            id: { S: 'o1' },
            holding: { S: 'STORE_V2' },
            vendorId: { S: 'ACME' },
            rate: { N: '1.5' },
        }
        expect(Listing.unsafeDecode(stored).holding).toBe('STORE_V2')
        expect(Listing.unsafeDecode(stored).vendorId).toBe('ACME')
    })

    it('is written every time, so a row read once stops being old', () => {
        const old: AttributeMap = { id: { S: 'o1' }, rate: { N: '1.5' } }
        expect(Listing.unsafeEncode(Listing.unsafeDecode(old)).holding).toEqual(
            {
                S: 'STORE_V1',
            },
        )
    })

    it('is not the same as optional, which says the entity may lack it', () => {
        // the entity type says `holding` is always there; only the data may not have it
        const back: Listing = Listing.unsafeDecode({
            id: { S: 'o1' },
            rate: { N: '1' },
        })
        expect(back.holding).toBe('STORE_V1')
    })

    /**
     * **A union reads a row without the name to one value, so a fill value needs a partner that
     * reads no such row.** The field with a fill value reads a map without the name to a value
     * with the name. An `optional` field reads the same map to a value without the name, so the
     * two options read one attribute to two values, and the order of the options would choose.
     * A `req` field reads no map without the name, so the two agree.
     */
    it('refuses a union beside an optional field, and declares it beside a required one', () => {
        const filled = object({
            a: fill(string, 'z'),
        })
        expect(() => union([filled, object({ a: optional(string) })])).toThrow(
            CodecError,
        )
        const either = union([filled, object({ a: string })])
        expect(either.unsafeDecode({ M: {} })).toEqual({ a: 'z' })
        expect(either.unsafeDecode({ M: { a: { S: 'b' } } })).toEqual({
            a: 'b',
        })
    })

    /**
     * **A copy per read, so a mutable fill value cannot be shared between entities.**
     *
     * The declaration holds one value — that is what makes the rule `(fill)`'s premise checkable
     * where the declaration is, rather than on whichever read reaches it first — and each read
     * that needs one gets a `structuredClone`. Both halves matter and this asserts both: the
     * value is right, and it is not the *same* value twice.
     *
     * The failure this pins is a caller mutating what they decoded. It shipped once as the
     * opposite behaviour and the two assertions below were `toEqual(['x'])` and `toBe(a.tags)`.
     */
    it('is a copy per read, not one shared value', () => {
        const C = item(
            object({
                id: string,
                tags: fill({ ...listOfStrings }, []),
            }),
        )
        const a = C.unsafeDecode({ id: { S: 'a' } })
        const b = C.unsafeDecode({ id: { S: 'b' } })
        a.tags.push('x')
        expect(b.tags).toEqual([])
        expect(b.tags).not.toBe(a.tags)
    })

    /** A primitive is handed over as it is: there is nothing to copy and nothing to leak. */
    it('does not copy a primitive fill value', () => {
        const C = item(
            object({
                id: string,
                tier: fill(string, 'FREE'),
            }),
        )
        expect(C.unsafeDecode({ id: { S: 'a' } }).tier).toBe('FREE')
    })

    /**
     * **A decode is writable, so the copy keeps the class of each value in the fill value.**
     *
     * `structuredClone` turns an instance of a class the platform does not know into a plain
     * object. A `DynamoNumber` fill value then decoded to `{ digits: '1' }`, and the encode of that
     * decode refused it as not a `DynamoNumber`. The element of an array failed the same way.
     */
    it('decodes a fill value that holds a DynamoNumber to a value that encodes back', () => {
        const one = orThrow(DynamoNumber.from('1'))
        const C = object({
            b: fill(dynamoNumber, one),
            bs: fill(array(dynamoNumber), [one]),
        })
        const read = C.unsafeDecode({ M: {} })
        expect(read.b).toBeInstanceOf(DynamoNumber)
        expect(read.bs[0]).toBeInstanceOf(DynamoNumber)
        expect(C.unsafeEncode(read)).toEqual({
            M: { b: { N: '1' }, bs: { L: [{ N: '1' }] } },
        })
    })

    /**
     * **And the one value that cannot be copied is shared, rather than throwing on a read.**
     *
     * `structuredClone` refuses anything holding a function. No declared codec admits such a
     * value — a fill value comes from the value language, and all of that clones — but an adapter's
     * read hands back whatever its own function builds, so a codec can admit one. The
     * cloneability is settled at the declaration, so this is a shared fill value and not a
     * `DataCloneError` arriving out of a `decode` months later.
     */
    it('shares a fill value structuredClone refuses, rather than failing the read', () => {
        type Holder = { tag: string; run: () => number }
        const holding = held(string, anything<Holder>(), {
            encode: (value: Holder) => value.tag,
            decode: () => ({ tag: 'x', run: () => 1 }),
        })
        const stand: Holder = { tag: 'x', run: () => 1 }
        expect(() => structuredClone(stand)).toThrow()

        const C = item(
            object({
                id: string,
                h: fill(holding, stand),
            }),
        )
        const a = C.unsafeDecode({ id: { S: 'a' } })
        const b = C.unsafeDecode({ id: { S: 'b' } })
        expect(a.h).toBe(b.h)
    })
})

/**
 * **A fill value that the codec writes through a `ref`.** The scope that binds the `ref` checks the
 * fill value on the closed copy. So an unwritable fill value still refuses, at the scope.
 */
describe('a fill value for a recursive codec', () => {
    type Leaf = { end: string } | { name: string; next: Leaf }

    it('a recursion with a fill value encodes and decodes, and a read that lacks the attribute fills it', () => {
        const { Leaf } = scope({
            Leaf: union([
                object({ end: string }),
                object({
                    name: string,
                    next: fill(ref('Leaf'), { end: 'x' }),
                }),
            ]),
        })
        const value: Leaf = { name: 'a', next: { end: 'b' } }
        const written = Leaf.encode(value)
        expect(written).not.toBeInstanceOf(CodecError)
        expect(Leaf.decode(written as AttributeValue)).toEqual(value)
        expect(Leaf.decode({ M: { name: { S: 'a' } } })).toEqual({
            name: 'a',
            next: { end: 'x' },
        })
    })

    it('an unwritable fill value for a recursive codec refuses at the scope, and names the reason', () => {
        const declare = () =>
            scope({
                Ended: refine(
                    union([
                        object({ end: string }),
                        object({
                            name: string,
                            next: fill(ref('Ended'), { end: '' }),
                        }),
                    ]),
                    (leaf): leaf is Leaf => !('end' in leaf) || leaf.end !== '',
                    { describe: 'an end that is not empty' },
                ),
            })
        expect(declare).toThrow(
            /The fill value of `fill` must be a value the codec it fills can write, and this `ref` refuses the fill value: .*an end that is not empty/,
        )
        expect(declare).not.toThrow(/\[object Object\]/)
    })
})

describe('a fill value that makes the codec throw', () => {
    it('is refused at `fill`, because a row missing the attribute would read back as a value that cannot be written', () => {
        const strict = refine(string, (_text): _text is string => {
            throw new Error('the predicate read the fill value')
        })
        expect(() => fill(strict, 'x')).toThrow(
            /The fill value of `fill` must be a value the codec it fills can write, and this `refine` refuses the fill value: the predicate of this refinement threw: the predicate read the fill value/,
        )
    })
})

/**
 * **A fill value across two entries.** `Branch` writes its fill value through a `ref` to `Tree`, and
 * `Tree` reads `Branch` through a `ref`. The scope binds both names in its closed copy, then
 * checks the fill value.
 */
describe('a fill check runs on the closed copy of the scope that binds every name it writes through', () => {
    type Tree = { end: string } | Branch
    type Branch = { name: string; next: Tree }

    it('a writable fill value encodes, decodes, and fills a missing attribute', () => {
        const { Tree } = scope({
            Tree: union([object({ end: string }), ref('Branch')]),
            Branch: object({
                name: string,
                next: fill(ref('Tree'), { end: 'x' }),
            }),
        })
        const value: Tree = { name: 'a', next: { end: 'b' } }
        const written = Tree.encode(value)
        expect(written).not.toBeInstanceOf(CodecError)
        expect(Tree.decode(written as AttributeValue)).toEqual(value)
        expect(Tree.decode({ M: { name: { S: 'a' } } })).toEqual({
            name: 'a',
            next: { end: 'x' },
        })
    })

    it('an unwritable fill value refuses at the scope, and names the reason', () => {
        const declare = () =>
            scope({
                Tree: union([
                    refine(
                        object({ end: string }),
                        (end): end is { end: string } => end.end !== '',
                        { describe: 'an end that is not empty' },
                    ),
                    ref('Branch'),
                ]),
                Branch: object({
                    name: string,
                    next: fill(ref('Tree'), { end: '' }),
                }),
            })
        expect(declare).toThrow(
            /The fill value of `fill` must be a value the codec it fills can write, and this `ref` refuses the fill value: .*no option admits this value/,
        )
    })
})

/**
 * **The first use through either entry.** The scope runs the check of the fill value before any use,
 * so the entry used first decides nothing. Each order runs in a fresh module instance, so no state
 * that an earlier use left in the module decides the verdict.
 */
describe('a fill verdict does not depend on which recursive entry is used first', () => {
    type Tree = { end: string } | Branch
    type Branch = { name: string; next: Tree }

    const declare = async () => {
        vi.resetModules()
        const { CodecError, fill, object, ref, scope, string, union } =
            await import('../../codec')
        const { Tree, Branch } = scope({
            Tree: union([object({ end: string }), ref('Branch')]),
            Branch: object({
                name: string,
                next: fill(ref('Tree'), { end: 'x' }),
            }),
        })
        return { CodecError, Tree, Branch }
    }
    const value: Branch = { name: 'a', next: { end: 'b' } }

    for (const first of ['Tree', 'Branch'] as const) {
        it(`a writable fill value encodes, decodes, and fills a missing attribute when ${first} is used first`, async () => {
            const codecs = await declare()
            const written = codecs[first].encode(value)
            expect(written).not.toBeInstanceOf(codecs.CodecError)
            expect(codecs.Tree.decode(written as AttributeValue)).toEqual(value)
            expect(codecs.Branch.decode({ M: { name: { S: 'a' } } })).toEqual({
                name: 'a',
                next: { end: 'x' },
            })
        })
    }
})

/**
 * **Every order of first use.** The scope runs the check before any use, so the order of first use
 * decides nothing. A fragment stays open, whether its scope refuses or not, so each fragment
 * refuses each use, and no read returns the fill value. Each order runs in a fresh module instance,
 * so no state that an earlier use left in the module decides the verdict.
 */
describe('a writable fill value is accepted and fills, and an unwritable one refuses each use, in every order of first use', () => {
    type Tree = { end: string } | Branch
    type Branch = { name: string; next: Tree }

    const declare = async () => {
        vi.resetModules()
        const { CodecError, fill, object, ref, scope, string, union } =
            await import('../../codec')
        const { Tree, Branch } = scope({
            Tree: union([object({ end: string }), ref('Branch')]),
            Branch: object({
                name: string,
                next: fill(ref('Tree'), { end: 'x' }),
            }),
        })
        const missing = { M: { name: { S: 'a' } } }
        const uses = {
            tree: () => Tree.encode({ end: 'b' }),
            branch: () => Branch.encode({ name: 'a', next: { end: 'b' } }),
            treeDecode: () => Tree.decode(missing),
            branchDecode: () => Branch.decode(missing),
        }
        return { CodecError, uses }
    }

    const orders = [
        ['tree', 'branch', 'branchDecode', 'tree', 'branch', 'branchDecode'],
        ['branch', 'branch', 'branchDecode', 'tree', 'branch', 'branchDecode'],
        ['branchDecode', 'tree', 'branch', 'branchDecode'],
        ['treeDecode', 'branch', 'tree', 'branchDecode'],
    ] as const

    const declareUnwritable = async () => {
        vi.resetModules()
        const { CodecError, fill, object, ref, refine, scope, string, union } =
            await import('../../codec')
        const Tree = refine(
            union([object({ end: string }), ref('Branch')]),
            (tree: unknown): tree is Tree =>
                typeof tree !== 'object' ||
                tree === null ||
                !('end' in tree) ||
                tree.end !== '',
            { describe: 'an end that is not empty' },
        )
        const Branch = object({
            name: string,
            next: fill(ref('Tree'), { end: '' }),
        })
        expect(() => scope({ Tree, Branch })).toThrow(
            /The fill value of `fill` must be a value the codec it fills can write/,
        )
        const missing = { M: { name: { S: 'a' } } }
        const uses = {
            // @ts-expect-error a use needs a closed codec
            tree: () => Tree.encode({ end: 'b' }),
            // @ts-expect-error a use needs a closed codec
            branch: () => Branch.encode({ name: 'a', next: { end: 'b' } }),
            // @ts-expect-error a use needs a closed codec
            treeDecode: () => Tree.decode(missing),
            // @ts-expect-error a use needs a closed codec
            branchDecode: () => Branch.decode(missing),
        }
        return { CodecError, uses }
    }

    for (const order of orders) {
        it(`an unwritable fill value refuses each use, and no read returns the fill value, in the order ${order.join(' > ')}`, async () => {
            const { CodecError, uses } = await declareUnwritable()
            for (const use of order) {
                const got = uses[use]()
                expect(got, use).toBeInstanceOf(CodecError)
                expect(String(got), use).toMatch(
                    /reads '(Tree|Branch)'(, '(Tree|Branch)')? through a `ref` that no scope binds/,
                )
            }
        })
        it(`a writable fill value is accepted and fills a missing attribute, in the order ${order.join(' > ')}`, async () => {
            const { CodecError, uses } = await declare()
            for (const use of order) {
                const got = uses[use]()
                // the row of `treeDecode` has a name and no `end`: a Branch without `next`, filled
                expect(got, use).not.toBeInstanceOf(CodecError)
                if (use === 'branchDecode' || use === 'treeDecode') {
                    expect(got, use).toEqual({ name: 'a', next: { end: 'x' } })
                }
            }
        })
    }
})

describe('an attribute written in an older encoding', () => {
    it('reads the current one', () => {
        expect(
            Listing.unsafeDecode(listingWith({ rate: { N: '1.5' } })).rate,
        ).toBe('1.5')
    })

    it('reads the older one too', () => {
        expect(
            Listing.unsafeDecode(listingWith({ rate: { S: '1.5' } })).rate,
        ).toBe('1.5')
    })

    it('writes only the current one', () => {
        const fromOld = Listing.unsafeDecode(
            listingWith({ rate: { S: '1.5' } }),
        )
        expect(Listing.unsafeEncode(fromOld).rate).toEqual({ N: '1.5' })
    })

    /**
     * **Pins wording no law has, deliberately.** The refusal is asserted as a `CodecError` beside
     * it; what the regex adds is the diagnostic, which is this test's subject. Here it is that the refusal
     * says *how many* encodings were tried, which is what tells a caller the migration ran at all
     * rather than the current reader having failed alone.
     */
    it('reports when no encoding can read it', () => {
        expect(() =>
            Listing.unsafeDecode(listingWith({ rate: { BOOL: true } })),
        ).toThrow(CodecError)
        expect(() =>
            Listing.unsafeDecode(listingWith({ rate: { BOOL: true } })),
        ).toThrow(
            /no encoding could read this attribute; tried the current one and one older/,
        )
    })

    it('a legacy whose older reader throws refuses the read as a value', () => {
        const Rate = legacy({
            current: decimal,
            older: {
                decode: () => {
                    throw new Error('the old format is gone')
                },
            },
        })
        const read = Rate.decode({ BOOL: true })
        expect(read).toBeInstanceOf(CodecError)
        expect((read as CodecError).reason).toMatch(
            /no encoding could read this attribute; tried the current one and one older: .*the older reader threw: the old format is gone/,
        )
        expect(Rate.decode({ N: '1.5' })).toBe('1.5')
    })

    it('keeps the round-trip law, because it only ever writes one shape', () => {
        checkRoundTrip(Listing, { count: 200, seed: 20260826 })
    })

    it('cannot be got backwards, because the roles are named', () => {
        // the whole point of the shape: `current` is the encoding the entity is in now
        const toNumber = legacy({ current: decimal, older: string })
        const toString = legacy({ current: string, older: decimal })

        expect(toNumber.unsafeDecode({ S: '1.5' })).toBe('1.5')
        expect(toNumber.unsafeEncode('1.5')).toEqual({ N: '1.5' })

        expect(toString.unsafeDecode({ N: '1.5' })).toBe('1.5')
        expect(toString.unsafeEncode('1.5')).toEqual({ S: '1.5' })
    })

    it('deliberately does not keep the member stable — that is the migration', () => {
        expect(() =>
            checkMembersStable(Listing, [listingWith({ rate: { S: '1.5' } })]),
        ).toThrow(CodecError)
    })
})

describe('a legacy read lands on a value that writes back at the level of the legacy', () => {
    /**
     * The premise of `legacy` is that the older reader lands on a value the current codec writes. The
     * write refuses a value that nests past what DynamoDB stores, so the premise holds at the level
     * of the row and at no other. A premise checked at level 0 reads a value that the write then
     * refuses.
     */
    it('refuses a read that its own write refuses, at every depth of the row', () => {
        const older = () => [['PET']]
        const wrapped = (depth: number) => {
            let codec: unknown = legacy({
                current: array(array(string)),
                older: { decode: older },
            } as never)
            for (let i = 0; i < depth; i++) codec = array(codec as never)
            return codec as {
                decode: (attribute: AttributeValue) => unknown
                encode: (value: never) => unknown
            }
        }
        const stored = (depth: number): AttributeValue => {
            let attribute: AttributeValue = { S: 'old' }
            for (let i = 0; i < depth; i++) attribute = { L: [attribute] }
            return attribute
        }
        const refused: number[] = []
        for (let depth = 0; depth <= 31; depth++) {
            const codec = wrapped(depth)
            const read = codec.decode(stored(depth))
            if (read instanceof Error) {
                refused.push(depth)
                continue
            }
            expect(
                codec.encode(read as never),
                `depth ${depth}`,
            ).not.toBeInstanceOf(Error)
        }
        expect(refused).not.toEqual([])
        expect(refused).toEqual(
            Array.from(
                { length: refused.length },
                (_, at) => 31 - at,
            ).reverse(),
        )
    })
})

/** An adapter whose read hands back a value its write never produced. */
const listOfStrings = held(array(string), anything<string[]>(), {
    encode: (value: string[]) => value,
    decode: () => [] as string[],
})

function listingWith(extra: AttributeMap): AttributeMap {
    return {
        id: { S: 'o1' },
        holding: { S: 'STORE_V1' },
        vendorId: { S: 'PICKUP' },
        ...extra,
    }
}
