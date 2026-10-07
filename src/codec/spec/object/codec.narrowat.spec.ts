/**
 * An attribute two variants store differently, and where narrowing does and does not reach.
 *
 * An entity whose `from` is an `OwnerParty` in one variant and a `StaffParty` in another puts two
 * codecs at one attribute name. Where variants disagree about how an attribute is stored, the name
 * alone does not say which codec to encode with, and `at` reports that rather than guessing.
 *
 * `when` settles it where the clause narrows the frontier to options that agree: the walk of `at`
 * keeps each option that the clause does not separate. The variant's own codec settles it too, at
 * the cost of a path relative to that variant.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    number,
    object,
    string,
    union,
    valueKinds,
} from '../../codec'

const OpCodec = discriminatedUnion('type', [
    object({ type: string('SHIPMENT'), amount: decimal, note: string }),
    object({ type: string('COUNTER'), amount: string, note: string }),
])

const Entity = object({ op: OpCodec }).item

describe('where the variants disagree', () => {
    it('is reported rather than guessed', () => {
        const ambiguous = Entity.at((p) => p.op.amount)
        expect(() => ambiguous.unsafeEncode('1.5')).toThrow(CodecError)
    })

    it('is a refusal that the safe halves return, not a throw', () => {
        const ambiguous = Entity.at((p) => p.op.amount)
        const written = ambiguous.encode('1.5')
        const read = ambiguous.decode({ S: '1.5' })
        expect(written).toBeInstanceOf(CodecError)
        expect(read).toBeInstanceOf(CodecError)
        expect(String(written)).toMatch(
            /declared differently in different variants/,
        )
        expect(String(read)).toMatch(
            /declared differently in different variants/,
        )
    })

    it('says where to go instead', () => {
        expect(() => Entity.at((p) => p.op.amount).unsafeEncode('1.5')).toThrow(
            /Reach for the variant you mean — `variant\(\.\.\.\)` is an item codec with its own `at`/,
        )
    })

    it('is settled by the variant codec, with a path relative to it', () => {
        const asNumber = OpCodec.item.variant('SHIPMENT').at((p) => p.amount)
        const asString = OpCodec.item.variant('COUNTER').at((p) => p.amount)

        expect(asNumber.unsafeEncode('1.5')).toEqual({ N: '1.5' })
        expect(asString.unsafeEncode('1.5')).toEqual({ S: '1.5' })
        // relative, because the variant codec does not know where it was reached from
        expect(asNumber.path()).toBe('amount')
    })

    /**
     * And it says nothing about *what* is there, because there is no single thing. This used to be
     * a `Def` kind — a definition, in a language of codec definitions, for something that was
     * not a codec — so every reader of a definition had to carry a case for it.
     *
     * **The rule is that this codec writes nothing and reads nothing, and the assertions are that
     * rule.** It used to be asserted as `def === undefined`, which was the implementation of the
     * rule rather than the rule, and then as `custom`, "a pair of functions, nothing beneath".
     * `custom` is gone with its constructor, and it was the only definition whose `valueKinds`
     * answered *unknown*. What is left says the truth about this codec rather than declining to:
     * both halves throw, so it admits no value, which is what `never` means and what `valueKinds`
     * now reports. `member` still answers nothing, which is the half `at` cares about.
     */
    it('describes nothing readable, because there is no one codec to describe', () => {
        const ambiguous = Entity.at((p) => p.op.amount)
        expect(valueKinds(ambiguous.def)).toEqual([])
        expect(ambiguous.def.kind).toBe('never')
        // the path half is untouched, which is what `at` is most often for
        expect(ambiguous.path()).toBe('op.amount')
    })

    it('is settled by a clause that keeps the options that agree, with the path unchanged', () => {
        const asString = Entity.at(
            (p) => p.op.when({ type: string('COUNTER') }).amount,
        )
        const asNumber = Entity.at(
            (p) => p.op.when({ type: string('SHIPMENT') }).amount,
        )
        expect(asString.path()).toBe('op.amount')
        expect(asString.unsafeEncode('1.5')).toEqual({ S: '1.5' })
        expect(asNumber.unsafeEncode('1.5')).toEqual({ N: '1.5' })
    })
})

describe('where they agree, or only one declares it', () => {
    it('resolves an attribute the variants store the same way', () => {
        expect(Entity.at((p) => p.op.note).unsafeEncode('hello')).toEqual({
            S: 'hello',
        })
    })

    it('resolves an attribute only one variant has, under the clause that keeps that variant', () => {
        const M = object({
            m: discriminatedUnion('tag', [
                object({ tag: string('A'), only: number }),
                object({ tag: string('B'), shared: string }),
            ]),
        }).item
        expect(
            M.at((p) => p.m.when({ tag: string('A') }).only).unsafeEncode(7),
        ).toEqual({ N: '7' })
    })
})

/**
 * Narrowing keeps each option that the clause does not separate. It is not the slice, which keeps
 * only the options that the clause describes: a pin `'A' | 'B'` and an option with no pin both stay
 * under the clause `'A'`, because each admits a value that the clause admits.
 */
describe('a clause narrows the frontier of `at`', () => {
    const Pinned = object({
        u: union([
            object({ tag: string('A'), a: number }),
            object({ tag: string('A', 'B'), ab: number }),
            object({ tag: string('B'), b: string }),
            object({ tag: string, free: number }),
        ]),
    }).item
    const isA = { tag: string('A') }

    it('keeps an option whose pin the clause does not separate', () => {
        // the second clause keeps the one option that declares the name, so the path resolves only
        // where the first clause kept that option
        const ab = Pinned.at((p) => p.u.when(isA).when({ ab: number }).ab)
        const free = Pinned.at((p) => p.u.when(isA).when({ free: number }).free)
        expect(ab.unsafeEncode(1)).toEqual({ N: '1' })
        expect(free.unsafeEncode(2)).toEqual({ N: '2' })
    })

    it('drops an option whose pin the clause separates', () => {
        // @ts-expect-error the clause separates the option that declares `b`
        const dropped = () => Pinned.at((p) => p.u.when(isA).b)
        expect(dropped).toThrow(/no attribute is declared at 'u\.b'/)
    })

    it('narrows a union with no tag by the presence of a key', () => {
        const Line = object({
            leg: union([
                object({ petId: string, price: string }),
                object({ petIds: array(string), price: number }),
            ]),
        }).item
        const bundle = Line.at(
            (p) => p.leg.when({ petIds: array(string) }).price,
        )
        const single = Line.at((p) => p.leg.when({ petId: string }).price)
        expect(bundle.path()).toBe('leg.price')
        expect(bundle.unsafeEncode(3)).toEqual({ N: '3' })
        expect(single.unsafeEncode('3')).toEqual({ S: '3' })
    })

    it('refuses on use where the clause separates every option, and names the keys', () => {
        const none = Entity.at(
            // @ts-expect-error the clause separates every member
            (p) => p.op.when({ type: string('REFUND') }).note,
        )
        expect(none.path()).toBe('op.note')
        const written = none.encode('x')
        expect(written).toBeInstanceOf(CodecError)
        expect(String(written)).toMatch(
            /the clause on 'type' separates every option/,
        )
    })
})

/**
 * **The type and the walk of `at` narrow on the stored side.** An adapter stores what its inner
 * codec stores: `number` and `decimal` each write `N`, and `number(1)` and `decimal('1')` each
 * store the text `1`. So a clause separates by the attribute that the store holds, not by the
 * value that the caller holds. Each case asserts that the member the type keeps is the member the
 * walk keeps, and that the member the type drops is a refusal at run time.
 */
describe('the type and the walk of `at` agree on the stored side', () => {
    const nested = object({ nested: number })
    const z = object({ z: string })
    const NumberOrString = object({
        u: union([
            object({ k: string('x'), n: string }),
            object({ k: string('y'), n: number }),
        ]),
    }).item
    const MapOrString = object({
        u: union([
            object({ tag: string('F'), data: string }),
            object({ tag: string('D'), data: nested }),
        ]),
    }).item
    const MapOrDecimal = object({
        u: union([
            object({ tag: string('F'), data: decimal }),
            object({ tag: string('D'), data: nested }),
        ]),
    }).item
    const NumberTags = object({
        u: union([
            object({ k: number(1), a: string }),
            object({ k: number(2), a: number }),
        ]),
    }).item
    const DecimalTags = object({
        u: union([
            object({ k: decimal('1'), a: string }),
            object({ k: decimal('2'), a: number }),
        ]),
    }).item
    const NativeOrString = object({
        u: union([
            object({ tag: string('A'), v: dynamoNumber }),
            object({ tag: string('B'), v: string }),
        ]),
    }).item
    const DecimalOrMap = object({
        u: union([
            object({ tag: string('A'), v: decimal }),
            object({ tag: string('B'), v: z }),
        ]),
    }).item
    const DecimalOrString = object({
        u: union([
            object({ tag: string('A'), v: decimal }),
            object({ tag: string('B'), v: string }),
        ]),
    }).item

    it('an adapter clause keeps the member that stores its attribute', () => {
        const k = NumberOrString.at((p) => p.u.when({ n: number }).k)
        expect(k.unsafeEncode('y')).toEqual({ S: 'y' })
        // @ts-expect-error the clause separates the member that stores `S`
        expect(k.encode('x')).toBeInstanceOf(CodecError)
    })

    it('a map clause drops the member that stores a string', () => {
        const tag = MapOrString.at((p) => p.u.when({ data: nested }).tag)
        expect(tag.unsafeEncode('D')).toEqual({ S: 'D' })
        // @ts-expect-error the clause separates the member that stores `S`
        expect(tag.encode('F')).toBeInstanceOf(CodecError)
    })

    it('a map clause drops the member that stores a decimal', () => {
        const tag = MapOrDecimal.at((p) => p.u.when({ data: nested }).tag)
        expect(tag.unsafeEncode('D')).toEqual({ S: 'D' })
        // @ts-expect-error the clause separates the member that stores `N`
        expect(tag.encode('F')).toBeInstanceOf(CodecError)
    })

    it('a numeric tag keeps the option with its pin', () => {
        const a = NumberTags.at((p) => p.u.when({ k: number(1) }).a)
        expect(a.unsafeEncode('x')).toEqual({ S: 'x' })
        // @ts-expect-error the clause separates the option pinned at 2
        expect(a.encode(3)).toBeInstanceOf(CodecError)
    })

    it('a decimal tag keeps the option with its pin', () => {
        const a = DecimalTags.at((p) => p.u.when({ k: decimal('1') }).a)
        expect(a.unsafeEncode('x')).toEqual({ S: 'x' })
        // @ts-expect-error the clause separates the option pinned at 2
        expect(a.encode(3)).toBeInstanceOf(CodecError)
    })

    it('a numeric pin meets the decimal pin that stores the same text', () => {
        const a = DecimalTags.at((p) => p.u.when({ k: number(1) }).a)
        expect(a.unsafeEncode('x')).toEqual({ S: 'x' })
        // @ts-expect-error the clause separates the option pinned at 2
        expect(a.encode(3)).toBeInstanceOf(CodecError)
    })

    it('a `number` clause keeps a native number and drops a string', () => {
        const tag = NativeOrString.at((p) => p.u.when({ v: number }).tag)
        expect(tag.unsafeEncode('A')).toEqual({ S: 'A' })
        // @ts-expect-error the clause separates the member that stores `S`
        expect(tag.encode('B')).toBeInstanceOf(CodecError)
    })

    it('a `decimal` clause keeps a native number and drops a string', () => {
        const tag = NativeOrString.at((p) => p.u.when({ v: decimal }).tag)
        expect(tag.unsafeEncode('A')).toEqual({ S: 'A' })
        // @ts-expect-error the clause separates the member that stores `S`
        expect(tag.encode('B')).toBeInstanceOf(CodecError)
    })

    it('a map clause drops a decimal and keeps the map', () => {
        const tag = DecimalOrMap.at((p) => p.u.when({ v: z }).tag)
        expect(tag.unsafeEncode('B')).toEqual({ S: 'B' })
        // @ts-expect-error the clause separates the member that stores `N`
        expect(tag.encode('A')).toBeInstanceOf(CodecError)
    })

    it('a `decimal` clause drops a string, although both decode to a string', () => {
        const tag = DecimalOrString.at((p) => p.u.when({ v: decimal }).tag)
        expect(tag.unsafeEncode('A')).toEqual({ S: 'A' })
        // @ts-expect-error the clause separates the member that stores `S`
        expect(tag.encode('B')).toBeInstanceOf(CodecError)
    })

    it('a `string` clause drops a decimal, although both decode to a string', () => {
        const tag = DecimalOrString.at((p) => p.u.when({ v: string }).tag)
        expect(tag.unsafeEncode('B')).toEqual({ S: 'B' })
        // @ts-expect-error the clause separates the member that stores `N`
        expect(tag.encode('A')).toBeInstanceOf(CodecError)
    })

    it('a `number` clause keeps a decimal and drops a map', () => {
        const tag = DecimalOrMap.at((p) => p.u.when({ v: number }).tag)
        expect(tag.unsafeEncode('A')).toEqual({ S: 'A' })
        // @ts-expect-error the clause separates the member that stores `M`
        expect(tag.encode('B')).toBeInstanceOf(CodecError)
    })
})

/**
 * **A path carries the strong law**: an item that the codec reads stays readable after a write at
 * the path. A closed option that lacks the name admits no value there, so a write at the name
 * leaves an item of that option that no option reads. An option whose stored member the segment
 * cannot enter is no such risk: the store refuses the write on that item, so the option leaves the
 * frontier.
 */
describe('a path keeps every item that the codec reads readable', () => {
    const M = object({
        m: discriminatedUnion('tag', [
            object({ tag: string('A'), only: number }),
            object({ tag: string('B'), shared: string }),
        ]),
    }).item
    const isA = { tag: string('A') }

    it('refuses on use a name that a closed option lacks, and names `when`', () => {
        const only = M.at((p) => p.m.only)
        expect(only.path()).toBe('m.only')
        const written = only.encode(7)
        expect(written).toBeInstanceOf(CodecError)
        expect(String(written)).toMatch(
            /'m\.only' is declared by some variants only.*narrow the union with `when\(\{\.\.\.\}\)`/i,
        )
    })

    it('writes no attribute that leaves an item of a kept option unreadable', () => {
        const itemA = M.unsafeEncode({ m: { tag: 'A', only: 1 } })
        const itemB = M.unsafeEncode({ m: { tag: 'B', shared: 's' } })
        const cases = [
            [M.at((p) => p.m.only), [itemA, itemB]],
            [M.at((p) => p.m.when(isA).only), [itemA]],
        ] as const
        let writes = 0
        for (const [at, kept] of cases) {
            const wrote = at.encode(7)
            if (wrote instanceof CodecError) continue
            writes++
            for (const item of kept) {
                const stored = item.m as { M: Record<string, unknown> }
                // the write at the path, as `UpdateItem` sets `m.only`
                const after = {
                    ...item,
                    m: { M: { ...stored.M, only: wrote } },
                }
                expect(M.decode(after as never)).not.toBeInstanceOf(CodecError)
            }
        }
        expect(writes).toBe(1)
    })

    it('drops an option whose stored member the segment cannot enter', () => {
        const U = object({ u: union([string, object({ x: number })]) }).item
        // @ts-expect-error the path type offers no key on a union with a primitive member
        const x = U.at((p) => p.u.x)
        expect(x.unsafeEncode(7)).toEqual({ N: '7' })
    })

    it('refuses at the call a name on a list, because the store refuses the name on a list', () => {
        const L = object({ xs: array(string) }).item
        // @ts-expect-error a list has positions, not names
        expect(() => L.at((p) => p.xs.foo)).toThrow(
            /no attribute is declared at 'xs\.foo'/,
        )
    })
})
