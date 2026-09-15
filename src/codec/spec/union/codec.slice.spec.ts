/**
 * The slice of a union: `extract` and `exclude`, over a dissection and over a plain union of
 * objects.
 *
 * `Calculus.AltClause` at the host. A clause names some keys and admits a set of tags at each; the
 * extraction keeps the members it describes and the exclusion keeps the rest. Both give a codec
 * over the **same keys** and fewer members, which is the ruling the model's `Slice.lean` carries:
 * no normalisation drops a constant key, because the codec writes the tag out of the member's own
 * field whatever the key set says.
 */
import { describe, expect, it } from 'vitest'
import {
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    mdunion,
    number,
    object,
    optional,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'

const pet = object({ kind: string('pet'), size: string('small'), toy: string })
const dog = object({ kind: string('pet'), size: string('large'), pen: string })
const food = object({
    kind: string('food'),
    size: string('small'),
    gram: boolean,
})

const twoKey = mdunion(['kind', 'size'], [pet, dog, food])

describe('the extraction keeps the members a clause describes', () => {
    /**
     * A clause admits a **set** at each key, which is what makes this more than a lookup: naming
     * one tag reaches one member, and naming two reaches the fibre over both.
     */
    it('keeps every member whose tags lie inside the clause set', () => {
        const small = twoKey.extract({ size: string('small', 'large') })
        // all three, because every member's `size` is one of the two named
        expect(
            small.unsafeEncode({ kind: 'pet', size: 'small', toy: 't' }),
        ).toEqual({
            M: {
                kind: { S: 'pet' },
                size: { S: 'small' },
                toy: { S: 't' },
            },
        })
        expect(
            small.unsafeEncode({ kind: 'food', size: 'small', gram: true }),
        ).toEqual({
            M: {
                kind: { S: 'food' },
                size: { S: 'small' },
                gram: { BOOL: true },
            },
        })
    })

    it('drops the members the clause does not describe', () => {
        const pets = twoKey.extract({ kind: string('pet') })
        // `food` is gone, so the codec that admitted it no longer does — which is the whole of
        // what an extraction is, and it is visible only as a refusal
        expect(
            failed(
                pets.encode({
                    kind: 'food',
                    size: 'small',
                    gram: true,
                } as never),
            ),
        ).toBe(true)
        expect(
            pets.unsafeEncode({ kind: 'pet', size: 'large', pen: 'p' }),
        ).toEqual({
            M: { kind: { S: 'pet' }, size: { S: 'large' }, pen: { S: 'p' } },
        })
    })

    /**
     * **No key is dropped, and a pinned key is not special.** A key the clause pins to one tag says
     * the same thing of every member kept, and it stays a key: the field is still a required
     * literal in every member's body, so every item still carries it.
     */
    it('keeps every key, so a one-member result still reads its key', () => {
        const one = twoKey.extract({
            kind: string('pet'),
            size: string('large'),
        })
        expect(one.item.keys).toEqual(['kind', 'size'])
        const written = one.unsafeEncode({
            kind: 'pet',
            size: 'large',
            pen: 'p',
        })
        // the two discriminators are written, not normalised away, and the item reads back
        expect(written).toEqual({
            M: { kind: { S: 'pet' }, size: { S: 'large' }, pen: { S: 'p' } },
        })
        expect(one.unsafeDecode(written)).toEqual({
            kind: 'pet',
            size: 'large',
            pen: 'p',
        })
    })

    /**
     * **An extraction that keeps nothing is the bottom, and the bottom has one name.** Not an empty
     * dissection, which `dissect` refuses: an empty option list is what a typo produces, so a rule
     * reading it as the bottom would read that accident as intent.
     *
     * Reached through the containment rule rather than through an unknown tag: a tag no member
     * carries is refused at the call, so what is left to keep nothing is a clause the members' own
     * tags do not fit inside.
     */
    it('answers never where the clause keeps no member', () => {
        const spans = union([
            object({ tier: string('gold', 'silver'), n: boolean }),
            object({ tier: string('bronze'), m: boolean }),
        ])
        const none = spans.extract({ tier: string('gold') })
        expect(none.def).toEqual({ kind: 'never' })
        expect(failed(none.encode({} as never))).toBe(true)
    })

    /**
     * A member whose literal spans several tags is kept only where **all** of them lie inside the
     * clause. Keeping it on a one-tag overlap would make the extraction admit a value the clause
     * does not describe, which is why the model's `altsSub` reads containment and not membership.
     */
    it('drops a member whose tags reach outside the clause', () => {
        // a `union` and not an `mdunion`: a dissection refuses a member spanning two tags at a key,
        // because a lookup reaches one member per tag. A union has no such rule, so it is where the
        // containment reading can be seen at all
        const tiers = union([
            object({ tier: string('gold', 'silver'), n: boolean }),
            object({ tier: string('bronze'), m: boolean }),
        ])
        expect(tiers.extract({ tier: string('gold') }).def).toEqual({
            kind: 'never',
        })
        expect(tiers.extract({ tier: string('gold', 'silver') }).def.kind).toBe(
            'union',
        )
    })
})

/**
 * **The same tag text at two bases is two clauses.**
 *
 * `string('1')` and `decimal('1')` carry the same character and are read from different members;
 * `number(1)` is a third thing again. This is the whole reason a clause value is a codec and not a
 * tag: a tag is text, and text does not say which base it was written at. `Calculus.AltClause`
 * carries `Alts` per key for the same reason, and `altsSub` declines across bases.
 */
describe('a clause is a literal at a base', () => {
    const byBase = union([
        object({ k: string('1'), a: string }),
        object({ k: decimal('1'), b: boolean }),
    ])

    it('keeps the string member for a string literal', () => {
        const kept = byBase.extract({ k: string('1') })
        expect(kept.unsafeEncode({ k: '1', a: 'x' })).toEqual({
            M: { k: { S: '1' }, a: { S: 'x' } },
        })
        expect(failed(kept.encode({ k: '1', b: true } as never))).toBe(true)
    })

    it('keeps the decimal member for a decimal literal, at the same text', () => {
        const kept = byBase.extract({ k: decimal('1') })
        expect(kept.unsafeEncode({ k: '1', b: true } as never)).toEqual({
            M: { k: { N: '1' }, b: { BOOL: true } },
        })
        expect(failed(kept.encode({ k: '1', a: 'x' } as never))).toBe(true)
    })

    /**
     * A base no member carries at the key is the same class of fact as a key no member pins: it
     * describes no member whatever the alternatives are, and it is decidable from the declaration.
     * So it is refused where the foreign key is refused, rather than answered with the empty
     * extraction — which stays the answer where the bases agree and the alternatives do not meet.
     */
    it('refuses a base no member carries at that key', () => {
        // the type catches this one too — `number(1)` decodes to `1` and the members carry `'1'` —
        // so the cast is a caller reaching past it, which is who the runtime refusal is for. What
        // the type cannot catch is `string('1')` against `decimal('1')`: both decode to `'1'`, and
        // the base is exactly what an entity type does not carry
        expect(() => byBase.extract({ k: number(1) } as never)).toThrow(
            CodecError,
        )
        expect(() => byBase.extract({ k: number(1) } as never)).toThrow(
            /`number` literal and no member pins 'k' at that base/,
        )
    })

    it('refuses a clause value that is no literal at all', () => {
        expect(() =>
            // @ts-expect-error a bare tag says nothing about the base
            byBase.extract({ k: '1' }),
        ).toThrow(CodecError)
        expect(() =>
            // @ts-expect-error the plain base admits more than a literal does
            byBase.extract({ k: string }),
        ).toThrow(/is not a literal codec/)
    })
})

describe('the exclusion is the complement of the same clause', () => {
    it('keeps exactly the members the extraction drops, over the same keys', () => {
        const kept = twoKey.exclude({ kind: string('pet') })
        expect(kept.item.keys).toEqual(['kind', 'size'])
        expect(
            kept.unsafeEncode({ kind: 'food', size: 'small', gram: true }),
        ).toEqual({
            M: {
                kind: { S: 'food' },
                size: { S: 'small' },
                gram: { BOOL: true },
            },
        })
        expect(
            failed(
                kept.encode({
                    kind: 'pet',
                    size: 'small',
                    toy: 't',
                } as never),
            ),
        ).toBe(true)
    })

    it('answers never where the clause describes every member', () => {
        expect(twoKey.exclude({ size: string('small', 'large') }).def).toEqual({
            kind: 'never',
        })
    })
})

describe('the clause carries no order', () => {
    /**
     * `Calculus.AltClause` is a key set and a function on it, and the host's clause is an object
     * literal for the same reason: an object type has no order on its keys, so two spellings of one
     * clause are one clause.
     */
    it('gives the same result whichever order the keys are written in', () => {
        const one = twoKey.extract({
            kind: string('pet'),
            size: string('large'),
        })
        const other = twoKey.extract({
            size: string('large'),
            kind: string('pet'),
        })
        expect(one.def).toEqual(other.def)
    })

    it('gives the same members whichever order they were declared in', () => {
        const reversed = mdunion(['kind', 'size'], [food, dog, pet])
        const fromOne = twoKey.extract({ kind: string('pet') }).def as {
            readonly options: readonly unknown[]
        }
        const fromOther = reversed.extract({ kind: string('pet') }).def as {
            readonly options: readonly unknown[]
        }
        // the same two members, and the declaration order each was written in is what each keeps —
        // a selection reorders nothing
        expect(fromOne.options).toHaveLength(2)
        expect(fromOther.options).toHaveLength(2)
        expect([...fromOther.options].reverse()).toEqual(fromOne.options)
    })
})

describe('a clause key no member pins is refused', () => {
    /**
     * The model cannot have this failure: its clause keys are a subset of the dissection's by the
     * type. Here a clause is an object literal a caller writes, and an empty result is a legitimate
     * answer, so a typo would read as "no member matched" rather than as the typo it is.
     */
    it('names the keys a clause may use', () => {
        expect(() =>
            twoKey.extract({ colour: string('red') } as never),
        ).toThrow(CodecError)
        expect(() =>
            twoKey.extract({ colour: string('red') } as never),
        ).toThrow(/'kind', 'size'/)
    })

    it('refuses a key declared without a literal, which pins nothing', () => {
        // `toy` is declared by one member and is a plain `string`, so no clause can select on it
        expect(() => twoKey.extract({ toy: string('t') } as never)).toThrow(
            CodecError,
        )
    })
})

describe('a union of objects has the same slice', () => {
    /**
     * A dissection is a union of objects with a tag table over it, so the operation is one
     * implementation and not two. What the union has and the dissection does not is that a member
     * need not carry a tag at every key — the clause simply describes fewer of them.
     */
    const plain = union([
        object({ kind: string('a'), x: string }),
        object({ kind: string('b'), x: boolean }),
        object({ kind: string('c'), x: boolean, extra: optional(string) }),
    ])

    it('keeps the options the clause describes, and rebuilds a union', () => {
        const kept = plain.extract({ kind: string('a', 'b') })
        expect(kept.def.kind).toBe('union')
        expect(kept.unsafeEncode({ kind: 'a', x: 'v' })).toEqual({
            M: { kind: { S: 'a' }, x: { S: 'v' } },
        })
        expect(failed(kept.encode({ kind: 'c', x: true } as never))).toBe(true)
    })

    /**
     * **A tag no option carries is refused by the type and answered by the runtime**, and the two
     * are not in disagreement. It is a typo, decidable from the declaration, so the type says so at
     * the call. The runtime has nothing to add: the base matches and the alternatives simply do not
     * meet, which is a fact about values, and the answer to that is the empty extraction.
     */
    it('refuses a tag no option carries at the type, and answers never past it', () => {
        const none = plain.extract(
            // @ts-expect-error `z` is a tag no option carries
            { kind: string('z') },
        )
        expect(none.def).toEqual({ kind: 'never' })
    })

    /**
     * **The slice runs the declaration guard again, and it has to.** A sub-selection of a certified
     * union is certified and a sub-selection of an uncertified one is not, which is the premise
     * `Calculus.uAtAct_extract` takes. Rebuilding through `union` is how the host takes it.
     */
    it('rebuilds through the declaration guard rather than assembling the term', () => {
        const kept = plain.exclude({ kind: string('c') })
        // two options with one name set, told apart by their required literals — which stands only
        // because structural admission decides it, and the guard is what says so
        expect(
            kept.unsafeDecode({ M: { kind: { S: 'b' }, x: { BOOL: true } } }),
        ).toEqual({ kind: 'b', x: true })
    })
})

describe('discriminatedUnion slices like the dissection it is', () => {
    const visit = discriminatedUnion('type', [
        object({ type: string('CHECKUP'), petId: string }),
        object({ type: string('SHOT'), vaccine: string }),
    ])

    it('keeps the variant named and still reads its discriminator', () => {
        const only = visit.extract({ type: string('CHECKUP') })
        const written = only.unsafeEncode({ type: 'CHECKUP', petId: 'p1' })
        expect(written).toEqual({
            M: { type: { S: 'CHECKUP' }, petId: { S: 'p1' } },
        })
        expect(only.unsafeDecode(written)).toEqual({
            type: 'CHECKUP',
            petId: 'p1',
        })
        expect(only.item.discriminator).toBe('type')
    })

    it('excludes it and leaves the other', () => {
        const rest = visit.exclude({ type: string('CHECKUP') })
        expect(rest.unsafeEncode({ type: 'SHOT', vaccine: 'v' })).toEqual({
            M: { type: { S: 'SHOT' }, vaccine: { S: 'v' } },
        })
    })
})
