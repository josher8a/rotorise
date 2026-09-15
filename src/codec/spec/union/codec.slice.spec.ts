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
    discriminatedUnion,
    mdunion,
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
        const small = twoKey.extract({ size: ['small', 'large'] })
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
        const pets = twoKey.extract({ kind: 'pet' })
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
        const one = twoKey.extract({ kind: 'pet', size: 'large' })
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
     */
    it('answers never where the clause keeps no member', () => {
        const none = twoKey.extract({ kind: 'reptile' as never })
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
        expect(tiers.extract({ tier: 'gold' }).def).toEqual({ kind: 'never' })
        expect(tiers.extract({ tier: ['gold', 'silver'] }).def.kind).toBe(
            'union',
        )
    })
})

describe('the exclusion is the complement of the same clause', () => {
    it('keeps exactly the members the extraction drops, over the same keys', () => {
        const kept = twoKey.exclude({ kind: 'pet' })
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
        expect(twoKey.exclude({ size: ['small', 'large'] }).def).toEqual({
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
        const one = twoKey.extract({ kind: 'pet', size: 'large' })
        const other = twoKey.extract({ size: 'large', kind: 'pet' })
        expect(one.def).toEqual(other.def)
    })

    it('gives the same members whichever order they were declared in', () => {
        const reversed = mdunion(['kind', 'size'], [food, dog, pet])
        const fromOne = twoKey.extract({ kind: 'pet' }).def as {
            readonly options: readonly unknown[]
        }
        const fromOther = reversed.extract({ kind: 'pet' }).def as {
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
        expect(() => twoKey.extract({ colour: 'red' } as never)).toThrow(
            CodecError,
        )
        expect(() => twoKey.extract({ colour: 'red' } as never)).toThrow(
            /'kind', 'size'/,
        )
    })

    it('refuses a key declared without a literal, which pins nothing', () => {
        // `toy` is declared by one member and is a plain `string`, so no clause can select on it
        expect(() => twoKey.extract({ toy: 't' } as never)).toThrow(CodecError)
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
        const kept = plain.extract({ kind: ['a', 'b'] })
        expect(kept.def.kind).toBe('union')
        expect(kept.unsafeEncode({ kind: 'a', x: 'v' })).toEqual({
            M: { kind: { S: 'a' }, x: { S: 'v' } },
        })
        expect(failed(kept.encode({ kind: 'c', x: true } as never))).toBe(true)
    })

    it('answers never where the clause keeps no option', () => {
        expect(plain.extract({ kind: 'z' as never }).def).toEqual({
            kind: 'never',
        })
    })

    /**
     * **The slice runs the declaration guard again, and it has to.** A sub-selection of a certified
     * union is certified and a sub-selection of an uncertified one is not, which is the premise
     * `Calculus.uAtAct_extract` takes. Rebuilding through `union` is how the host takes it.
     */
    it('rebuilds through the declaration guard rather than assembling the term', () => {
        const kept = plain.exclude({ kind: 'c' })
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
        const only = visit.extract({ type: 'CHECKUP' })
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
        const rest = visit.exclude({ type: 'CHECKUP' })
        expect(rest.unsafeEncode({ type: 'SHOT', vaccine: 'v' })).toEqual({
            M: { type: { S: 'SHOT' }, vaccine: { S: 'v' } },
        })
    })
})
