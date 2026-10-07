/**
 * The multi-key `dunion`: a dissection is a key set and a set of members, and a member carries one
 * tag per key.
 *
 * `mdunion` builds one at any arity, and `discriminatedUnion` is `mdunion` at one key. The term
 * it builds is a `Term.union` of objects; the tag table is the builder's own index, and each test
 * below names one rule that index needs.
 */
import { describe, expect, it } from 'vitest'
import { boolean, mdunion, object, string } from '../../codec'
import type { ItemPair } from '../../denote'
import { assignmentOf } from '../../denote'
import { failed } from '../../result'
import type { Term } from '../../term'

const pet = object({ kind: string('pet'), size: string('small'), toy: string })
const dog = object({ kind: string('pet'), size: string('large'), pen: string })
const food = object({
    kind: string('food'),
    size: string('small'),
    gram: boolean,
})

/** A dissection's term is an ordinary union of its members now; the tag table is the builder's. */
const unionTerm = (codec: { readonly def: Term }) =>
    codec.def as Extract<Term, { readonly kind: 'union' }>

/** Two discriminators, `kind` and `size`, and three members over their assignments. */
const twoKey = mdunion(['kind', 'size'], [pet, dog, food])
// the untyped item pair, which is what these tests are about: several of them feed a partial or a
// mistyped entity on purpose, to assert the runtime refusal the tag index gives. The typed
// `Dissected` reading refuses those at the call, where the rule under test is the run-time one
const pair = twoKey.item as unknown as ItemPair

describe("a member's assignment is read off the member's own body", () => {
    /**
     * The tag at each key is the one alternative the body's own `req` literal names. The field
     * cannot go — the codec writes the tag out of it — so the index reads its keys off the members
     * rather than carrying them beside the members.
     */
    it('reads one tag per key off the body, and names the key it cannot read', () => {
        const body = unionTerm(twoKey).options[0] as Extract<
            Term,
            { readonly kind: 'object' }
        >
        expect(assignmentOf(['kind', 'size'], body.body)).toEqual({
            kind: 'pet',
            size: 'small',
        })
        const missing = assignmentOf(['kind', 'colour'], body.body)
        expect(failed(missing)).toBe(true)
        expect(String(missing)).toMatch(/must name 'colour' with a literal/)
    })

    /**
     * `req` only: a `withLegacyRead` discriminator would fill an absent tag with a default, and the
     * index would key a member on a value no item carries.
     */
    it('refuses a member whose discriminator is not required', () => {
        const optionalTag = {
            kind: 'object',
            body: {
                fields: {
                    kind: {
                        mark: 'optional',
                        t: { kind: 'literal', base: 'string', ls: ['pet'] },
                    },
                },
            },
        } as unknown as Extract<Term, { readonly kind: 'object' }>
        const refused = assignmentOf(['kind'], optionalTag.body)
        expect(failed(refused)).toBe(true)
        expect(String(refused)).toMatch(/declares it `optional`/)
    })
})

describe('the members of a dissection form a set', () => {
    /** The index must be a lookup, so one assignment reaches at most one member. */
    it('refuses two members carrying the same assignment', () => {
        const twin = object({
            kind: string('pet'),
            size: string('small'),
            other: string,
        })
        expect(() =>
            // @ts-expect-error the type refuses the pair; this asserts the runtime half too
            mdunion(['kind', 'size'], [pet, twin]),
        ).toThrow(/two options answer to 'kind' = 'pet' and 'size' = 'small'/)
    })

    /** …and the same rule at one key is the refusal `discriminatedUnion` always gave. */
    it('refuses two members carrying the same tag at one key', () => {
        expect(() =>
            // @ts-expect-error the same refusal at one key, on both levels
            mdunion(['kind'], [pet, dog]),
        ).toThrow(/two options answer to 'kind' = 'pet'/)
    })
})

describe('selection reads every key', () => {
    it('reaches the member whose whole assignment matches, and no other', () => {
        // the two agree at `kind` and differ at `size`, which is the case one key cannot tell
        // apart: `kind` alone reaches both
        expect(
            pair.encode({ kind: 'pet', size: 'small', toy: 'ball' }),
        ).toEqual({
            kind: { S: 'pet' },
            size: { S: 'small' },
            toy: { S: 'ball' },
        })
        expect(pair.encode({ kind: 'pet', size: 'large', pen: 'p1' })).toEqual({
            kind: { S: 'pet' },
            size: { S: 'large' },
            pen: { S: 'p1' },
        })
    })

    it('decodes back through the same member, where two members share a tag', () => {
        for (const entity of [
            { kind: 'pet', size: 'small', toy: 'ball' },
            { kind: 'pet', size: 'large', pen: 'p1' },
            { kind: 'food', size: 'small', gram: true },
        ]) {
            const written = pair.encode(entity)
            expect(failed(written)).toBe(false)
            expect(pair.decode(written as Record<string, never>)).toEqual(
                entity,
            )
        }
    })

    /** One absent tag chooses nothing: the assignment is incomplete, so no member matches it. */
    it('refuses a value missing one discriminator', () => {
        const written = pair.encode({ kind: 'pet', toy: 'ball' })
        expect(failed(written)).toBe(true)
        expect(String(written)).toMatch(/'size' chooses the variant/)
    })

    /** …and an item missing it on the stored side, which is the reader's own half. */
    it('refuses a stored item missing one discriminator', () => {
        const read = pair.decode({ kind: { S: 'pet' }, toy: { S: 'ball' } })
        expect(failed(read)).toBe(true)
        expect(String(read)).toMatch(/'size' chooses the variant/)
    })

    /**
     * An assignment no member carries names the **key** whose tag no member carries, which is a
     * question each key answers on its own and so needs no order to ask.
     */
    it('names the discriminator whose tag matched nothing', () => {
        const read = pair.decode({
            kind: { S: 'pet' },
            size: { S: 'enormous' },
            toy: { S: 'ball' },
        })
        expect(failed(read)).toBe(true)
        expect(String(read)).toMatch(/'enormous' is not a variant of 'size'/)
    })
})

describe('neither the keys nor the members carry an order', () => {
    /**
     * **The rule the term exists to state.** A dissection is a *set* of keys, so declaring the same
     * dissection with `size` written first declares the same term. A shape with a head and a tail
     * made two terms for one dissection, and this is the test it could not pass.
     */
    it('reads the same dissection declared with the keys the other way round', () => {
        const swapped = mdunion(['size', 'kind'], [pet, dog, food])
            .item as unknown as ItemPair
        for (const entity of [
            { kind: 'pet', size: 'small', toy: 'ball' },
            { kind: 'pet', size: 'large', pen: 'p1' },
            { kind: 'food', size: 'small', gram: true },
        ]) {
            expect(swapped.encode(entity)).toEqual(pair.encode(entity))
            const written = pair.encode(entity) as Record<string, never>
            expect(swapped.decode(written)).toEqual(pair.decode(written))
        }
    })

    /** …and a *set* of members, so the order the caller listed them in reaches nothing. */
    it('reads the same dissection with the members declared in another order', () => {
        const reordered = mdunion(['kind', 'size'], [food, dog, pet])
            .item as unknown as ItemPair
        for (const entity of [
            { kind: 'pet', size: 'small', toy: 'ball' },
            { kind: 'pet', size: 'large', pen: 'p1' },
            { kind: 'food', size: 'small', gram: true },
        ]) {
            expect(reordered.encode(entity)).toEqual(pair.encode(entity))
            const written = pair.encode(entity) as Record<string, never>
            expect(reordered.decode(written)).toEqual(pair.decode(written))
        }
    })
})

describe('a member is selected by its assignment', () => {
    /** An object literal, matched key by key: the clause is as unordered as the term's key. */
    it('reaches a member by the assignment it carries', () => {
        const Holder = object({ x: twoKey }).item
        const chosen = Holder.at(
            (p) =>
                p.x.narrow({ kind: string('pet'), size: string('large') }).pen,
        )
        const reordered = Holder.at(
            (p) =>
                p.x.narrow({ size: string('large'), kind: string('pet') }).pen,
        )
        expect(chosen.unsafeEncode('p1')).toEqual({ S: 'p1' })
        expect(reordered.unsafeEncode('p1')).toEqual({ S: 'p1' })
    })

    /** The key set, and no `discriminator`: at several keys there is no single name to give. */
    it('carries the key set', () => {
        expect(twoKey.item.keys).toEqual(['kind', 'size'])
    })
})

/**
 * **Every rule is refused at the declaration, and asked of each member.**
 *
 * A dissection is correct when the members are pairwise distinguishable by a lookup, and that is a
 * property of every member rather than of the collection: an option that names no tag at a key
 * cannot be found there, whatever its neighbours name. `tsc` is the assertion — each directive
 * below has to be used, so a rule that stops firing fails the build as an unused directive.
 */
describe('the type refuses what a lookup could not reach', () => {
    const noSize = object({ kind: string('food'), gram: string })
    const twoTags = object({
        kind: string('a', 'b'),
        size: string('small'),
        z: string,
    })

    it('refuses a member that names no tag at one key', () => {
        expect(() =>
            // @ts-expect-error `noSize` declares no `size`, so no assignment reaches it
            mdunion(['kind', 'size'], [pet, noSize]),
        ).toThrow(/must name 'size' with a literal/)
    })

    it('refuses a member whose literal admits several values at one key', () => {
        expect(() =>
            // @ts-expect-error arity one: a member answers to one tag at each key
            mdunion(['kind', 'size'], [pet, twoTags]),
        ).toThrow(/names 2 values at one option/)
    })

    it('refuses an empty member list, which is `never` and not a dissection', () => {
        expect(() =>
            // @ts-expect-error an empty list is a typo, and the bottom has its own name
            mdunion(['kind'], []),
        ).toThrow(/needs at least one option/)
    })

    it('admits a dissection whose members are pairwise distinct', () => {
        expect(() => mdunion(['kind', 'size'], [pet, dog, food])).not.toThrow()
    })
})
