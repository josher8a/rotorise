/**
 * The two walks over a key spec, held against each other.
 *
 * `KeyComponents<Spec>` is a type and `keyComponents(spec)` is a function, and they traverse the
 * same four shapes independently: a bare attribute name, a list of them, a list carrying transform
 * tuples, and a discriminated spec whose discriminant is itself a component. Nothing made them
 * agree — they were written apart and only ever tested apart.
 *
 * Divergence is quiet in the direction that matters. The type decides what `keyUpdates` asks the
 * caller for; the function decides what it needs to rebuild the key. A shape the type learns and
 * the function does not means context demanded and never used. A shape the function learns and the
 * type does not means a key rebuilt from a value nobody was asked for — which is how an index ends
 * up disagreeing with the item, the failure this whole layer exists to prevent.
 *
 * `agree` is the test: `expected` is checked against the type by the compiler and against the
 * function by the assertion, so a walk that drifts fails one or the other.
 */
import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { KeyComponents, MovesTheItem } from './Rotorise'
import { keyComponents } from './Rotorise'

/**
 * What the runtime walk found, for the runtime half of each pairing.
 *
 * The type half is `attest<[KeyComponents<typeof spec>], [...]>()` beside it, exact in both
 * directions. Written per test rather than in a helper: `attest` reads its own source position, so
 * a type-only assertion inside one would compare the helper's *generic* types once and say nothing
 * about any particular spec.
 *
 * Exactness matters in both directions here. The type learning *less* than the function is the
 * dangerous one — a key rebuilt from a value nobody was asked for is how an index comes to disagree
 * with the item. The type learning *more* is the direction this file's prose calls safe, and it is
 * nearly right: an unused component only costs the caller a value that is ignored. But
 * {@link MovesTheItem} reads this same walk to decide which changes rewrite the item's address, so a
 * component over-reported there refuses a legal update at compile time.
 *
 * The asymmetry the prose describes is untouched: it is about the walk *narrowed* by `given`
 * returning a subset, and nothing here passes `given`.
 */
const found = (spec: unknown): readonly string[] =>
    [...keyComponents(spec)].sort()

describe('the type walk and the runtime walk agree', () => {
    it('on a bare attribute name', () => {
        const spec = 'petId'
        attest<[KeyComponents<typeof spec>], ['petId']>()
        expect(found(spec)).toEqual(['petId'])
    })

    it('on a list of names', () => {
        const spec = ['TAG', 'ownerId', 'petId'] as const
        attest<[KeyComponents<typeof spec>], ['TAG' | 'ownerId' | 'petId']>()
        expect(found(spec)).toEqual(['TAG', 'ownerId', 'petId'].sort())
    })

    it('on a list carrying a transform tuple, whose head is the attribute', () => {
        const spec = [
            'TAG',
            ['createdAt', (d: string) => d.slice(0, 10)],
        ] as const
        attest<[KeyComponents<typeof spec>], ['TAG' | 'createdAt']>()
        expect(found(spec)).toEqual(['TAG', 'createdAt'].sort())
    })

    it('on a three-tuple, where the third slot is a default and not a component', () => {
        const spec = [
            ['status', (s: string) => s.toUpperCase(), 'DRAFT'],
        ] as const
        attest<[KeyComponents<typeof spec>], ['status']>()
        expect(found(spec)).toEqual(['status'])
    })

    it('on a discriminated spec, counting the discriminant itself', () => {
        const spec = {
            discriminator: 'type',
            spec: { CARD: ['vendorId'], PICKUP: ['storeId'] },
        } as const
        attest<
            [KeyComponents<typeof spec>],
            ['type' | 'vendorId' | 'storeId']
        >()
        expect(found(spec)).toEqual(['type', 'vendorId', 'storeId'].sort())
    })

    it('on a discriminated spec with a null variant, which contributes nothing', () => {
        const spec = {
            discriminator: 'type',
            spec: { CARD: ['vendorId'], PICKUP: null },
        } as const
        attest<[KeyComponents<typeof spec>], ['type' | 'vendorId']>()
        expect(found(spec)).toEqual(['type', 'vendorId'].sort())
    })

    it('on a discriminated spec nesting a transform tuple', () => {
        const spec = {
            discriminator: 'kind',
            spec: {
                EMAIL: [['email', (e: string) => e.toLowerCase()]],
                PHONE: ['phone'],
            },
        } as const
        attest<[KeyComponents<typeof spec>], ['kind' | 'email' | 'phone']>()
        expect(found(spec)).toEqual(['kind', 'email', 'phone'].sort())
    })

    /**
     * Only the runtime walk takes `given`, because narrowing needs a value and the type has none.
     * That is a deliberate asymmetry rather than a drift: with the discriminant known, the walk
     * returns a subset of what the type asks for, and asking for more than is needed is the safe
     * direction.
     */
    it('narrows to one variant when the discriminant is known, and never widens', () => {
        const spec = {
            discriminator: 'type',
            spec: { CARD: ['vendorId'], PICKUP: ['storeId'] },
        } as const

        const wide = keyComponents(spec)
        const narrow = keyComponents(spec, { type: 'CARD' })

        expect([...narrow].sort()).toEqual(['type', 'vendorId'])
        for (const component of narrow) expect(wide.has(component)).toBe(true)
    })
})
