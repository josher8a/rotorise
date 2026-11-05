/**
 * The two answers to "does this codec decide its value", held against each other.
 *
 * `ConstantAttributes<Spec>` is a type and `decides(codec)` is a function, and they reach the answer
 * by different routes: the type reads the term, the function reads `def.kind` and
 * how many values the literal admits. Nothing makes them agree.
 *
 * Disagreement is quiet in one direction and loud in the other. If the type says decided where the
 * function says not, `keyUpdates` does not ask the caller for that component and then throws at
 * runtime demanding it — a signature that promises something the implementation refuses. That is
 * exactly what a `ConstantCodec<'A' | 'B'>` used to do, because the type asked whether a constant
 * was *declared* rather than whether one value was admissible.
 *
 * The sibling walks have this test already — see `keycomponents.spec.ts`. This is the other pair.
 */
import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { ConstantAttributes } from '../../../Rotorise'
import type { ObjectSlot } from '../../codec'
import {
    CodecError,
    constantOf,
    decimal,
    held,
    number,
    optional,
    refine,
    string,
    withLegacyRead,
} from '../../codec'

/**
 * What the shipped walk answers, for the runtime half of each pairing.
 *
 * The type half is `attest<[Expected], [Actual]>()`, written at each call rather than in here.
 * `attest` reads its own source position, so a type-only assertion inside a helper would compare
 * the helper's *generic* types once and say nothing about any particular spec.
 *
 * Wrapped in tuples so that `never` is expressible: `attest`'s second parameter defaults to `never`
 * and it refuses that as an explicit argument, since it cannot tell it from the default.
 */
const decided = (spec: Record<string, ObjectSlot>): readonly string[] =>
    Object.entries(spec)
        .filter(([, declared]) => constantOf(declared) !== undefined)
        .map(([name]) => name)
        .sort()

describe('the type and the function agree on what is decided', () => {
    it('on a single-valued literal, which is the whole point', () => {
        const spec = { TAG: string('PET'), id: string }
        attest<[ConstantAttributes<typeof spec>], ['TAG']>()
        expect(decided(spec)).toEqual(['TAG'])
    })

    it('on a many-valued literal, which decides nothing', () => {
        const spec = { status: string('NEW', 'DONE'), id: string }
        attest<[ConstantAttributes<typeof spec>], [never]>()
        expect(decided(spec)).toEqual([])
    })

    it('on several, and on a spec with none at all', () => {
        const several = {
            TAG: string('PET'),
            kind: string('DOG'),
            id: string,
        }
        attest<[ConstantAttributes<typeof several>], ['TAG' | 'kind']>()
        expect(decided(several)).toEqual(['TAG', 'kind'])

        const none = { id: string, price: decimal }
        attest<[ConstantAttributes<typeof none>], [never]>()
        expect(decided(none)).toEqual([])
    })

    /**
     * A literal whose one argument has a union type. The type cannot name one value, so the type
     * decides nothing. The run time holds the one value that the call passed, so the run time decides it.
     *
     * Asking only whether a `constant` was declared made the type call a union decided. The type reads
     * the term now, and a union of texts is refused there. The type answers "nothing" where the run
     * time answers "one value", which is the quiet direction: `keyUpdates` asks for a component that it
     * could build.
     */
    it('on a literal whose argument has a union type, where the type is the more careful', () => {
        const either = string('A' as 'A' | 'B')
        const spec = { kind: either, id: string }
        attest<[ConstantAttributes<typeof spec>], [never]>()
        expect(decided(spec)).toEqual(['kind'])
    })

    /**
     * A wrapper may change the value or admit absence, so neither side should call it decided —
     * and `optional` is the one that used to keep the claim on the record.
     */
    it('on a wrapped literal, which neither calls decided', () => {
        const wrapped = { TAG: optional(string('PET')), id: string }
        attest<[ConstantAttributes<typeof wrapped>], [never]>()
        expect(decided(wrapped)).toEqual([])

        const refined = {
            TAG: refine(string('PET'), (v): v is 'PET' => v === 'PET'),
            id: string,
        }
        attest<[ConstantAttributes<typeof refined>], [never]>()
        expect(decided(refined)).toEqual([])
    })

    /**
     * A stand-in is written on **every** write, so the attribute still holds one value, and both
     * halves say so.
     *
     * They did not until the mark carried the codec it marks. A field named that codec as an
     * `AttributeCodec`, which has no `constant`, so the brand was gone before the derivation asked
     * and the type answered `never` while the walk answered the value. It was the quiet direction —
     * the caller was asked for a component the runtime could have supplied — and it predated the
     * field types becoming declarations rather than being caused by it.
     */
    it('on a withLegacyRead over a literal, which both call decided', () => {
        const stood = {
            TAG: withLegacyRead({
                current: string('PET'),
                whenMissing: 'PET' as const,
            }),
            id: string,
        }
        attest<[ConstantAttributes<typeof stood>], ['TAG']>()
        expect(decided(stood)).toEqual(['TAG'])
    })

    /**
     * A `number` literal is the adapter over a numeral. The function reads the value that the call
     * named, so a numeric discriminator or tag decides, and the type read it as no text and asked
     * for the component that the function could supply.
     */
    it('on a single-valued number, which decides, and on a number of two values, which does not', () => {
        const counted = { age: number(5), litter: number(1, 2), id: string }
        attest<[ConstantAttributes<typeof counted>], ['age']>()
        expect(decided(counted)).toEqual(['age'])
    })

    /**
     * A caller's adapter over a literal owes that the pair cancels. One that refuses its own literal
     * admits no value, so it decides none. The refusal is not a value, and a key built from it would
     * hold a `CodecError` as a component.
     */
    it('on an adapter that refuses its own literal, which decides no value', () => {
        const broken = {
            kind: held(string('DOG'), string, {
                encode: () => 'DOG' as const,
                decode: () => new CodecError('this adapter reads no DOG'),
            }),
            id: string,
        }
        attest<[ConstantAttributes<typeof broken>], [never]>()
        expect(decided(broken)).toEqual([])
    })
})
