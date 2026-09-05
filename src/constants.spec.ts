/**
 * The two answers to "does this codec decide its value", held against each other.
 *
 * `ConstantAttributes<Spec>` is a type and `decides(codec)` is a function, and they reach the answer
 * by different routes: the type reads the `ConstantCodec` brand, the function reads `def.kind` and
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
import type { AnyCodec, AnyDeclaration, ConstantCodec } from './codec'
import { decides, decimal, fallback, optional, refine, string } from './codec'
import type { ConstantAttributes } from './Rotorise'

/**
 * What `decides` answers, for the runtime half of each pairing.
 *
 * The type half is `attest<[Expected], [Actual]>()`, written at each call rather than in here.
 * `attest` reads its own source position, so a type-only assertion inside a helper would compare
 * the helper's *generic* types once and say nothing about any particular spec.
 *
 * Wrapped in tuples so that `never` is expressible: `attest`'s second parameter defaults to `never`
 * and it refuses that as an explicit argument, since it cannot tell it from the default.
 */
const decided = (spec: Record<string, AnyDeclaration>): readonly string[] =>
    Object.entries(spec)
        .filter(([, declared]) => constantOf(declared) !== undefined)
        .map(([name]) => name)
        .sort()

/**
 * The runtime half, with §4's two marks read.
 *
 * A mirror of `Rotorise.ts`'s `constantOf`, which is not exported, and a mirror to the same degree
 * the walk above always was. `keycomponents.spec.ts` is the test that runs the real one.
 */
const constantOf = (declared: AnyDeclaration): unknown => {
    const def = declared.def
    if (def.kind === 'optional') return undefined
    if (def.kind === 'fallback') return decides(def.inner)
    return decides(declared as AnyCodec)
}

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
     * The case that was wrong, and is not reachable through the constructors — which is why it
     * survived.
     *
     * A codec branded as deciding *two* values decides neither. Asking only whether a `constant` was
     * declared made the type call this decided while `decides` called it undecided: `keyUpdates`
     * would not ask for the component, then throw demanding it.
     */
    it('on a codec branded with two values, which decides neither', () => {
        const twoValued = string('A', 'B') as unknown as ConstantCodec<
            'A' | 'B'
        >
        const spec = { kind: twoValued, id: string }
        attest<[ConstantAttributes<typeof spec>], [never]>()
        expect(decided(spec)).toEqual([])
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
     * The pairing where the two do **not** agree, pinned so the next reader sees it.
     *
     * A stand-in is written on every write, so the function calls the attribute decided. The type
     * does not, and cannot as written: a field names the codec it marks as an `AttributeCodec`, which
     * carries no `constant`, so the brand is gone by the time the derivation asks. This predates R4 —
     * `FallbackCodec` erased the brand the same way when it was an intersection — and R4 moved both
     * halves without changing either answer.
     *
     * It is the quiet direction. The caller is asked for a component the runtime could have supplied,
     * which costs an argument rather than a throw. The loud direction is what this file exists for.
     */
    it('on a fallback over a literal, where the two disagree', () => {
        const stood = {
            TAG: fallback(string('PET'), 'PET' as const),
            id: string,
        }
        attest<[ConstantAttributes<typeof stood>], [never]>()
        expect(decided(stood)).toEqual(['TAG'])
    })
})
