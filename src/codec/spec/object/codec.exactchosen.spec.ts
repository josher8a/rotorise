/**
 * A candidate is compared with the members of a union that it can be, and a name of another member is refused.
 *
 * The members that the candidate can be are found by the intersection of each member with the
 * candidate. An intersection of two objects with disjoint unit types at one property reduces to
 * `never`, so a member whose literal no literal of the candidate shares is not a member of the
 * candidate. The name that only that member holds is refused. A literal that the member holds as an
 * optional name, a number, a boolean, a union of literals, `null` and a name below an object follow
 * the same rule.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

// `ExactDeep` keeps the members of a union that the candidate can be. A name of another member is
// refused where an intersection of the two objects, with disjoint unit types at one property,
// reduces to `never`. Each compiler of the matrix must give each refusal.
type ChosenA = { k: 'a'; x?: number } | { k: 'b'; y?: number }
const chosenA = tableEntry<ChosenA>()({})
const chosenAKept = chosenA.unsafeToEntry({ k: 'a', x: 1 })
// @ts-expect-error y belongs to the other member
const chosenARefused = chosenA.unsafeToEntry({ k: 'a', y: 1 })

type ChosenB = { t?: 'x'; p: string } | { t?: 'y'; q: string }
const chosenB = tableEntry<ChosenB>()({})
const chosenBKept = chosenB.unsafeToEntry({ t: 'y', q: 'q' })
// @ts-expect-error p belongs to the member whose optional literal contradicts
const chosenBRefused = chosenB.unsafeToEntry({ t: 'y', p: 'p', q: 'q' })
// @ts-expect-error p belongs to the member whose optional literal contradicts
const chosenBOnly = chosenB.unsafeToEntry({ t: 'y', p: 'p' })

type ChosenC = { n: 1; p: string } | { n: 2; q: string }
const chosenC = tableEntry<ChosenC>()({})
// @ts-expect-error p belongs to the member of the other number
const chosenCRefused = chosenC.unsafeToEntry({ n: 2, p: 'p' })

type ChosenD = { f: true; p: string } | { f: false; q: string }
const chosenD = tableEntry<ChosenD>()({})
// @ts-expect-error p belongs to the member of the other boolean
const chosenDRefused = chosenD.unsafeToEntry({ f: false, p: 'p' })

type ChosenE = { m: 'a' | 'b'; p: string } | { m: 'c'; q: string }
const chosenE = tableEntry<ChosenE>()({})
const chosenEKept = chosenE.unsafeToEntry({ m: 'a', p: 'p' })
// @ts-expect-error p belongs to the member of the other literal
const chosenERefused = chosenE.unsafeToEntry({ m: 'c', p: 'p' })

type ChosenF = { z: null; p: string } | { z: 'x'; q: string }
const chosenF = tableEntry<ChosenF>()({})
// @ts-expect-error p belongs to the member that holds null
const chosenFRefused = chosenF.unsafeToEntry({ z: 'x', p: 'p' })

type ChosenG = { r: { s: 'a'; p: string } | { s: 'b'; q: string } }
const chosenG = tableEntry<ChosenG>()({})
const chosenGKept = chosenG.unsafeToEntry({ r: { s: 'a', p: 'p' } })
// @ts-expect-error q belongs to the member of the other literal, below a name
const chosenGRefused = chosenG.unsafeToEntry({ r: { s: 'a', q: 'q' } })

describe('a name of another member of a union is refused where the member cannot be the candidate', () => {
    it('keeps each call that a member admits', () => {
        expect(chosenAKept).toEqual({ k: 'a', x: 1 })
        expect(chosenBKept).toEqual({ t: 'y', q: 'q' })
        expect(chosenEKept).toEqual({ m: 'a', p: 'p' })
        expect(chosenGKept).toEqual({ r: { s: 'a', p: 'p' } })
    })

    it('refuses a name of the other member, in each kind of literal', () => {
        const refused = [
            chosenARefused,
            chosenBRefused,
            chosenBOnly,
            chosenCRefused,
            chosenDRefused,
            chosenERefused,
            chosenFRefused,
            chosenGRefused,
        ]
        expect(refused).toHaveLength(8)
    })
})
