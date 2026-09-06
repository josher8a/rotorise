/**
 * The three facts a codec used to store, read from its definition instead.
 *
 * `child`, `member` and `constant` were fields every constructor had to set and every wrapper had
 * to carry, and the carrying is what kept going wrong: `refine` dropped `child` and `member`;
 * `item`, `map`, `tagged` and `untagged` each wrote an `M` without saying so; `optional` kept a
 * `constant` it had no business keeping. There was a list — `inherited` — naming which survived a
 * wrapper, and it existed only because they were stored.
 *
 * `writes`, `decides` and `deeper` read them off `def` instead, so there is nothing to forget.
 * `inherited` is down to `arbitrary` and `shrink`, which are the escape hatch and not facts.
 */
import { describe, expect, it } from 'vitest'
import { memberOf } from './attribute'
import { CodecError, nullable, number, refine, string } from './codec'

const isTag = (v: string): v is `t-${string}` => v.startsWith('t-')

describe('the member a codec writes', () => {
    /**
     * **`number` writes `N`, and the Lean corpus structurally cannot say so.**
     *
     * `src/lean.ts` refuses every numeric *value*: `Double` is an axiom with no closed terms, so
     * `Value.num` is unconstructible and no positive vector at `number` can be stated. The term is
     * emittable — `Term.number` appears in the refusal cross product and in the separation pairs —
     * and only the value side is blocked, which is enough to block the vector.
     *
     * So this is one of exactly **two** members the corpus cannot pin, and the member is read off
     * the attribute rather than off a reader, which is the only instrument left.
     *
     * A trap for whoever tries to close it by adding a vector: `scalar_number` is already a
     * twenty-seventh codec, added by hand at three sites in `lean.spec.ts` with no value. Putting
     * it in `sampleVectors` would list it twice and move the pair count from 351 to 378, taking
     * the separation and refusal counts with it.
     */
    it('is `N` for `number`, which no vector in the corpus can state', () => {
        expect(memberOf(number.unsafeEncode(1))).toBe('N')
    })

    /** …and for a numeric literal, refused one level up at `GroundKind.number`'s carrier. */
    it('is `N` for a numeric literal, refused at the same axiom', () => {
        expect(memberOf(number(0, 1).unsafeEncode(1))).toBe('N')
    })

    /** What the set builder reads, and the reason a codec has to be able to say it at all. */
    it('is what lets a refined scalar still be a set element', () => {
        expect(() => refine(string, isTag).set()).not.toThrow()
        // @ts-expect-error `nullable` writes no single member, so the type declines the capability
        expect(() => refine(nullable(string), isTag).set()).toThrow(CodecError)
    })
})
