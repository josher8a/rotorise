/**
 * **The refinement predicates the Lean bridge recognises, and the much larger set it still refuses.**
 *
 * `src/codec/lean.ts` used to refuse every `refine`, on the ground that `Pred.closure` carries
 * `q : Value → Bool` and this library carries a JavaScript closure. That ground is sound for an
 * arbitrary closure and unsound as a blanket: a predicate *this package exported* is not arbitrary,
 * it is a function with a specification, and the model has the same specification under a name. The
 * emitter now recognises those by reference and refuses the rest, so the boundary is "refinements
 * this library did not build" rather than "refinements".
 *
 * The defect this guards is the one the emitter exists to prevent, and it is a *silent* one: an
 * approximation — `fun _ => true` for a predicate, or a near-miss like a test for an `N` for `isNumeral` —
 * yields a Lean file that compiles and proves a theorem about a codec nobody shipped. So the
 * negative direction is tested at least as hard as the positive: a caller's own predicate must
 * still throw, and it must throw *naming itself*, so the boundary is legible from the error.
 *
 * Two facts found while wiring this up, both recorded here because each one is a trap:
 *
 * 1. **The correspondence is only over strings.** `isStoredNumeral` takes a `string`; the printed
 *    predicate takes a `Value`. `RegExp.test` stringifies, so `isStoredNumeral(['1'])` is `true` where
 *    the printed predicate at `Value.arr …` is `false`. The emitter confines itself to inner terms that write
 *    nothing but `Value.str`, where the gap is unobservable, and refuses otherwise.
 * 2. **`refine`'s two halves are not symmetric here, and are in the model.** This library's
 *    `refine` does *not* run `is` on encode (`src/codec/codec.ts:1466` says why: the argument is already
 *    typed), while `Codec.restrict`'s `e` is `if q v then c.e v else none`. So a value the
 *    predicate rejects is written by the library and refused by the model. That divergence is
 *    real, it is now *emittable*, and a vector built on such a value will fail the Lean build
 *    rather than pass — which is the differential test working, not the emitter mis-emitting.
 */
import { describe, expect, it } from 'vitest'
import { isNumeral, isStoredNumeral } from '../attribute'
import type { AnyCodec, AttributeCodec } from '../codec'
import { array, decimal, held, refine, string, withLegacyRead } from '../codec'
import { LeanUnemittable, leanClosedOf, leanVector } from '../lean'

/** The emitter takes the erased codec; the library's types are richer than it needs. */
const erase = (codec: unknown): AnyCodec => codec as AnyCodec

/**
 * `refine` wants a type predicate and `isNumeral` returns a `boolean`, so a caller passing one
 * writes a cast. The cast is what keeps the *reference* — which is the only thing the registry
 * looks at, and the reason it does not look at the source text.
 */
const narrowing = <T>(is: (value: string) => boolean) =>
    is as unknown as (value: string) => value is T & string

/** The root entry of a closed codec of one entry, as the scoped printer prints the entry. */
const rootOf = (codec: AnyCodec): string => {
    const printed = leanClosedOf(codec)
    const entry =
        /^\(⟨1, \(fun i => match i with \| ⟨0, _⟩ => \((.*) : Scoped\.Term 1 0\)\), 0⟩ : Closed\)$/.exec(
            printed,
        )
    if (entry?.[1] === undefined)
        throw new Error(`not a closed codec of one entry: ${printed}`)
    return entry[1]
}

const refusal = (emit: () => unknown): LeanUnemittable => {
    try {
        emit()
    } catch (error) {
        if (error instanceof LeanUnemittable) return error
        throw error
    }
    throw new Error('expected a refusal')
}

describe('the predicates this library ships', () => {
    /**
     * `isStoredNumeral` is what DynamoDB hands back, and `Numeral.Stored` is the same set —
     * `src/codec/attribute.ts:138` claims it and the two were checked against each other in the kernel
     * over a corpus of numeral spellings before this emission was allowed. The emitter writes
     * `Numeral.Stored` at the text carrier, because a refinement over `decimal` tests the caller's
     * text. The model's `isStored` decides a `.num`, and is false at every text.
     */
    it('emits `Numeral.Stored` at the text carrier for `isStoredNumeral`', () => {
        const stored = refine(decimal, narrowing(isStoredNumeral))
        expect(rootOf(erase(stored))).toBe(
            'Scoped.Term.refine ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) [])) (Pred.closure (fun v => match v with | .str s => Numeral.Stored s | _ => false)) ()',
        )
    })

    /**
     * `isNumeral` is the model's `Numeral.WF`. The model carries it in the type of `.num`, as a
     * `WFNumeral`, and names no predicate on values for it. So the emitter writes it out at the
     * text carrier, which is a closed expression in the model's own vocabulary and needs nothing
     * added to `formal/`.
     */
    it('emits `Numeral.WF` at the text carrier for `isNumeral`', () => {
        const wf = refine(string, narrowing(isNumeral))
        expect(rootOf(erase(wf))).toBe(
            'Scoped.Term.refine (Scoped.Term.string) (Pred.closure (fun v => match v with | .str s => Numeral.WF s | _ => false)) ()',
        )
    })

    /** Nested, because a refinement writes where its inner term does and the guard has to recurse. */
    it('emits a refinement of a refinement', () => {
        const both = refine(
            refine(string, narrowing(isNumeral)),
            narrowing(isStoredNumeral),
        )
        expect(rootOf(erase(both))).toContain(
            'Scoped.Term.refine (Scoped.Term.refine (',
        )
    })

    /** A string literal writes only strings, so the side condition is met there too. */
    it('emits over a string literal', () => {
        const one = refine(
            string('1', '2') as AttributeCodec<string>,
            narrowing(isStoredNumeral),
        )
        expect(rootOf(erase(one))).toContain('Numeral.Stored s')
    })

    /** The whole point: it has to survive the vector writer, not just the term writer. */
    it('reaches a whole vector', () => {
        const emitted = leanVector({
            name: 'stored',
            codec: erase(refine(decimal, narrowing(isStoredNumeral))),
            value: '1.5',
        })
        expect(emitted).toContain(
            'Scoped.Term.refine ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) [])) (Pred.closure (fun v => match v with | .str s => Numeral.Stored s | _ => false)) ()',
        )
        expect(emitted).toContain('Attr.n (WFNumeral.of "1.5")')
    })
})

describe('what is still refused', () => {
    /**
     * The negative direction, and the reason the registry is keyed by reference rather than by
     * `Function.prototype.toString`. A caller's closure is not the library's, however much it
     * looks like it — this one *is* `isStoredNumeral`, wrapped — and there is nothing in Lean it
     * names.
     */
    it('refuses a caller-supplied predicate, and says which one', () => {
        const mine = refine(
            string,
            (value: string): value is string => isStoredNumeral(value),
            { describe: 'a stored numeral' },
        )
        const why = refusal(() => leanClosedOf(erase(mine))).reason
        expect(why).toContain('Value → Bool')
        expect(why).toContain('not one this library ships')
        expect(why).toContain('a stored numeral')
    })

    /**
     * The coercion trap, refused rather than emitted. `String(['1'])` is `'1'`, so
     * `isStoredNumeral(['1'])` is `true` while `isStored (Value.arr …)` is `false` — and
     * `Codec.restrict`'s `e` consults `q` at every value, not only the ones the inner term likes.
     * Emitting here would be the near-miss this module refuses to make.
     */
    it('refuses a shipped predicate over an inner term that writes non-strings', () => {
        const coerced = refine(
            array(string) as unknown as AttributeCodec<string>,
            narrowing(isStoredNumeral),
        )
        expect(refusal(() => leanClosedOf(erase(coerced))).reason).toContain(
            'not strings',
        )
    })

    /**
     * **A caller's adapter, which is the one `held` the model has no name for.**
     *
     * This test used to say the library ships no adapters at all. It ships two now — `number` and
     * `decimal` are `held` over `dynamoNumber` — and the model names one of their pairs,
     * `numeralOfStoredText`/`textOfNumeral`, so `decimal` emits. What stays refused is a pair with
     * no name: a caller's closure has none, and `number`'s has none either, because its content is
     * binary64 rounding and writing that down is the axiom this development deleted.
     *
     * The registry is keyed by reference for the same reason the predicates are. A caller's
     * function is not the library's however much it looks alike.
     */
    it('refuses an adapter whose pair the model does not name', () => {
        const adapted = held(string, string, {
            encode: (value: string) => value,
            decode: (holding: string) => holding,
        })
        const why = refusal(() => leanClosedOf(erase(adapted))).reason
        expect(why).toContain('numeralOfStoredText')
        expect(why).toContain("a caller's closure has no name in the model")
    })

    /**
     * `withLegacyRead` is stuck on the closure, and on that alone now.
     *
     * It used to be stuck twice over, and this asserted the second reason: `Def['withLegacyRead']`
     * recorded only `current` and dropped the older readers at construction, so there was no `r`
     * in this library to recognise even if the model named one. The definition carries the reader
     * now, so that half is gone and the assertion moved to the half that remains — `r` is a JS
     * closure. A quantified verdict binds it as a variable, and an evaluation vector cannot run it,
     * so the emitter refuses a `withLegacyRead` outside a verdict.
     */
    it('refuses `withLegacyRead` outside a verdict, whose reader is a closure', () => {
        const older = withLegacyRead({
            current: string,
            older: { decode: () => 'older' as string },
        })
        expect(refusal(() => leanClosedOf(erase(older))).reason).toContain(
            'no evaluation vector prints one',
        )
    })
})
