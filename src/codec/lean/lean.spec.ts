/**
 * **The half of the bridge to `formal/` that runs here.**
 *
 * `src/codec/lean.ts` emits Lean source; only Lean can say whether that source is *true*. What this file
 * can say — and what nothing else says — is whether the emitter produces the text it thinks it
 * does, and, more importantly, whether it **refuses everything it cannot say**. A differential test
 * whose generator silently approximates is worse than no differential test: it produces a file that
 * compiles and proves a theorem about a codec nobody shipped.
 *
 * So the refusals are tested as carefully as the emissions, and they are the reason this file is
 * long. Each one names a fact about the model rather than about this library:
 *
 * - `Double` is an axiom, so `Value.num` has no closed term. `number` is out permanently.
 * - `refine`, `held` and `withLegacyRead` carry *functions* in the model and *closures* here.
 *   There is no expression in Lean for a closure. Out until somebody writes the Lean side by hand.
 * - `optional` and `withLegacyRead` are §4 `Field`s and `restOf` is a §4 `Rest`. Asking for a `Term` at
 *   one of them is a stratification error, and the emitter reports it as one rather than flattening
 *   it — which is the same discipline `NotAboutAbsence` enforces in the types.
 *
 * ── the sample ─────────────────────────────────────────────────────────────────────────────────
 *
 * `formal/lean.sample.lean` is a committed file of generated output, and the last test here regenerates
 * it and compares. It exists so a human can read the *shape* of what gets proposed without running
 * anything, and the comparison exists so it cannot rot: change the emitter and this test tells you
 * the sample is stale. Every theorem in it has been checked against the real `Calculus` build.
 */
import { readFileSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from '../attribute'
import { DynamoNumber } from '../attribute'
import type { AnyCodec, AttributeCodec } from '../codec'
import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    held,
    lazy,
    list,
    mdunion,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    product,
    refine,
    spread,
    string,
    union,
    withLegacyRead,
} from '../codec'
import { accepts } from '../denote'
import type {
    MeetPair,
    ReadResolution,
    ReadVerdict,
    Refusal,
    Resolution,
    Separation,
    Vector,
} from '../lean'
import {
    LeanUnemittable,
    leanAttrOf,
    leanMeet,
    leanMeetModule,
    leanReadModule,
    leanReadResolution,
    leanReadVector,
    leanReadVectorModule,
    leanResolutionModule,
    leanSeparation,
    leanSeparationModule,
    leanTermOf,
    leanValueOf,
    leanVector,
    leanVectorModule,
    readResolutionIsUnstatable,
    readRowIsStuck,
    readVectorIsUnstatable,
} from '../lean'
import { orThrow } from '../result'

/** The emitter takes the erased codec; the constructors return precise ones. */
const erase = (codec: unknown): AnyCodec => codec as AnyCodec

/** Whether the emitter can state this codec's term at all, which is a different axis from
 * whether its value has a Lean form. */
const statesTerm = (codec: AnyCodec, name: string): boolean => {
    try {
        leanTermOf(codec, name)
        return true
    } catch {
        return false
    }
}

/** What the emitter refused, and why — the part of a failure worth asserting on. */
const refusal = (emit: () => unknown): { at: string; reason: string } => {
    try {
        emit()
    } catch (error) {
        if (error instanceof LeanUnemittable) {
            return { at: error.at, reason: error.reason }
        }
        throw error
    }
    throw new Error('expected the emitter to refuse, and it did not')
}

describe('terms', () => {
    it('emits the ground terms by name', () => {
        expect(leanTermOf(erase(string))).toBe('Term.string')
        expect(leanTermOf(erase(dynamoNumber))).toBe('Term.number')
        // `decimal` is an adapter over that native, and the model names its pair
        expect(leanTermOf(erase(decimal))).toBe(
            '(Term.held (Term.number) numeralOfStoredText textOfNumeral)',
        )
        expect(leanTermOf(erase(boolean))).toBe('Term.boolean')
        expect(leanTermOf(erase(binary))).toBe('Term.binary')
        expect(leanTermOf(erase(nullValue))).toBe('Term.null')
    })

    /**
     * `literal` is base-indexed in the model and value-indexed here, and the two agree only at the
     * string base. `GroundKind` is the index and `k.Carrier` the value — so §3's premise line
     * (`g ground`, `ℓ ⊆ T`) is discharged by the type and the emitter writes one value.
     *
     * **Several alternatives are a union of singletons**, which is what the model says a set of
     * alternatives is. `string('A', 'B', 'C')` builds that union, so the emitter writes it.
     */
    it('emits a string literal as its base and its one value', () => {
        expect(leanTermOf(erase(string('only')))).toBe(
            'Term.literal GroundKind.string "only"',
        )
        expect(leanTermOf(erase(string('A', 'B', 'C')))).toBe(
            'Term.union [Term.literal GroundKind.string "A", Term.literal GroundKind.string "B", Term.literal GroundKind.string "C"]',
        )
    })

    /**
     * **A name, a literal or a tag outside ASCII reaches the model as a string Lean accepts.**
     *
     * Lean takes exactly four hex digits after `\u` and has no `\u{...}` form, so this emitted
     * `invalid hexadecimal numeral` for every non-ASCII character until the first one arrived.
     * Above `U+FFFF` no escape is correct at all — `\u1d538` lexes as `\u1d53` then `8` — so a
     * printable character goes raw and the control range keeps a four-digit escape.
     *
     * `literal_non_ascii` in the corpus is the vector, which is what makes this a gated rule
     * rather than an assertion about a string.
     */
    it('emits a character outside ASCII as one Lean accepts, at every code point', () => {
        // the BMP, where a four-digit escape would also have worked
        expect(leanTermOf(erase(string('⊥')))).toBe(
            'Term.literal GroundKind.string "⊥"',
        )
        // above `U+FFFF`, where no escape is correct and the raw character is the only spelling
        expect(leanTermOf(erase(string('𝔸')))).toBe(
            'Term.literal GroundKind.string "𝔸"',
        )
        // an object's names and a tag go through the same writer
        expect(leanTermOf(erase(object({ π: string }).item))).toContain('"π"')
        // and the control range keeps an escape, zero-padded to the four digits Lean wants
        expect(leanTermOf(erase(string('\u0001')))).toBe(
            'Term.literal GroundKind.string "\\u0001"',
        )
    })

    /**
     * **A decimal literal is a literal at the native base, under the named pair.** `decimal` was a
     * `GroundKind` with a `StoredNumeral` carrier, so an alternative was a pair gated by `by
     * decide`. The base is gone: `dynamoNumber` is the one native at `number` and `decimal` is
     * `held` over it, so the alternative is a `WFNumeral` and the gate it used to carry is the
     * adapter's own.
     *
     * The literal sits *under* the adapter and not beside it, which is what makes the pair
     * cancel: `numeralOfStoredText` carries the caller's text to the numeral the literal names.
     */
    it('emits a decimal literal at the native base, under the named pair', () => {
        expect(leanTermOf(erase(decimal('-1.5')))).toBe(
            '(Term.held (Term.literal GroundKind.number (WFNumeral.of "-1.5")) numeralOfStoredText textOfNumeral)',
        )
        expect(leanTermOf(erase(decimal('1', '2.5')))).toBe(
            '(Term.held (Term.union [Term.literal GroundKind.number (WFNumeral.of "1"), Term.literal GroundKind.number (WFNumeral.of "2.5")]) numeralOfStoredText textOfNumeral)',
        )
    })

    /**
     * And a binary literal, which was refused for a reason that was never true: `leanValueOf` has
     * emitted `Value.bin` for a `Uint8Array` all along, so a vector at a binary literal can state
     * both halves. Kernel-checked the same way.
     */
    it('emits a binary literal as its octets', () => {
        expect(leanTermOf(erase(binary(new Uint8Array([0, 127, 255]))))).toBe(
            'Term.literal GroundKind.binary [0, 127, 255]',
        )
    })

    /**
     * **`number` is refused because its conversion has no name, and the refusal is permanent.**
     *
     * It used to be refused because `GroundKind.number` carried the `Double` axiom. That axiom is
     * deleted, and `dynamoNumber` above emits. What is refused now is the *adapter*: `number`
     * carries a JS float over the native, so its pair is binary64 rounding, and writing that down
     * is the axiom this development removed. The model names one pair and this is not it.
     */
    it('refuses a numeric literal, permanently', () => {
        const why = refusal(() => leanTermOf(erase(number(1)))).reason
        expect(why).toContain('numeralOfStoredText')
        expect(why).toContain('binary64 rounding')
    })

    it('emits the containers structurally', () => {
        expect(leanTermOf(erase(array(string)))).toBe(
            'Term.array (Term.string)',
        )
        expect(leanTermOf(erase(object([string, optional(boolean)])))).toBe(
            'Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.boolean)))',
        )
        expect(leanTermOf(erase(list(string, boolean)))).toBe(
            'Term.tuple [Term.string, Term.boolean] none',
        )
    })

    /**
     * A set is **not** structural, and stopped being so the day `Term.set` took a `SetBase`. This
     * emitted `Term.set (<element term>)` until then, and the generated file stopped compiling —
     * which is the defect this test now guards.
     *
     * **There is one numeric set base now, and two adapters over it.** `SetBase.decimal` went with
     * the `decimal` ground base: `number.set()` and `decimal.set()` are one wire set under two
     * elementwise conversions, so the base that used to tell them apart no longer exists and the
     * adapter is what does.
     */
    it('emits a set as its base, not as its element term', () => {
        expect(leanTermOf(erase(string.set()))).toBe('Term.set SetBase.string')
        expect(leanTermOf(erase(dynamoNumber.set()))).toBe(
            'Term.set SetBase.number',
        )
        expect(leanTermOf(erase(binary.set()))).toBe('Term.set SetBase.binary')
    })

    /**
     * **A set of an adapter is refused, and this is the model's gap rather than the library's.**
     *
     * `decimal` emits as a scalar, because `DynamoDB.lean` names its pair —
     * `numeralOfStoredText`/`textOfNumeral`. `.set()` maps that conversion over the wire set, and
     * the model has no name for the set-level pair: writing one wants the element pair carried
     * over an `NEFinset`, which is a `Finset.image` and a proof that the image is nonempty.
     *
     * So the emitter refuses rather than invent a name, and this test is where the gap is
     * recorded. **It is meant to fail when the model gains the pair**, and the failure is the
     * signal to emit these two instead.
     */
    it('refuses a set of an adapter, which the model cannot name yet', () => {
        for (const codec of [decimal.set(), number.set()]) {
            const why = refusal(() => leanTermOf(erase(codec))).reason
            expect(why).toContain('numeralOfStoredText')
        }
    })

    /**
     * A *restricted* element is printed as the restriction of the set it is.
     *
     * `string.set('a','b')` is `refine(set(string), each(members …))` and the model spells that
     * predicate the same way, `Pred.each (Pred.members k ls)` — the two `Predicate` types are one
     * shape. It used to print the predicate's *meaning*, `liftQ (inL k ls)`, because `Term.refine`
     * carried a function and there was no constructor to print; `Pred.eval` is where those two
     * expressions live now. Both halves are data the term carries, so both print, and the equation
     * licensing the spelling is `setCodec_restrict` on `e` and `setCodec_restrict_p` on `p`.
     *
     * **A closure element is still refused, and permanently.** The predicate is a caller's
     * JavaScript function; the registry recognises two by reference and there is no expression for
     * any other. That refusal is not waiting on a pass.
     */
    it('prints a set of a literal element, and refuses one over a closure', () => {
        expect(leanTermOf(erase(string.set('a', 'b')))).toBe(
            'Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "a" {"b"})))',
        )
        const positive = refine(
            decimal,
            (value: string): value is string => !value.startsWith('-'),
            { describe: 'non-negative' },
        )
        expect(() => leanTermOf(erase(positive.set()))).toThrow(
            /not one this library ships/,
        )
    })

    /**
     * The refusal that had no test, and it needs a cast to reach.
     *
     * A codec's definition is a term, so nothing well typed hands the emitter a field and the branch
     * reads as dead. It is not: a brand is not a proof and a cast defeats a brand, which is why the
     * entry takes a declaration and refuses one, and why this is asserted through `erase` rather than
     * left to the type. `ObjectSlot.optional` is emitted where a field belongs — in an object's table —
     * and the two spellings are what §4's strata mean.
     */
    it('refuses a field where a term belongs, reached past a cast', () => {
        expect(() => leanTermOf(erase(optional(string)))).toThrow(
            /a §4 \*field\*, not a term/,
        )
        expect(() =>
            leanTermOf(
                erase(withLegacyRead({ current: string, whenMissing: 'x' })),
            ),
        ).toThrow(/`optional`\/`fallback` denote `Field`/)
        expect(leanTermOf(erase(object({ a: optional(string) })))).toContain(
            'ObjectSlot.optional',
        )
    })

    /**
     * §4's field table is a `Finset Name` with a function on it, not a list of pairs — so an object
     * emits a key set and a chain of key tests, and the last field is the `else`. That is total
     * because the subtype's inhabitants are exactly the declared keys.
     */
    it('emits an object as a key set and a function on it', () => {
        expect(
            leanTermOf(erase(object({ a: string, b: optional(boolean) }))),
        ).toBe(
            'Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) none)',
        )
    })

    /** The empty key set has no `else` to fall through to, so the function is the absurd one. */
    it('emits an object with no fields as the absurd function', () => {
        expect(leanTermOf(erase(object({})))).toBe(
            'Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) none)',
        )
    })

    /**
     * **A field's stand-in value has no slot, and the model put that stratum elsewhere.**
     *
     * This emitted `Field.fallback (t) (v)` against a `Field` with three constructors. An
     * `ObjectSlot` has two, and the older reader lives in `Codec.extendRead` — a codec *outside*
     * `Term`, over the current term's codec. `ExactA.lean` says so in as many words: its table has
     * no alternate-reader row because an alternate reader is outside `Term`.
     *
     * So this is not a slot the model declined to add. It is a stratum the model moved, and a
     * `Body` has nowhere to print it. The refusal is the honest answer until the emitter states a
     * `Codec.extendRead` rather than a `Term` for such a codec.
     */
    it('refuses a missing-value field, which is a stratum outside the term', () => {
        const why = refusal(() =>
            leanTermOf(
                erase(
                    object({
                        a: withLegacyRead({
                            current: string,
                            whenMissing: 'd',
                        }),
                    }),
                ),
            ),
        ).reason
        expect(why).toContain('Codec.extendRead')
        expect(why).toContain('no alternate-reader slot')
    })

    it('emits an open object as the one open block', () => {
        expect(
            leanTermOf(
                erase(object({ a: string }, [string, optional(boolean)])),
            ),
        ).toBe(
            'Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) (some (Term.boolean)))',
        )
    })

    /**
     * **The place the emitter used to guess.**
     *
     * `Def` recorded the rest *codec*, and both `'drop'` and `'refuse'` recorded nothing — so
     * the definition alone could not tell them apart and this wrote `Rest.drop` for either. It was
     * not wrong for the vectors this module writes: `objectCodec`'s `e` is `objWrite sems rc?`,
     * which never sees the `kn` filter the policy decides, and `rcOf` is `none` for both, so the two
     * denote the *same* `e`. It was wrong about the codec, and a decode-direction vector — whose `p`
     * is exactly where they differ — would have been silently false. `Body['rest']` now carries
     * the policy, and the emitter reads it rather than guessing.
     */
    it('emits the strict object policy', () => {
        expect(leanTermOf(erase(object({ a: string })))).toBe(
            'Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) none)',
        )
    })

    it('emits a union as its option list', () => {
        expect(leanTermOf(erase(union([string, boolean])))).toBe(
            'Term.union [Term.string, Term.boolean]',
        )
        // `nullable` is a builder, so the null point emits as the union it is
        expect(leanTermOf(erase(nullable(string)))).toBe(
            'Term.union [Term.string, Term.null]',
        )
    })

    /**
     * **A dissection emits as the `Term.union` of objects it is.**
     *
     * There is one sum, so there is one row. The members are `Term.object` terms, each declaring
     * its discriminator as a required literal in its own body, and the tag table is the builder's
     * own index that no term carries.
     */
    it('emits a discriminated union as the union of objects it is', () => {
        const emitted = leanTermOf(
            erase(
                discriminatedUnion('kind', [
                    object({ kind: string('a'), x: string }),
                    object({ kind: string('b'), y: string }),
                ]),
            ),
        )
        // **there is one sum, so there is one row.** The members are `object` terms and the tag
        // table is the builder's own index, carried by no term — so what reaches the model is the
        // union the declaration always was, and the discriminators are the required literals in
        // each member's body
        expect(emitted).toContain('Term.union [Term.object')
        expect(emitted).toContain(
            'ObjectSlot.req (Term.literal GroundKind.string "a")',
        )
        expect(emitted).toContain(
            'ObjectSlot.req (Term.literal GroundKind.string "b")',
        )
        expect(emitted).not.toContain('Term.dunion')
        expect(emitted.split('Body.mk')).toHaveLength(3)
    })

    it('forces a lazy and emits what it finds', () => {
        expect(leanTermOf(erase(lazy(() => string)))).toBe(
            'Term.lazy (Term.string)',
        )
    })

    /**
     * **The canonical `opaque` is the model's exact `opaq`**, and a numeric policy has no
     * term there. Each policy is a `held` over the canonical term whose pair converts a JS number,
     * and the model names no such pair, so the emitter refuses it as it refuses a caller's closure.
     */
    it('emits the total opaque as the exact opaq, and refuses each numeric policy', () => {
        expect(leanTermOf(erase(opaque))).toBe('Term.opaq')
        expect(leanTermOf(erase(opaque()))).toBe('Term.opaq')
        for (const numbers of ['lossy', 'refuse'] as const) {
            expect(
                refusal(() => leanTermOf(erase(opaque(numbers)))).reason,
            ).toContain('Value → Value')
        }
    })
})

describe('what cannot be emitted', () => {
    /**
     * **A JS float is refused, and a numeral is not. The line moved and this is where.**
     *
     * `Value.num` carried a `Double`, an axiom with no constructor, so *no* numeric value could be
     * written and the refusal was permanent on both sides. `Value.num` carries a `WFNumeral` now:
     * the digits are the value, so a numeral is a closed term and `dynamoNumber` emits in both
     * directions.
     *
     * What is refused is the conversion, not the carrier. A JS number is a binary64 float, so
     * putting one into a `WFNumeral` is IEEE-754 rounding, which is exactly the axiom this
     * development deleted rather than a gap to be filled later.
     */
    it('refuses a JS float, and emits the numeral the carrier holds', () => {
        expect(leanTermOf(erase(dynamoNumber))).toBe('Term.number')
        expect(leanValueOf(orThrow(DynamoNumber.from('1.5')))).toBe(
            'Value.num (WFNumeral.of "1.5")',
        )
        expect(refusal(() => leanValueOf(1.5)).reason).toContain('WFNumeral')
        expect(refusal(() => leanValueOf(new Set([1, 2]))).reason).toContain(
            'binary64 float',
        )
    })

    /**
     * And a `number` literal, which is refused as the *adapter* it is rather than for its
     * alternatives. `dynamoNumber('1.5')` is a literal at `GroundKind.number` and emits; `number(1,
     * 2)` is that literal under a pair the model does not name.
     */
    it('refuses a numeric literal, which is the adapter and not the base', () => {
        const why = refusal(() => leanTermOf(erase(number(1, 2)))).reason
        expect(why).toContain('binary64 rounding')
        expect(
            leanTermOf(erase(dynamoNumber(orThrow(DynamoNumber.from('1.5'))))),
        ).toBe('Term.literal GroundKind.number (WFNumeral.of "1.5")')
    })

    /**
     * Four of §3's constructors carry functions. The model's `refine` holds `q : Value → Bool`;
     * this library holds a JavaScript predicate. Nothing translates one into the other, and
     * emitting a *different* predicate — `fun _ => true`, say — would produce a file that compiles
     * and proves the wrong theorem, which is the failure mode this whole module exists to avoid.
     */
    it('refuses the four function-carrying terms', () => {
        const notEmpty = refine(
            string,
            (value: string): value is string => value.length > 0,
            { describe: 'non-empty' },
        )
        expect(refusal(() => leanTermOf(erase(notEmpty))).reason).toContain(
            'Value → Bool',
        )
        const adapted = held(string.set(), {
            encode: (value: readonly string[]) => new Set(value),
            decode: (holding: ReadonlySet<string>) => [...holding],
        })
        expect(refusal(() => leanTermOf(erase(adapted))).reason).toContain(
            'Value → Value',
        )
        const older = withLegacyRead({
            current: string,
            older: { decode: () => 'older' as string },
        })
        expect(refusal(() => leanTermOf(erase(older))).reason).toContain(
            'Attr → Option Value',
        )
    })

    /**
     * §4's stratification, reported as itself. `optional(c)` denotes a `Field` and no `Term`
     * position accepts one — the model makes that a fact about the types (`Field` is a separate
     * inductive), and this library makes it a fact about markers. Asking the emitter for a `Term`
     * at one is a category error, and it says so rather than unwrapping to the inner term, which
     * would quietly emit a *required* field where the caller declared an optional one.
     */
    it('refuses a field where a term is asked for', () => {
        expect(
            refusal(() => leanTermOf(erase(optional(string)))).reason,
        ).toContain('§4 *field*')
        expect(
            refusal(() =>
                leanTermOf(
                    erase(
                        withLegacyRead({ current: string, whenMissing: 'd' }),
                    ),
                ),
            ).reason,
        ).toContain('§4 *field*')
    })

    /**
     * §1 types all three wire sets as `℘⁺fin`, so `NEFinset` has no empty inhabitant and an empty
     * set has no expression at all. This library refuses an empty set too — but at encode time,
     * with a `CodecError`; here it is refused at emit time, with the model's reason.
     */
    it('refuses an empty wire set', () => {
        expect(refusal(() => leanAttrOf({ SS: [] })).reason).toContain('℘⁺fin')
    })

    /**
     * A recursive codec is not a deep term; it is *no* term. `Term.lazy` carries a `Term` and not a
     * thunk, deliberately — `formal/Calculus/Continuity.lean` shows `union`'s admission is
     * anti-monotone, so a genuinely recursive union has no fixpoint semantics in any system. The
     * emitter therefore stops at a depth rather than diverging, and reports that.
     */
    it('refuses a recursive lazy rather than looping', () => {
        const recursive: AnyCodec = erase(
            lazy(() => recursive as unknown as AttributeCodec<unknown>),
        )
        expect(refusal(() => leanTermOf(recursive)).reason).toContain(
            'no fixpoint semantics',
        )
    })

    /**
     * **The two sides agree about what a tag is now, at two of the three bases.**
     *
     * The host carries a tag as `S` or `N`, so `discriminatedUnion` admits a discriminator at
     * `string`, `number` or `decimal` and refuses `boolean` and `binary`. The model reads a
     * discriminator as the literal it is, through `Calculus.altsOfField`, at `string` and at
     * `decimal` alike — a decimal literal holds its numeral as text — so a decimal discriminator
     * emits on both halves.
     *
     * **`number` stays refused and the reason changed twice.** It was a disagreement between two
     * rules; then it was `Calculus.Double`, an axiom with no closed terms. That axiom is deleted
     * and the refusal is now the adapter's: a `number` tag is a literal at the native base under a
     * pair whose content is binary64 rounding, and the model names no such pair.
     */
    it('refuses a tag at the numeric adapter, whose pair has no name', () => {
        const numeric = erase(
            discriminatedUnion('kind', [
                object({ kind: number(0), a: string }),
                object({ kind: number(1), b: string }),
            ]),
        )
        // the refusal is the adapter's, not a row about tags: a numeric discriminator is a
        // `number` literal field, and `number` is `held` over the native wherever it appears.
        // Deleting the tagged row lost no refusal, only a second statement of this one
        const why = refusal(() => leanTermOf(numeric)).reason
        expect(why).toContain('binary64 rounding')

        // **a decimal tag emits now**, which is the half of the disagreement that closed: it is
        // stored in an `N` and carried as text, and both of the model's tag readers answer that
        const decimals = erase(
            discriminatedUnion('v', [
                object({ v: decimal('1'), a: string }),
                object({ v: decimal('2'), b: string }),
            ]),
        )
        expect(leanTermOf(decimals)).toContain('Term.union')
        expect(leanTermOf(decimals)).toContain('numeralOfStoredText')

        // and a string tag emits, which it always did
        expect(
            leanTermOf(
                erase(
                    discriminatedUnion('kind', [
                        object({ kind: string('A'), a: string }),
                        object({ kind: string('B'), b: string }),
                    ]),
                ),
            ),
        ).toContain('Term.union')
    })
})

describe('values and attributes', () => {
    it('emits the scalars', () => {
        expect(leanValueOf('hi')).toBe('Value.str "hi"')
        expect(leanValueOf(true)).toBe('Value.bool true')
        expect(leanValueOf(null)).toBe('Value.null')
        expect(leanValueOf(new Uint8Array([1, 2]))).toBe('Value.bin [1, 2]')
        expect(leanAttrOf({ N: '1.5' })).toBe('Attr.n (WFNumeral.of "1.5")')
    })

    /**
     * `M` is a key set with a function on it on both sides of §1, so a map value and a map
     * attribute emit the same shape. The empty one is the interesting case: there is no key to
     * test, so the function is `absurd` on the membership proof.
     */
    it('emits a map as a key set and a chain of key tests', () => {
        expect(leanValueOf({ a: 'x', b: 'y' })).toBe(
            'Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y")',
        )
        expect(leanValueOf({})).toBe(
            'Value.map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1))',
        )
    })

    /**
     * §4's `optional` is about *presence*, so an absent attribute is a name the key set does not
     * have. Emitting `Value.null` for it would be a different vector — one about `nullable` — and
     * would pass or fail for the wrong reason.
     */
    it('drops an absent optional rather than writing null for it', () => {
        expect(leanValueOf({ a: 'x', b: undefined })).toBe(
            'Value.map {"a"} (fun k => Value.str "x")',
        )
    })

    /**
     * Lean's escape language and JSON's overlap and disagree, silently, and this test asserted the
     * disagreement backwards. Lean has no `\u{...}` form: it takes exactly four hex digits, so
     * everything this wrote outside printable ASCII was a file that does not parse. A printable
     * character goes out raw, at every code point, and the control range keeps a padded escape.
     */
    it('escapes strings the way Lean reads them, not the way JSON writes them', () => {
        expect(leanValueOf('a\tb')).toBe('Value.str "a\\tb"')
        expect(leanValueOf('q"\\')).toBe('Value.str "q\\"\\\\"')
        expect(leanValueOf('\u0001')).toBe('Value.str "\\u0001"')
        expect(leanValueOf('é')).toBe('Value.str "é"')
    })
})

describe('a whole vector', () => {
    /**
     * The attribute is not an argument: it is read out of the library by running the encode the
     * theorem is about. That is what makes this a differential test rather than a restatement — a
     * change to `codec.ts` that changes what it writes makes the Lean file stop compiling, and no
     * human has to remember to update an expected value.
     */
    it('takes its right-hand side from the library, not from the caller', () => {
        const emitted = leanVector({
            name: 'scalar_string',
            codec: erase(string),
            value: 'hello',
        })
        expect(emitted).toContain('theorem scalar_string :')
        expect(emitted).toContain('(denote (Term.string)).e')
        expect(emitted).toContain('(Value.str "hello")')
        expect(emitted).toContain('(some (Attr.s "hello")) = .same')
    })

    /**
     * The same claim in the older protocol, kept because it depends on nothing but `denote` and
     * is what a tree without `Calculus/Vectors.lean` can still check. It cannot state a refusal,
     * and on a map `rfl` does not fail but diverges — which is why it is no longer the default.
     */
    it('still emits the bare equation when asked for it', () => {
        const emitted = leanVector(
            { name: 'scalar_string', codec: erase(string), value: 'hello' },
            'equation',
        )
        expect(emitted).toContain('= some (Attr.s "hello")')
        expect(emitted).not.toContain('check ')
        expect(emitted.trimEnd().endsWith('vector')).toBe(true)
    })

    it('sanitizes a name into a Lean identifier', () => {
        expect(
            leanVector({
                name: 'set of string',
                codec: erase(string),
                value: 'x',
            }),
        ).toContain('theorem set_of_string :')
    })

    it('imports the comparator the default protocol is cashed against', () => {
        const module = leanVectorModule([])
        expect(module).toContain('import Calculus.Vectors')
        expect(module).toContain('namespace Calculus')
        expect(module.trimEnd().endsWith('end Calculus')).toBe(true)
    })

    /** The equation protocol carries its own proof, so its preamble is the one with the tactic. */
    it('carries the tactic and the imports the equation protocol needs', () => {
        const module = leanVectorModule([], 'equation')
        expect(module).toContain('import Calculus.Denote')
        expect(module).toContain('import Mathlib.Tactic.FinCases')
        expect(module).toContain('macro "vector" : tactic')
        expect(module.trimEnd().endsWith('end Calculus')).toBe(true)
    })
})

/**
 * The vectors in the committed sample, in the order they appear there.
 *
 * Chosen to cover one of each *shape the emitter has a branch for*, not one of each codec: the
 * emitter's branches are where it can be wrong, and the model's branches are where the two can
 * disagree. Every one of these has been checked against a real `Calculus` build.
 */
export const sampleVectors: readonly Vector[] = [
    { name: 'scalar_string', codec: erase(string), value: 'hello' },
    { name: 'scalar_decimal', codec: erase(decimal), value: '1.5' },
    { name: 'scalar_boolean', codec: erase(boolean), value: true },
    {
        name: 'scalar_binary',
        codec: erase(binary),
        value: new Uint8Array([0, 127, 255]),
    },
    { name: 'scalar_null', codec: erase(nullValue), value: null },
    {
        name: 'literal_alternatives',
        codec: erase(string('A', 'B')),
        value: 'B',
    },
    {
        name: 'literal_decimal',
        codec: erase(decimal('1', '2.5')),
        value: '2.5',
    },
    // one alternative in the BMP and one above `U+FFFF`, which is where no escape is correct
    {
        name: 'literal_non_ascii',
        codec: erase(string('⊥', '𝔸')),
        value: '𝔸',
    },
    {
        name: 'literal_binary',
        codec: erase(binary(new Uint8Array([0, 127, 255]))),
        value: new Uint8Array([0, 127, 255]),
    },
    {
        name: 'set_of_string',
        codec: erase(string.set()),
        value: new Set(['b', 'a']),
    },
    /**
     * A set over a **literal** element, which is a restriction of the set and not a `set` term.
     *
     * Added when the emitter learned to print a data predicate. The model reads it as
     * `refine (set string) (liftQ (inL …))`, which is the equation `setCodec_restrict` proves on
     * `e` and `setCodec_restrict_p` on `p` — so this vector is the differential asking the model
     * about the one shape that took three passes to spell.
     */
    {
        name: 'set_of_literal',
        codec: erase(string.set('a', 'b')),
        value: new Set(['b', 'a']),
    },
    // **at the native, not at `decimal`.** `decimal.set()` is an adapter over this one, and the
    // model has no name for a set-level pair yet, so the vector states the base the model has
    {
        name: 'set_of_number',
        codec: erase(dynamoNumber.set()),
        value: new Set([
            orThrow(DynamoNumber.from('1.5')),
            orThrow(DynamoNumber.from('2')),
        ]),
    },
    { name: 'array_of_string', codec: erase(array(string)), value: ['a', 'b'] },
    /**
     * **The two shapes that put `meetLists` and `dominates` to the model.**
     *
     * Before these, every list in the corpus was `array` or `tuple`: three shapes with a spread
     * and an empty prefix and suffix, and one with a prefix of two and no spread. So `dominates`
     * was only ever asked about a shape against itself, where it answers true for both reasons,
     * and the fixed-arity branch only ever answered `never`. The bridge never asked the model
     * about a suffix, about a flattening that survives, or about the refusal at all.
     *
     * These two are the smallest pair that asks all four, and it takes two because the refusal
     * needs *two* shapes neither of which dominates. Against the corpus they state:
     * the meet of a prefix against a plain spread, where the prefix side dominates
     * (`array_of_string`); the meet against a fixed arity that **flattens and survives**
     * (`list_spread_suffix` against `tuple_pair`, which answers the tuple itself); and the
     * window where neither dominates, `p1 s0` against `p0 s1`, which answers `none`.
     */
    {
        name: 'list_prefix_spread',
        codec: erase(list(string, spread(string))),
        value: ['a', 'b', 'c'],
    },
    {
        name: 'list_spread_suffix',
        codec: erase(list(spread(string), boolean)),
        value: ['a', 'b', true],
    },
    { name: 'array_empty', codec: erase(array(string)), value: [] },
    {
        name: 'tuple_pair',
        codec: erase(list(string, boolean)),
        value: ['a', true],
    },
    {
        name: 'open_of_string',
        codec: erase(object([string, optional(string)])),
        value: { a: 'x', b: 'y' },
    },
    {
        name: 'open_empty',
        codec: erase(object([string, optional(string)])),
        value: {},
    },
    {
        name: 'object_two_fields',
        codec: erase(object({ a: string, b: boolean })),
        value: { a: 'x', b: true },
    },
    {
        name: 'object_optional_absent',
        codec: erase(object({ a: string, b: optional(boolean) })),
        value: { a: 'x' },
    },
    {
        name: 'object_fallback_present',
        codec: erase(
            object({
                a: withLegacyRead({ current: string, whenMissing: 'stand-in' }),
            }),
        ),
        value: { a: 'x' },
    },
    {
        name: 'object_open',
        codec: erase(object({ a: string }, [string, optional(boolean)])),
        value: { a: 'x', z: true },
    },
    {
        name: 'object_nested',
        codec: erase(object({ a: object({ b: string }) })),
        value: { a: { b: 'x' } },
    },
    /**
     * **Two open objects, each with a refinement.** Both meet an object at `none`, because the model's `objObj` refuses a pair unless both open blocks are absent. The
     * bridge asserts that refusal in both orders.
     */
    {
        name: 'open_of_restricted_set',
        codec: erase(object([string, optional(string.set('a', 'b'))])),
        value: { a: new Set(['a']) },
    },
    {
        name: 'object_restricted_rest',
        codec: erase(
            object({ a: string.set('b', 'c') }, [
                string,
                optional(string.set('b', 'c')),
            ]),
        ),
        value: { a: new Set(['b']), z: new Set(['c']) },
    },
    {
        name: 'map_inside_a_list',
        codec: erase(array(object([string, optional(string)]))),
        value: [{ a: 'x' }],
    },
    {
        name: 'union_of_two',
        codec: erase(union([string, boolean])),
        value: true,
    },
    { name: 'nullable_null', codec: erase(nullable(string)), value: null },
    // **The vector pass 7 owed.** Two object options with the *same* names, told apart by a
    // required literal and by nothing else — so the names alone resolve neither and `byStructure`
    // resolves both. Nothing in this corpus exercised the literal half of admission before, which
    // is why the bridge passed unchanged while the model gained it.
    {
        name: 'union_by_literal',
        codec: erase(
            union([
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), x: boolean }),
            ]),
        ),
        value: { kind: 'a', x: 'v' },
    },
    {
        name: 'discriminated_union',
        codec: erase(
            discriminatedUnion('kind', [
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), y: boolean }),
            ]),
        ),
        value: { kind: 'a', x: 'v' },
    },
    // a product, so the bridge sees one: the merged body is an ordinary `object` term, which is
    // the whole content of `Body.merge` on the host side
    {
        name: 'product_two_objects',
        codec: erase(product(object({ a: string }), object({ n: boolean }))),
        value: { a: 'x', n: true },
    },
    // the distribution: a product over a union of objects is a flat union of the merges
    {
        name: 'product_union_object',
        codec: erase(
            product(
                union([object({ a: string }), object({ b: boolean })]),
                object({ n: decimal }),
            ),
        ),
        value: { a: 'x', n: '1' },
    },
    // and the fold, which `merge_assoc` on `fields` and `rest` is why either nesting gives
    {
        name: 'product_three',
        codec: erase(
            product(
                object({ p: string }),
                object({ q: boolean }),
                object({ r: decimal }),
            ),
        ),
        value: { p: 'x', q: true, r: '1' },
    },
    // **a two-key dissection**, which is a union of three objects each pinning two required
    // literals. Built through `mdunion`, where it used to be a hand-written term: there is one sum
    // now, so the builder's result is an ordinary union and the public surface makes it
    {
        name: 'dunion_two_keys',
        codec: erase(
            mdunion(
                ['kind', 'size'],
                [
                    object({
                        kind: string('pet'),
                        size: string('small'),
                        toy: string,
                    }),
                    object({
                        kind: string('pet'),
                        size: string('large'),
                        pen: string,
                    }),
                ],
            ),
        ),
        value: { kind: 'pet', size: 'small', toy: 'ball' },
    },
    { name: 'opaque_map', codec: erase(opaque), value: { a: 'x' } },
    { name: 'lazy_string', codec: erase(lazy(() => string)), value: 'x' },
]

/**
 * The refusal corpus, both readings of it.
 *
 * {@link allRefusals} is every pair from the positive corpus the codec refuses — the full cross
 * product, which `scripts/gate.sh` generates and elaborates. {@link sampleRefusals} is the
 * readable subset committed to `lean.sample*.lean`: **one per codec kind**, the first corpus value
 * that codec turns down. The subset says its own size against the full count in the file header,
 * because a subset that does not say it is one is the same defect as a count nobody can reproduce.
 *
 * `number` is in the codec list and in no positive vector, which is the point: `Term.number` is a
 * closed term whose *values* are unwritable, so it has refusals and no agreements.
 *
 * `opaque` is the one codec with **no** refusal, and that is a result rather than a gap: it is the
 * fixpoint of everything self-identifying, so it admits every value in this corpus. A codec that
 * refuses nothing contributes no refusal vector, and the subset says one less than the whole
 * for that reason.
 */
const refusalCodecs: readonly (readonly [string, AnyCodec])[] = [
    ...sampleVectors.map((v) => [v.name, v.codec] as const),
    ['scalar_number', erase(dynamoNumber)] as const,
    ['never', erase(never)] as const,
    // a refusal vector states the term and no value, so a codec whose *term* the model cannot
    // spell states nothing here either. `object_fallback_present` is the one, and it is named by
    // the read-side test rather than dropped in silence
].filter(([cn, codec]) => statesTerm(codec, cn))

export const allRefusals = (): readonly Refusal[] => {
    const out: Refusal[] = []
    for (const [cn, codec] of refusalCodecs) {
        for (const vector of sampleVectors) {
            if (accepts(codec, vector.value)) continue
            out.push({
                name: `${cn}__refuses__${vector.name}`,
                codec,
                value: vector.value,
            })
        }
    }
    return out
}

/** Whether the emitter can state this codec's term at all, which is a different axis from its
 * value. `object_fallback_present` is the one corpus entry that fails it: a field's older reader
 * lives in `Codec.extendRead`, outside `Term`, so a `Body` has no slot to print it. */
const emittable = (one: Vector): boolean => statesTerm(one.codec, one.name)

/**
 * The **read** vectors the committed sample carries: the same "one per kind" rule the refusals use.
 *
 * `.readvectors.lean` holds all 27 and the gate elaborates every one. A sample is for reading, so
 * it takes the ground scalars, one container, one object and one union — enough that a reader sees
 * what the shape of a read vector is without scrolling through the corpus.
 */
const readSample: readonly Vector[] = sampleVectors.filter((one) =>
    [
        'scalar_string',
        'scalar_boolean',
        'set_of_string',
        'array_of_string',
        'object_two_fields',
        'union_of_two',
    ].includes(one.name),
)

export const sampleRefusals: readonly Refusal[] = refusalCodecs.flatMap(
    ([cn, codec]) => {
        const first = sampleVectors.find((v) => !accepts(codec, v.value))
        return first
            ? [
                  {
                      name: `${cn}__refuses__${first.name}`,
                      codec,
                      value: first.value,
                  },
              ]
            : []
    },
)

describe('the `check` protocol', () => {
    /**
     * The second protocol exists because `formal/Calculus/Vectors.lean` does — a hand-written
     * three-valued comparator with `check_same` proved about it, so `.same` is a *proof* of
     * equality and not a comparator's opinion. Where it is available it is the better target: no
     * tactic, no `funext` gymnastics, and it can state a negative vector, which an equation cannot.
     *
     * The fuel is computed from the attribute rather than fixed generously, because `aeq` recurses
     * on the budget — only structural recursion reduces in the kernel — so the generator owes it a
     * number. One layer per `L` or `M`, one for the scalar at the bottom.
     */
    it('states the claim through `check`, with fuel for the attribute it wrote', () => {
        expect(
            leanVector(
                { name: 'scalar', codec: erase(string), value: 'x' },
                'check',
            ),
        ).toContain('check 1')
        expect(
            leanVector(
                {
                    name: 'nested',
                    codec: erase(object({ a: object({ b: string }) })),
                    value: { a: { b: 'x' } },
                },
                'check',
            ),
        ).toContain('check 3')
        expect(
            leanVector(
                { name: 'scalar', codec: erase(string), value: 'x' },
                'check',
            ).trimEnd(),
        ).toMatch(/= \.same := rfl$/)
    })

    it('imports the comparator instead of carrying a tactic', () => {
        const module = leanVectorModule([], 'check')
        expect(module).toContain('import Calculus.Vectors')
        expect(module).not.toContain('macro "vector"')
    })
})

/**
 * Every option pair the corpus offers, with `src/`'s declaration verdict.
 *
 * `leanTermOf` is what bounds it: a pair either side of which is term-inexpressible cannot be put
 * to the model at all. Over the emittable pairs the split measured 268 both-certify, 17
 * both-refuse, **0** where `src/` refuses and `Orth` certifies, and 66 where `src/` accepts and
 * `Orth` declines — the last being `Orth`'s sufficiency rather than a disagreement.
 */
const separationPairs = (): readonly Separation[] => {
    const codecs: readonly (readonly [string, AnyCodec])[] = [
        ...sampleVectors.map((v) => [v.name, v.codec] as const),
        ['scalar_number', erase(dynamoNumber)] as const,
        ['never', erase(never)] as const,
    ]
    const out: Separation[] = []
    for (let x = 0; x < codecs.length; x++) {
        for (let y = x + 1; y < codecs.length; y++) {
            const [an, left] = codecs[x] as readonly [string, AnyCodec]
            const [bn, right] = codecs[y] as readonly [string, AnyCodec]
            try {
                leanTermOf(left, an)
                leanTermOf(right, bn)
            } catch {
                continue
            }
            try {
                union([left, right] as never)
                continue // accepted: the law does not run in this direction
            } catch {
                out.push({ name: `${an}__vs__${bn}`, left, right })
            }
        }
    }
    return out
}

/**
 * Every pair of corpus terms, for the meet differential.
 *
 * Bounded the same way the separation pairs are — a term the emitter has no closed expression for
 * cannot be put to the model — and bounded once more at the *answer*, because a meet can build a
 * term out of two that the printer declines. Both bounds are skips and not failures.
 *
 * Every pair is emitted, the refusals included. `none` and `.never` are the distinction the meet
 * exists to keep, so a pair this library refuses is as much of a claim as one it answers.
 */
const MEET_DEFERRED: readonly string[] = []

const meetPairs = (): readonly MeetPair[] => {
    const codecs: readonly (readonly [string, AnyCodec])[] = [
        ...sampleVectors.map((v) => [v.name, v.codec] as const),
        ['scalar_number', erase(dynamoNumber)] as const,
        ['never', erase(never)] as const,
    ]
    const out: MeetPair[] = []
    for (let x = 0; x < codecs.length; x++) {
        for (let y = x + 1; y < codecs.length; y++) {
            const [an, left] = codecs[x] as readonly [string, AnyCodec]
            const [bn, right] = codecs[y] as readonly [string, AnyCodec]
            const one: MeetPair = { name: `${an}__meet__${bn}`, left, right }
            try {
                leanMeet(one)
            } catch {
                continue
            }
            if (MEET_DEFERRED.includes(one.name)) continue
            out.push(one)
        }
    }
    return out
}

/**
 * Every (codec, attribute) pair the corpus offers, for the read-side differential.
 *
 * The attributes are what the corpus actually *writes*, plus six raw shapes for the members no
 * corpus vector produces alone. Bounded by `leanAttrOf` the way the pairs are bounded by
 * `leanTermOf`: an attribute the model has no closed expression for cannot be put to it.
 */
const readVerdicts = (): readonly ReadVerdict[] => {
    const codecs: readonly (readonly [string, AnyCodec])[] = [
        ...sampleVectors.map((v) => [v.name, v.codec] as const),
        ['scalar_number', erase(dynamoNumber)] as const,
    ]
    const attributes: [string, AttributeValue][] = []
    for (const v of sampleVectors) {
        try {
            attributes.push([
                v.name,
                v.codec.unsafeEncode(v.value as never) as AttributeValue,
            ])
        } catch {
            // a value its own codec refuses writes no attribute to read back
        }
    }
    attributes.push(['raw_S', { S: 'x' } as AttributeValue])
    attributes.push(['raw_N', { N: '1.5' } as AttributeValue])
    attributes.push(['raw_BOOL', { BOOL: true } as AttributeValue])
    attributes.push(['raw_NULL', { NULL: true } as AttributeValue])
    attributes.push(['raw_L_empty', { L: [] } as AttributeValue])
    attributes.push(['raw_M_empty', { M: {} } as AttributeValue])

    const out: ReadVerdict[] = []
    for (const [cn, codec] of codecs) {
        try {
            leanTermOf(codec, cn)
        } catch {
            continue
        }
        for (const [an, attribute] of attributes) {
            try {
                leanAttrOf(attribute, an)
            } catch {
                continue
            }
            out.push({ name: `${cn}__reads__${an}`, codec, attribute })
        }
    }
    return out
}

/**
 * The unions this bridge resolves, and why they are a list rather than the corpus.
 *
 * `sampleVectors` carries two — `union_of_two` and `discriminated_union` — and both are already
 * pinned in the committed sample. These widen that: the pair `ff75c6b` un-refused
 * (`set(string)`/`set(number)`, which `Orth` certifies), objects chosen by name, two literals,
 * a `nullValue` arm, an `optional` inside a variant, and a three-way `dunion`. Every one is legal
 * at the declaration and emittable.
 */
const resolutionUnions = (): readonly (readonly [string, AnyCodec])[] => [
    ['u_string_boolean', erase(union([string, boolean]))],
    ['u_string_null', erase(union([string, nullValue]))],
    ['u_setstring_setnumber', erase(union([string.set(), dynamoNumber.set()]))],
    [
        'u_objects_by_name',
        erase(union([object({ a: string }), object({ b: boolean })])),
    ],
    ['u_literal_pair', erase(union([string('A'), string('B')]))],
    // **the slice, as a term the model can read.** An extraction is a `union` over the members it
    // kept, so what the bridge elaborates here is `Calculus.AltClause.extract`'s result spelled as
    // an ordinary union — which is the whole claim: the slice builds no new kind of term
    [
        'u_extracted',
        erase(
            union([
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), x: boolean }),
                object({ kind: string('c'), x: decimal }),
            ]).extract({ kind: string('a', 'b') }),
        ),
    ],
    [
        'u_objects_by_literal',
        erase(
            union([
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), x: boolean }),
            ]),
        ),
    ],
    [
        'u_optional_inner',
        erase(union([string, object({ z: optional(boolean) })])),
    ],
    [
        'd_two_variants',
        erase(
            discriminatedUnion('kind', [
                object({ kind: string('a'), x: string }),
                object({ kind: string('b'), y: boolean }),
            ]),
        ),
    ],
    [
        'd_three_variants',
        erase(
            discriminatedUnion('t', [
                object({ t: string('p'), v: string }),
                object({ t: string('q'), v: boolean }),
                object({ t: string('r'), v: decimal }),
            ]),
        ),
    ],
]

const writeResolutions = (): readonly Resolution[] =>
    resolutionUnions().flatMap(([un, u]) =>
        sampleVectors.flatMap((v) => {
            try {
                leanValueOf(v.value, v.name)
            } catch {
                return []
            }
            return [{ name: `ur_${un}__${v.name}`, union: u, value: v.value }]
        }),
    )

const readResolutions = (): readonly ReadResolution[] => {
    const attributes: [string, AttributeValue][] = []
    for (const v of sampleVectors) {
        try {
            attributes.push([
                v.name,
                v.codec.unsafeEncode(v.value as never) as AttributeValue,
            ])
        } catch {
            // a value its own codec refuses writes no attribute to read back
        }
    }
    attributes.push(['raw_S', { S: 'x' } as AttributeValue])
    attributes.push(['raw_BOOL', { BOOL: true } as AttributeValue])
    attributes.push(['raw_NULL', { NULL: true } as AttributeValue])
    return resolutionUnions().flatMap(([un, u]) =>
        attributes.flatMap(([an, attribute]) => {
            try {
                leanAttrOf(attribute, an)
            } catch {
                return []
            }
            return [{ name: `rr_${un}__${an}`, union: u, attribute }]
        }),
    )
}

describe('union resolution, model against library', () => {
    /**
     * **Coverage, and it is worth being exact about that.** Two resolutions were pinned before —
     * a positive vector *is* an agreement about which option answered, since the attribute it
     * names is the one that option produced — and the refusal set carries 88 more union lines.
     * This widens two to 208, and the value is the corpus rather than the question. 216 with
     * `set_of_literal`, and 248 by `literal_non_ascii` and the three products: each new entry
     * adds the resolutions of the unions it takes part in.
     */
    it('offers 370 write pairs and every one of 400 read pairs', () => {
        expect(writeResolutions().length).toBe(370)
        const reads = readResolutions()
        expect(reads.length).toBe(400)
        /**
         * **No pair is unstatable now, and the one that was is the axiom's last appearance here.**
         *
         * `rr_u_setstring_setnumber__set_of_decimal` read back to a `Value.numSet` over a
         * `NEFinset Double`, which had no closed terms. `Value.num` carries a `WFNumeral` since
         * `ac951ae`, so a numeral set is a closed term and the pair states. This asserts the empty
         * list rather than dropping the check, because a pair becoming unstatable again is the
         * thing worth failing on.
         */
        expect(
            reads
                .filter((one) => readResolutionIsUnstatable(one) === 'Double')
                .map((one) => one.name),
        ).toEqual([])
    })

    /**
     * The five a `Value` comparator closed, named — they read back to a map, whose `Value.map`
     * carries a function, and `aeq`/`check` compare `Attr` only. `veq` is that comparator and
     * these are the pairs it was built for, so they are pinned as **statable** rather than as a
     * shortfall, and pinned by the fact that they go through `vcheck`.
     */
    it('states the five map-valued reads that wanted `veq`', () => {
        const byName = new Map(
            readResolutions().map((one) => [one.name, one] as const),
        )
        for (const name of [
            'rr_u_objects_by_name__object_optional_absent',
            'rr_u_objects_by_name__object_fallback_present',
            'rr_u_objects_by_name__opaque_map',
            'rr_u_optional_inner__open_empty',
            'rr_d_two_variants__discriminated_union',
        ]) {
            const one = byName.get(name) as ReadResolution
            expect(readResolutionIsUnstatable(one)).toBeUndefined()
            expect(leanReadResolution(one)).toContain('vcheck')
        }
    })

    it('emits them for the gate to elaborate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.resolutions.lean'),
                leanResolutionModule(writeResolutions(), readResolutions()),
            )
        }
        const module = leanResolutionModule(
            writeResolutions(),
            readResolutions(),
        )
        expect(module).toContain('import Calculus.Vectors')
        // the one pair that stays out, and the reason, both in the header
        expect(module).toContain('cannot be written down at all')
        expect(module).toContain('vcheck')
    })
})

describe("the read side, against the model's read row", () => {
    /**
     * **The measurement that rejected a port.** HANDOFF's fourth item wanted the resolver's read
     * side decided through a port of `AdmA`. `decode` already agrees with `AdmA` at every pair
     * the kernel can check, because `decode` validates — it parses data somebody else wrote —
     * where `encode` trusted its argument's type. So the port would have been a second
     * description of one thing, and this differential is the guard that a second description
     * would have needed anyway.
     */
    it('offers 1326 pairs, three of them stuck on the `Double` axiom', () => {
        const verdicts = readVerdicts()
        // 1634 until `object_fallback_present` left the emittable corpus: a field's older
        // reader lives in `Codec.extendRead`, outside `Term`, so a `Body` has no slot to print it
        expect(verdicts.length).toBe(1591)
        const stuck = verdicts.filter(readRowIsStuck)
        expect(stuck.map((one) => one.name)).toEqual([
            'scalar_number__reads__scalar_decimal',
            'scalar_number__reads__literal_decimal',
            'scalar_number__reads__raw_N',
        ])
    })

    it('emits them for the gate to elaborate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.readverdicts.lean'),
                leanReadModule(readVerdicts()),
            )
        }
        const module = leanReadModule(readVerdicts())
        expect(module).toContain('import Calculus.DynamoDB')
        // the excluded ones are named in the header rather than dropped in silence
        expect(module).toContain('excluded, not skipped')
        expect(module).toContain('scalar_number__reads__raw_N')
    })
})

describe("the declaration guard, against the model's classifier", () => {
    /**
     * **`src/` refuses seventy-three pairs, and each one carries a warrant.** That is the whole
     * law, and it is one-directional on purpose: `Orth` is sufficient and not necessary, so a
     * pair it declines may still be separable. What would be a defect is `src/` refusing a
     * declaration the model *proves* works — which is what it did to
     * `union([string.set(), number.set()])` until `ff75c6b`, and what `Orth` certifies.
     *
     * **It was thirty-six, and the ones that arrived all have `never` on a side.** `never` admits
     * no value, so every value it admits every other option admits, and {@link restricts} answers
     * the containment at its narrowest width.
     *
     * **Those carry the other warrant, and needed it.** `Orth` *certifies* a pair with `never` on
     * a side — `never` occupies no slot and meets nothing — so asserting `Orth x y = false` about
     * one is false, and `decide` refuted nineteen of them the first time this corpus carried the
     * bottom. The model types the union too: `HNever` is disjoint from every held
     * set, and §5's (D) admits a disjoint pair. So these carry the *permits*-form, `dincomp_never_left` and
     * `dincomp_never_right`, and the emitter states which warrant a pair carries. `src/` refuses
     * them on usefulness — an option admitting nothing can never be chosen — and that is a
     * divergence the artifact records rather than a disagreement about soundness.
     *
     * **The four before those all have a *restriction* on a side**, which is `opaque`'s rule at a
     * narrower width: a literal against its own base's ground term, three of them, and a set of a
     * literal against the plain set at that base. Every value the narrower option admits, the
     * wider one admits too, so `select` acts nowhere on the narrower and it can never be chosen.
     * The type level already refused all four; this is the runtime agreeing with it. `Orth`
     * declines every one, `not_orth_literal_string` on purpose, so the law is untouched.
     *
     * **It was seventeen, and the fifteen that arrived all have `opaque` on a side.** The guard
     * exempted an `opaque` option rather than comparing it, on the ground that its occupancy is
     * `⊤`. §5 separates the two things a `⊤` covers, and `opaque` is the *everything* one: the
     * model states it as a closed form, so it can be compared and it meets every option. Every one
     * of the fifteen new theorems holds — `Orth Term.opaq Term.string` is `false` — so the
     * law was untouched either way, and what moved is that a union no value can resolve is now
     * refused where it used to be declared. JH's ruling, landed in `ff75c6b`.
     *
     * **It was seventy-three, and the seven that arrived are all object against object.** Pass 7
     * gave the runtime guard the structural meet, where its object row used to answer `true`
     * unconditionally and defer to the type's `Collides`. So a pair of object options whose name
     * intervals meet and which no required literal tells apart is now refused at construction as
     * well as at the declaration:
     * `object_two_fields__vs__object_optional_absent`, `object_optional_absent__vs__` each of
     * `object_fallback_present`, `object_open` and `object_nested`,
     * `object_fallback_present__vs__` each of `object_open` and `object_nested`, and
     * `object_open__vs__object_nested`. `Orth` declines every one, so the law is untouched and
     * what moved is that the two levels now answer one rule instead of two.
     *
     * **It was 111, then 117, and it is 112.** Two corpus movements, and neither is the guard
     * changing its mind. Six pairs arrived with the `decimal` base being deleted, and five left
     * with `object_fallback_present`, which stopped being emittable: a field's older reader lives
     * in `Codec.extendRead`, a codec outside `Term`, so a `Body` has no slot to print it.
     *
     * The six that arrived:
     * `dynamoNumber` is the one native at `number` and `decimal` is `held` over it, so two codecs
     * a *base* used to tell apart now collide at `N` and the pairs are refused:
     * `scalar_decimal__vs__scalar_number` and `literal_decimal__vs__scalar_number` are that
     * collision named, and `set_of_number` replaced `set_of_decimal` because a set of an adapter
     * cannot be emitted yet. `crossesStringDecimal` and `crossesNumberDecimal` went with the base,
     * which is the same fact from the other side.
     *
     * **It was 157, and the eight that arrived all have a sum on the wider side.** {@link restricts}
     * reads a term inside one option of a sum as inside the sum, and `opaque` is the universal
     * sum. Four pairs have `opaque_map` on a side, against `literal_alternatives`,
     * `literal_binary`, `literal_non_ascii` and `set_of_literal`. Four have a union that holds the
     * base of the literal: `literal_alternatives` and `literal_non_ascii`, each against
     * `union_of_two` and `nullable_null`. `identifies` accepted all eight, and `Orth` declines
     * all eight.
     *
     * **It was 165, and the one that arrived is `opaque_map__vs__scalar_number`.** The canonical
     * `opaque` is total now: it holds a number as a `DynamoNumber`, so it writes the `number`
     * slot and reads `N`, where the `'refuse'` policy that `opaque_map` used to carry wrote
     * neither. `dynamoNumber` writes and reads exactly those, so the two options meet on both
     * sides and the pair is refused. `Orth Term.opaq Term.number` is `false`, so the
     * warrant is `Orth` declining, and no pair left.
     *
     * **Measured, and it is the question this count exists to answer**: the disjointness law
     * `6536d91` added refuses **none** of these pairs. Every refusal here is an occupancy or a
     * restriction, and no pair is refused for carrying a value another pair also carries.
     *
     * **The count pins a fact no law has, deliberately.** That it is 117 is a property of this
     * corpus, so widening the corpus is meant to fail here and be looked at; the *law* is the loop
     * below, that every refusal the model also declines. Both are kept, and the number stays.
     */
    it('refuses only pairs the classifier also declines', () => {
        const separations = separationPairs()
        expect(separations.length).toBe(166)
        // each one emits, which is where `leanSeparation` re-checks that `src/` really refuses,
        // and it carries one of the two warrants: `Orth` declines, or — for a `never` pair, where
        // the model permits what `src/` lints away — the permits-form states what the model says
        for (const one of separations) {
            const emitted = leanSeparation(one)
            expect(
                emitted.includes('= false := by decide') ||
                    emitted.includes(': ∀ T : Held, DIncomp '),
            ).toBe(true)
        }
    })

    it('emits them for the gate to elaborate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.separations.lean'),
                leanSeparationModule(separationPairs()),
            )
        }
        expect(leanSeparationModule([])).toContain(
            'import Calculus.Orthogonality',
        )
        // a `held` term spells `numeralOfStoredText`, which only `Separation` declares, and
        // without the import Lean auto-binds the name and every verdict fails to elaborate
        expect(leanSeparationModule([])).toContain('import Calculus.DynamoDB')
    })

    /**
     * **The meet, both directions.** `Term.meet` and `meetTerms` are one function written twice,
     * so a disagreement either way is a defect on one side. This is the only check that measures
     * the meet: the host's `unionOk` reads `separable`, which exempts what the model's `Orth` does
     * not, and no other guard holds that divergence.
     */
    it('puts every corpus meet to the model', () => {
        const meets = meetPairs()
        expect(meets.length).toBe(703)
        expect(MEET_DEFERRED.length).toBe(0)
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.meets.lean'),
                leanMeetModule(meets, MEET_DEFERRED),
            )
        }
        expect(leanMeetModule([])).toContain('import Calculus.Meet')
    })

    /** And the direction the law does not run, refused rather than emitted as a vacuous claim. */
    it('refuses to state a verdict about a pair src accepts', () => {
        expect(
            refusal(() =>
                leanSeparation({
                    name: 'accepted',
                    left: erase(string),
                    right: erase(boolean),
                }),
            ).reason,
        ).toContain('one-directional')
    })
})

describe('the full refusal set, for the gate', () => {
    /**
     * **The subset is committed for reading; this is what gets verified.**
     *
     * `scripts/gate.sh` runs this with `EMIT_LEAN_REFUSALS=1` and elaborates the file it writes,
     * which is why the file is gitignored rather than committed: a 599-line artifact regenerated
     * on every gate run has nothing to gain from being in the tree, and a diff nobody reads is a
     * diff nobody checks. The committed sample is the readable half and says so in its header.
     */
    it('emits every refusal the corpus produces', () => {
        const refusals = allRefusals()
        expect(refusals.length).toBeGreaterThan(sampleRefusals.length)
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.vectors.full.lean'),
                leanVectorModule([], 'check', refusals),
            )
        }
        // every corpus value is refused by some codec, which is what makes the cross product a
        // corpus rather than a sample of one
        const values = new Set(
            refusals.map((r) => r.name.split('__refuses__')[1]),
        )
        expect(values.size).toBe(sampleVectors.length)
    })
})

/**
 * **The read side of every corpus codec, which the write vectors could not reach.**
 *
 * A write vector asserts `(denote t).e v = some a` and a refusal vector asserts `= none`. Both are
 * about `e`. The model's `p` was asserted only where a union had to choose — `.resolutions.lean`
 * states `(denote t).p a = some v` per read resolution — so for the corpus at large one half of
 * every pair was proposed to the model and the other half was not.
 *
 * These close that. Both halves come from running the library: `a` is what `encode` wrote for the
 * corpus value, `v` is what the same codec's `decode` read back from `a`. So the theorem says the
 * model's `p`, given what this library wrote, answers what this library read — and a change to
 * either direction stops the file compiling.
 */
describe("the read side of every corpus codec, against the model's `p`", () => {
    /**
     * **One is skipped, and it is the term rather than the value.**
     *
     * No *value* is unspellable any more. `Value.num` carried a `Double`, an axiom with no closed
     * terms; it carries a `WFNumeral` now, so a numeral is a closed term and a numeric value on
     * the read side states like any other.
     *
     * What is skipped is `object_fallback_present`, whose **term** the emitter refuses: a field's
     * older reader lives in `Codec.extendRead`, a codec outside `Term`, so a `Body` has no slot to
     * print it. It is named here rather than filtered in silence, because a second exclusion
     * arriving is the thing worth failing on.
     */
    it('states a read vector for every codec whose term the model can spell', () => {
        expect(
            sampleVectors.filter((one) => !emittable(one)).map((o) => o.name),
        ).toEqual(['object_fallback_present'])
        const statable = sampleVectors.filter(
            (one) =>
                readVectorIsUnstatable(one) === undefined && emittable(one),
        )
        expect(statable.length).toBe(sampleVectors.length - 1)
        expect(statable.length).toBe(36)
        // each asserts the model's `p`, through the comparator that crosses `Value.map`'s binder
        for (const one of statable) {
            const vector = leanReadVector(one)
            expect(vector).toContain('vcheck')
            expect(vector).toContain('.p')
            expect(vector).toContain('= .same := rfl')
        }
    })

    it('emits them for the gate to elaborate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.readvectors.lean'),
                leanReadVectorModule(sampleVectors.filter(emittable)),
            )
        }
        const module = leanReadVectorModule(sampleVectors.filter(emittable))
        expect(module).toContain('import Calculus.Vectors')
        // a `held` term spells `numeralOfStoredText`, which only `Separation` declares, and
        // without the import `denote` sticks on a free variable and no vector elaborates
        expect(module).toContain('import Calculus.DynamoDB')
        // the header states what it could not state, which for this corpus is nothing
        expect(module).toContain('every corpus codec round trips')
    })
})

describe('the committed sample', () => {
    /**
     * A sample that is not regenerated is a sample that lies — **and a regenerated one lies just
     * as well, because regeneration is not verification.** This compares the emitter's bytes
     * against files the emitter produced, so a *stale generator agrees with its own stale
     * output*: it cannot see the generator being wrong, and for a day it did not. `db444e3`
     * changed `Term.object` from three arguments to one, this test stayed green, and both sample
     * files typechecked against no `Calculus/` for ten commits (`e9f5b31`).
     *
     * What this test *can* see is the emitter changing without the sample being rewritten, which
     * is worth keeping. What says the samples are **true** is `scripts/gate.sh`, which elaborates
     * them — and the full refusal cross product — against `Calculus/`. Do not read a pass here as
     * the bridge working.
     */
    it('is what the emitter produces today', () => {
        // `process.cwd()` rather than `import.meta.url`: `tsconfig.json` targets a module setting
        // that has no `import.meta`, and vitest runs from the package root
        for (const [file, protocol] of [
            ['lean.sample.lean', 'equation'],
            ['lean.sample.check.lean', 'check'],
        ] as const) {
            const at = join(process.cwd(), 'formal', file)
            const emitted = leanVectorModule(
                // `object_fallback_present` is excluded and named by the test above: its term has
                // no `ObjectSlot`, so the sample states the codecs the model can spell
                sampleVectors.filter(emittable),
                protocol,
                sampleRefusals,
                allRefusals().length,
                // the read subset is the `check` sample's alone: a read vector needs `vcheck`, and
                // the `equation` sample depends on nothing beyond `denote` by design
                protocol === 'check' ? readSample : [],
            )
            // `UPDATE_LEAN_SAMPLE=1 vitest run src/codec/lean/lean.spec.ts` rewrites them — and then they have
            // to go through Lean again, because nothing here can say the new theorems are true
            if (process.env.UPDATE_LEAN_SAMPLE) writeFileSync(at, emitted)
            expect(emitted).toBe(readFileSync(at, 'utf8'))
        }
    })
})
