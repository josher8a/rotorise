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
 * - A JS number is a binary64 float, and `Value.num` carries an exact `WFNumeral`, so a JS number
 *   has no Lean value. A `DynamoNumber` is a numeral and emits.
 * - `refine`, `held` and `withLegacyRead` carry *functions* in the model and *closures* here.
 *   There is no expression in Lean for a closure. A declaration verdict binds a caller's closure
 *   and a caller's adapter as variables of the theorem, and every other vector refuses them.
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
import { DynamoNumber, isNumeral } from '../attribute'
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
    DisjointPair,
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
    leanDisjoint,
    leanDisjointModule,
    leanGuard,
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
            '(Term.held (Term.number) (Term.string) [(.decimalText, false)])',
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
            '(Term.held (Term.literal GroundKind.number (WFNumeral.of "-1.5")) (Term.literal GroundKind.string "-1.5") [(.decimalText, false)])',
        )
        expect(leanTermOf(erase(decimal('1', '2.5')))).toBe(
            '(Term.held (Term.union [Term.literal GroundKind.number (WFNumeral.of "1"), Term.literal GroundKind.number (WFNumeral.of "2.5")]) (Term.union [Term.literal GroundKind.string "1", Term.literal GroundKind.string "2.5"]) [(.decimalText, false)])',
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
     * A set prints as `Term.set` of its element term, because the model's `Term.set` takes one:
     * the set is the finite-powerset lift of its element.
     */
    it('emits a set as the set of its element term', () => {
        expect(leanTermOf(erase(string.set()))).toBe('Term.set (Term.string)')
        expect(leanTermOf(erase(dynamoNumber.set()))).toBe(
            'Term.set (Term.number)',
        )
        expect(leanTermOf(erase(binary.set()))).toBe('Term.set (Term.binary)')
    })

    /**
     * **A set of an adapter prints as the set of the adapter**, because the conversion rides at the
     * element. `decimal` has a pair the model names, so its set prints. The float adapter has no
     * name in the model, so its set is refused for the reason its scalar is.
     */
    it('emits the set of a named adapter, and refuses the set of an unnamed one', () => {
        expect(leanTermOf(erase(decimal.set()))).toBe(
            'Term.set ((Term.held (Term.number) (Term.string) [(.decimalText, false)]))',
        )
        const why = refusal(() => leanTermOf(erase(number.set()))).reason
        expect(why).toContain('numeralOfStoredText')
    })

    /**
     * A *restricted* element prints at the element. `string.set('a','b')` is the set of the union
     * of the two literals.
     *
     * **A closure element is still refused, and permanently.** The predicate is a caller's
     * JavaScript function; the registry recognises two by reference and there is no expression for
     * any other. That refusal is not waiting on a pass.
     */
    it('prints a set of a literal element, and refuses one over a closure', () => {
        expect(leanTermOf(erase(string.set('a', 'b')))).toBe(
            'Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"])',
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

    it('prints a thunk that closes no cycle as the term it returns', () => {
        expect(leanTermOf(erase(lazy(() => string)))).toBe('Term.string')
    })

    /**
     * **A thunk that throws is a free variable, and the emitter returns a term for it.** The
     * thunk names a codec not yet declared. The host reads the thunk as a variable that pairs with
     * no binder, so the emitter prints the first index past the binders that enclose the thunk.
     */
    it('prints a thunk that names a codec under declaration as a variable that no binder binds', () => {
        expect(leanTermOf(array(undeclared))).toBe('Term.array (Term.var 0)')
        expect(leanTermOf(underBinder)).toBe(
            'Term.mu (Term.tuple [Term.var 1, Term.array (Term.var 0)] none)',
        )
    })

    /**
     * **A caller's function is a variable of a quantified verdict.** The model has no expression
     * for a caller's closure or adapter, so a verdict binds one variable for each function, and the
     * claim holds at every function. One function is one variable on both sides of the pair.
     * Outside a verdict the emitter refuses the function, because no vector states a value there.
     */
    it('binds each caller function of a declaration verdict as a variable, and refuses it elsewhere', () => {
        const verdict = leanSeparation({
            name: 'flags',
            left: textFlags,
            right: numberFlags,
        })
        expect(verdict).toContain('theorem flags (q0 : Value → Bool) :')
        expect(verdict.endsWith('= false := rfl')).toBe(true)
        expect(refusal(() => leanTermOf(textFlags)).reason).toContain(
            'Value → Bool',
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
        const adapted = held(string.set(), array(string), {
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
     * **A recursive schema is a binder and its variable.** A thunk that returns a term being
     * printed closes a cycle, so the emitter prints `Term.mu` at that term and `Term.var k` at the
     * thunk, where `k` counts the binders between the two. The emitter ends on every cycle.
     */
    it('prints a schema that recurses below a list as a binder whose variable sits in the list', () => {
        expect(leanTermOf(json)).toBe(
            'Term.mu (Term.union [Term.string, Term.array (Term.var 0)])',
        )
        // the top thunk of `Category` returns the object, and the object holds the same thunk
        expect(leanTermOf(erase(Category))).toMatch(
            /^Term\.mu \(Term\.object .*Term\.array \(Term\.var 0\).*\)$/,
        )
    })

    /**
     * **A thunk that returns its own term is printed, and the guard refuses it.** Its stages never
     * grow, so the model has no limit for it, and `Term.guarded` answers `false`.
     * `.vectors.full.lean` carries the verdict.
     */
    it('prints a thunk that returns itself as a binder the guard refuses', () => {
        expect(leanTermOf(selfThunk)).toBe('Term.mu (Term.var 0)')
        expect(
            leanGuard({ name: 'self_thunk', codec: selfThunk, guarded: false }),
        ).toContain('Term.guarded (Term.mu (Term.var 0)) = false := rfl')
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
        expect(leanTermOf(decimals)).toContain('.decimalText')

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
        expect(emitted).toContain(
            '(denote (libTable noCallers) (Term.string)).e',
        )
        expect(emitted).toContain('(Value.str "hello")')
        expect(emitted).toContain('(some (Attr.s "hello")) = .same')
    })

    /**
     * The same claim in the older protocol, kept because it depends on nothing but `denote` and
     * is what a tree without `Calculus/Bridge/Vectors.lean` can still check. It cannot state a refusal,
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
        expect(module).toContain('import Calculus.Bridge.Vectors')
        expect(module).toContain('namespace Calculus')
        expect(module.trimEnd().endsWith('end Calculus')).toBe(true)
    })

    /** The equation protocol carries its own proof, so its preamble is the one with the tactic. */
    it('carries the tactic and the imports the equation protocol needs', () => {
        const module = leanVectorModule([], 'equation')
        expect(module).toContain('import Calculus.Dynamo.Lang.Denote')
        expect(module).toContain('import Mathlib.Tactic.FinCases')
        expect(module).toContain('macro "vector" : tactic')
        expect(module.trimEnd().endsWith('end Calculus')).toBe(true)
    })
})

/**
 * **The recursive schemas the host accepts**, each a cycle of term objects closed by a thunk below a
 * list or an object. The model states each as `Term.mu`, with `Term.var` at the thunk.
 */
const json: AnyCodec = erase(
    union([
        string,
        array(lazy(() => json as never)),
    ] as unknown as readonly AnyCodec[]),
)
const tree: AnyCodec = erase(
    object({ v: string, kids: array(lazy(() => tree as never)) }),
)
type Category = { name: string; children?: readonly Category[] }
const Category: AttributeCodec<Category> = lazy(() =>
    object({ name: string, children: optional(array(Category)) }),
)
type Tree = { name: string; children?: readonly Tree[] }
const Tree: AttributeCodec<Tree> = lazy(() =>
    object({ name: string, children: optional(array(Tree)) }),
)
/** A recursive union whose recursion sits under an optional field of an object. */
const underObject: AnyCodec = erase(
    union([
        string,
        object({ m: optional(lazy(() => underObject as never)) }),
    ] as unknown as readonly AnyCodec[]),
)
/** A thunk that returns its own term: no container sits between the binder and its variable. */
const selfThunk: AnyCodec = erase(
    lazy(() => selfThunk as unknown as AttributeCodec<unknown>),
)

/**
 * **A thunk that names the constant under declaration**, as a recursive schema's thunk does
 * before the constant is assigned. The thunk throws when forced, so the host reads it as a free
 * variable, and the emitter prints a variable that no binder of the term binds.
 */
const undeclared = lazy((): AttributeCodec<string> => {
    throw new ReferenceError('the constant under declaration')
})
/** A recursive union of decimals: a library adapter below a binder. */
type DecimalJson = string | readonly DecimalJson[]
const decimalJson: AttributeCodec<DecimalJson> = lazy(() =>
    union([decimal, array(decimalJson)]),
)
/** A recursive pair with a thunk that throws below its binder. */
type Chain = readonly [string, readonly Chain[]]
const underBinder: AttributeCodec<Chain> = lazy(() =>
    list(undeclared, array(underBinder)),
)
/** A caller's type guard over every boolean, and two caller adapters to a boolean. */
const anyBoolean = (value: boolean): value is boolean => value || !value
const textFlag = held(string, boolean, {
    encode: (value: boolean) => (value ? 'y' : 'n'),
    decode: (text: string) => text === 'y',
})
const numberFlag = held(decimal, boolean, {
    encode: (value: boolean) => (value ? '1' : '0'),
    decode: (text: string) => text === '1',
})
/** A set of a caller's adapter: the caller side of a set needs a refinement to have a set. */
const textFlags = refine(textFlag, anyBoolean).set()
const numberFlags = refine(numberFlag, anyBoolean).set()
/** A caller's type guard over text, which the model names by no predicate. */
const nonEmpty = (value: string): value is string => value.length > 0
/** A caller's type guard that asks the shipped `isNumeral`, and is itself the caller's closure. */
const numeralText = (value: string): value is string => isNumeral(value)

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
     * A set over a **literal** element: the set of the union of the literals, with the
     * restriction at the element.
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
    // required literal and by nothing else. The names alone resolve neither, and admission by
    // attempt resolves both, because one option admits the value. Nothing in this corpus
    // exercised the literal half of admission before, which is why the bridge passed unchanged
    // while the model gained it.
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
    { name: 'recursive_json', codec: json, value: ['a', ['b', []]] },
    {
        name: 'recursive_tree',
        codec: tree,
        value: { v: 'r', kids: [{ v: 'c', kids: [] }] },
    },
    {
        name: 'recursive_category',
        codec: erase(Category),
        value: { name: 'pets', children: [{ name: 'dogs' }] },
    },
    {
        name: 'recursive_tree_optional',
        codec: erase(Tree),
        value: { name: 'root' },
    },
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
     * The second protocol exists because `formal/Calculus/Bridge/Vectors.lean` does — a hand-written
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
        expect(module).toContain('import Calculus.Bridge.Vectors')
        expect(module).not.toContain('macro "vector"')
    })
})

/**
 * Every option pair the corpus offers. `leanTermOf` is what bounds it: a pair either side of which
 * is term-inexpressible cannot be put to the model at all.
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
            out.push({ name: `${an}__vs__${bn}`, left, right })
        }
    }
    // two numeric literal sets, one under the `decimal` adapter, which the meet of two numbers
    // separates. No sample pairs a numeric literal with a literal decimal
    const numeral = (text: string) => orThrow(DynamoNumber.from(text))
    out.push({
        name: 'pinned_numerals__vs__literal_decimal_23',
        left: erase(dynamoNumber(numeral('0'), numeral('1'))),
        right: erase(decimal('2', '3')),
    })
    // a literal string beside a literal decimal of the same texts: both write "1", at S and at N
    out.push({
        name: 'literal_strings_12__vs__literal_decimal_12',
        left: erase(string('1', '2.5')),
        right: erase(decimal('1', '2.5')),
    })
    // a literal decimal beside a wider literal decimal: one adapter, and each side of the first is
    // below one option of a union of literals on the second
    out.push({
        name: 'literal_decimal_1__vs__literal_decimal_12',
        left: erase(decimal('1')),
        right: erase(decimal('1', '2.5')),
    })
    // a caller's closure refinement beside a list of adapters. The meet answers the bottom,
    // because `string` meets the list at the bottom, so the verdict holds at every closure
    out.push({
        name: 'numeral_text__vs__array_of_decimal',
        left: refine(string, numeralText),
        right: array(decimal),
    })
    // a caller's closure refinement of text beside the text adapter: both write a string
    out.push({
        name: 'caller_text__vs__scalar_decimal',
        left: refine(string, nonEmpty),
        right: decimal,
    })
    // a thunk that throws beside three partners: a free variable pairs with no binder
    out.push(
        {
            name: 'free_array__vs__scalar_decimal',
            left: array(undeclared),
            right: decimal,
        },
        {
            name: 'free_variable__vs__scalar_string',
            left: undeclared,
            right: string,
        },
        {
            name: 'free_json__vs__scalar_string',
            left: union([string, array(undeclared)]),
            right: string,
        },
    )
    // a set of a caller's adapter beside three sets: the model's caller carrier has no set of
    // booleans, so the caller sides of two such sets meet at the booleans
    out.push(
        {
            name: 'text_flags__vs__number_flags',
            left: textFlags,
            right: numberFlags,
        },
        {
            name: 'text_flags__vs__decimal_set',
            left: textFlags,
            right: decimal.set(),
        },
        {
            name: 'text_flags__vs__string_set',
            left: textFlags,
            right: string.set(),
        },
    )
    // a library adapter below a binder, beside three partners
    out.push(
        {
            name: 'recursive_decimal_json__vs__scalar_binary',
            left: decimalJson,
            right: binary,
        },
        {
            name: 'recursive_decimal_json__vs__scalar_string',
            left: decimalJson,
            right: string,
        },
        {
            name: 'recursive_decimal_json__vs__never',
            left: decimalJson,
            right: never,
        },
    )
    return out
}

/**
 * Every pair of corpus terms, for the disjointness differential.
 *
 * Bounded the same way the separation pairs are — a term the emitter has no closed expression for
 * cannot be put to the model. The bound is a skip and not a failure.
 *
 * Every pair is emitted, the declines included: `false` states nothing about a pair, and a port
 * that answered `true` where the model answers `false` would be unsound.
 */
const disjointPairs = (): readonly DisjointPair[] => {
    const codecs: readonly (readonly [string, AnyCodec])[] = [
        ...sampleVectors.map((v) => [v.name, v.codec] as const),
        ['scalar_number', erase(dynamoNumber)] as const,
        ['never', erase(never)] as const,
    ]
    const out: DisjointPair[] = []
    for (let x = 0; x < codecs.length; x++) {
        for (let y = x + 1; y < codecs.length; y++) {
            const [an, left] = codecs[x] as readonly [string, AnyCodec]
            const [bn, right] = codecs[y] as readonly [string, AnyCodec]
            const one: DisjointPair = {
                name: `${an}__disjoint__${bn}`,
                left,
                right,
            }
            try {
                leanDisjoint(one)
            } catch {
                continue
            }
            out.push(one)
        }
    }
    // two recursive unions whose bodies share `string`, and the same pair under one required field
    out.push(
        {
            name: 'recursive_json__disjoint__recursive_under_object',
            left: json,
            right: underObject,
        },
        {
            name: 'field_json__disjoint__field_under_object',
            left: erase(object({ a: json as never })),
            right: erase(object({ a: underObject as never })),
        },
    )
    // a thunk that throws beside three partners: a free variable pairs with no binder, so the
    // test declines beside every term but the bottom. A list of such a thunk beside a scalar is
    // disjoint, because the two shape classes are
    out.push(
        {
            name: 'free_array__disjoint__scalar_decimal',
            left: array(undeclared),
            right: decimal,
        },
        {
            name: 'free_variable__disjoint__scalar_string',
            left: undeclared,
            right: string,
        },
        {
            name: 'free_json__disjoint__scalar_string',
            left: union([string, array(undeclared)]),
            right: string,
        },
    )
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
 * (`set(string)`/`set(number)`, which the certificate certifies), objects chosen by name, two literals,
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
    it('offers 410 write pairs and every one of 440 read pairs', () => {
        expect(writeResolutions().length).toBe(410)
        const reads = readResolutions()
        expect(reads.length).toBe(440)
        /**
         * **Every pair is stated, and no filter decides otherwise.** A read value with no Lean
         * form makes `leanValueOf` throw, so a pair becoming unstatable fails the emission rather
         * than leaving the module in silence.
         */
        for (const one of reads) {
            expect(() => leanReadResolution(one)).not.toThrow()
        }
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
        expect(module).toContain('import Calculus.Bridge.Vectors')
        expect(module).toContain('440 on the read side')
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
     *
     * **All 1591 are asserted, and it was 1588.** Three pairs were excluded as stuck on the
     * `Double` axiom: `scalar_number__reads__scalar_decimal`,
     * `scalar_number__reads__literal_decimal` and `scalar_number__reads__raw_N`, each a `number`
     * codec against an `N` attribute. The model has no axiom, and `AdmA .number`'s `.n` row decides
     * a concrete numeral by `rfl`, so the filter excluded pairs the row answers. The filter is
     * deleted, and the three are theorems in `.readverdicts.lean` like every other pair.
     */
    it('offers 1927 pairs, and asserts every one', () => {
        const verdicts = readVerdicts()
        // 1634 until `object_fallback_present` left the emittable corpus: a field's older
        // reader lives in `Codec.extendRead`, outside `Term`, so a `Body` has no slot to print it
        expect(verdicts.length).toBe(1927)
        const module = leanReadModule(verdicts)
        for (const name of [
            'scalar_number__reads__scalar_decimal',
            'scalar_number__reads__literal_decimal',
            'scalar_number__reads__raw_N',
        ]) {
            expect(module).toContain(`theorem ${name} :`)
        }
    })

    it('emits them for the gate to elaborate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.readverdicts.lean'),
                leanReadModule(readVerdicts()),
            )
        }
        const module = leanReadModule(readVerdicts())
        expect(module).toContain('import Calculus.Dynamo.Lang.Store')
        expect(module).toContain('All 1927 pairs are asserted here.')
    })
})

describe("the declaration guard, against the model's classifier", () => {
    /**
     * **Each pair carries the warrant of the host's verdict**, and the gate elaborates each one.
     * An accepted pair carries the model's proof that the pair is compatible, through the warrant
     * the host used. A refused pair carries `compatPair dynOracle x y = false`: the host decides
     * the model's decision, so the model refuses what the host refuses.
     *
     * **The counts pin a fact no law has, deliberately.** They are a property of this corpus, so
     * widening the corpus is meant to fail here and be looked at.
     */
    it("accepts only pairs the model proves compatible, and refuses only pairs the model's decision refuses", () => {
        const emitted = separationPairs().map(leanSeparation)
        const accepted = emitted.filter((one) =>
            one.includes('PairwiseCompat (libTable κ) ['),
        )
        const refused = emitted.filter((one) =>
            /= false := (by decide|rfl)$/.test(one),
        )
        expect(accepted.length + refused.length).toBe(emitted.length)
        expect([accepted.length, refused.length]).toEqual([849, 26])
    })

    /**
     * **A recursive option is decided per half, as the model decides it.** The model reads a
     * variable as held-free, and bounds each stage of a held-free binder by `opaque`. So `json`
     * beside `array(string)` is accepted: both options are held-free, and the top bounds both. `json`
     * beside a number is accepted because the two are disjoint, and `json` beside `decimal` is
     * refused, because `decimal` writes a text that `json` writes to another attribute.
     */
    it('decides a recursive option per half, and bounds a held-free binder by the top, as the model does', () => {
        const recursive = separationPairs().filter((one) =>
            one.name.includes('recursive'),
        )
        const emitted = recursive.map(leanSeparation)
        const byDecision = emitted.filter((one) =>
            one.includes('pairwiseCompat_of_compatPair'),
        )
        const refused = emitted.filter((one) =>
            one.endsWith('= false := by decide'),
        )
        expect([byDecision.length, refused.length]).toEqual([158, 3])
        expect(byDecision.length + refused.length).toBe(recursive.length)
        const verdict = (left: AnyCodec, right: AnyCodec) =>
            leanSeparation({ name: 'probe', left, right })
        expect(verdict(erase(dynamoNumber), json)).toContain(
            'pairwiseCompat_of_compatPair',
        )
        expect(verdict(erase(array(string)), json)).toContain(
            'pairwiseCompat_of_compatPair',
        )
        expect(verdict(erase(decimal), json)).toContain('= false := by decide')
        expect(verdict(erase(string), tree)).toContain(
            'pairwiseCompat_of_compatPair',
        )
        // `tree` requires `v` and `Category` holds no `v`, and both are held-free
        expect(verdict(tree, erase(Category))).toContain(
            'pairwiseCompat_of_compatPair',
        )
    })

    it('emits them for the gate to elaborate', () => {
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.separations.lean'),
                leanSeparationModule(separationPairs()),
            )
        }
        expect(leanSeparationModule([])).toContain(
            'import Calculus.Dynamo.Analysis.Meet',
        )
        // a verdict spells `libTable`, which only `Store` declares, and without the import
        // Lean auto-binds the name and every verdict fails to elaborate
        expect(leanSeparationModule([])).toContain(
            'import Calculus.Dynamo.Lang.Store',
        )
    })

    /**
     * **Disjointness, both directions.** `Term.disjoint` and `disjoint` are one function written
     * twice, so a disagreement either way is a defect on one side. The raw terms and the two pairs
     * of views are asserted apart.
     */
    it("puts every corpus pair to the model's disjointness test", () => {
        const pairs = disjointPairs()
        expect(pairs.length).toBe(866)
        if (process.env.EMIT_LEAN_REFUSALS) {
            writeFileSync(
                join(process.cwd(), 'formal', '.disjoints.lean'),
                leanDisjointModule(pairs),
            )
        }
        expect(leanDisjointModule([])).toContain(
            'import Calculus.Dynamo.Analysis.Meet',
        )
    })

    /** A pair `src/` accepts carries the decision the host ran, and a refused pair its refusal. */
    it('states the warrant of each verdict, both ways', () => {
        const accepted = leanSeparation({
            name: 'accepted',
            left: erase(string),
            right: erase(boolean),
        })
        expect(accepted).toContain(
            'PairwiseCompat (libTable κ) [Term.string, Term.boolean]',
        )
        expect(accepted).toContain('pairwiseCompat_of_compatPair (by decide)')
        const refused = leanSeparation({
            name: 'refused',
            left: erase(string),
            right: erase(decimal),
        })
        expect(refused).toMatch(
            /^ {4}Alg\.compatPair dynOracle \(Term\.string\)$/m,
        )
        expect(refused.endsWith('= false := by decide')).toBe(true)
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
                leanVectorModule(
                    [],
                    'check',
                    refusals,
                    refusals.length,
                    [],
                    [
                        {
                            name: 'self_thunk__unguarded',
                            codec: selfThunk,
                            guarded: false,
                        },
                    ],
                ),
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
        expect(statable.length).toBe(40)
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
        expect(module).toContain('import Calculus.Bridge.Vectors')
        // a vector spells `libTable noCallers`, which only `Store` declares, and without the import
        // `denote` sticks on a free variable and no vector elaborates
        expect(module).toContain('import Calculus.Dynamo.Lang.Store')
        // the header states what it could not state, which for this corpus is nothing
        expect(module).toContain('every corpus codec round trips')
    })
})

/**
 * **The recursive maps the `equation` protocol cannot state.** `vector` asks the elaborator's `whnf`
 * for the codec's answer, and a recursive term reads the stage its input's depth names. A map's
 * depth is a `Finset.sup` over its key set, which `whnf` does not reduce: `recursive_tree` timed out
 * at 4000000 heartbeats, twenty times the default. The `check` sample states both by `rfl`, and the
 * gate elaborates it, so the vectors are checked there and deferred here.
 */
const EQUATION_DEFERRED: readonly string[] = [
    'recursive_tree',
    'recursive_category',
]

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
                sampleVectors.filter(
                    (one) =>
                        emittable(one) &&
                        (protocol === 'check' ||
                            !EQUATION_DEFERRED.includes(one.name)),
                ),
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
