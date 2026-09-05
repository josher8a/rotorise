/**
 * **The half of the bridge to `formal/` that runs here.**
 *
 * `src/lean.ts` emits Lean source; only Lean can say whether that source is *true*. What this file
 * can say — and what nothing else says — is whether the emitter produces the text it thinks it
 * does, and, more importantly, whether it **refuses everything it cannot say**. A differential test
 * whose generator silently approximates is worse than no differential test: it produces a file that
 * compiles and proves a theorem about a codec nobody shipped.
 *
 * So the refusals are tested as carefully as the emissions, and they are the reason this file is
 * long. Each one names a fact about the model rather than about this library:
 *
 * - `Double` is an axiom, so `Value.num` has no closed term. `number` is out permanently.
 * - `refine`, `held`, `legacy` and `custom` carry *functions* in the model and *closures* here.
 *   There is no expression in Lean for a closure. Out until somebody writes the Lean side by hand.
 * - `optional` and `fallback` are §4 `Field`s and `restOf` is a §4 `Rest`. Asking for a `Term` at
 *   one of them is a stratification error, and the emitter reports it as one rather than flattening
 *   it — which is the same discipline `NotAboutAbsence` enforces in the types.
 *
 * ── the sample ─────────────────────────────────────────────────────────────────────────────────
 *
 * `src/lean.sample.lean` is a committed file of generated output, and the last test here regenerates
 * it and compares. It exists so a human can read the *shape* of what gets proposed without running
 * anything, and the comparison exists so it cannot rot: change the emitter and this test tells you
 * the sample is stale. Every theorem in it has been checked against the real `Calculus` build.
 */
import { readFileSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import type { AttributeValue } from './attribute'
import type { AnyCodec, AttributeCodec } from './codec'
import {
    admits,
    array,
    binary,
    boolean,
    custom,
    decimal,
    discriminatedUnion,
    fallback,
    held,
    lazy,
    legacy,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    refine,
    string,
    tuple,
    union,
} from './codec'
import type {
    ReadResolution,
    ReadVerdict,
    Refusal,
    Resolution,
    Separation,
    Vector,
} from './lean'
import {
    LeanUnemittable,
    leanAttrOf,
    leanReadModule,
    leanReadResolution,
    leanResolutionModule,
    leanSeparation,
    leanSeparationModule,
    leanTermOf,
    leanValueOf,
    leanVector,
    leanVectorModule,
    readResolutionIsUnstatable,
    readRowIsStuck,
} from './lean'

/** The emitter takes the erased codec; the constructors return precise ones. */
const erase = (codec: unknown): AnyCodec => codec as AnyCodec

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
        expect(leanTermOf(erase(decimal))).toBe('Term.decimal')
        expect(leanTermOf(erase(boolean))).toBe('Term.boolean')
        expect(leanTermOf(erase(binary))).toBe('Term.binary')
        expect(leanTermOf(erase(nullValue))).toBe('Term.null')
    })

    /**
     * `literal` is base-indexed in the model and value-indexed here, and the two agree only at the
     * string base. `GroundKind` is the index and `NEFinset k.Carrier` the alternatives — so the
     * whole of §3's premise line (`g ground`, `n ≥ 1`, pairwise distinct, homogeneous) is
     * discharged by the type, and the emitter's only job is to write the first element and the rest.
     */
    it('emits a string literal as its base and its alternatives', () => {
        expect(leanTermOf(erase(string('A', 'B', 'C')))).toBe(
            'Term.literal GroundKind.string (NEFinset.of "A" {"B", "C"})',
        )
        expect(leanTermOf(erase(string('only')))).toBe(
            'Term.literal GroundKind.string (NEFinset.of "only" ∅)',
        )
    })

    /**
     * `GroundKind.decimal`'s carrier is `StoredNumeral`, a subtype gated on `Numeral.Stored`, so an
     * alternative is a pair and not a string. `by decide` is the gate run at elaboration time — the
     * same discipline `WFNumeral.of` uses on the attribute side, and the reason a numeral this
     * library writes and §1 refuses would fail the build rather than prove something false.
     *
     * This was refused outright until `decimal` became a `GroundKind`. The kernel accepts the term
     * and both directions of its admission; `literal_decimal` in the sample is the vector.
     */
    it('emits a decimal literal at its own base, with the stored gate discharged', () => {
        expect(leanTermOf(erase(decimal('1', '2.5')))).toBe(
            'Term.literal GroundKind.decimal (NEFinset.of ⟨"1", by decide⟩ {⟨"2.5", by decide⟩})',
        )
        expect(leanTermOf(erase(decimal('-1.5')))).toBe(
            'Term.literal GroundKind.decimal (NEFinset.of ⟨"-1.5", by decide⟩ ∅)',
        )
    })

    /**
     * And a binary literal, which was refused for a reason that was never true: `leanValueOf` has
     * emitted `Value.bin` for a `Uint8Array` all along, so a vector at a binary literal can state
     * both halves. Kernel-checked the same way.
     */
    it('emits a binary literal as its octets', () => {
        expect(leanTermOf(erase(binary(new Uint8Array([0, 127, 255]))))).toBe(
            'Term.literal GroundKind.binary (NEFinset.of [0, 127, 255] ∅)',
        )
    })

    /** `GroundKind.number`'s carrier is the `Double` axiom, and that refusal is permanent. */
    it('refuses a numeric literal, permanently', () => {
        expect(refusal(() => leanTermOf(erase(number(1)))).reason).toContain(
            '`Double`',
        )
    })

    it('emits the containers structurally', () => {
        expect(leanTermOf(erase(array(string)))).toBe(
            'Term.array (Term.string)',
        )
        expect(leanTermOf(erase(record(boolean)))).toBe(
            'Term.record (Term.boolean)',
        )
        expect(leanTermOf(erase(tuple(string, boolean)))).toBe(
            'Term.tuple [Term.string, Term.boolean] none',
        )
    })

    /**
     * A set is **not** structural, and stopped being so the day `Term.set` took a `SetBase`
     * (`formal/Calculus/Term.lean:60`). This emitted `Term.set (<element term>)` until then, and
     * the generated file stopped compiling — which is the defect this test now guards.
     *
     * Both numeric bases are emitted, and they are different terms writing the same member: `NS`
     * cannot tell `number` from `decimal`, and the index can.
     */
    it('emits a set as its base, not as its element term', () => {
        expect(leanTermOf(erase(string.set()))).toBe('Term.set SetBase.string')
        expect(leanTermOf(erase(decimal.set()))).toBe(
            'Term.set SetBase.decimal',
        )
        expect(leanTermOf(erase(number.set()))).toBe('Term.set SetBase.number')
        expect(leanTermOf(erase(binary.set()))).toBe('Term.set SetBase.binary')
    })

    /**
     * And a *restricted* element is refused rather than emitted as its base.
     *
     * `setCodec_restrict` says the set of a restriction writes what the restriction of a set writes,
     * so nothing is lost as a **codec** — but it is an equation between codecs, and `Term.set` has
     * no room for the predicate. Emitting `Term.set SetBase.string` for `string('a','b')` would
     * state a theorem about a term that admits `'z'`, which this one does not.
     */
    it('refuses a set of a restricted element rather than widening it', () => {
        expect(() => leanTermOf(erase(string.set('a', 'b')))).toThrow(
            /\*restricted\* element/,
        )
        const positive = refine(
            decimal,
            (value: string): value is string => !value.startsWith('-'),
            { describe: 'non-negative' },
        )
        expect(() => leanTermOf(erase(positive.set()))).toThrow(
            /\*restricted\* element/,
        )
    })

    /**
     * The refusal that had no test, and it needs a cast to reach.
     *
     * A codec's definition is a term, so nothing well typed hands the emitter a field and the branch
     * reads as dead. It is not: a brand is not a proof and a cast defeats a brand, which is why the
     * entry takes a declaration and refuses one, and why this is asserted through `erase` rather than
     * left to the type. `Field.optional` is emitted where a field belongs — in an object's table —
     * and the two spellings are what §4's strata mean.
     */
    it('refuses a field where a term belongs, reached past a cast', () => {
        expect(() => leanTermOf(erase(optional(string)))).toThrow(
            /a §4 \*field\*, not a term/,
        )
        expect(() => leanTermOf(erase(fallback(string, 'x')))).toThrow(
            /`optional`\/`fallback` denote `Field`/,
        )
        expect(leanTermOf(erase(object({ a: optional(string) })))).toContain(
            'Field.optional',
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
            'Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.optional (Term.boolean)) Rest.drop)',
        )
    })

    /** The empty key set has no `else` to fall through to, so the function is the absurd one. */
    it('emits an object with no fields as the absurd function', () => {
        expect(leanTermOf(erase(object({})))).toBe(
            'Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)) Rest.drop)',
        )
    })

    it('emits a fallback field with its stand-in value', () => {
        expect(leanTermOf(erase(object({ a: fallback(string, 'd') })))).toBe(
            'Term.object (Body.mk {"a"} (fun k => Field.fallback (Term.string) (Value.str "d")) Rest.drop)',
        )
    })

    it('emits an open object as `Rest.codec`', () => {
        expect(leanTermOf(erase(object({ a: string }, boolean)))).toBe(
            'Term.object (Body.mk {"a"} (fun k => Field.req (Term.string)) (Rest.codec (Term.boolean)))',
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
     * is exactly where they differ — would have been silently false. `Def['rest']` now carries
     * the policy, and the emitter reads it rather than guessing.
     */
    it('tells `refuse` from `drop`, which a decode vector would need', () => {
        expect(leanTermOf(erase(object({ a: string }, 'refuse')))).toBe(
            'Term.object (Body.mk {"a"} (fun k => Field.req (Term.string)) Rest.refuse)',
        )
        expect(leanTermOf(erase(object({ a: string }, 'drop')))).toBe(
            'Term.object (Body.mk {"a"} (fun k => Field.req (Term.string)) Rest.drop)',
        )
    })

    it('emits a union as its option list', () => {
        expect(leanTermOf(erase(union([string, boolean])))).toBe(
            'Term.union [Term.string, Term.boolean]',
        )
        expect(leanTermOf(erase(nullable(string)))).toBe(
            'Term.nullable (Term.string)',
        )
    })

    /**
     * **This checked that one codec occupying two table entries is emitted once**, because
     * repeating an option in `Term.dunion`'s list would give it a tag set overlapping itself and
     * `Typed.dunion` carries `hdisj` against exactly that. Arity one refuses the two-entry option
     * at the declaration, so the emitter's dedup went with the test and the invariant is answered
     * in one place instead of two. What is left worth pinning is that the list is emitted at all.
     */
    it('emits a discriminated union as its option list', () => {
        const emitted = leanTermOf(
            erase(
                discriminatedUnion('kind', [
                    object({ kind: string('a'), x: string }),
                    object({ kind: string('b'), y: string }),
                ]),
            ),
        )
        expect(emitted).toContain('Term.dunion "kind" [Term.object')
        expect(emitted.split('Term.object')).toHaveLength(3)
    })

    it('forces a lazy and emits what it finds', () => {
        expect(leanTermOf(erase(lazy(() => string)))).toBe(
            'Term.lazy (Term.string)',
        )
    })

    it('emits opaque with its number policy as the `lossy` flag', () => {
        expect(leanTermOf(erase(opaque))).toBe('Term.opaq false')
        expect(leanTermOf(erase(opaque('lossy')))).toBe('Term.opaq true')
    })
})

describe('what cannot be emitted', () => {
    /**
     * The permanent one, **and it is a fact about values, not about the term.** `Double` is
     * axiomatized with a round trip and a decidable equality and *no constructor* — see
     * `formal/Calculus/Domain.lean:236` — so no closed term inhabits it, `#eval` cannot print one,
     * and there is no text a generator could emit for one. This is not a gap to be filled later:
     * filling it would mean adding a numeral-to-double literal the model deliberately omits,
     * because IEEE-754 rounding is not a theorem of the calculus.
     *
     * `Term.number` used to be refused here too, which read the impossibility one level too high.
     * The term is closed and emits; `Value.num` is what cannot be written. Refusal vectors are
     * what made the difference visible, because they need the term and *not* a value at it.
     */
    it('refuses every numeric value, and emits the term', () => {
        expect(leanTermOf(erase(number))).toBe('Term.number')
        expect(refusal(() => leanValueOf(1.5)).reason).toContain('decimal')
        expect(refusal(() => leanValueOf(new Set([1, 2]))).reason).toContain(
            'NEFinset Double',
        )
    })

    /**
     * And the numeric literal, which really *is* term-inexpressible and so did not move with
     * `Term.number`: its alternatives are `NEFinset Double`, so there is no set to write. No
     * vector reaches this term in either direction.
     */
    it('refuses a numeric literal, which is the term and not the value', () => {
        expect(refusal(() => leanTermOf(erase(number(1, 2)))).reason).toContain(
            'GroundKind.number',
        )
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
        const older = legacy({
            current: string,
            older: { decode: () => 'older' as string },
        })
        expect(refusal(() => leanTermOf(erase(older))).reason).toContain(
            'Attr → Option Value',
        )
        const byHand = custom({
            encode: (value: string) => ({ S: value }),
            decode: (attribute: { S?: string }) => attribute.S as string,
        })
        expect(refusal(() => leanTermOf(erase(byHand))).reason).toContain(
            'Term.custom',
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
            refusal(() => leanTermOf(erase(fallback(string, 'd')))).reason,
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
            'Value.map ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1))',
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
     * Lean's escape language and JSON's overlap and disagree, silently. JSON writes `\uXXXX` for
     * the control range and Lean 4 reads `\u` as wanting braces — so a tab in an attribute name
     * would have produced a file that does not parse, with no hint of where. Everything outside
     * printable ASCII goes out as `\u{...}`.
     */
    it('escapes strings the way Lean reads them, not the way JSON writes them', () => {
        expect(leanValueOf('a\tb')).toBe('Value.str "a\\tb"')
        expect(leanValueOf('q"\\')).toBe('Value.str "q\\"\\\\"')
        expect(leanValueOf('\u0001')).toBe('Value.str "\\u{1}"')
        expect(leanValueOf('é')).toBe('Value.str "\\u{e9}"')
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
    {
        name: 'set_of_decimal',
        codec: erase(decimal.set()),
        value: new Set(['1.5', '2']),
    },
    { name: 'array_of_string', codec: erase(array(string)), value: ['a', 'b'] },
    { name: 'array_empty', codec: erase(array(string)), value: [] },
    {
        name: 'tuple_pair',
        codec: erase(tuple(string, boolean)),
        value: ['a', true],
    },
    {
        name: 'record_of_string',
        codec: erase(record(string)),
        value: { a: 'x', b: 'y' },
    },
    { name: 'record_empty', codec: erase(record(string)), value: {} },
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
        codec: erase(object({ a: fallback(string, 'stand-in') })),
        value: { a: 'x' },
    },
    {
        name: 'object_open',
        codec: erase(object({ a: string }, boolean)),
        value: { a: 'x', z: true },
    },
    {
        name: 'object_nested',
        codec: erase(object({ a: object({ b: string }) })),
        value: { a: { b: 'x' } },
    },
    {
        name: 'map_inside_a_list',
        codec: erase(array(record(string))),
        value: [{ a: 'x' }],
    },
    {
        name: 'union_of_two',
        codec: erase(union([string, boolean])),
        value: true,
    },
    { name: 'nullable_null', codec: erase(nullable(string)), value: null },
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
 * refuses nothing contributes no refusal vector, and the subset says twenty-six of twenty-seven
 * for that reason.
 */
const refusalCodecs: readonly (readonly [string, AnyCodec])[] = [
    ...sampleVectors.map((v) => [v.name, v.codec] as const),
    ['scalar_number', erase(number)] as const,
]

export const allRefusals = (): readonly Refusal[] => {
    const out: Refusal[] = []
    for (const [cn, codec] of refusalCodecs) {
        for (const vector of sampleVectors) {
            if (admits(codec, vector.value)) continue
            out.push({
                name: `${cn}__refuses__${vector.name}`,
                codec,
                value: vector.value,
            })
        }
    }
    return out
}

export const sampleRefusals: readonly Refusal[] = refusalCodecs.flatMap(
    ([cn, codec]) => {
        const first = sampleVectors.find((v) => !admits(codec, v.value))
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
        ['scalar_number', erase(number)] as const,
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
 * Every (codec, attribute) pair the corpus offers, for the read-side differential.
 *
 * The attributes are what the corpus actually *writes*, plus six raw shapes for the members no
 * corpus vector produces alone. Bounded by `leanAttrOf` the way the pairs are bounded by
 * `leanTermOf`: an attribute the model has no closed expression for cannot be put to it.
 */
const readVerdicts = (): readonly ReadVerdict[] => {
    const codecs: readonly (readonly [string, AnyCodec])[] = [
        ...sampleVectors.map((v) => [v.name, v.codec] as const),
        ['scalar_number', erase(number)] as const,
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
    ['u_setstring_setnumber', erase(union([string.set(), number.set()]))],
    [
        'u_objects_by_name',
        erase(union([object({ a: string }), object({ b: boolean })])),
    ],
    ['u_literal_pair', erase(union([string('A'), string('B')]))],
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
     * This widens two to 208, and the value is the corpus rather than the question.
     */
    it('offers 208 write pairs and 231 statable of 232 read pairs', () => {
        expect(writeResolutions().length).toBe(208)
        const reads = readResolutions()
        expect(reads.length).toBe(232)
        // one pair only, and it is the `Double` axiom reaching the decoded value; the five
        // map-valued reads beside it are stated through `vcheck` now
        expect(
            reads
                .filter((one) => readResolutionIsUnstatable(one) === 'Double')
                .map((one) => one.name),
        ).toEqual(['rr_u_setstring_setnumber__set_of_decimal'])
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
            'rr_u_optional_inner__record_empty',
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
    it('offers 864 pairs, three of them stuck on the `Double` axiom', () => {
        const verdicts = readVerdicts()
        expect(verdicts.length).toBe(864)
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
        expect(module).toContain('import Calculus.Exactness')
        // the stuck ones are named in the header rather than dropped in silence
        expect(module).toContain('stuck, not skipped')
        expect(module).toContain('scalar_number__reads__raw_N')
    })
})

describe("the declaration guard, against the model's classifier", () => {
    /**
     * **`src/` refuses seventeen pairs and the model certifies none of them.** That is the whole
     * law, and it is one-directional on purpose: `Orth` is sufficient and not necessary, so a
     * pair it declines may still be separable and 66 of the 351 are. What would be a defect is
     * `src/` refusing a declaration the model *proves* works — which is what it did to
     * `union([string.set(), number.set()])` until `ff75c6b`, and what `Orth` certifies.
     *
     * **The count pins a fact no law has, deliberately.** That it is seventeen is a property of
     * this corpus, so widening the corpus is meant to fail here and be looked at; the *law* is
     * the loop below, that every refusal the model also declines. Both are kept, and the number
     * stays.
     */
    it('refuses only pairs the classifier also declines', () => {
        const separations = separationPairs()
        expect(separations.length).toBe(17)
        // each one emits, which is where `leanSeparation` re-checks that `src/` really refuses
        for (const one of separations) {
            expect(leanSeparation(one)).toContain('= false := by decide')
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
            const at = join(process.cwd(), 'src', file)
            const emitted = leanVectorModule(
                sampleVectors,
                protocol,
                sampleRefusals,
                allRefusals().length,
            )
            // `UPDATE_LEAN_SAMPLE=1 vitest run src/lean.spec.ts` rewrites them — and then they have
            // to go through Lean again, because nothing here can say the new theorems are true
            if (process.env.UPDATE_LEAN_SAMPLE) writeFileSync(at, emitted)
            expect(emitted).toBe(readFileSync(at, 'utf8'))
        }
    })
})
