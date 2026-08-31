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
import type { AnyCodec, AttributeCodec } from './codec'
import {
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
    literal,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    refine,
    set,
    string,
    tuple,
    union,
} from './codec'
import type { Vector } from './lean'
import {
    LeanUnemittable,
    leanAttrOf,
    leanTermOf,
    leanValueOf,
    leanVector,
    leanVectorModule,
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
        expect(leanTermOf(erase(literal('A', 'B', 'C')))).toBe(
            'Term.literal GroundKind.string (NEFinset.of "A" {"B", "C"})',
        )
        expect(leanTermOf(erase(literal('only')))).toBe(
            'Term.literal GroundKind.string (NEFinset.of "only" ∅)',
        )
    })

    it('emits the containers structurally', () => {
        expect(leanTermOf(erase(array(string)))).toBe(
            'Term.array (Term.string)',
        )
        expect(leanTermOf(erase(set(string)))).toBe('Term.set (Term.string)')
        expect(leanTermOf(erase(record(boolean)))).toBe(
            'Term.record (Term.boolean)',
        )
        expect(leanTermOf(erase(tuple(string, boolean)))).toBe(
            'Term.tuple [Term.string, Term.boolean] none',
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
            'Term.object {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.optional (Term.boolean)) Rest.drop',
        )
    })

    /** The empty key set has no `else` to fall through to, so the function is the absurd one. */
    it('emits an object with no fields as the absurd function', () => {
        expect(leanTermOf(erase(object({})))).toBe(
            'Term.object ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)) Rest.drop',
        )
    })

    it('emits a fallback field with its stand-in value', () => {
        expect(
            leanTermOf(erase(object({ a: fallback(string, () => 'd') }))),
        ).toBe(
            'Term.object {"a"} (fun k => Field.fallback (Term.string) (Value.str "d")) Rest.drop',
        )
    })

    it('emits an open object as `Rest.codec`', () => {
        expect(leanTermOf(erase(object({ a: string }, boolean)))).toBe(
            'Term.object {"a"} (fun k => Field.req (Term.string)) (Rest.codec (Term.boolean))',
        )
    })

    /**
     * **The place the emitter used to guess.**
     *
     * `CodecDef` recorded the rest *codec*, and both `'drop'` and `'refuse'` recorded nothing — so
     * the definition alone could not tell them apart and this wrote `Rest.drop` for either. It was
     * not wrong for the vectors this module writes: `objectCodec`'s `e` is `objWrite sems rc?`,
     * which never sees the `kn` filter the policy decides, and `rcOf` is `none` for both, so the two
     * denote the *same* `e`. It was wrong about the codec, and a decode-direction vector — whose `p`
     * is exactly where they differ — would have been silently false. `CodecDef['rest']` now carries
     * the policy, and the emitter reads it rather than guessing.
     */
    it('tells `refuse` from `drop`, which a decode vector would need', () => {
        expect(leanTermOf(erase(object({ a: string }, 'refuse')))).toBe(
            'Term.object {"a"} (fun k => Field.req (Term.string)) Rest.refuse',
        )
        expect(leanTermOf(erase(object({ a: string }, 'drop')))).toBe(
            'Term.object {"a"} (fun k => Field.req (Term.string)) Rest.drop',
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
     * A discriminated union's table is keyed by *tag*, and an option may answer to several — so one
     * codec can occupy two entries. `Term.dunion` takes the option *list*, and repeating an option
     * there would give it a tag set overlapping itself, which is exactly the disjointness premise
     * `Typed.dunion` carries. Deduplicated by identity.
     */
    it('emits a discriminated union once per option, not once per tag', () => {
        const many = object({ kind: literal('a', 'b'), x: string })
        const emitted = leanTermOf(erase(discriminatedUnion('kind', [many])))
        expect(emitted).toContain('Term.dunion "kind" [Term.object')
        expect(emitted.split('Term.object')).toHaveLength(2)
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
     * The permanent one. `Double` is axiomatized with a round trip and a decidable equality and *no
     * constructor* — see `formal/Calculus/Domain.lean:236` — so no closed term inhabits it, `#eval`
     * cannot print one, and there is no text a generator could emit. This is not a gap to be filled
     * later: filling it would mean adding a numeral-to-double literal the model deliberately omits,
     * because IEEE-754 rounding is not a theorem of the calculus.
     */
    it('refuses `number`, and says why it is permanent', () => {
        expect(refusal(() => leanTermOf(erase(number))).reason).toContain(
            'Double',
        )
        expect(refusal(() => leanValueOf(1.5)).reason).toContain('decimal')
        expect(refusal(() => leanValueOf(new Set([1, 2]))).reason).toContain(
            'NEFinset Double',
        )
    })

    it('refuses a numeric literal, which is the same fact one level up', () => {
        expect(
            refusal(() => leanTermOf(erase(literal(1, 2)))).reason,
        ).toContain('GroundKind.number')
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
        const adapted = held(set(string), {
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
            refusal(() => leanTermOf(erase(fallback(string, () => 'd'))))
                .reason,
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
        codec: erase(literal('A', 'B')),
        value: 'B',
    },
    {
        name: 'set_of_string',
        codec: erase(set(string)),
        value: new Set(['b', 'a']),
    },
    {
        name: 'set_of_decimal',
        codec: erase(set(decimal)),
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
        codec: erase(object({ a: fallback(string, () => 'stand-in') })),
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
                object({ kind: literal('a'), x: string }),
                object({ kind: literal('b'), y: boolean }),
            ]),
        ),
        value: { kind: 'a', x: 'v' },
    },
    { name: 'opaque_map', codec: erase(opaque), value: { a: 'x' } },
    { name: 'lazy_string', codec: erase(lazy(() => string)), value: 'x' },
]

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

describe('the committed sample', () => {
    /**
     * A sample that is not regenerated is a sample that lies. This is the whole of the check: emit
     * the same vectors again and compare bytes. If it fails, the emitter changed and
     * `src/lean.sample.lean` needs rewriting — and, since the sample was verified against a real
     * `Calculus` build, so does that verification.
     */
    it('is what the emitter produces today', () => {
        // `process.cwd()` rather than `import.meta.url`: `tsconfig.json` targets a module setting
        // that has no `import.meta`, and vitest runs from the package root
        for (const [file, protocol] of [
            ['lean.sample.lean', 'equation'],
            ['lean.sample.check.lean', 'check'],
        ] as const) {
            const at = join(process.cwd(), 'src', file)
            const emitted = leanVectorModule(sampleVectors, protocol)
            // `UPDATE_LEAN_SAMPLE=1 vitest run src/lean.spec.ts` rewrites them — and then they have
            // to go through Lean again, because nothing here can say the new theorems are true
            if (process.env.UPDATE_LEAN_SAMPLE) writeFileSync(at, emitted)
            expect(emitted).toBe(readFileSync(at, 'utf8'))
        }
    })
})
