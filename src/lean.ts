/**
 * Test vectors for the Lean model, emitted as Lean source.
 *
 * `formal/` is a mechanization of the codec calculus; this library is what it is supposed to
 * certify. The correspondence between the two is a *paper* obligation — somebody reads `denote`
 * and reads `src/codec.ts` and believes they agree — and `docs/codec-audit.md` records it as the
 * largest remaining risk. This module is the machine-checkable half of that belief.
 *
 * ── why the traffic goes this way ───────────────────────────────────────────────────────────────
 *
 * The obvious design is the other one: let Lean produce the expected attribute and compare it here.
 * That is not available, and the reason is structural rather than a missing feature.
 *
 * `denote` is `noncomputable` — `funImage` (`formal/Calculus/Combinators.lean:174`) is a `dite` on
 * a `Decidable` instance the kernel does not evaluate for free, and `Double` is an *axiom* with no
 * closed terms at all. So `#eval` fails on every denoted codec, and Lean can generate nothing.
 *
 * What Lean *can* do is check. `(denote t).e v = some a` is a closed proposition, and for every
 * term form this library can express it is provable by kernel reduction — see the `vector` tactic
 * this module emits, and `src/lean.spec.ts` for the boundary. So TypeScript proposes and Lean
 * disposes: {@link leanVectorModule} writes a file of `theorem`s, and `lake build` on it either
 * succeeds or names the vector the two sides disagree about.
 *
 * ── the tactic, and why it is not `rfl` ────────────────────────────────────────────────────────
 *
 * `rfl` closes a scalar vector and dies on every map-shaped one, which was the surprise. `M`'s
 * payload is a `Finset Name` with a *function* on it (`formal/Calculus/Domain.lean:377`), so the
 * attribute the model computes is `fun k => (c.e (f k)).get _` — a lambda whose body is stuck on
 * the bound key. It is pointwise equal to the lambda emitted here and not definitionally equal to
 * it, and no amount of reduction closes that gap: it needs `funext` plus a case split on the key
 * set. The emitted `vector` tactic is exactly that, applied to a fixpoint so it reaches nested
 * maps:
 *
 * ```lean
 * refine congrArg some ?_
 * repeat' first
 *   | (refine congrArg (Attr.m _) (funext fun k => ?_); obtain ⟨_, hk⟩ := k; fin_cases hk)
 *   | rfl
 *   | congr 1
 * ```
 *
 * The order matters and cost a probe to find: `rfl` first sends the top-level goal into an
 * `isDefEq` loop that exhausts the heartbeat budget rather than failing.
 *
 * ── what cannot be emitted ─────────────────────────────────────────────────────────────────────
 *
 * {@link LeanUnemittable} is thrown, never guessed around, and its cases are the honest boundary of
 * the bridge. See {@link leanTermOf}. The largest of them is **numbers**: `Double` is an axiom, so
 * `Value.num` has no closed inhabitant and no vector can mention one, ever. `decimal` is the
 * numeric escape hatch — it is text on both sides, and it evaluates.
 */
import type { AttributeValue } from './attribute'
import { isNumeral, isStoredNumeral, memberOf } from './attribute'
import type { AnyCodec, CodecDef } from './codec'
import { admits, admitsAttribute, setBase, shapeOf, union } from './codec'
import { failed } from './result'

/**
 * A term, value or attribute the Lean model has no closed expression for.
 *
 * Thrown rather than reported as a `Result`, because there is nothing a caller can do with half a
 * vector — and because a *silent* approximation is the one failure mode a differential test must
 * not have. Emitting `Term.refine inner (fun _ => true)` for a refinement whose predicate is a
 * TypeScript closure would produce a file that compiles and proves the wrong theorem.
 */
export class LeanUnemittable extends Error {
    /** Where in the codec or value the obstruction is, as a dotted path. */
    readonly at: string
    /** Why the model cannot say it. */
    readonly reason: string
    constructor(at: string, reason: string) {
        super(`cannot emit Lean for ${at}: ${reason}`)
        this.name = 'LeanUnemittable'
        this.at = at
        this.reason = reason
    }
}

const refuse = (at: string, reason: string): never => {
    throw new LeanUnemittable(at, reason)
}

/* ── lexical ─────────────────────────────────────────────────────────────────────────────── */

/**
 * A Lean string literal.
 *
 * Not `JSON.stringify`: the two escape languages overlap but do not agree, and the disagreements
 * are silent. Lean 4 takes `\n`, `\t`, `\\`, `\"` and `\u{...}`; JSON emits `\uXXXX` for the
 * control range, which Lean reads as a *different* escape (`\u` there wants braces), and neither
 * escapes DEL. Everything outside the printable ASCII range is written as `\u{...}` here, which is
 * unambiguous in Lean and survives a copy-paste through any editor.
 */
export const leanString = (value: string): string => {
    let out = '"'
    for (const ch of value) {
        const code = ch.codePointAt(0) as number
        out +=
            ch === '"'
                ? '\\"'
                : ch === '\\'
                  ? '\\\\'
                  : ch === '\n'
                    ? '\\n'
                    : ch === '\t'
                      ? '\\t'
                      : code < 0x20 || code === 0x7f || code > 0x7e
                        ? `\\u{${code.toString(16)}}`
                        : ch
    }
    return `${out}"`
}

/** A `Finset Name` literal — `∅` when empty, because `{}` is notation Lean does not have here. */
const leanFinset = (names: readonly string[]): string =>
    names.length === 0 ? '∅' : `{${names.map(leanString).join(', ')}}`

/**
 * A `℘⁺fin` literal, as `NEFinset.of` wants it: one element and the rest.
 *
 * The helper (`formal/Calculus/Domain.lean:271`) exists so the non-emptiness proof is discharged by
 * `insert` rather than at the call site, which is why this can be pure text.
 */
const leanNonEmptySet = (elements: readonly string[], at: string): string => {
    const [first, ...rest] = elements
    if (first === undefined) {
        return refuse(
            at,
            'an empty wire set — §1 types SS/NS/BS as ℘⁺fin, so `NEFinset` has no empty inhabitant',
        )
    }
    return `NEFinset.of ${first} ${rest.length === 0 ? '∅' : `{${rest.join(', ')}}`}`
}

/**
 * The `{k // k ∈ keys} → α` half of a map, as a chain of key tests.
 *
 * The last entry is the `else`, which is total by accident of the type rather than by luck: the
 * subtype's inhabitants are exactly the declared keys, so `fin_cases` in the `vector` tactic
 * reaches the final branch only for the final key.
 */
const leanKeyFunction = (
    entries: readonly (readonly [string, string])[],
): string => {
    if (entries.length === 0) {
        return 'fun k => absurd k.2 (Finset.not_mem_empty k.1)'
    }
    const last = entries[entries.length - 1] as readonly [string, string]
    const tests = entries
        .slice(0, -1)
        .map(
            ([name, body]) => `if k.1 = ${leanString(name)} then ${body} else `,
        )
        .join('')
    return `fun k => ${tests}${last[1]}`
}

/** A byte string, as the `List UInt8` §1 calls `Bytes`. */
const leanBytes = (bytes: Uint8Array): string =>
    `[${Array.from(bytes).join(', ')}]`

/* ── values ──────────────────────────────────────────────────────────────────────────────── */

const isRecord = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value)

/**
 * A `Value` — §1's value language, as `denote`'s `e` consumes it.
 *
 * Directed by the *value*, not by the codec, which is sound because §5's `κ` is: a value and the
 * attribute it writes have the same kind, and every codec in this library takes the kind its
 * grammar says it takes. The one place that would bite is `held`, whose whole job is to change the
 * kind held — and `held` is unemittable for a different reason anyway.
 *
 * A `number` is refused here rather than approximated. `Double` is an axiom
 * (`formal/Calculus/Domain.lean:236`) with `toDec`, `ofDec` and a round-trip law but no
 * constructor, so `Value.num` has no closed term and no `#print`able spelling. This is permanent,
 * not a gap: writing one would need a numeral-to-double literal the model deliberately does not
 * have.
 */
export const leanValueOf = (value: unknown, at = 'value'): string => {
    if (typeof value === 'string') return `Value.str ${leanString(value)}`
    if (typeof value === 'boolean') return `Value.bool ${value}`
    if (value === null || value === undefined) return 'Value.null'
    if (typeof value === 'number' || typeof value === 'bigint') {
        return refuse(
            at,
            '`Double` is an axiom with no closed terms, so `Value.num` is unconstructible — use `decimal`',
        )
    }
    if (value instanceof Uint8Array) return `Value.bin ${leanBytes(value)}`
    if (value instanceof Set) {
        const members = [...value]
        const first = members[0]
        if (typeof first === 'string') {
            return `Value.strSet (${leanNonEmptySet(
                members.map((m) => leanString(m as string)),
                at,
            )})`
        }
        if (first instanceof Uint8Array) {
            return `Value.binSet (${leanNonEmptySet(
                members.map((m) => leanBytes(m as Uint8Array)),
                at,
            )})`
        }
        if (typeof first === 'number') {
            return refuse(
                at,
                '`Value.numSet` is a `NEFinset Double`, and `Double` has no closed terms',
            )
        }
        return refuse(
            at,
            'an empty set, or one whose element kind is not S, N or B',
        )
    }
    if (Array.isArray(value)) {
        return `Value.arr [${value
            .map((element, index) => leanValueOf(element, `${at}[${index}]`))
            .join(', ')}]`
    }
    if (isRecord(value)) {
        // an absent optional attribute is a name the map does not have, not a name holding null —
        // §4's `optional` is about presence, and emitting `null` would test a different vector
        const names = Object.keys(value).filter(
            (name) => value[name] !== undefined,
        )
        return `Value.map ${leanFinset(names)} (${leanKeyFunction(
            names.map(
                (name) =>
                    [name, leanValueOf(value[name], `${at}.${name}`)] as const,
            ),
        )})`
    }
    return refuse(at, `no Value for a ${typeof value}`)
}

/* ── attributes ──────────────────────────────────────────────────────────────────────────── */

/** A numeral, with §1's well-formedness discharged by `by decide` where it is written. */
const leanNumeral = (numeral: string): string =>
    `WFNumeral.of ${leanString(numeral)}`

/**
 * An `Attr` — §1's attribute domain, one member per attribute.
 *
 * `N` carries `WFNumeral`, a subtype, so `WFNumeral.of` runs §1's grammar at elaboration time with
 * its `by decide` default argument. A numeral this library will happily write but §1 refuses does
 * not produce a false theorem: it produces a *file that will not elaborate*, naming the numeral.
 * That is the bridge working, and it is worth knowing that is what such a failure means.
 */
export const leanAttrOf = (
    attribute: AttributeValue,
    at = 'attribute',
): string => {
    const member = memberOf(attribute)
    switch (member) {
        case 'S':
            return `Attr.s ${leanString(attribute.S as string)}`
        case 'N':
            return `Attr.n (${leanNumeral(attribute.N as string)})`
        case 'B':
            return `Attr.b ${leanBytes(attribute.B as Uint8Array)}`
        case 'BOOL':
            return `Attr.bool ${attribute.BOOL}`
        case 'NULL':
            return 'Attr.null'
        case 'SS':
            return `Attr.ss (${leanNonEmptySet(
                (attribute.SS as readonly string[]).map(leanString),
                at,
            )})`
        case 'NS':
            return `Attr.ns (${leanNonEmptySet(
                (attribute.NS as readonly string[]).map(
                    (n) => `(${leanNumeral(n)})`,
                ),
                at,
            )})`
        case 'BS':
            return `Attr.bs (${leanNonEmptySet(
                (attribute.BS as readonly Uint8Array[]).map(leanBytes),
                at,
            )})`
        case 'L':
            return `Attr.l [${(attribute.L as readonly AttributeValue[])
                .map((element, index) => leanAttrOf(element, `${at}[${index}]`))
                .join(', ')}]`
        case 'M': {
            const map = attribute.M as Record<string, AttributeValue>
            const names = Object.keys(map)
            return `Attr.m ${leanFinset(names)} (${leanKeyFunction(
                names.map(
                    (name) =>
                        [
                            name,
                            leanAttrOf(
                                map[name] as AttributeValue,
                                `${at}.${name}`,
                            ),
                        ] as const,
                ),
            )})`
        }
        default:
            return refuse(at, 'an attribute carrying no member')
    }
}

/* ── the predicates this library ships ───────────────────────────────────────────────────── */

/**
 * A `refine` predicate the model can name, and the Lean expression that names it.
 *
 * ── why this is a registry of two, and not of everything ───────────────────────────────────────
 *
 * `Term.refine` carries `q : Value → Bool` and this library carries a JavaScript closure, so the
 * general case has no emission and never will. What makes *some* cases emittable is that a closure
 * this library itself exported is not arbitrary: it is a function with a specification, and the
 * model has the same specification under a name. Recognition is by **reference** against the
 * exported function — not by `Function.prototype.toString`, which a minifier or a refactor changes
 * without changing meaning, and which would therefore go on emitting after the correspondence had
 * stopped holding.
 *
 * The inventory is small, and the smallness is the finding rather than an omission: `src/` builds
 * **no** `refine`, `held`, `legacy` or `custom` internally — every one of the four is a combinator
 * a caller reaches for, and `codec.ts` never reaches for them itself. The only functions this
 * package exports that can stand in a predicate position at all are {@link isNumeral} and
 * {@link isStoredNumeral} (`src/attribute.ts`), which are properties of the `N` carrier rather
 * than of any codec. So the boundary this registry moves is exactly two predicates wide.
 *
 * ── the correspondence, and what checked it ────────────────────────────────────────────────────
 *
 * `isStoredNumeral` ↦ `isStored` (`formal/Calculus/Combinators.lean:409`) and `isNumeral` ↦ the
 * same shape over `Numeral.WF`, which the model spells only at the `.num` carrier (`inD`,
 * `Combinators.lean:405`) and so is written out here. Both were checked against the kernel rather
 * than read across: a corpus of numeral spellings was run through the TypeScript predicates, the
 * verdicts emitted as `Numeral.WF s = b` / `Numeral.Stored s = b` rows, and all of them closed by
 * `rfl`. `inD` is deliberately *not* used for `isNumeral`: it decides `Numeral.WF d.toDec` for a
 * **double**, which is a different predicate on a different carrier, and it is `noncomputable`, so
 * a vector mentioning it would not reduce.
 *
 * ── the side condition, which is not decoration ────────────────────────────────────────────────
 *
 * The two TypeScript predicates take a `string`; a `Value → Bool` takes anything. They disagree
 * where JavaScript coerces: `isStoredNumeral(['1'])` is `true`, because `RegExp.test` stringifies
 * its argument and `String(['1'])` is `'1'`, while `isStored (Value.arr …)` is `false`. So the
 * correspondence holds *on string values only*, and {@link writesOnlyStrings} confines the emission
 * to inner terms that write nowhere else — where `Codec.restrict`'s `e` is `if q v then c.e v else
 * none` and `c.e v` is already `none` off the strings, so `q`'s verdict there cannot be observed.
 */
type ShippedPredicate = {
    /** The Lean expression, parenthesised where it is not an identifier. */
    readonly lean: string
    /** What it is, for the refusal message when the side condition fails. */
    readonly what: string
}

const shippedPredicates: ReadonlyMap<unknown, ShippedPredicate> = new Map<
    unknown,
    ShippedPredicate
>([
    [
        isStoredNumeral,
        {
            lean: 'isStored',
            what: '`isStoredNumeral`, which is `Numeral.Stored`',
        },
    ],
    [
        isNumeral,
        {
            lean: '(fun v => match v with | .str s => Numeral.WF s | _ => false)',
            what: '`isNumeral`, which is `Numeral.WF` at the text carrier',
        },
    ],
])

/**
 * Whether every value this term writes is a `Value.str`.
 *
 * The side condition on {@link shippedPredicates}. Deliberately a short whitelist rather than a
 * walk over `writes`: a term whose written *attribute* is `S` is not the same as a term whose
 * accepted *value* is a string — `held` is the counterexample, and `opaque` writes whatever it is
 * handed. Recurses through `refine`, because a refinement writes where its inner term does.
 */
const writesOnlyStrings = (def: CodecDef | undefined): boolean => {
    if (!def) return false
    if (def.kind === 'string' || def.kind === 'decimal') return true
    // read off the base rather than off the values, which is the same change the definition made:
    // a `decimal` literal's alternatives are text, and so is what it writes
    if (def.kind === 'literal') {
        return def.base === 'string' || def.base === 'decimal'
    }
    if (def.kind === 'refine') return writesOnlyStrings(def.inner.def)
    return false
}

/* ── terms ───────────────────────────────────────────────────────────────────────────────── */

/** How deep a `lazy` chain may be forced before the emitter calls it recursive and gives up. */
const lazyLimit = 16

/**
 * A `Term` — §3's syntax, from what the codec says it is.
 *
 * Read off `codec.def`, which is this library's own abstract syntax and is documented as such. The
 * mapping is one-to-one where it exists at all; where it does not, this throws
 * {@link LeanUnemittable}, and the throwing cases are the interesting half of the bridge:
 *
 * **Two kinds of inexpressible, and they were one bullet until refusal vectors split them.**
 * A term is unemittable when *the term* has no Lean expression; a positive vector is impossible
 * when the term is fine and no *value* at it can be written. Only the first belongs here.
 *
 * - **A numeric `literal`.** Term-inexpressible: `Term.literal GroundKind.number ls` needs `ls :
 *   NEFinset Double`, and `Double` is an axiom with no closed terms, so there is no alternatives
 *   set to write. Permanent, in both directions — no refusal vector can name this term either.
 * - **`number` itself is *not* here.** `Term.number` is a closed term. `Value.num` is what has no
 *   inhabitant, and `leanValueOf` refuses it, so the impossibility is reported where it lives and
 *   refusal vectors reach `number` with no flag and no mode parameter.
 * - **`held`, `legacy`, `custom`.** Three of §3's constructors carry *functions* —
 *   `f g : Value → Value`, `r : Attr → Option Value`, `ce`/`cp` — and this library carries
 *   JavaScript closures in the same positions. There is no expression in Lean for an arbitrary
 *   closure. `legacy` is the worst of the three and for a second reason: `CodecDef` keeps only the
 *   *current* codec, so the older readers are not even recorded to be refused about.
 * - **`refine`, unless the predicate is one this library shipped.** The fourth
 *   function-carrying constructor, and the one where the line has moved. See
 *   {@link ShippedPredicate}: `isNumeral` and `isStoredNumeral` are recognised by reference and
 *   emitted as the model's own predicates, and everything else is still refused, by name. The
 *   boundary is no longer "all refinements" but "refinements this library did not build", which is
 *   the honest line — and it is only two predicates wide, because `src/` constructs none of these
 *   four internally.
 *
 * `Rest.drop` vs `Rest.refuse` used to be a fourth entry here: `CodecDef` recorded the rest *codec*
 * and nothing when the policy was a string, so this wrote `Rest.drop` for either. It was sound for
 * the vectors this module writes and only for them — `objectCodec`'s `e` is `objWrite`, which takes
 * `rc?` and not the `kn` filter (`formal/Calculus/Combinators.lean:1691`), and `rcOf` is `none` for
 * both policies, so the two denote the same `e` and differ only under `p`. A decode-direction
 * vector would have needed them apart and would have been silently wrong. `CodecDef['rest']` now
 * carries the policy rather than only its codec, and this emits all three.
 */
export const leanTermOf = (
    codec: AnyCodec,
    at = 'codec',
    forced = 0,
): string => {
    return leanTermOfDef(codec.def, at, forced)
}

const leanTermOfDef = (def: CodecDef, at: string, forced: number): string => {
    switch (def.kind) {
        case 'string':
            return 'Term.string'
        case 'decimal':
            return 'Term.decimal'
        case 'boolean':
            return 'Term.boolean'
        case 'binary':
            return 'Term.binary'
        case 'null':
            return 'Term.null'
        // **Emittable, and it took refusal vectors to see that.** `Term.number` is a closed term;
        // what has no closed inhabitant is `Value.num`, and `leanValueOf` refuses that with an
        // accurate message. So a *positive* vector here still fails, at the value where the
        // impossibility actually is, and a *refusal* vector — `(denote Term.number).e
        // (Value.str "x") = none` — is `rfl`. The refusal used to sit here and made the whole
        // term unmentionable, which is a fact about positive vectors written as a fact about the
        // syntax. Contrast `literal` at `number` below, which really is unemittable.
        case 'number':
            return 'Term.number'
        /**
         * `Term.literal` is indexed by a `GroundKind`, and this emits every base whose carrier has
         * closed terms — which, since `decimal` became one, is four of the six.
         *
         * - `string` → `GroundKind.string`, carrier `String`.
         * - `boolean` → `GroundKind.boolean`, carrier `Bool`.
         * - `decimal` → `GroundKind.decimal`, carrier `StoredNumeral`, a **subtype** of `Numeral`
         *   gated on `Numeral.Stored`. So an alternative is `⟨"1", by decide⟩` and not `"1"`: the
         *   gate is §1's grammar run at elaboration time, exactly as `WFNumeral.of` runs it on the
         *   attribute side. A numeral this library would write and §1 refuses does not produce a
         *   false theorem — it produces a file that will not elaborate, naming the numeral. The
         *   constructor already refuses a non-stored alternative (`literalCodec`'s `ℓ ⊆ D` at
         *   `decimal`), so in practice the two gates agree and `lean.predicates.spec.ts` is what
         *   says they are the same predicate.
         * - `binary` → `GroundKind.binary`, carrier `Bytes`, which is §1's `List UInt8` and emits
         *   as one.
         * - `number` → `GroundKind.number`, carrier `Double`, which is an axiom. Permanent — and
         *   **not** the same refusal `Term.number` used to get, which is the distinction refusal
         *   vectors forced. `Term.number` is a closed term whose *values* are unwritable; this one
         *   has no closed term at all, because the alternatives set is `NEFinset Double`. The first
         *   moved to the value side and the second cannot.
         *
         * `binary` was refused here too, on the ground that "`leanValue` has no `B` case". It has
         * one — `leanValueOf` emits `Value.bin` for a `Uint8Array`, and has for as long as the
         * refusal has been there — so the refusal was reachable only by never being tried. The
         * kernel accepts the term and both directions of its admission.
         *
         * `decimal` was refused here until `decimal` became a `GroundKind`, on the ground that
         * `GroundKind` was `string | number | boolean | binary | null`. That was true when written
         * and stopped being true; the base and its `StoredNumeral` carrier are in `Domain.lean`'s
         * `GroundKind.Carrier`, and `GroundKind.toValue` sends a decimal alternative to `.str x.1`,
         * so the value side needed no change at all. The old note also reasoned that emitting it as
         * `GroundKind.string` would denote a codec writing `S` and `GroundKind.number` would lose
         * the exactness — both still true, and both now beside the point.
         */
        case 'literal': {
            const base = def.base
            if (base === 'number') {
                return refuse(
                    at,
                    'a numeric literal sits at `GroundKind.number`, whose carrier is `Double`',
                )
            }
            const allowed = [...new Set(def.allowed as readonly unknown[])]
            const alternative = (one: unknown): string =>
                base === 'boolean'
                    ? String(one)
                    : base === 'binary'
                      ? leanBytes(one as Uint8Array)
                      : base === 'decimal'
                        ? `⟨${leanString(one as string)}, by decide⟩`
                        : leanString(one as string)
            return `Term.literal GroundKind.${base} (${leanNonEmptySet(
                allowed.map(alternative),
                at,
            )})`
        }
        /**
         * `Term.set` is indexed by a **`SetBase`**, not by an element term.
         *
         * This emitted `Term.set (<element term>)` and stopped compiling the day
         * `formal/Calculus/Term.lean:60` changed: the rule's premise `setMember μ = some μS` was
         * partial, so the old constructor accepted element terms the rule then refused, and the
         * index makes that refusal a type error instead.
         *
         * A **restricted** element — `refine(b, q).set()`, `string.set('a','b')` — is still a
         * perfectly good codec and still has no *term*. `setCodec_restrict` says the set of a
         * restriction and the restriction of a set write the same attribute, but that is an
         * equation between `Codec`s, and the restriction it lifts is not itself a `Term.set`. So a
         * bare base is emitted and everything else is named and refused, rather than emitted as its
         * base — which would denote a codec that admits members this one rejects.
         */
        case 'set': {
            const base = setBase(def.element)
            if (!base || def.element.def?.kind !== base) {
                return refuse(
                    `${at}.element`,
                    base
                        ? `a set of a *restricted* element — this one is a \`${def.element.def?.kind}\` over \`${base}\`. \`Term.set\` is indexed by a bare \`SetBase\`, and the lift \`setCodec_restrict\` is an equation between codecs rather than a term`
                        : 'a set whose element is not one of the four `SetBase` bases',
                )
            }
            return `Term.set SetBase.${base}`
        }
        case 'array':
            return `Term.array (${leanTermOf(def.element, `${at}.element`, forced)})`
        case 'tuple': {
            const elements = def.elements
                .map((element, index) =>
                    leanTermOf(element, `${at}[${index}]`, forced),
                )
                .join(', ')
            const tail = def.tail
                ? `(some (${leanTermOf(def.tail, `${at}.tail`, forced)}))`
                : 'none'
            return `Term.tuple [${elements}] ${tail}`
        }
        case 'record':
            return `Term.record (${leanTermOf(def.value, `${at}.value`, forced)})`
        case 'attributes': {
            const names = Object.keys(def.of)
            const fields = leanKeyFunction(
                names.map(
                    (name) =>
                        [
                            name,
                            leanFieldOf(
                                def.of[name] as AnyCodec,
                                `${at}.${name}`,
                                forced,
                            ),
                        ] as const,
                ),
            )
            // three policies, three terms — `CodecDef` records the policy itself, so nothing here
            // has to guess which of `drop` and `refuse` an absent codec meant
            const rest =
                typeof def.rest === 'string'
                    ? `Rest.${def.rest}`
                    : `(Rest.codec (${leanTermOf(def.rest, `${at}.rest`, forced)}))`
            // **One argument, a `Body`.** `db444e3` made the object payload a stratum, so
            // `Term.object` takes `Body.mk names fields rest` where it used to take the three
            // separately — and this row kept emitting the three, which typechecked against no
            // `Calculus/` after that commit. Nothing caught it for a day: the committed samples
            // are generated *by this function*, so `lean.spec.ts`'s byte comparison agreed with a
            // stale emitter, and no gate ran a generated file through Lean. Both are fixed; see
            // `ARCHITECTURE.md` §2, where the emitter is now the ninth companion a stratum owes.
            return `Term.object (Body.mk ${leanFinset(names)} (${fields}) ${rest})`
        }
        case 'tagged': {
            // One option, one tag: `discriminatedUnion` refuses a literal admitting several
            // values at the declaration, so the table cannot hold one codec twice and the option
            // list cannot repeat one. `Typed.dunion`'s `hdisj` is answered upstream of here — this
            // used to dedup by identity, which was the same invariant enforced in two places
            const options = Object.values(def.variants)
                .map((variant, index) =>
                    leanTermOf(variant, `${at}.variants[${index}]`, forced),
                )
                .join(', ')
            return `Term.dunion ${leanString(def.discriminator)} [${options}]`
        }
        case 'untagged':
            return `Term.union [${def.variants
                .map((variant, index) =>
                    leanTermOf(variant, `${at}[${index}]`, forced),
                )
                .join(', ')}]`
        case 'nullable':
            return `Term.nullable (${leanTermOf(def.inner, `${at}.inner`, forced)})`
        case 'opaque':
            return `Term.opaq ${def.numbers === 'lossy'}`
        case 'lazy': {
            if (forced >= lazyLimit) {
                return refuse(
                    at,
                    `a lazy chain deeper than ${lazyLimit} — `.concat(
                        'a genuinely recursive codec has no term at all: `Term.lazy` carries a `Term`, ',
                        'not a thunk, and `Continuity.lean` shows a recursive union has no fixpoint semantics',
                    ),
                )
            }
            return `Term.lazy (${leanTermOf(def.get(), `${at}.inner`, forced + 1)})`
        }
        case 'refine': {
            // recognised by reference against the function this package exported, so a rename or a
            // reimplementation of the predicate is a type error here rather than a silent misemission
            const known = shippedPredicates.get(def.refined.is)
            if (!known) {
                return refuse(
                    at,
                    `\`Term.refine\` carries \`q : Value → Bool\`, and this predicate is not one this library ships — it is the caller's closure for ${JSON.stringify(def.refined.what)}. The recognised ones are \`isNumeral\` and \`isStoredNumeral\` from \`src/attribute.ts\`, passed by reference`,
                )
            }
            if (!writesOnlyStrings(def.inner.def)) {
                return refuse(
                    at,
                    `${known.what} decides a *string*, and this refinement's inner term writes values that are not strings — where JavaScript would coerce and the model would not, so the two predicates would part company`,
                )
            }
            return `Term.refine (${leanTermOf(def.inner, `${at}.inner`, forced)}) ${known.lean}`
        }
        case 'held':
            return refuse(
                at,
                '`Term.held` carries two `Value → Value` functions; this one carries a pair of closures, and this library ships no adapters of its own to recognise — `held` is a combinator callers reach for and `codec.ts` never uses',
            )
        case 'legacy':
            return refuse(
                at,
                "`Term.legacy` carries `r : Attr → Option Value`; `CodecDef['legacy']` records only the *current* codec and drops the older readers entirely, so there is nothing here to emit even for a reader this library recognised",
            )
        case 'custom':
            return refuse(
                at,
                '`Term.custom` carries its pair as data, and a hand-written codec has no data to give',
            )
        case 'optional':
        case 'fallback':
            return refuse(
                at,
                'a §4 *field*, not a term — `optional`/`fallback` denote `Field`, and no `Term` position accepts one',
            )
        case 'restOf':
            return refuse(
                at,
                'a §4 *rest policy*, not a term — it denotes `Rest`, which is a third stratum',
            )
    }
}

/** A `Field` — §4's stratum, which is a *position* in a map and not a codec. */
const leanFieldOf = (codec: AnyCodec, at: string, forced: number): string => {
    const def = codec.def
    if (def?.kind === 'optional') {
        return `Field.optional (${leanTermOf(def.inner, at, forced)})`
    }
    if (def?.kind === 'fallback') {
        return `Field.fallback (${leanTermOf(def.inner, at, forced)}) (${leanValueOf(
            def.value,
            `${at}.fallback`,
        )})`
    }
    return `Field.req (${leanTermOf(codec, at, forced)})`
}

/* ── vectors ─────────────────────────────────────────────────────────────────────────────── */

/**
 * How a vector states its claim to the kernel.
 *
 * `'check'` writes `check n ((denote t).e v) (some a) = .same := rfl` and is the default. It
 * depends on `Calculus/Vectors.lean` — a fuelled three-valued comparator with `check_same` and
 * `check_differ` proved about it, so a passing line cashes to `(denote t).e v = some a` as a
 * theorem. No tactic, no `funext` gymnastics, an order of magnitude faster on maps, and it can
 * state a **negative** vector (`= .differ`), which an equation cannot. The `n` is fuel, because
 * only structural recursion reduces in the kernel; {@link leanVector} computes it from the
 * attribute, and under-fuelling reduces to `.exhausted`, which matches neither side and fails the
 * build rather than passing quietly.
 *
 * `'equation'` writes `(denote t).e v = some a` and proves it with a tactic the generated file
 * carries. It depends on nothing beyond `denote`, which is worth keeping for a tree where
 * `Vectors.lean` is absent — but it cannot express a refusal, and on maps `rfl` does not merely
 * fail, it **diverges**: `Attr.m` holds a function, so the model's answer is stuck under a binder,
 * pointwise equal to the emitted lambda and not definitionally equal, and `isDefEq` runs to the
 * heartbeat limit.
 */
export type Protocol = 'equation' | 'check'

/** One proposed agreement: this codec, given this value, writes this attribute. */
export type Vector = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly value: unknown
}

/** Lean identifiers are not JavaScript ones — keep it to the safe intersection. */
const leanIdent = (name: string): string => {
    const cleaned = name.replace(/[^A-Za-z0-9_]/g, '_')
    return /^[A-Za-z_]/.test(cleaned) ? cleaned : `v_${cleaned}`
}

/**
 * One vector, as a Lean `theorem`.
 *
 * The attribute is not supplied — it is *taken from the library*, by running the encode this
 * theorem is about. That is the whole design: what gets checked is what this library actually
 * writes on this input, today, and a change to `codec.ts` that changes it makes the Lean file stop
 * compiling. Supplying the attribute by hand would check the vector's author instead.
 *
 * `unsafeEncode` throwing is left to propagate: a value this library refuses is not a vector about
 * agreement, it is a vector about refusal, and `e v = none` is the theorem for that.
 */
export const leanVector = (
    { name, codec, value }: Vector,
    protocol: Protocol = 'check',
): string => {
    const term = leanTermOf(codec, name)
    const attribute = codec.unsafeEncode(value as never)
    const head = [`/-- \`${name}\` -/`, `theorem ${leanIdent(name)} :`]
    return protocol === 'equation'
        ? [
              ...head,
              `    (denote (${term})).e`,
              `      (${leanValueOf(value, name)})`,
              `    = some (${leanAttrOf(attribute, name)}) := by`,
              '  vector',
          ].join('\n')
        : [
              ...head,
              `    check ${fuelFor(attribute)}`,
              `      ((denote (${term})).e`,
              `        (${leanValueOf(value, name)}))`,
              `      (some (${leanAttrOf(attribute, name)})) = .same := rfl`,
          ].join('\n')
}

/**
 * One proposed **refusal**: this codec, given this value, writes nothing — and neither does the
 * model.
 *
 * **The class of vector 573 loose rows never produced.** A positive vector is an agreement about
 * what `encode` wrote, so a value `encode` refuses produced no vector at all — which is exactly
 * the half of the pair where `src/` and the model could disagree unobserved. `leanVector`'s own
 * docstring had named the shape and left it unbuilt: "a value this library refuses is not a
 * vector about agreement, it is a vector about refusal, and `e v = none` is the theorem for that."
 *
 * **It needs neither the comparator nor fuel, and that is not an optimisation.** The gap positive
 * vectors fight is `Attr.m`'s payload — a function under a binder, pointwise equal to the emitted
 * lambda and not definitionally equal — so they need `check`, or `funext` and a case split. A
 * refusal's answer is `none`, which carries no payload, so `rfl` closes it outright at every
 * codec including the map-shaped ones.
 *
 * **And it reaches `number`**, where no positive vector can: `Term.number` is a closed term and
 * only its *values* are unwritable, so `(denote Term.number).e (Value.str "x") = none` is `rfl`.
 * A numeric `literal` stays out, its alternatives being `NEFinset Double`.
 */
export type Refusal = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly value: unknown
}

/**
 * One refusal, as a Lean `theorem` — and the `src/` side is checked here rather than emitted.
 *
 * A refusal vector claims *both* sides refuse. The model's half is the theorem; this library's
 * half cannot be a theorem in a Lean file, so it is asserted at emit time and throws. Emitting a
 * refusal for a value this library admits would write a Lean theorem that is *true* about a
 * disagreement — the worst possible artifact, a green check over a real divergence.
 */
export const leanRefusal = ({ name, codec, value }: Refusal): string => {
    if (admits(codec, value)) {
        throw new LeanUnemittable(
            name,
            'this codec admits this value, so a refusal vector about it would assert the model refuses what `src/` writes — pass it as a `Vector` instead',
        )
    }
    return [
        `/-- \`${name}\` — refused on both sides -/`,
        `theorem ${leanIdent(name)} :`,
        `    (denote (${leanTermOf(codec, name)})).e`,
        `      (${leanValueOf(value, name)}) = none := rfl`,
    ].join('\n')
}

/**
 * One proposed **separation verdict**: `src/` refuses this pair at the declaration, and the model
 * must not certify it.
 *
 * **The bridge from `src/`'s declaration-time guard to `Orth`, and it runs one way only.** `Orth`
 * is a *sufficient* decidable condition for a fragment of (U) — `formal/ARCHITECTURE.md` §5's own
 * by-phase table puts it at six of twenty-five hand discharges directly — so `Orth x y = false`
 * does **not** mean the model cannot separate the pair. It means the cheap syntactic test
 * declines. Measured over the corpus, 66 of 351 pairs are exactly that and every one is
 * legitimate, each landing in one of the guard's three documented exemptions: a literal (which
 * identifies its own values), an object option (chosen by names), or an option whose kind is
 * unknown (`opaque`, `lazy`, an adapter).
 *
 * So the checkable law is the converse. **If the model certifies a pair, `src/` must accept it** —
 * refusing a declaration the model *proves* separable is `src/` rejecting a union that works.
 * Stated as a theorem per refusal: `Orth x y = false`, which stops compiling the moment `Orth`
 * starts certifying a pair `src/` turns down. Zero counterexamples today, and the pair that
 * motivated `ff75c6b` is the reason the law is worth gating rather than asserting once:
 * `Orth (Term.set .string) (Term.set .number) = true`, which `src/` refused until that commit.
 */
export type Separation = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly left: AnyCodec
    readonly right: AnyCodec
}

/**
 * One separation verdict, as a Lean `theorem` — and the `src/` side is checked here, as with
 * {@link leanRefusal}.
 *
 * `union([left, right])` must throw. Emitting this for a pair `src/` *accepts* would assert the
 * model declines a pair nobody is refusing, which says nothing about either side.
 */
export const leanSeparation = ({ name, left, right }: Separation): string => {
    let refused = false
    try {
        union([left, right] as never)
    } catch {
        refused = true
    }
    if (!refused) {
        throw new LeanUnemittable(
            name,
            '`src/` accepts this pair at the declaration, so there is no refusal for the model to contradict — the law is one-directional and this is the direction it does not run',
        )
    }
    return [
        `/-- \`${name}\` — \`src/\` refuses this pair; the model must not certify it -/`,
        `theorem ${leanIdent(name)} :`,
        `    Orth (${leanTermOf(left, name)})`,
        `      (${leanTermOf(right, name)}) = false := by decide`,
    ].join('\n')
}

/**
 * The separation verdicts as a module of their own, because they need `Orth`.
 *
 * `Calculus.Vectors` reaches `Denote` and not `Orthogonality`, and adding the import to the
 * committed vector samples would make them depend on a module they have nothing to say about.
 * Generated at gate time and elaborated, never committed — the counts are in
 * `formal/ARCHITECTURE.md` §5, which is where the verdict this checks is written down.
 */
export const leanSeparationModule = (
    separations: readonly Separation[],
): string =>
    `import Calculus.Orthogonality

/-!
# Declaration-guard verdicts, proposed to the classifier

**Generated — do not edit.** One theorem per option pair \`src/\`'s \`union\` refuses at the
declaration. \`Orth\` is *sufficient* and not necessary, so this runs one way: a pair the model
certifies must not be refused by \`src/\`. See \`src/lean.ts\`'s \`Separation\`.
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${separations.map(leanSeparation).join('\n\n')}

end Calculus
`

/**
 * One proposed **read verdict**: this codec, given this attribute, decodes exactly when the
 * model's read row admits it.
 *
 * **The differential that replaced a port.** HANDOFF's fourth item was to give the resolver's
 * read side a decision through a port of `AdmA`, in the style `admits` ports `Adm`. Measured
 * first: over 864 (codec, attribute) pairs the two agree at **861 of 861 checkable** ones and
 * disagree at none. `decode` validates — it parses data somebody else wrote, which is its job —
 * where `encode` trusted its argument's *type*, and that asymmetry is the whole reason wiring
 * `admits` into the write side changed real answers and a read-side port would change none. So a
 * def-reading port would be a second description of what `decode` already computes exactly, and
 * two descriptions of one thing need a guard between them. **The guard is what landed.**
 *
 * `AdmA` is `noncomputable` — it consults `Double.ofDec` and `ownsNull` — so this cannot be
 * `#eval`. The kernel unfolds it anyway, which is the same fact `Vectors.lean` opens with, so the
 * verdict is asserted and elaboration is the test.
 */
export type ReadVerdict = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly attribute: AttributeValue
}

/**
 * Whether the model's read row is **stuck** on this pair rather than answering.
 *
 * `AdmA .number`'s `.n` row is `match Double.ofDec x.1 with | some d => …`, and `Double.ofDec` is
 * an axiom with **no computation rule** — so the row reduces to neither `true` nor `false` for
 * any concrete numeral. Both assertions fail, which is how it was told apart from a
 * disagreement; `AdmA .decimal` and `AdmA .string` on the same attribute reduce fine.
 *
 * Recorded rather than skipped: three pairs in today's corpus match, they are named in the
 * generated module's header, and a *new* stuck pair outside this shape does not slip through —
 * it fails to elaborate, and the reason gets read.
 *
 * The shape is the mirror of `number`'s other boundary and worth the contrast: a positive
 * *vector* at `number` is impossible because no `Value.num` can be **written**, while here the
 * term and the attribute are both writable and the **row** will not compute.
 */
export const readRowIsStuck = ({ codec, attribute }: ReadVerdict): boolean =>
    codec.def?.kind === 'number' &&
    Object.hasOwn(attribute as Record<string, unknown>, 'N')

/** One read verdict, as a Lean `theorem`; `src/`'s answer is taken by running `decode`. */
export const leanReadVerdict = (one: ReadVerdict): string => {
    const { name, codec, attribute } = one
    const decodes = admitsAttribute(codec, attribute)
    return [
        `/-- \`${name}\` — \`src/\` ${decodes ? 'decodes' : 'refuses'} this attribute -/`,
        `theorem ${leanIdent(name)} :`,
        `    AdmA (${leanTermOf(codec, name)})`,
        `      (${leanAttrOf(attribute, name)}) = ${decodes} := rfl`,
    ].join('\n')
}

/**
 * The read verdicts as a module of their own, because they need `AdmA`.
 *
 * Generated at gate time and elaborated, never committed — the counts are in
 * `formal/ARCHITECTURE.md` §10, where the rejected port is recorded.
 */
export const leanReadModule = (verdicts: readonly ReadVerdict[]): string => {
    const stuck = verdicts.filter(readRowIsStuck)
    const live = verdicts.filter((one) => !readRowIsStuck(one))
    return `import Calculus.Exactness

/-!
# Read verdicts, proposed to the model's read row

**Generated — do not edit.** One theorem per (codec, attribute) pair: \`AdmA t a\` equals whether
\`src/\`'s \`decode\` accepted it. ${live.length} of ${verdicts.length} pairs are asserted here.

The other ${stuck.length} are **stuck, not skipped**: \`AdmA .number\`'s \`.n\` row goes through
\`Double.ofDec\`, an axiom with no computation rule, so it reduces to neither \`true\` nor
\`false\` and *both* assertions fail. That is how it was told apart from a disagreement.
${stuck.map((one) => `  * \`${one.name}\``).join('\n')}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${live.map(leanReadVerdict).join('\n\n')}

end Calculus
`
}

/**
 * One proposed **resolution**: this union, given this value or attribute, picks what the model's
 * `select` picks.
 *
 * **Coverage, not a hole.** `lean.sample*.lean` already pins two — `union_of_two` and
 * `discriminated_union`, one value each — and the refusal cross product carries 88 more union and
 * `dunion` lines. Those check the same thing this does: a positive vector *is* an agreement about
 * which option answered, because the attribute it names is the one that option produced. What was
 * thin was the corpus, so this widens two pinned resolutions to 208 on the write side and 226 on
 * the read side, and the artifact is worth having for that and not for closing a gap.
 *
 * The write side reuses the `check` comparator, which is what crosses `Attr.m`'s binder. The read
 * side cannot: its answer is a `Value`, `Value.map` carries a function, and `Vectors.lean` has no
 * `Option Value` twin of `aeq`. See {@link readResolutionIsUnstatable}.
 */
export type Resolution = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly union: AnyCodec
    readonly value: unknown
}

/** One write-side resolution: what the union wrote, or that it wrote nothing. */
export const leanResolution = ({
    name,
    union: u,
    value,
}: Resolution): string => {
    const term = leanTermOf(u, name)
    let written: unknown
    let wrote = true
    try {
        const out = u.encode(value as never)
        wrote = !failed(out)
        written = out
    } catch {
        wrote = false
    }
    const head = [
        `/-- \`${name}\` — the option the union picked -/`,
        `theorem ${leanIdent(name)} :`,
    ]
    return wrote
        ? [
              ...head,
              `    check ${fuelFor(written as AttributeValue)}`,
              `      ((denote (${term})).e`,
              `        (${leanValueOf(value, name)}))`,
              `      (some (${leanAttrOf(written as AttributeValue, name)})) = .same := rfl`,
          ].join('\n')
        : [
              ...head,
              `    (denote (${term})).e`,
              `      (${leanValueOf(value, name)}) = none := rfl`,
          ].join('\n')
}

/** One read-side resolution, addressed by the attribute rather than the value. */
export type ReadResolution = {
    readonly name: string
    readonly union: AnyCodec
    readonly attribute: AttributeValue
}

/**
 * Whether a read-side resolution **cannot be stated**, for want of a comparator.
 *
 * A union that reads an attribute back to a **map** produces a `Value.map`, which carries a
 * function — so the model's answer is a lambda stuck under a binder, pointwise equal to the
 * emitted one and not definitionally equal. That is the same funext gap `Vectors.lean` opens by
 * describing for `Attr.m`, and the write side solves it with `aeq`: a fuelled comparator that
 * never compares two functions, only their values at every key of a key set it has already
 * checked is the same.
 *
 * **There is no `Option Value` twin of it.** `aeq` and `check` compare attributes. So these are
 * recorded rather than asserted, exactly as the three `Double`-stuck read verdicts are — and
 * unlike those, this one is a gap in the *machinery* and closable: the `veq` that would close it
 * is `aeq`'s construction over `Value.map` instead of `Attr.m`.
 *
 * **The second reason is the `Double` axiom arriving a third way**, and the three are worth
 * distinguishing because each closes differently or not at all. A numeric `literal` is
 * *term*-inexpressible: its alternatives are `NEFinset Double`. `AdmA .number`'s `.n` row is
 * *row*-irreducible: `Double.ofDec` has no computation rule. And here it is the **decoded value**
 * — `union([string.set(), number.set()])` reads an `NS` back to a `Set<number>`, whose Lean form
 * is `Value.numSet` over a `NEFinset Double`. Same axiom, three places, and only the funext one
 * has a repair.
 */
export const readResolutionIsUnstatable = (
    one: ReadResolution,
): 'Double' | undefined => {
    let read: unknown
    try {
        const out = one.union.decode(one.attribute as never)
        if (failed(out)) return undefined
        read = out
    } catch {
        return undefined
    }
    try {
        leanValueOf(read)
    } catch {
        return 'Double'
    }
    // a map-valued read was unstatable until `veq` — `Calculus/Vectors.lean` has the `Value`
    // twin of `aeq` now, so the funext gap is crossed on this side too
    return undefined
}

/** One read-side resolution: what the union read, or that it read nothing. */
export const leanReadResolution = (one: ReadResolution): string => {
    const { name, union: u, attribute } = one
    let read: unknown
    let did = true
    try {
        const out = u.decode(attribute as never)
        did = !failed(out)
        read = out
    } catch {
        did = false
    }
    const head = [
        `/-- \`${name}\` — the option the union read it back through -/`,
        `theorem ${leanIdent(name)} :`,
    ]
    // `vcheck` where something was read, for the reason the write side uses `check`: a `Value.map`
    // carries a function, so `rfl` on the assembled closure does not close. A refusal answers
    // `none`, which carries nothing, so it needs no comparator.
    return did
        ? [
              ...head,
              `    vcheck ${fuelForValue(read)}`,
              `      ((denote (${leanTermOf(u, name)})).p`,
              `        (${leanAttrOf(attribute, name)}))`,
              `      (some (${leanValueOf(read, name)})) = .same := rfl`,
          ].join('\n')
        : [
              ...head,
              `    (denote (${leanTermOf(u, name)})).p`,
              `      (${leanAttrOf(attribute, name)}) = none := rfl`,
          ].join('\n')
}

/**
 * The resolutions as a module of their own.
 *
 * Generated at gate time and elaborated, never committed — the counts are in
 * `formal/ARCHITECTURE.md` §5, beside the classifier this is the other half of.
 */
export const leanResolutionModule = (
    writes: readonly Resolution[],
    reads: readonly ReadResolution[],
): string => {
    const statable = reads.filter((one) => !readResolutionIsUnstatable(one))
    const doubled = reads.filter(
        (one) => readResolutionIsUnstatable(one) === 'Double',
    )
    return `import Calculus.Vectors

/-!
# Union resolution, model against library

**Generated — do not edit.** One theorem per (union, value) and (union, attribute) pair: the
option the model's \`select\` resolves to, against the one this library's resolver picked.
${writes.length} on the write side, ${statable.length} on the read side.

A map-valued read is stated like the others: it goes through \`vcheck\`, the \`Value\` twin of
\`check\`, because \`Value.map\` carries a function and \`rfl\` on the assembled closure does not
close. Five of these were recorded as unstatable until \`veq\` existed.

${doubled.length} **cannot be written down at all**: the value read back is a set of numbers,
so its Lean form is \`Value.numSet\` over a \`NEFinset Double\`, and \`Double\` is an axiom with no
closed terms. That is the same axiom the numeric \`literal\` and \`AdmA .number\` meet, arriving a
third way — at the *decoded value* rather than the term or the row — and it has no repair.
${doubled.map((one) => `  * \`${one.name}\``).join('\n')}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${writes.map(leanResolution).join('\n\n')}

${statable.map(leanReadResolution).join('\n\n')}

end Calculus
`
}

/**
 * How much fuel the `check` protocol's comparator needs for this attribute.
 *
 * `aeq` recurses on a `Nat` rather than on the attribute, because only a *structurally* recursive
 * function reduces in the kernel — a well-founded one elaborates to `WellFounded.fix` and no `rfl`
 * would close a vector line. So the budget is the generator's job, and it is exactly the
 * attribute's document nesting: one layer per `L` or `M`, one for the scalar at the bottom.
 *
 * Computed rather than fixed at a generous constant. Under-fuelling does not produce a false
 * theorem — `Verdict` has a third constructor, and an exhausted run matches neither `.same` nor
 * `.differ`, so the file fails to compile — but it does produce a puzzling failure, and there is no
 * reason to risk one when the number is right here.
 */
/**
 * The same budget on the value side, for `veq`.
 *
 * `fuelFor` walks an attribute's `L`/`M` nesting; this walks a value's arrays and plain objects,
 * which is the same document depth read off the other half of the pair. A set is one layer: its
 * members are scalars by construction.
 */
const fuelForValue = (value: unknown): number => {
    if (Array.isArray(value)) {
        return 1 + Math.max(0, ...value.map(fuelForValue))
    }
    const held = asRecordish(value)
    if (held) {
        return 1 + Math.max(0, ...Object.values(held).map(fuelForValue))
    }
    return 1
}

/** A plain object, as `shapeOf` recognises one — a map's payload and nothing else. */
const asRecordish = (value: unknown): Record<string, unknown> | undefined =>
    shapeOf(value) === 'map' ? (value as Record<string, unknown>) : undefined

const fuelFor = (attribute: AttributeValue): number => {
    const member = memberOf(attribute)
    if (member === 'L') {
        return (
            1 +
            Math.max(
                0,
                ...(attribute.L as readonly AttributeValue[]).map(fuelFor),
            )
        )
    }
    if (member === 'M') {
        return (
            1 +
            Math.max(
                0,
                ...Object.values(
                    attribute.M as Record<string, AttributeValue>,
                ).map(fuelFor),
            )
        )
    }
    return 1
}

/**
 * The `vector` tactic, and why the file carries it rather than `formal/` doing so.
 *
 * A generated file is a *proposal*. If it needed a tactic that lives in the mechanization, then
 * regenerating it could require editing the thing it is supposed to be independent of, and the
 * bridge would stop being one-directional. Everything the generated file needs is in the generated
 * file.
 */
const preamble = `import Calculus.Denote
import Calculus.Combinators
import Mathlib.Tactic.FinCases

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by \`src/lean.ts\` from the shipped TypeScript codecs: each
theorem below is one \`encode\` this library actually performed, proposed to the model as an
equation. A failure here is a disagreement between \`src/codec.ts\` and \`Calculus.denote\`, and the
theorem's name says which vector.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a \`k\` it never reads. \`Calculus/\` itself builds warning-free and so should this file; the
binder cannot be \`_\` because a multi-name object *does* read \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

/-- The one tactic every vector uses.

    \`rfl\` alone closes the scalar vectors and none of the map-shaped ones: \`M\`'s payload is a
    key set with a *function* on it, so the model's answer is \`fun k => (c.e (f k)).get _\` — stuck
    on the bound key, pointwise equal to the emitted lambda and not definitionally equal to it. The
    gap is closed by \`funext\` and a case split on the key set, applied to a fixpoint so that a map
    nested inside a map is reached too.

    The three wire-set alternatives are the second surprise. §1 types \`SS\`/\`NS\`/\`BS\` as
    \`Finset\`s, so their *order* carries no information — but a \`Finset\` is a \`Multiset\` with a
    proof, a \`Multiset\` is a quotient of lists, and two \`Quot.mk\`s of differently-ordered lists
    are not definitionally equal. This library sorts a set on the way out and the model keeps the
    order it was given, so \`rfl\` diverges on every set whose two sides disagree about order.
    \`decide\` settles it, because \`Finset\` equality at a concrete element type is decidable.

    The alternatives are ordered as they are because \`rfl\` first sends both the top-level goal and
    a mis-ordered set into an \`isDefEq\` loop that exhausts the heartbeat budget rather than
    failing. -/
macro "vector" : tactic => \`(tactic|
  (refine congrArg some ?_
   repeat' first
     | (refine congrArg (Attr.m _) (funext fun k => ?_)
        obtain ⟨_, hk⟩ := k
        fin_cases hk)
     | (refine congrArg Attr.ss (Subtype.ext ?_); decide)
     | (refine congrArg Attr.ns (Subtype.ext ?_); decide)
     | (refine congrArg Attr.bs (Subtype.ext ?_); decide)
     | rfl
     | congr 1))
`

const checkPreamble = `import Calculus.Vectors

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by \`src/lean.ts\` from the shipped TypeScript codecs: each
theorem below is one \`encode\` this library actually performed, proposed to the model. A failure
here is a disagreement between \`src/codec.ts\` and \`Calculus.denote\`, and the theorem's name says
which vector.

The verdict is \`Calculus.check\`'s, and \`check_same\` is what makes it worth having: \`.same\`
*implies* the two attributes are equal, so a line that reduces to \`.same\` is a proof and not a
comparator's opinion. The fuel on each line is the attribute's own nesting, computed by the
generator — an under-fuelled line reduces to \`.exhausted\`, which matches neither \`.same\` nor
\`.differ\`, so it fails to compile rather than passing quietly.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a \`k\` it never reads. \`Calculus/\` itself builds warning-free and so should this file; the
binder cannot be \`_\` because a multi-name object *does* read \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus
`

/**
 * A whole Lean module: a preamble and one theorem per vector.
 *
 * Two protocols, and the choice is not cosmetic — see {@link Protocol}.
 */
export const leanVectorModule = (
    vectors: readonly Vector[],
    protocol: Protocol = 'check',
    refusals: readonly Refusal[] = [],
    /**
     * How many refusals the *gate* checks, where this file carries a readable subset.
     *
     * Stated in the header so the committed sample cannot be mistaken for the coverage. A subset
     * that does not say it is one is the same defect as a count nobody can reproduce.
     */
    refusalsChecked = refusals.length,
): string => {
    const body = vectors
        .map((vector) => leanVector(vector, protocol))
        .join('\n\n')
    if (refusals.length === 0) {
        return `${protocol === 'equation' ? preamble : checkPreamble}\n${body}\n\nend Calculus\n`
    }
    const refused = refusals.map(leanRefusal).join('\n\n')
    const heading = [
        '',
        '/-! ## Refusals — neither side writes anything for these',
        '',
        `${refusals.length} of ${refusalsChecked} shown; \`scripts/gate.sh\` elaborates all`,
        `${refusalsChecked}. One \`rfl\` each, no comparator and no fuel: the answer is \`none\`,`,
        'which carries no function for the funext gap to open under.',
        '-/',
        '',
    ].join('\n')
    return `${protocol === 'equation' ? preamble : checkPreamble}\n${body}\n${heading}\n${refused}\n\nend Calculus\n`
}
