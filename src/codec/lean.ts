/**
 * Test vectors for the Lean model, emitted as Lean source.
 *
 * `formal/` is a mechanization of the codec calculus; this library is what it is supposed to
 * certify. The correspondence between the two is a *paper* obligation — somebody reads `denote`
 * and reads `src/codec/codec.ts` and believes they agree — and no instrument closes it, which is
 * the third of the three warranties `docs/architecture.md` keeps apart. This module is the
 * machine-checkable half of that belief.
 *
 * ── why the traffic goes this way ───────────────────────────────────────────────────────────────
 *
 * The obvious design is the other one: let Lean produce the expected attribute and compare it here.
 * `#eval` runs `denote`, so Lean can produce it, but a printed value certifies nothing, and
 * `native_decide` rests on `Lean.ofReduceBool`, outside the model's axiom base. The model declares no
 * axiom: `N` is carried exactly, as `WFNumeral`.
 *
 * What Lean *can* do is check. `(denote t).e v = some a` is a closed proposition, and for every
 * term form this library can express it is provable by kernel reduction — see the `vector` tactic
 * this module emits, and `src/codec/lean/lean.spec.ts` for the boundary. So TypeScript proposes and Lean
 * disposes: {@link leanVectorModule} writes a file of `theorem`s, and `lake build` on it either
 * succeeds or names the vector the two sides disagree about.
 *
 * ── the tactic, and why it is not `rfl` ────────────────────────────────────────────────────────
 *
 * `rfl` closes a scalar vector and dies on every map-shaped one, which was the surprise. `M`'s
 * payload is a `Finset Name` with a *function* on it (`MapOf`), so the
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
 *   | (refine congrArg Attr.l ?_)
 *   | (refine congrArg₂ List.cons ?_ ?_)
 *   | rfl
 *   | congr 1
 * ```
 *
 * The order matters and cost a probe to find: `rfl` first sends the top-level goal into an
 * `isDefEq` loop that exhausts the heartbeat budget rather than failing. A list that holds an
 * object does the same, because the object answers with a lookup at a bound key. So the tactic
 * splits a list into its elements before `rfl` runs.
 *
 * ── what cannot be emitted ─────────────────────────────────────────────────────────────────────
 *
 * {@link LeanUnemittable} is thrown, never guessed around, and its cases are the honest boundary of
 * the bridge. See {@link leanTermOf}. A JS number is one of them: it is a binary64 float, and
 * `Value.num` carries a `WFNumeral`, which is exact, so writing one down is a rounding the model
 * does not state. A `DynamoNumber` is a numeral, and it emits as `Value.num`.
 */
import type { AttributeValue } from './attribute'
import { DynamoNumber, isNumeral, isStoredNumeral, memberOf } from './attribute'
import type { AnyCodec, LiteralValue, ObjectSlot } from './codec'
import { union } from './codec'
import { accepts, readsBack } from './denote'
import { failed } from './result'
import type {
    Alternatives,
    Body,
    Literal,
    Predicate,
    Term,
    Field as TermField,
} from './term'
import {
    agrees,
    bindersOf,
    disjoint,
    force,
    readsFreeVariable,
    recursionUse,
    type Scope,
    viewsDisjoint,
} from './term'
import { shapeOf } from './value'

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
 * Not `JSON.stringify`, and **not `\u{...}`**, which Lean answers with `invalid hexadecimal
 * numeral`: it takes exactly four hex digits after `\u`, and neither language escapes DEL.
 *
 * **A code point above `U+FFFF` has no escape that is correct**, and the two spellings that look
 * like one fail in silence: `\u1d538` lexes as `\u1d53` then `8`, and the surrogate pair
 * `\ud835\udd38` lexes as two characters. Both elaborate, and both build the wrong string. So a
 * printable character is emitted raw, which is right at every code point and is what this emitter
 * already does with `∅` and `⟨⟩`. `\uHHHH` is kept for the control range and DEL, where a raw
 * character would be invisible in the generated file.
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
                      : code < 0x20 || code === 0x7f
                        ? `\\u${code.toString(16).padStart(4, '0')}`
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
 * The helper exists so the non-emptiness proof is discharged by
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
 * **The key arrives rendered**, not as a bare name: an object's keys are `Name`, a `dunion`'s
 * members are assignments, and a `dunion`'s own keys are `Name` again. One caller renders one way
 * and one the other, so this does not have to know which it is serving.
 *
 * The last entry is the `else`, which is total by accident of the type rather than by luck: the
 * subtype's inhabitants are exactly the declared keys, so `fin_cases` in the `vector` tactic
 * reaches the final branch only for the final key.
 */
const leanKeyFunction = (
    entries: readonly (readonly [string, string])[],
): string => {
    if (entries.length === 0) {
        return 'fun k => absurd k.2 (Finset.notMem_empty k.1)'
    }
    const last = entries[entries.length - 1] as readonly [string, string]
    const tests = entries
        .slice(0, -1)
        .map(([name, body]) => `if k.1 = ${name} then ${body} else `)
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
 * A JS `number` is refused here rather than approximated. `Value.num` carries a `WFNumeral`,
 * which is exact, and a JS number is a binary64 float, so writing one down is a rounding the model
 * does not state. A `DynamoNumber` is a numeral, and it emits as `Value.num`.
 */
export const leanValueOf = (value: unknown, at = 'value'): string => {
    if (typeof value === 'string') return `Value.str ${leanString(value)}`
    if (typeof value === 'boolean') return `Value.bool ${value}`
    if (value === null || value === undefined) return 'Value.null'
    if (typeof value === 'number' || typeof value === 'bigint') {
        return refuse(
            at,
            '`Value.num` carries a `WFNumeral`, which is exact, and a JS number is a binary64 float — so writing one down is the rounding this development refused to axiomatize; hand a `DynamoNumber`, which `dynamoNumber` and `decimal` both carry',
        )
    }
    // **the carrier `N` actually has**, and it is emitted before the record row below, which would
    // otherwise read its `digits` field and emit a `Value.map` — a vector that is quietly false
    if (value instanceof DynamoNumber) {
        return `Value.num (${leanNumeral(value.toString())})`
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
        if (first instanceof DynamoNumber) {
            return `Value.numSet (${leanNonEmptySet(
                members.map(
                    (m) => `(${leanNumeral((m as DynamoNumber).toString())})`,
                ),
                at,
            )})`
        }
        if (typeof first === 'number') {
            return refuse(
                at,
                '`Value.numSet` is a set of `WFNumeral`, and a JS number is a binary64 float — hand a set of `DynamoNumber`',
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
                    [
                        leanString(name),
                        leanValueOf(value[name], `${at}.${name}`),
                    ] as const,
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
                            leanString(name),
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
 * `Pred.closure` carries `q : Value → Bool` and this library carries a JavaScript closure, so the
 * general case has no emission and never will. What makes *some* cases emittable is that a closure
 * this library itself exported is not arbitrary: it is a function with a specification, and the
 * model has the same specification under a name. Recognition is by **reference** against the
 * exported function — not by `Function.prototype.toString`, which a minifier or a refactor changes
 * without changing meaning, and which would therefore go on emitting after the correspondence had
 * stopped holding.
 *
 * The inventory is small, and the smallness is the finding rather than an omission: `src/` builds
 * **no** `refine`, `held` or `legacy` internally — every one of the three is a combinator
 * a caller reaches for, and `codec.ts` never reaches for them itself. The only functions this
 * package exports that can stand in a predicate position at all are {@link isNumeral} and
 * {@link isStoredNumeral} (`src/codec/attribute.ts`), which are properties of the `N` carrier rather
 * than of any codec. So the boundary this registry moves is exactly two predicates wide.
 *
 * ── the correspondence, and what checked it ────────────────────────────────────────────────────
 *
 * `isStoredNumeral` ↦ `isStored` and `isNumeral` ↦ the same shape over `Numeral.WF`, which the
 * model spells only at the `.num` carrier (`inD`) and so is written out here. Both were checked
 * against the kernel rather than read across: a corpus of numeral spellings was run through the
 * TypeScript predicates, the verdicts emitted as `Numeral.WF s = b` / `Numeral.Stored s = b` rows,
 * and all of them closed by `rfl`. `inD` is deliberately *not* used for `isNumeral`: it asks only
 * whether a value is an `N`, which is a different predicate on a different carrier.
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
    /** The `Value → Bool` the model names, which the emitter wraps in `Pred.closure`. */
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
 * walk over `member`: a term whose written *attribute* is `S` is not the same as a term whose
 * accepted *value* is a string — `held` is the counterexample, and `opaque` writes whatever it is
 * handed. Recurses through `refine`, because a refinement writes where its inner term does.
 */
const writesOnlyStrings = (t: Term | undefined): boolean => {
    if (!t) return false
    if (t.kind === 'string') return true
    // an adapter answers from its held side: `decimal` hands the caller text, so a refinement
    // outside it tests a string even though the base beneath writes a numeral
    if (t.kind === 'held') return writesOnlyStrings(t.outer)
    // read off the base rather than off the values. `decimal` was the second base writing text
    // and is an adapter over `number` now, so `string` is the only one left
    if (t.kind === 'literal') {
        return t.base === 'string'
    }
    if (t.kind === 'refine') return writesOnlyStrings(t.inner)
    // `string('1', '2')` is a union of literals, and a union writes only strings exactly where
    // every option does
    if (t.kind === 'union')
        return t.options.length > 0 && t.options.every(writesOnlyStrings)
    return false
}

/* ── terms ───────────────────────────────────────────────────────────────────────────────── */

/**
 * The scope of a term printed at the top: its own binders, and no enclosing binder. A thunk that
 * throws names a codec not yet declared, and the printer reports the throw.
 */
const topScope = (t: Term): Scope => ({
    binds: bindersOf(t),
    inside: [],
})

/**
 * **The caller's functions that a quantified vector binds.** A caller closure has no expression in
 * the model, so the theorem binds one variable for each, and the claim holds at every function.
 * A caller adapter is a generator `caller n`, and the theorem quantifies its pair through the
 * caller table. Keyed by the function, so one function is one variable or one generator wherever
 * the pair uses it. `Value` holds each value that a caller function receives, except a JS float,
 * so an adapter this library ships over a float is still refused.
 */
type Bound = {
    readonly closures: Map<unknown, string>
    readonly adapters: Map<unknown, string>
    /** The older reader of each `legacy`, a variable of the theorem, keyed by the function. */
    readonly readers: Map<unknown, string>
}

/** A scope, and the functions that the theorem binds where the vector is quantified. */
type At = Scope & { readonly bound?: Bound }

/** The variable of one caller function, made on the first use. */
const boundName = (
    names: Map<unknown, string>,
    fn: unknown,
    prefix: string,
): string => {
    const known = names.get(fn)
    if (known !== undefined) return known
    const made = `${prefix}${names.size}`
    names.set(fn, made)
    return made
}

/**
 * **The generator of one caller adapter**, made on the first use. The key is the term's caller-side
 * function, which `held` builds once for each adapter, so one adapter is one generator wherever the
 * pair uses it. The theorem quantifies the pair of each generator through the caller table.
 */
const callerOf = (generators: Map<unknown, string>, fn: unknown): string => {
    const known = generators.get(fn)
    if (known !== undefined) return known
    const made = `${generators.size}`
    generators.set(fn, made)
    return made
}

/** The binders of a quantified theorem, or nothing where the vector binds no function. */
const leanBinders = (bound: Bound): string => {
    const group = (names: Map<unknown, string>, type: string): string[] =>
        names.size === 0 ? [] : [`(${[...names.values()].join(' ')} : ${type})`]
    return [
        ...group(bound.closures, 'Value → Bool'),
        ...group(bound.readers, 'Attr → Option Value'),
    ].join(' ')
}

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
 * - **`number` and a numeric `literal` are *not* here.** `Term.number` is a closed term, and a
 *   numeric alternative is `WFNumeral.of`, so both emit. A JS number *value* is what has no
 *   exact image, and `leanValueOf` refuses it, so the refusal is reported where it lives.
 * - **`held`, `legacy`.** This library carries JavaScript closures in both. The model's `held`
 *   carries an adapter word, and a table gives the word its pair `f g : Value → Value`. So a
 *   caller's adapter prints as a generator `caller n` inside a quantified verdict, and the
 *   emitter refuses a caller's adapter elsewhere. The model's `legacy` carries
 *   `r : Attr → Option Value`, and there is no expression in Lean for an arbitrary closure.
 *   `legacy` used to be the worse of the two for a second reason, and is not any more:
 *   the definition dropped the older readers entirely, so there was nothing to be refused about.
 *   It carries `older` now, and the refusal below names it.
 * - **`refine`, unless the predicate is one this library shipped.** The third
 *   function-carrying constructor, and the one where the line has moved. See
 *   {@link ShippedPredicate}: `isNumeral` and `isStoredNumeral` are recognised by reference and
 *   emitted as the model's own predicates, and everything else is still refused, by name. The
 *   boundary is no longer "all refinements" but "refinements this library did not build", which is
 *   the honest line — and it is only two predicates wide, because `src/` constructs none of these
 *   three internally. A declaration verdict passes a {@link Bound}, and there a caller's closure
 *   prints as a variable that the theorem binds, and a caller's adapter prints as a generator
 *   `caller n` whose pair the theorem quantifies through the caller table.
 * - **A thunk that throws is not here.** It names a codec not yet declared, and it prints as a
 *   variable that no binder of the term binds, as the host's disjointness test reads it. The
 *   host's guard reads the same thunk as the root of the term, and {@link leanRooted} spells that
 *   second reading.
 *
 * `Rest.drop` vs `Rest.refuse` used to be a fourth entry here: `Def` recorded the rest *codec*
 * and nothing when the policy was a string, so this wrote `Rest.drop` for either. It was sound for
 * the vectors this module writes and only for them — `objectCodec`'s `e` is `objWrite`, which takes
 * `rc?` and not the `kn` filter, and `rcOf` is `none` for both policies, so the two denote the
 * same `e` and differ only under `p`. A decode-direction
 * vector would have needed them apart and would have been silently wrong. The `attributes` term
 * carries the policy now rather than only its codec, and this emits all three.
 */
export const leanTermOf = (
    declared: ObjectSlot,
    at = 'codec',
    bound?: Bound,
): string => {
    // the entry takes a declaration and the printer below takes a term, so the refusal has a place
    // to live and stays reachable. A codec's definition is a term in the type, and the caller this
    // is for is the one that arrived past a cast — `termOf` draws the same line for the same reason
    const def = declared.def
    if ('mark' in def) {
        return refuse(
            at,
            'a §4 *field*, not a term — `optional`/`fallback` denote `Field`, and no `Term` position accepts one',
        )
    }
    return leanTermOfTerm(def, at, { ...topScope(def), bound })
}

/**
 * A literal's base and alternatives, as the two arguments `Term.literal` and `inL` both take.
 *
 * Factored out because `inL k ls` is those two arguments and nothing else — the model writes the
 * membership predicate over exactly the pair the term carries, which is what makes a `members`
 * predicate printable where a closure never will be.
 */
const leanAlternative = (base: Literal['base'], one: unknown): string => {
    // **A numeric literal is emittable, and it was not.** `GroundKind.number` carried an axiom
    // with no closed terms, so no alternative at it could be written down. It carries
    // `WFNumeral` now, which is a numeral text with its own well-formedness proof, and
    // `WFNumeral.of` discharges that proof by `decide` at elaboration.
    if (base === 'number') {
        return `(WFNumeral.of ${leanString(String(one))})`
    }
    return base === 'boolean'
        ? String(one)
        : base === 'binary'
          ? leanBytes(one as Uint8Array)
          : leanString(one as string)
}

/** One literal, as the base and the one inhabitant of its carrier. */
const leanLiteral = (literal: Literal): string =>
    `GroundKind.${literal.base} ${leanAlternative(literal.base, literal.v)}`

/**
 * …and a set of alternatives, which `Pred.members` still carries.
 *
 * `Pred.members` is a refinement predicate over a `NEFinset`, so this keeps the wire-set spelling
 * a literal gave up. `string.set('a', 'b')` is where it is reached.
 */
const leanGround = (alts: Alternatives, at: string): string => {
    const base = alts.base
    // an annotation rather than a cast: widening to the union's supertype is something
    // the checker can do on its own, and `as` here would only hide it doing so
    const alternatives: readonly LiteralValue[] = alts.ls
    return `GroundKind.${base} (${leanNonEmptySet(
        [...new Set(alternatives)].map((one) => leanAlternative(base, one)),
        at,
    )})`
}

/**
 * §3 `(refine)`'s predicate, as the model's `Pred`.
 *
 * **The two sides are one shape now.** {@link Predicate} is `members | closure`, and
 * `Calculus.Pred` has those two constructors and `except`, which the host does not spell. So this
 * is a rename and not a translation: `members` to `Pred.members`, a recognised closure to
 * `Pred.closure`. `Pred.eval` is where the meaning lives in the model, and this prints the data.
 *
 * Every case comes back parenthesised, because each is an application and `Term.refine` takes its
 * second argument juxtaposed. That includes the recognised closures, which used to come back bare
 * because they were identifiers and are now wrapped.
 *
 * The third case has no data and never will. A `closure` is a caller's JavaScript function; the
 * registry below recognises two of them **by reference**, and everything else is refused. That is
 * the case `Pred` keeps rather than removes: `refine` still carries an arbitrary predicate.
 */
const leanPredicate = (q: Predicate, at: string, bound?: Bound): string => {
    switch (q.kind) {
        case 'members':
            return `(Pred.members ${leanGround(q.literal, at)})`
        case 'closure': {
            // recognised by reference against the function this package exported, so a rename or a
            // reimplementation of the predicate is a type error here rather than a silent misemission
            const known = shippedPredicates.get(q.q.is)
            // a caller's closure in a quantified vector is a variable of the theorem
            if (!known && bound)
                return `(Pred.closure ${boundName(bound.closures, q.q.is, 'q')})`
            if (!known) {
                return refuse(
                    at,
                    `\`Pred.closure\` carries \`q : Value → Bool\`, and this predicate is not one this library ships — it is the caller's closure for ${JSON.stringify(q.q.what)}. The recognised ones are \`isNumeral\` and \`isStoredNumeral\` from \`src/codec/attribute.ts\`, passed by reference`,
                )
            }
            return `(Pred.closure ${known.lean})`
        }
    }
}

/**
 * §4's object payload, as the model's `Body.mk`.
 *
 * One row prints it: an object's payload. It used to be two, the second being each variant of a
 * tagged union — and there is one sum now, so a member of a dissection is an `object` term like
 * any other union option and prints through the row above.
 */
const leanBodyOf = (body: Body, at: string, scope: At): string => {
    const declared = Object.entries(body.fields)
    const names = declared.map(([name]) => name)
    const fields = leanKeyFunction(
        declared.map(
            ([name, field]) =>
                [
                    leanString(name),
                    leanSlotOf(field, `${at}.${name}`, scope),
                ] as const,
        ),
    )
    /**
     * **The open block, as an `Option` on both sides.** A body is a partition of the key space,
     * so a name is declared, or it falls in the one open block, or the body refuses it. The
     * closed body is the *absence* of an open block, and the open block is the term every
     * undeclared name holds.
     */
    const rest = body.rest
    const restTerm =
        rest === undefined
            ? 'none'
            : `(some (${leanTermOfTerm(rest, `${at}.rest`, scope)}))`
    return `(Body.mk ${leanFinset(names)} (${fields}) ${restTerm})`
}

/**
 * **The guard's reading of a term**: a thunk that throws is the variable of a root `Term.mu`.
 *
 * A thunk that throws is an unknown term, and each host check takes its worst case. The
 * disjointness and compatibility tests read the open term, where the thunk is a variable that no
 * binder binds. The guard reads the thunk as a path to the root of the option, because at a
 * declaration such a thunk throws as a thunk that names the codec under declaration does.
 * {@link leanTermOf} prints that variable one binder beyond each enclosing binder, so one `Term.mu`
 * around the whole term binds it to the root. A term with no such thunk has no root binder.
 */
export const leanRooted = (printed: string, declared: AnyCodec): string =>
    readsFreeVariable(declared.def) ? `Term.mu (${printed})` : printed

const leanTermOfTerm = (t: Term, at: string, scope: At): string =>
    scope.binds.has(t) && !scope.inside.includes(t)
        ? `Term.mu (${leanTermCore(t, at, { ...scope, inside: [...scope.inside, t] })})`
        : leanTermCore(t, at, scope)

const leanTermCore = (t: Term, at: string, scope: At): string => {
    switch (t.kind) {
        case 'string':
            return 'Term.string'
        case 'boolean':
            return 'Term.boolean'
        case 'binary':
            return 'Term.binary'
        case 'null':
            return 'Term.null'
        /**
         * **Emittable, and it took refusal vectors to see that.** `Term.number` is a closed term.
         * A `Value.num` is a closed term too, over a `WFNumeral`. What {@link leanValueOf} refuses
         * is a JS number, which is a float, and this row used to refuse on its behalf one level
         * too early.
         */
        case 'number':
            return 'Term.number'
        case 'literal':
            return `Term.literal ${leanLiteral(t)}`
        /** `Term.set` takes its element term, as the host term does. */
        case 'set':
            return `Term.set (${leanTermOfTerm(t.elem, `${at}.elem`, scope)})`
        /**
         * **The builder where the shape is one, the constructor where it is not.**
         *
         * `Term.array` and `Term.tuple` are definitions over `Term.list` in `Term.lean`, kept so
         * that a statement about either shape reads as it always did. A shape either builder can
         * spell is printed through that builder, so the vectors keep their spelling and the
         * committed samples stay the file they were. Only a suffix, which neither builder can
         * spell, prints the constructor.
         */
        case 'list': {
            const positions = (
                ts: readonly Term[],
                part: (index: number) => string,
            ) =>
                ts
                    .map((element, index) =>
                        leanTermOfTerm(element, part(index), scope),
                    )
                    .join(', ')
            const spread = t.spread
            if (t.suf.length === 0) {
                if (t.pre.length === 0 && spread)
                    return `Term.array (${leanTermOfTerm(spread, `${at}.element`, scope)})`
                const tail = spread
                    ? `(some (${leanTermOfTerm(spread, `${at}.tail`, scope)}))`
                    : 'none'
                return `Term.tuple [${positions(t.pre, (index) => `${at}[${index}]`)}] ${tail}`
            }
            const middle = spread
                ? `(some (${leanTermOfTerm(spread, `${at}.spread`, scope)}))`
                : 'none'
            return `Term.list [${positions(t.pre, (index) => `${at}[${index}]`)}] ${middle} [${positions(t.suf, (index) => `${at}.suffix[${index}]`)}]`
        }
        case 'object': {
            // **One argument, a `Body`.** `db444e3` made the object payload a stratum, so
            // `Term.object` takes `Body.mk names fields rest` where it used to take the three
            // separately — and this row kept emitting the three, which typechecked against no
            // `Calculus/` after that commit. Nothing caught it for a day: the committed samples
            // are generated *by this function*, so `lean.spec.ts`'s byte comparison agreed with a
            // stale emitter, and no gate ran a generated file through Lean. Both are fixed; see
            // `docs/architecture.md`, where the emitter is a companion every stratum owes.
            //
            // A `dunion`'s variants are `Body`s too, so the payload is emitted by
            // {@link leanBodyOf} and both rows print the same thing.
            return `Term.object ${leanBodyOf(t.body, at, scope)}`
        }
        case 'never':
            return 'Term.never'
        case 'union':
            return `Term.union [${t.options
                .map((variant, index) =>
                    leanTermOfTerm(variant, `${at}[${index}]`, scope),
                )
                .join(', ')}]`
        // The model's `opaq` is the exact codec: its number option is `numberCodec`, so it is this
        // total term. The two policies are `held` over this term, and the `held` row refuses them
        case 'opaq':
            return 'Term.opaq'
        // a thunk that returns a term being printed closes a cycle, and prints the variable of
        // that term's binder; any other thunk prints the term it returns. A thunk that throws
        // names a codec not yet declared, and prints a variable that no binder of the term binds
        case 'lazy': {
            const target = force(t)
            if (target === undefined) return `Term.var ${scope.inside.length}`
            const k = scope.inside.lastIndexOf(target)
            return k === -1
                ? leanTermOfTerm(target, `${at}.inner`, scope)
                : `Term.var ${scope.inside.length - 1 - k}`
        }
        /**
         * §3 `(refine)`. The predicate is printed by {@link leanPredicate}, and the side condition
         * below applies to a **shipped closure** only. A caller's closure in a quantified vector
         * is a variable, and the claim holds at every function, so no coercion can part the two.
         *
         * `writesOnlyStrings` exists because the two shipped predicates take a `string` and a
         * `Value → Bool` takes anything: they disagree where JavaScript coerces, so the emission is
         * confined to inner terms that write nowhere else. `members` is a `Pred`
         * constructor over data the term carries, and `Pred.eval` sends it to the model's own
         * `inL`, so the two agree at every value by construction and the gate has nothing
         * to say about them.
         */
        case 'refine': {
            const q = leanPredicate(t.q, at, scope.bound)
            if (
                t.q.kind === 'closure' &&
                shippedPredicates.has(t.q.q.is) &&
                !writesOnlyStrings(t.inner)
            ) {
                return refuse(
                    at,
                    `${shippedPredicates.get(t.q.q.is)?.what ?? 'this predicate'} decides a *string*, and this refinement's inner term writes values that are not strings — where JavaScript would coerce and the model would not, so the two predicates would part company`,
                )
            }
            // the stored predicate is the top of the store universe: the truth, which is `()`
            return `Term.refine (${leanTermOfTerm(t.inner, `${at}.inner`, scope)}) ${q} ()`
        }
        /**
         * **An adapter this library ships is printed by name**, the way a recognised predicate
         * is. `decimal` is `number` under the text adapter now, so refusing every `held` would
         * take every decimal vector with it.
         *
         * A caller's pair prints a generator `caller n` of a quantified vector, and is refused
         * elsewhere.
         * The float adapter is refused everywhere, for a reason that is not about closures:
         * `Value` carries no float, so the conversion would be numeral to numeral and its content
         * is binary64 rounding. That is the host axiom this development deleted.
         *
         * A `held` is an adapter at one absolute side. The store names no generator, so each
         * `held` is at the caller side `false`, with a non-empty word. The stored side has no
         * `held`, so the term prints no stored outer and no stored word.
         */
        case 'held':
            if (t.via === undefined && scope.bound)
                return `(Term.held false (${leanTermOfTerm(t.inner, at, scope)}) (${leanTermOfTerm(t.outer, at, scope)}) (.caller ${callerOf(scope.bound.adapters, t.f)}, false) [])`
            return t.via === 'decimalText'
                ? `(Term.held false (${leanTermOfTerm(t.inner, at, scope)}) (${leanTermOfTerm(t.outer, at, scope)}) (.decimalText, false) [])`
                : refuse(
                      at,
                      "`Term.held` carries a word of adapter generators, and a table gives each generator two `Value → Value` functions. The library ships one generator the model names, `decimalText`, whose pair is `numeralOfStoredText`/`textOfNumeral`, and this is not it — a caller's closure has no name in the model, and the adapter carrying a JS float has none either, because writing binary64 rounding down is the host axiom this development deleted",
                  )
        // the older reader is caller code: a quantified verdict binds it as a variable, and an
        // evaluation vector would have to run it
        case 'legacy':
            return scope.bound
                ? `(Term.legacy (${leanTermOfTerm(t.inner, at, scope)}) ${boundName(scope.bound.readers, t.r, 'r')})`
                : refuse(
                      at,
                      '`Term.legacy` carries `r : Attr → Option Value`, a JS closure: a quantified verdict binds it as a variable, and no evaluation vector prints one',
                  )
    }
}

/**
 * An `ObjectSlot` — §4's stratum, which is a *position* in a map and not a codec.
 *
 * **The slot has three constructors.** A name is required, optional, or filled: a fill is required
 * on the write and reads an absent name as its stand-in. The presence lattice reads the rest.
 */
const leanSlotOf = (field: TermField, at: string, scope: At): string => {
    switch (field.mark) {
        case 'optional':
            return `ObjectSlot.optional (${leanTermOfTerm(field.t, at, scope)})`
        /**
         * `ObjectSlot.fill`: the stand-in is data, so it prints as a `Value`. An older reader of a
         * present value stays in the term, as `Term.legacy`.
         */
        case 'fallback':
            return `ObjectSlot.fill (${leanTermOfTerm(field.t, at, scope)}) (${leanValueOf(field.v, at)})`
        case 'req':
            return `ObjectSlot.req (${leanTermOfTerm(field.t, at, scope)})`
        /**
         * `ObjectSlot.optional`, because that is what it denotes rather than an approximation of
         * it.
         *
         * `Value` has no `undefined` and `Value.map` is a key set with a total function on it, so
         * `{ k: undefined }` and `{}` are one `Value` and there is no second thing to mean. The
         * quotient that rests on is {@link leanValueOf}'s, which was already there for `optional`.
         */
        case 'undefinable':
            return `ObjectSlot.optional (${leanTermOfTerm(field.t, at, scope)})`
    }
}

/* ── vectors ─────────────────────────────────────────────────────────────────────────────── */

/**
 * How a vector states its claim to the kernel.
 *
 * `'check'` writes `check n ((denote t).e v) (some a) = .same := rfl` and is the default. It
 * depends on `Calculus/Bridge/Vectors.lean` — a fuelled three-valued comparator with `check_same` and
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
    // a recursive term the library wrote through is a term the guard accepts
    const guard = term.includes('Term.mu')
        ? `\n\n${leanGuard({ name: `${name}__guarded`, codec, guarded: true })}`
        : ''
    const vector =
        protocol === 'equation'
            ? [
                  ...head,
                  `    (denote (libTable noCallers) (${term})).e`,
                  `      (${leanValueOf(value, name)})`,
                  `    = some (${leanAttrOf(attribute, name)}) := by`,
                  '  vector',
              ].join('\n')
            : [
                  ...head,
                  `    check ${fuelFor(attribute)}`,
                  `      ((denote (libTable noCallers) (${term})).e`,
                  `        (${leanValueOf(value, name)}))`,
                  `      (some (${leanAttrOf(attribute, name)})) = .same := rfl`,
              ].join('\n')
    return `${vector}${guard}`
}

/**
 * **A guard verdict**: whether the model's `Alg.Term.guarded` accepts the term of a codec. A recursive
 * schema below a list or an object is guarded. A thunk that returns its own term reads the
 * binder's input itself, and the guard refuses it: the stages of such a term never grow.
 */
export type Guard = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly guarded: boolean
}

/** One guard verdict, as a Lean `theorem` closed by `rfl`. */
export const leanGuard = ({ name, codec, guarded }: Guard): string =>
    [
        `/-- \`${name}\` — the model's guard ${guarded ? 'accepts' : 'refuses'} this term -/`,
        `theorem ${leanIdent(name)} :`,
        `    Alg.Term.guarded (${leanTermOf(codec, name)}) = ${guarded} := rfl`,
    ].join('\n')

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
 * **And it reaches `number`**: `Term.number` is a closed term, so
 * `(denote Term.number).e (Value.str "x") = none` is `rfl`. A numeric `literal` is closed too, its
 * alternatives being `WFNumeral`s.
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
    if (accepts(codec, value)) {
        throw new LeanUnemittable(
            name,
            'this codec admits this value, so a refusal vector about it would assert the model refuses what `src/` writes — pass it as a `Vector` instead',
        )
    }
    return [
        `/-- \`${name}\` — refused on both sides -/`,
        `theorem ${leanIdent(name)} :`,
        `    (denote (libTable noCallers) (${leanTermOf(codec, name)})).e`,
        `      (${leanValueOf(value, name)}) = none := rfl`,
    ].join('\n')
}

/**
 * One **declaration verdict**: what `src/`'s `union` does with this pair, and what the model says.
 *
 * **The bridge runs both ways, because the two host defects of the certificate lived in the
 * direction that the one-way bridge did not check.**
 *
 * - `src/` **accepts** the pair: the model's guard accepts both options, on the terms that
 *   {@link leanRooted} spells, and the model proves `PairwiseCompat` for the pair, given lawful
 *   options. Where {@link agrees} holds, the host decided the model's `compatPair`, and the proof
 *   is `pairwiseCompat_of_compatPair` over that decision. A host warrant that the model does not
 *   prove stops the file.
 * - `src/` **refuses** the pair: the model's decision must refuse it too, `compatPair dynOracle x
 *   y = false`. A decision that starts to accept a pair `src/` turns down stops the file.
 * - `src/` **refuses** the pair **at the guard**: an option reads the input of its own binder, or
 *   holds an adapter on a recursive path. The model's guard must refuse an option too, on the
 *   terms that {@link leanRooted} spells.
 *
 * Compatibility is not decidable, so a refused pair carries no theorem that it is incompatible:
 * `not_compat_flip` and `not_compat_shout` are the model's witnesses of that class.
 */
export type Separation = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly left: AnyCodec
    readonly right: AnyCodec
}

/** One declaration verdict, as a Lean `theorem`, with the `src/` side decided here. */
export const leanSeparation = ({ name, left, right }: Separation): string => {
    let refused = false
    try {
        union([left, right] as never)
    } catch {
        refused = true
    }
    // a caller's function is a variable of the theorem, and the kernel's `decide` refuses a goal
    // with a free variable, so a quantified verdict reduces by `rfl`
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const l = leanTermOf(left, name, bound)
    const r = leanTermOf(right, name, bound)
    const binders = leanBinders(bound)
    const head = `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`
    // the term \`rfl\` exhausts the default heartbeats on a refusal of two terms of about 600
    // characters, where the tactic \`rfl\` closes the goal
    const reduce = binders === '' ? 'by decide' : 'by rfl'
    // a free variable names a codec not yet declared, which the host reads as unknown and a closed
    // denotation reads as the bottom, so the verdict states the decision at an unknown environment
    const decision =
        readsFreeVariable(left.def) || readsFreeVariable(right.def)
            ? (half: boolean) =>
                  `Alg.Term.compat dynOracle ${half} pair0 false false (${l})\n        (${r})`
            : undefined
    // the host's guard runs before its compatibility test, and reads each option on its own
    const guardRefuses = [left, right].some(
        (option) => recursionUse(option.def) >= 2,
    )
    if (refused && guardRefuses) {
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair at the guard; the model's guard refuses it too -/`,
            head,
            `    (Alg.Term.guarded (${leanRooted(l, left)}) &&`,
            `      Alg.Term.guarded (${leanRooted(r, right)})) = false := ${reduce}`,
        ].join('\n')
    }
    if (refused) {
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair; the model's decision refuses it too -/`,
            head,
            ...(decision === undefined
                ? [
                      `    Alg.compatPair dynOracle (${l})`,
                      `      (${r}) = false := ${reduce}`,
                  ]
                : [
                      `    (${decision(true)} &&`,
                      `      ${decision(false)}) = false := ${reduce}`,
                  ]),
        ].join('\n')
    }
    const warrant = agrees(left.def, right.def)
        ? `fun hl => pairwiseCompat_of_compatPair (${reduce}) hl`
        : refuse(
              name,
              '`src/` accepts this pair on no warrant that the model proves: the decision refuses it',
          )
    // the host's union verdict is the guard and the compatibility test, so the vector states both
    return [
        `/-- \`${name}\` — \`src/\` accepts this pair; the model's guard accepts it, and the model proves it compatible -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} (κ : Callers) :`,
        `    (Alg.Term.guarded (${leanRooted(l, left)}) &&`,
        `      Alg.Term.guarded (${leanRooted(r, right)})) = true ∧`,
        `    ((∀ t ∈ [${l}, ${r}], Lawful (denote (libTable κ) t)) →`,
        `      PairwiseCompat (libTable κ) [${l}, ${r}]) :=`,
        `  ⟨${reduce}, ${warrant}⟩`,
    ].join('\n')
}

/**
 * The declaration verdicts as a module of their own, because they need the decision `compatPair`
 * and the dischargers of `PairwiseCompat`.
 *
 * The header imports `Calculus.Dynamo.Lang.Store` as well, because a verdict spells
 * `libTable` and `Callers`, which the DynamoDB port defines, and
 * `Meet` does not reach them. Lean
 * auto-binds an unknown lower-case name, so the missing import reports a free variable in the
 * expected type of every verdict rather than an unknown identifier.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanSeparationModule = (
    separations: readonly Separation[],
): string =>
    `import Calculus.Dynamo.Analysis.Meet
import Calculus.Dynamo.Analysis.Compat
import Calculus.Dynamo.Lang.Store

/-!
# Declaration verdicts, both ways

**Generated — do not edit.** One theorem per option pair of the corpus. A pair \`src/\`'s \`union\`
accepts carries the model's proof that the pair is compatible, through the warrant the host used.
A pair \`src/\` refuses carries \`compatPair dynOracle x y = false\`: the model's decision refuses
it too.
See \`src/codec/lean.ts\`'s \`Separation\`.
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false
/-! A quantified verdict binds a caller's function, so \`decide\` refuses it and the elaborator
reduces \`Term.guarded\` by \`whnf\`. On a term with a binder and an object, that reduction needs
more than the default 200000 heartbeats. -/
set_option maxHeartbeats 1000000

namespace Calculus

${separations.map(leanSeparation).join('\n\n')}

end Calculus
`

/**
 * One proposed **read verdict**: this codec, given this attribute, decodes exactly when the
 * model's read row admits it.
 *
 * **The differential that replaced a port.** HANDOFF's fourth item was to give the resolver's
 * read side a decision through a port of `AdmA`, in the style the deleted reader ported `Adm`.
 * Measured
 * first: over 864 (codec, attribute) pairs the two agree at **861 of 861 checkable** ones and
 * disagree at none. `decode` validates — it parses data somebody else wrote, which is its job —
 * where `encode` trusted its argument's *type*, and that asymmetry is the whole reason wiring
 * `admits` into the write side changed real answers and a read-side port would change none. So a
 * def-reading port would be a second description of what `decode` already computes exactly, and
 * two descriptions of one thing need a guard between them. **The guard is what landed.**
 *
 * `#eval` runs `AdmA`, but a printed verdict proves nothing. The kernel unfolds it, which is the
 * fact `Vectors.lean` opens with, so the verdict is asserted and elaboration is the test.
 */
export type ReadVerdict = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly attribute: AttributeValue
}

/**
 * A pair of corpus terms, put to the model's disjointness test with the answers `src/` computes.
 *
 * The separations bridge checks the host's verdict on a union. This one checks the test itself,
 * both ways, at every pair: `Calculus.Alg.Term.disjoint` and {@link disjoint} are the *same
 * function* stated twice, so a disagreement in either direction is a defect on one side. The test
 * of the raw terms and the test of the two pairs of views are asserted apart, because the
 * certificate reads the views and a raw `held` is disjoint from the bottom alone.
 */
export type DisjointPair = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly left: AnyCodec
    readonly right: AnyCodec
}

/**
 * One pair, as a Lean `theorem`: the two terms, and the two answers this library gives.
 *
 * `false` is asserted as much as `true` is. `false` states nothing about the pair, but a port
 * that certified a pair the model declines would fail here on that pair.
 */
export const leanDisjoint = ({ name, left, right }: DisjointPair): string => {
    const one = left.def
    const other = right.def
    if ('mark' in one || 'mark' in other) {
        throw new LeanUnemittable(
            name,
            'a §4 *field*, not a term — no `Term` position accepts one, so the test has no pair to state',
        )
    }
    const views = viewsDisjoint(one, other)
    // a caller's function is a variable of the theorem, and the kernel's `decide` refuses a goal
    // with a free variable, so a quantified pair reduces by `rfl`
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const l = leanTermOf(left, name, bound)
    const r = leanTermOf(right, name, bound)
    const binders = leanBinders(bound)
    return [
        `/-- \`${name}\` — the answers \`src/\` computes, put to the model -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        `    Alg.Term.disjoint pair0 (${l})`,
        `        (${r}) = ${disjoint(one, other)} ∧`,
        `      viewsDisjoint (${l})`,
        `        (${r}) = ${views} := ${binders === '' ? 'by decide' : '⟨rfl, rfl⟩'}`,
    ].join('\n')
}

/**
 * The disjointness pairs as a module of their own.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanDisjointModule = (pairs: readonly DisjointPair[]): string =>
    `import Calculus.Dynamo.Analysis.Meet
import Calculus.Dynamo.Lang.Store

/-!
# Disjointness, proposed to the model

**Generated — do not edit.** One theorem per pair of corpus terms, asserting that
\`Calculus.Alg.Term.disjoint\` answers what \`src/\`'s \`disjoint\` answered on the two terms, and
that \`Calculus.viewsDisjoint\` answers what \`src/\`'s \`viewsDisjoint\` answered on the two pairs of
views. The two sides are one function written twice, so this runs in both directions.
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

namespace Calculus

${pairs.map(leanDisjoint).join('\n\n')}

end Calculus
`

/** One read verdict, as a Lean `theorem`; `src/`'s answer is taken by running `decode`. */
export const leanReadVerdict = (one: ReadVerdict): string => {
    const { name, codec, attribute } = one
    const decodes = readsBack(codec, attribute)
    return [
        `/-- \`${name}\` — \`src/\` ${decodes ? 'decodes' : 'refuses'} this attribute -/`,
        `theorem ${leanIdent(name)} :`,
        `    AdmA (libTable noCallers) (${leanTermOf(codec, name)})`,
        `      (${leanAttrOf(attribute, name)}) = ${decodes} := rfl`,
    ].join('\n')
}

/**
 * The read verdicts as a module of their own, because they need `AdmA`.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanReadModule = (verdicts: readonly ReadVerdict[]): string =>
    `import Calculus.Dynamo.Analysis.ExactA
import Calculus.Dynamo.Lang.Store

/-!
# Read verdicts, proposed to the model's read row

**Generated — do not edit.** One theorem per (codec, attribute) pair: \`AdmA t a\` equals whether
\`src/\`'s \`decode\` accepted it. All ${verdicts.length} pairs are asserted here.
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

namespace Calculus

${verdicts.map(leanReadVerdict).join('\n\n')}

end Calculus
`

/**
 * One **read vector**: this codec, given the attribute it wrote, reads that value back.
 *
 * The write vectors assert `(denote t).e v = some a` and the refusal vectors assert `= none`, so
 * one half of every pair was proposed to the model and the other half was not — for the corpus at
 * large. The read side *was* asserted, but only where a union had to choose:
 * {@link leanReadResolution} states `(denote t).p a = some v` for each read resolution. This is
 * that assertion over every corpus codec rather than over the unions alone.
 *
 * **The attribute comes from the library and so does the value.** `a` is what this codec's
 * `encode` wrote for `v`, and `v'` is what its own `decode` read back from `a` — both taken by
 * running them, never supplied. So the theorem says: the model's `p`, given what this library
 * wrote, answers what this library read. A change to either half stops the file compiling.
 *
 * **`vcheck`, for the reason the read resolutions use it.** A `Value.map` carries a function, so
 * `rfl` on the assembled closure does not close and `isDefEq` runs to the heartbeat limit.
 * `veq` is `aeq`'s construction over `Value.map`, with `veq_sound` proved, so a `.same` verdict
 * cashes to the equation.
 *
 * A codec that cannot read back its own attribute is skipped by {@link readVectorIsUnstatable}. A
 * value the emitter cannot spell is not skipped: {@link leanValueOf} throws, and the emission
 * fails where the reason is.
 */
export const leanReadVector = ({ name, codec, value }: Vector): string => {
    const attribute = codec.unsafeEncode(value as never)
    const out = codec.decode(attribute as never)
    if (failed(out)) {
        return refuse(
            name,
            'this codec cannot read back the attribute its own `encode` wrote, so there is no agreement to propose — `readVectorIsUnstatable` filters it, and reaching here means the filter and the emitter disagree',
        )
    }
    const read = out
    return [
        `/-- \`${name}\` — read back through the term that wrote it -/`,
        `theorem ${leanIdent(name)}__reads :`,
        `    vcheck ${fuelForValue(read)}`,
        `      ((denote (libTable noCallers) (${leanTermOf(codec, name)})).p`,
        `        (${leanAttrOf(attribute, name)}))`,
        `      (some (${leanValueOf(read, name)})) = .same := rfl`,
    ].join('\n')
}

/**
 * Whether a read vector **cannot be stated**, and the one reason it can be.
 *
 * A codec that refuses its own encode, or that cannot read its own attribute back, is not a read
 * vector: there is no agreement to propose if nothing round trips. The value read back needs a
 * Lean form too, and {@link leanValueOf} throws where it has none, so that failure is loud.
 */
export const readVectorIsUnstatable = (
    one: Vector,
): 'no round trip' | undefined => {
    try {
        const attribute = one.codec.unsafeEncode(one.value as never)
        const out = one.codec.decode(attribute as never)
        return failed(out) ? 'no round trip' : undefined
    } catch {
        return 'no round trip'
    }
}

/**
 * The read vectors as a module, with what it could not state named in the header.
 *
 * The header imports `Calculus.Dynamo.Lang.Store` as well, because a vector spells
 * `libTable` and `noCallers`, which the DynamoDB port defines, and `Vectors`
 * does not reach them. Lean auto-binds
 * an unknown lower-case name, so the missing import leaves `denote` stuck on a free variable and
 * each vector reports a failed definitional equality rather than an unknown identifier.
 */
export const leanReadVectorModule = (vectors: readonly Vector[]): string => {
    const blocked = vectors
        .map((one) => [one, readVectorIsUnstatable(one)] as const)
        .filter(([, why]) => why !== undefined)
    const live = vectors.filter(
        (one) => readVectorIsUnstatable(one) === undefined,
    )
    return `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store

/-!
# Read vectors, proposed to the model's \`p\`

**Generated — do not edit.** One theorem per corpus codec: the model's \`p\`, given the attribute
this library wrote, answers the value this library read back. ${live.length} of ${vectors.length}
codecs are asserted here.

Both halves are taken by running the library, never supplied: \`a\` is what \`encode\` wrote and
\`v\` is what \`decode\` read from it. So a change to either direction stops this file compiling,
which is the half the write vectors could not reach.
${
    blocked.length === 0
        ? '\nNothing is skipped: every corpus codec round trips to a value Lean can spell.\n'
        : `\nThe other ${blocked.length} cannot be stated:\n${blocked
              .map(([one, why]) => `  * \`${one.name}\` — ${why}`)
              .join('\n')}\n`
}-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

namespace Calculus

${live.map(leanReadVector).join('\n\n')}

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
 * side's answer is a `Value`, and `Value.map` carries a function, so it uses `vcheck`, the `Value`
 * twin that `Vectors.lean` states as `veq`.
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
              `      ((denote (libTable noCallers) (${term})).e`,
              `        (${leanValueOf(value, name)}))`,
              `      (some (${leanAttrOf(written as AttributeValue, name)})) = .same := rfl`,
          ].join('\n')
        : [
              ...head,
              `    (denote (libTable noCallers) (${term})).e`,
              `      (${leanValueOf(value, name)}) = none := rfl`,
          ].join('\n')
}

/** One read-side resolution, addressed by the attribute rather than the value. */
export type ReadResolution = {
    readonly name: string
    readonly union: AnyCodec
    readonly attribute: AttributeValue
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
              `      ((denote (libTable noCallers) (${leanTermOf(u, name)})).p`,
              `        (${leanAttrOf(attribute, name)}))`,
              `      (some (${leanValueOf(read, name)})) = .same := rfl`,
          ].join('\n')
        : [
              ...head,
              `    (denote (libTable noCallers) (${leanTermOf(u, name)})).p`,
              `      (${leanAttrOf(attribute, name)}) = none := rfl`,
          ].join('\n')
}

/**
 * The resolutions as a module of their own.
 *
 * Generated at gate time and elaborated, never committed — the counts are in
 * `docs/architecture.md`, beside the classifier this is the other half of.
 */
export const leanResolutionModule = (
    writes: readonly Resolution[],
    reads: readonly ReadResolution[],
): string =>
    `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store

/-!
# Union resolution, model against library

**Generated — do not edit.** One theorem per (union, value) and (union, attribute) pair: the
option the model's \`select\` resolves to, against the one this library's resolver picked.
${writes.length} on the write side, ${reads.length} on the read side.

A map-valued read is stated like the others: it goes through \`vcheck\`, the \`Value\` twin of
\`check\`, because \`Value.map\` carries a function and \`rfl\` on the assembled closure does not
close. Five of these were recorded as unstatable until \`veq\` existed.
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

namespace Calculus

${writes.map(leanResolution).join('\n\n')}

${reads.map(leanReadResolution).join('\n\n')}

end Calculus
`

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
const preamble = `import Calculus.Dynamo.Lang.Denote
import Calculus.Dynamo.Alg.Frontier
import Calculus.Dynamo.Lang.Store
import Mathlib.Tactic.FinCases

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by \`src/codec/lean.ts\` from the shipped TypeScript codecs: each
theorem below is one \`encode\` this library actually performed, proposed to the model as an
equation. A failure here is a disagreement between \`src/codec/codec.ts\` and \`Calculus.denote\`, and the
theorem's name says which vector.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a \`k\` it never reads. The gate fails this file on any warning, so the linter is off; the
binder cannot be \`_\` because a multi-name object *does* read \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

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

    The two list alternatives split a list into its elements before \`rfl\` runs. \`rfl\` on a whole
    list asks the kernel for each element at once, and an object inside the list answers with a
    lookup at a bound key, which \`rfl\` cannot reduce. After the split, each element is a goal of
    its own, and the map alternative reaches the object.

    The alternatives are ordered as they are because \`rfl\` first sends the top-level goal, a
    mis-ordered set, and a list that holds an object into an \`isDefEq\` loop. The loop exhausts the
    heartbeat budget rather than failing. -/
macro "vector" : tactic => \`(tactic|
  (refine congrArg some ?_
   repeat' first
     | (refine congrArg (Attr.m _) (funext fun k => ?_)
        obtain ⟨_, hk⟩ := k
        fin_cases hk)
     | (refine congrArg Attr.ss (Subtype.ext ?_); decide)
     | (refine congrArg Attr.ns (Subtype.ext ?_); decide)
     | (refine congrArg Attr.bs (Subtype.ext ?_); decide)
     | (refine congrArg Attr.l ?_)
     | (refine congrArg₂ List.cons ?_ ?_)
     | rfl
     | congr 1))
`

const checkPreamble = `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by \`src/codec/lean.ts\` from the shipped TypeScript codecs: each
theorem below is one \`encode\` this library actually performed, proposed to the model. A failure
here is a disagreement between \`src/codec/codec.ts\` and \`Calculus.denote\`, and the theorem's name says
which vector.

The verdict is \`Calculus.check\`'s, and \`check_same\` is what makes it worth having: \`.same\`
*implies* the two attributes are equal, so a line that reduces to \`.same\` is a proof and not a
comparator's opinion. The fuel on each line is the attribute's own nesting, computed by the
generator — an under-fuelled line reduces to \`.exhausted\`, which matches neither \`.same\` nor
\`.differ\`, so it fails to compile rather than passing quietly.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a \`k\` it never reads. The gate fails this file on any warning, so the linter is off; the
binder cannot be \`_\` because a multi-name object *does* read \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

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
    /**
     * A readable subset of the **read** vectors, for the `check` sample alone.
     *
     * A read vector has one form and it is `vcheck`: its answer is a `Value`, `Value.map` carries
     * a function, and `rfl` on the assembled closure diverges rather than failing. So it cannot be
     * written in the `equation` protocol at all, and the `equation` sample's whole premise is
     * depending on nothing beyond `denote` — putting a `vcheck` in it would cost that.
     *
     * The two samples are otherwise the same vectors in two protocols, and this is the one place
     * they part. The gate elaborates all of `.readvectors.lean` either way; what the sample
     * carries is the readable half.
     */
    reads: readonly Vector[] = [],
    /** Guard verdicts, for a term that no vector can write through. */
    guards: readonly Guard[] = [],
): string => {
    const written = vectors
        .map((vector) => leanVector(vector, protocol))
        .join('\n\n')
    const readBack =
        reads.length === 0
            ? ''
            : `\n\n/-! ### Read back, through the same term\n\nThe model's \`p\`, given the attribute the library wrote, against the value the library read. Only\nthe \`check\` sample carries these: a read vector's answer is a \`Value\`, so it needs \`vcheck\`, and\nthe \`equation\` sample depends on nothing beyond \`denote\` by design. -/\n\n${reads
                  .filter((one) => readVectorIsUnstatable(one) === undefined)
                  .map(leanReadVector)
                  .join('\n\n')}`
    const guarded =
        guards.length === 0
            ? ''
            : `\n\n/-! ### The guard of a binder -/\n\n${guards.map(leanGuard).join('\n\n')}`
    const body = `${written}${readBack}${guarded}`
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
