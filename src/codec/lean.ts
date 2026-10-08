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
import type { AttributeValue, StoredItem } from './attribute'
import {
    carrying,
    DynamoNumber,
    isNumeral,
    isStoredNumeral,
    memberOf,
} from './attribute'
import type { AnyCodec, LiteralValue, ObjectSlot } from './codec'
import { object, optional, union } from './codec'
import { accepts, assignmentOf, codecOfTerm, readsBack } from './denote'
import { CodecError, failed } from './result'
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
    clauseForm,
    disjoint,
    force,
    mapChildren,
    readsFreeVariable,
    recursionUse,
    type Scope,
    storedAlternatives,
    storedView,
    throughThunks,
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

/** The text of a numeral that {@link leanNumeral} or a numeric alternative writes. */
const numeralText = /WFNumeral\.of "[^"\\]*"/g

/**
 * **A module decides each numeral once.** `WFNumeral.of` decides `Numeral.WF x = true` where the
 * module writes the numeral, so a numeral at each occurrence is a decision at each occurrence. The
 * module states each distinct numeral as one `def` after `namespace Calculus`, and writes the name
 * of the `def` at each occurrence. Apply this once to a whole module: a `def` writes the numeral.
 */
export const leanNumeralsOnce = (module: string): string => {
    const names = new Map<string, string>()
    const named = module.replace(numeralText, (text) => {
        const known = names.get(text)
        if (known !== undefined) return known
        const made = `numeral${names.size}`
        names.set(text, made)
        return made
    })
    if (names.size === 0) return module
    const head = 'namespace Calculus\n'
    const at = named.indexOf(head)
    if (at < 0) {
        return refuse(
            'module',
            'a module that writes a numeral opens `namespace Calculus`, where the numerals are stated',
        )
    }
    const cut = at + head.length
    const defs = [...names].map(
        ([text, name]) => `def ${name} : WFNumeral := ${text}`,
    )
    return `${named.slice(0, cut)}
/-! Each numeral of this module, decided once. -/
${defs.join('\n')}
${named.slice(cut)}`
}

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
 * `isStoredNumeral` ↦ `Numeral.Stored` and `isNumeral` ↦ `Numeral.WF`, each written out at the text
 * carrier `.str`. The model's `isStored` decides a `.num`, and a refinement over `decimal` tests the
 * caller's text, so `isStored` is not the image of `isStoredNumeral`. Both were checked
 * against the kernel rather than read across: a corpus of numeral spellings was run through the
 * TypeScript predicates, the verdicts emitted as `Numeral.WF s = b` / `Numeral.Stored s = b` rows,
 * and all of them closed by `rfl`. A test of whether a value is an `N` is not `isNumeral`: it is a
 * different predicate on a different carrier.
 *
 * ── the side condition, which is not decoration ────────────────────────────────────────────────
 *
 * The two TypeScript predicates take a `string`; a `Value → Bool` takes anything. They disagree
 * where JavaScript coerces: `isStoredNumeral(['1'])` is `true`, because `RegExp.test` stringifies
 * its argument and `String(['1'])` is `'1'`, while the printed predicate at `Value.arr …` is `false`. So the
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
            lean: '(fun v => match v with | .str s => Numeral.Stored s | _ => false)',
            what: '`isStoredNumeral`, which is `Numeral.Stored` at the text carrier',
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
 * An adapter that the model does not name is a generator `caller n`, and the theorem quantifies
 * its pair through the caller table. Keyed by the identity that the host reads, the adapter's
 * library name or else its function, so one adapter is one generator wherever the pair uses it.
 */
type Bound = {
    readonly closures: Map<unknown, string>
    readonly adapters: Map<unknown, string>
    /** The older reader of each `legacy`, a variable of the theorem, keyed by the function. */
    readonly readers: Map<unknown, string>
    /**
     * The answers of each older reader that the host asked, as a Lean test on the attribute and
     * the printed answer. The term prints the reader as the variable with these answers pinned.
     */
    readonly pins?: ReadonlyMap<unknown, readonly (readonly [string, string])[]>
    /**
     * Print a fixed function in place of each caller's closure and older reader: the twin of one
     * shape that holds no free function, which the guard reads as it reads the term.
     */
    readonly standIn?: boolean
}

/**
 * **The frames of a printed term.** Each term object that the printer prints, at each position, with
 * the binders above the position, nearest first. A binder is a cell, and the printer writes the
 * text of the cell when the print of the binder ends.
 */
type Frames = {
    readonly at: Map<Term, Position[]>
    readonly above: readonly { text: string }[]
}

/** One position of a printed term: the print, and the binders above it, nearest first. */
type Position = {
    readonly term: string
    readonly above: readonly { text: string }[]
}

/** A scope, and the functions that the theorem binds where the vector is quantified. */
type At = Scope & { readonly bound?: Bound; readonly frames?: Frames }

/**
 * **The name of one caller function, made on the first use.** A prefix names a variable of the
 * theorem (`q0`, `r0`); the empty prefix names the index of an adapter's generator (`caller 0`).
 * The key is the identity that the host reads, so one function is one name wherever the pair uses
 * it.
 */
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
 * **How a vector closes a goal.** The kernel decides the goal, through `kernel_rfl%` of
 * `Calculus.Bridge.Vectors`, and the elaborator evaluates nothing. A closed goal closes by
 * `of_decide_eq_true kernel_rfl%`. A quantified goal binds a caller's function, and `decide`
 * refuses a goal with a free variable, so the goal closes by `kernel_rfl%` on the equation itself.
 */
const closing = (binders: string): string =>
    binders === '' ? 'of_decide_eq_true kernel_rfl%' : 'kernel_rfl%'

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
    frames?: Map<Term, Position[]>,
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
    return leanTermOfTerm(def, at, {
        ...topScope(def),
        bound,
        frames: frames && { at: frames, above: [] },
    })
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
                return bound.standIn
                    ? '(Pred.closure (fun _ => true))'
                    : `(Pred.closure ${boundName(bound.closures, q.q.is, 'q')})`
            if (!known) {
                return refuse(
                    at,
                    `\`Pred.closure\` carries \`q : Value → Bool\`, and this predicate is not one this library ships: it is the caller's closure for ${JSON.stringify(q.q.what)}, a JS closure. A quantified verdict binds it as a variable, and no evaluation vector prints one. The model names two predicates that this library ships, \`isNumeral\` and \`isStoredNumeral\` from \`src/codec/attribute.ts\`, passed by reference`,
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

const leanTermOfTerm = (t: Term, at: string, scope: At): string => {
    const frames = scope.frames
    const binder = { text: '' }
    const printed =
        scope.binds.has(t) && !scope.inside.includes(t)
            ? `Term.mu (${leanTermCore(t, at, {
                  ...scope,
                  inside: [...scope.inside, t],
                  frames: frames && {
                      ...frames,
                      above: [binder, ...frames.above],
                  },
              })})`
            : leanTermCore(t, at, scope)
    binder.text = printed
    if (frames) {
        const known = frames.at.get(t) ?? []
        known.push({ term: printed, above: frames.above })
        frames.at.set(t, known)
    }
    return printed
}

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
         * Every other adapter, a caller's pair or a float adapter of this library, prints a
         * generator `caller n` of a quantified vector: the analysis reads an adapter by its sides
         * and its identity, and the theorem holds at every pair of the caller table. The table is
         * total and a real adapter refuses some values, so a real adapter is `Sub` of a pair of
         * the table. Agreement is antitone in `Sub` (`agree_sub_left`, `agree_sub_right`), and
         * the zero test separates a `held` from the bottom alone, so the verdict holds at the real
         * adapter. Elsewhere the adapter is refused: a float adapter's content is binary64
         * rounding, the host axiom this development deleted.
         *
         * A `held` is an adapter at one absolute side. The store names no generator, so each
         * `held` is at the caller side `false`, with a non-empty word. The stored side has no
         * `held`, so the term prints no stored outer and no stored word.
         */
        case 'held':
            if (t.via !== 'decimalText' && scope.bound)
                return `(Term.held false (${leanTermOfTerm(t.inner, at, scope)}) (${leanTermOfTerm(t.outer, at, scope)}) (.caller ${boundName(scope.bound.adapters, t.via ?? t.f, '')}, false) [])`
            return t.via === 'decimalText'
                ? `(Term.held false (${leanTermOfTerm(t.inner, at, scope)}) (${leanTermOfTerm(t.outer, at, scope)}) (.decimalText, false) [])`
                : refuse(
                      at,
                      "`Term.held` carries a word of adapter generators, and a table gives each generator two `Value → Value` functions: a quantified verdict binds an adapter that the model does not name as a generator `caller n`, and no evaluation vector prints one. An evaluation vector would have to run the adapter: a caller's closure has no name in the model, and a float adapter's content is binary64 rounding, the host axiom this development deleted. The model names one generator that this library ships, `decimalText`, whose pair is `numeralOfStoredText`/`textOfNumeral`",
                  )
        // the older reader is caller code: a quantified verdict binds it as a variable, and an
        // evaluation vector would have to run it
        case 'legacy':
            return scope.bound
                ? `(Term.legacy (${leanTermOfTerm(t.inner, at, scope)}) ${scope.bound.standIn ? '(fun _ => none)' : pinned(scope.bound, t.r)})`
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
 * `'check'` writes `check n ((denote t).e v) (some a) = .same := kernel_rfl%` and is the default. It
 * depends on `Calculus/Bridge/Vectors.lean` — a fuelled three-valued comparator with `check_same` and
 * `check_differ` proved about it, so a passing line cashes to `(denote t).e v = some a` as a
 * theorem. No tactic, no `funext` gymnastics, an order of magnitude faster on maps, and it can
 * state a **negative** vector (`= .differ`), which an equation cannot. The `n` is fuel, because
 * only structural recursion reduces in the kernel; {@link leanVector} computes it from the
 * attribute, and under-fuelling reduces to `.exhausted`, which matches neither side and fails the
 * build rather than passing quietly.
 *
 * `'equation'` writes `(denote t).e v = some a` and proves it with a tactic the generated file
 * carries. The proof reads no comparator, and the file imports `Vectors.lean` for `kernel_rfl%`
 * alone. It cannot express a refusal, and on maps `rfl` does not merely
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
    const guard = guardedToo(term)
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
                  `      (some (${leanAttrOf(attribute, name)})) = .same := kernel_rfl%`,
              ].join('\n')
    return `${vector}${guard}`
}

/** A recursive term that the library wrote through is a term that the guard accepts. */
const guardedToo = (term: string): boolean => term.includes('Term.mu')

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

/** One guard verdict, as a Lean `theorem` closed by `kernel_rfl%`. */
export const leanGuard = ({ name, codec, guarded }: Guard): string =>
    [
        `/-- \`${name}\` — the model's guard ${guarded ? 'accepts' : 'refuses'} this term -/`,
        `theorem ${leanIdent(name)} :`,
        `    Alg.Term.guarded (${leanTermOf(codec, name)}) = ${guarded} := kernel_rfl%`,
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
 * refusal's answer is `none`, which carries no payload, so the kernel closes it by reduction at
 * every codec including the map-shaped ones.
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
    refusedBoth(name, codec, value)
    return [
        `/-- \`${name}\` — refused on both sides -/`,
        `theorem ${leanIdent(name)} :`,
        `    (denote (libTable noCallers) (${leanTermOf(codec, name)})).e`,
        `      (${leanValueOf(value, name)}) = none := kernel_rfl%`,
    ].join('\n')
}

/** The `src/` half of a refusal vector, decided at emit time: this library refuses the value. */
const refusedBoth = (name: string, codec: AnyCodec, value: unknown): void => {
    if (accepts(codec, value)) {
        throw new LeanUnemittable(
            name,
            'this codec admits this value, so a refusal vector about it would assert the model refuses what `src/` writes — pass it as a `Vector` instead',
        )
    }
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
 * - `src/` **refuses** the pair at its compatibility test: the model's guard accepts both options,
 *   and the model's decision refuses the pair, `compatPair dynOracle x y = false`. A decision that
 *   starts to accept a pair `src/` turns down stops the file.
 * - `src/` **refuses** the pair **at the guard**: an option reads the input of its own binder, or
 *   holds an adapter on a recursive path. The model's guard must refuse an option too, on the
 *   terms that {@link leanRooted} spells.
 *
 * A pair that reads a thunk that throws takes the same forms: the model's decision gives agreement
 * at every environment (`compatPair_sound`), so its warrant holds whatever codec the thunk names.
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

/**
 * **The form of a separation verdict**: accepted, refused at compatibility, or refused at the guard.
 * The host's guard runs before its compatibility test, and reads each option on its own. The
 * emitter refuses a pair that the host accepts on no warrant that the model proves.
 */
type SeparationForm = 'accepted' | 'refused' | 'guardRefused'

/** The form of one separation verdict, with the `src/` side decided here. */
const separationForm = ({ name, left, right }: Separation): SeparationForm => {
    try {
        union([left, right] as never)
    } catch {
        return [left, right].some((option) => recursionUse(option.def) >= 2)
            ? 'guardRefused'
            : 'refused'
    }
    return agrees(left.def, right.def)
        ? 'accepted'
        : refuse(
              name,
              '`src/` accepts this pair on no warrant that the model proves: the decision refuses it',
          )
}

/** One declaration verdict, as a Lean `theorem`, with the `src/` side decided here. */
export const leanSeparation = ({ name, left, right }: Separation): string => {
    // a caller's function is a variable of the theorem, and the goal closes as {@link closing} says
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const l = leanTermOf(left, name, bound)
    const r = leanTermOf(right, name, bound)
    const binders = leanBinders(bound)
    const head = `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`
    const reduce = closing(binders)
    // the guard reads the shape alone, so a quantified verdict closes the guard on a twin of one
    // shape that holds no free function, where \`decide\` runs on a closed goal
    const standIn: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
        standIn: true,
    }
    const guard =
        binders === ''
            ? 'of_decide_eq_true kernel_rfl%'
            : [
                  `(congrArg₂ (· && ·)`,
                  `      (Alg.guarded_of_sameShape _ (${leanRooted(leanTermOf(left, name, standIn), left)}) kernel_rfl%)`,
                  `      (Alg.guarded_of_sameShape _ (${leanRooted(leanTermOf(right, name, standIn), right)}) kernel_rfl%)).trans`,
                  `    (of_decide_eq_true kernel_rfl%)`,
              ].join('\n')
    const form = separationForm({ name, left, right })
    if (form === 'guardRefused') {
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair at the guard; the model's guard refuses it too -/`,
            head,
            `    (Alg.Term.guarded (${leanRooted(l, left)}) &&`,
            `      Alg.Term.guarded (${leanRooted(r, right)})) = false :=`,
            `  ${guard}`,
        ].join('\n')
    }
    // the host's guard accepted before its compatibility test refused, so the vector states both
    if (form === 'refused') {
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair; the model's guard accepts it, and the model's decision refuses it -/`,
            head,
            `    (Alg.Term.guarded (${leanRooted(l, left)}) &&`,
            `      Alg.Term.guarded (${leanRooted(r, right)})) = true ∧`,
            `    Alg.compatPair dynOracle (${l})`,
            `      (${r}) = false :=`,
            `  ⟨${guard}, ${reduce}⟩`,
        ].join('\n')
    }
    // the host's union verdict is the guard and the compatibility test, so the vector states both
    return [
        `/-- \`${name}\` — \`src/\` accepts this pair; the model's guard accepts it, and the model proves it compatible -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} (κ : Callers) :`,
        `    (Alg.Term.guarded (${leanRooted(l, left)}) &&`,
        `      Alg.Term.guarded (${leanRooted(r, right)})) = true ∧`,
        `    ((∀ t ∈ [${l}, ${r}], Lawful (denote (libTable κ) t)) →`,
        `      PairwiseCompat (libTable κ) [${l}, ${r}]) :=`,
        `  ⟨${guard}, fun hl => pairwiseCompat_of_compatPair (${reduce}) hl⟩`,
    ].join('\n')
}

/**
 * **A guard verdict on a term that a former refused.** Each former refuses a term where the host's
 * guard reads a recursion at its own input or an adapter on a recursive path, and the refusal
 * carries the term. No union reads such a term, so no {@link Separation} states the model's guard
 * on the term. This vector states the guard half of a separation on the term alone: the model's
 * guard refuses the term too, on the term that {@link leanRooted} spells.
 */
export type FormerGuard = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly term: Term
}

/** One guard verdict on a refused term, as a Lean `theorem`, with the `src/` side decided here. */
export const leanFormerGuard = ({ name, term }: FormerGuard): string => {
    // a thunk in the term can name a codec that is declared now, and the host's guard then reads
    // the term again with another answer. A vector about a term that the host accepts asserts a
    // refusal that the host does not make
    if (recursionUse(term) < 2) {
        return refuse(
            name,
            "the host's guard accepts this term now, so a vector that the model's guard refuses it states no host refusal",
        )
    }
    const rooted = (bound: Bound): string => {
        const printed = leanTermOfTerm(term, name, { ...topScope(term), bound })
        return readsFreeVariable(term) ? `Term.mu (${printed})` : printed
    }
    // a caller's function is a variable of the theorem, and the guard reads the shape alone, so a
    // quantified verdict closes the guard on a twin of one shape that holds no free function
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const printed = rooted(bound)
    const binders = leanBinders(bound)
    const guard =
        binders === ''
            ? 'of_decide_eq_true kernel_rfl%'
            : `(Alg.guarded_of_sameShape _ (${rooted({ closures: new Map(), adapters: new Map(), readers: new Map(), standIn: true })}) kernel_rfl%).trans (of_decide_eq_true kernel_rfl%)`
    return [
        `/-- \`${name}\` — a former refuses this term; the model's guard refuses it too -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        `    Alg.Term.guarded (${printed}) = false :=`,
        `  ${guard}`,
    ].join('\n')
}

/**
 * The guard verdicts on refused terms as a module of their own. A verdict spells the terms and the
 * lemma of a separation verdict, so the header imports `Compat`, and `Store`, which declares
 * `libTable` and which `Compat` does not reach.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanFormerGuardModule = (guards: readonly FormerGuard[]): string =>
    leanNumeralsOnce(`import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.Compat
import Calculus.Dynamo.Lang.Store

/-!
# Guard verdicts on refused terms

**Generated — do not edit.** One theorem per term that a former of \`src/\` refused at its guard.
The model's guard refuses the term too. See \`src/codec/lean.ts\`'s \`FormerGuard\`.
-/

set_option linter.unusedVariables false

namespace Calculus

${guards.map(leanFormerGuard).join('\n\n')}

end Calculus
`)

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

/** The two answers that `src/` computes on a pair: the raw terms, then the two pairs of views. */
const disjointAnswers = ({
    name,
    left,
    right,
}: DisjointPair): readonly [boolean, boolean] => {
    const one = left.def
    const other = right.def
    if ('mark' in one || 'mark' in other) {
        throw new LeanUnemittable(
            name,
            'a §4 *field*, not a term — no `Term` position accepts one, so the test has no pair to state',
        )
    }
    return [disjoint(one, other), viewsDisjoint(one, other)]
}

/**
 * One pair, as a Lean `theorem`: the two terms, and the two answers this library gives.
 *
 * `false` is asserted as much as `true` is. `false` states nothing about the pair, but a port
 * that certified a pair the model declines would fail here on that pair.
 */
export const leanDisjoint = ({ name, left, right }: DisjointPair): string => {
    const [disjointly, views] = disjointAnswers({ name, left, right })
    // a caller's function is a variable of the theorem, and each conjunct closes as
    // {@link closing} says
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
        `        (${r}) = ${disjointly} ∧`,
        `      viewsDisjoint (${l})`,
        `        (${r}) = ${views} := ⟨${closing(binders)}, ${closing(binders)}⟩`,
    ].join('\n')
}

/* ── the row form ──────────────────────────────────────────────────────────────────────────── */

/** The two terms that the tests read, and the two terms that the guard reads, as a row prints them. */
export type RowTerms = {
    readonly l: string
    readonly r: string
    readonly gl: string
    readonly gr: string
}

/**
 * **The distinct terms of a row module, one `def` each.** A caller's function of a term is a
 * parameter of the term's `def`, so two pairs that print one shape share one `def`. The row applies
 * the `def` to the argument that `argument` gives each function of the pair. One function is one
 * argument in both terms of the pair, as one function was one binder of the former theorem.
 * An adapter is one generator `caller n` in both terms of the pair, so the generator stays inside
 * the shape.
 */
export const leanShapes = (
    argument: (kind: 'closure' | 'reader') => string,
): {
    readonly pair: (left: AnyCodec, right: AnyCodec, at: string) => RowTerms
    readonly row: (pin?: Pin) => (codec: AnyCodec, at: string) => string
    readonly closed: (printed: string) => string
    readonly defs: () => string
} => {
    const names = new Map<string, string>()
    const defs: string[] = []
    const nameOf = (printed: string, binders: string): string => {
        const known = names.get(printed)
        if (known !== undefined) return known
        const name = `t${names.size}`
        names.set(printed, name)
        defs.push(
            `def ${name}${binders === '' ? '' : ` ${binders}`} : Term := ${printed}`,
        )
        return name
    }
    const row = (pin: Pin = (_, made) => made) => {
        const adapters = new Map<unknown, string>()
        const given = new Map<unknown, string>()
        const argumentOf = (fn: unknown, kind: 'closure' | 'reader') => {
            const known = given.get(fn)
            if (known !== undefined) return known
            const made = pin(fn, argument(kind))
            given.set(fn, made)
            return made
        }
        return (codec: AnyCodec, at: string): string => {
            const bound: Bound = {
                closures: new Map(),
                adapters,
                readers: new Map(),
            }
            const printed = leanTermOf(codec, at, bound)
            const name = nameOf(printed, leanBinders(bound))
            // the order of `leanBinders`: the closures, then the readers
            const applied = [
                ...[...bound.closures.keys()].map((fn) =>
                    argumentOf(fn, 'closure'),
                ),
                ...[...bound.readers.keys()].map((fn) =>
                    argumentOf(fn, 'reader'),
                ),
            ]
            return applied.length === 0
                ? name
                : `(${name} ${applied.join(' ')})`
        }
    }
    const pair = (left: AnyCodec, right: AnyCodec, at: string): RowTerms => {
        const one = row()
        const l = one(left, at)
        const r = one(right, at)
        return { l, r, gl: leanRooted(l, left), gr: leanRooted(r, right) }
    }
    return {
        pair,
        row,
        closed: (printed) => nameOf(printed, ''),
        defs: () => defs.join('\n'),
    }
}

/**
 * **The argument of a row for one caller function, given the argument that the shapes made.** A
 * former theorem that pinned the function at an input takes the pin around the argument, so the
 * `def` of the term stays the shape, and the row carries the pin.
 */
type Pin = (fn: unknown, made: string) => string

/** The shapes of one module. */
type Shapes = ReturnType<typeof leanShapes>

/** The rows of one list. One list of a whole file exceeds `maxRecDepth`. */
const rowsPerList = 100

/** The rows in lists of {@link rowsPerList}. */
export const listsOf = <T>(rows: readonly T[]): readonly (readonly T[])[] =>
    Array.from({ length: Math.ceil(rows.length / rowsPerList) }, (_, i) =>
        rows.slice(i * rowsPerList, (i + 1) * rowsPerList),
    )

/** The functions of a row theorem: one reader and one predicate per index. */
const rowBinders = '(ρ : Nat → Attr → Option Value) (π : Nat → Value → Bool)'

/**
 * **A fresh index for each caller function of the file.** Two functions never share an index, so
 * the row theorem quantifies each function as the former theorem bound each function.
 */
const kernelShapes = () => {
    let readers = 0
    let closures = 0
    return leanShapes((kind) =>
        kind === 'reader' ? `(ρ ${readers++})` : `(π ${closures++})`,
    )
}

/** A list of rows of `type` as a `def` over the functions, and the kernel's check of the list. */
const leanRowList = (
    name: string,
    type: string,
    rows: readonly string[],
    check: string,
): string =>
    [
        `def ${name} ${rowBinders} : List ${type} := [`,
        `  ${rows.join(',\n  ')}]`,
        '',
        `theorem ${name}_check ${rowBinders} :`,
        `    (${name} ρ π).all (fun p => ${check}) = true := kernel_rfl%`,
    ].join('\n')

/** What a row module states: the generated pool, or the corpus. */
type Subject = 'pool' | 'corpus'

/** The unit of a row of each subject, as the header names it. */
const unitOf = { pool: 'pair', corpus: 'vector' } as const satisfies Record<
    Subject,
    string
>

/** The header of a row module: the reason that a row carries no theorem name of its own. */
const rowForm = (
    subject: Subject,
) => `Each distinct term is one \`def\`, and a caller's function of the term is a parameter of the \`def\`.
A row applies the \`def\` to \`ρ n\` or \`π n\`, and each function of each ${unitOf[subject]} has an index of its own.
A list holds ${rowsPerList} rows, and the kernel decides one check per list by \`kernel_rfl%\`. A ${unitOf[subject]} carries no
theorem name of its own: the ${subject} pre-check names a failing ${unitOf[subject]}.`

/** A form of row list: the Lean type of a row, and the check of one row `p` as a `Bool`. */
type RowForm = { readonly type: string; readonly check: string }

/** One vector as a row: the name of its former theorem, its form, and the row as Lean prints it. */
type Row<F extends string> = {
    readonly name: string
    readonly form: F
    readonly row: string
}

/**
 * **The vectors of one file in the row form.** The rows print through the shapes that the reader
 * gives: the kernel module gives each caller function an index of `ρ` or `π`, and the pre-check
 * gives one instance of each function.
 */
export type RowFile<F extends string = string> = {
    readonly forms: Readonly<Record<F, RowForm>>
    readonly rows: (shapes: Shapes) => readonly Row<F>[]
}

/** The rows of a file, by form in the order of the forms, in lists of {@link rowsPerList}. */
const rowLists = <F extends string>(
    file: RowFile<F>,
    shapes: Shapes,
): readonly {
    readonly form: F
    readonly index: number
    readonly rows: readonly Row<F>[]
}[] => {
    const rows = file.rows(shapes)
    return (Object.keys(file.forms) as F[]).flatMap((form) =>
        listsOf(rows.filter((one) => one.form === form)).map((list, index) => ({
            form,
            index,
            rows: list,
        })),
    )
}

/** The kernel's lists of a file, each with its checker, and the name of each list. */
const kernelLists = <F extends string>(
    file: RowFile<F>,
    shapes: Shapes,
): readonly {
    readonly form: F
    readonly name: string
    readonly text: string
}[] =>
    rowLists(file, shapes).map(({ form, index, rows }) => {
        const name = `${form}${index}`
        const { type, check } = file.forms[form]
        return {
            form,
            name,
            text: leanRowList(
                name,
                type,
                rows.map((one) => one.row),
                check,
            ),
        }
    })

/** The disjointness pairs as rows: the two terms and the two answers of {@link leanDisjoint}. */
export const disjointRows = (
    pairs: readonly DisjointPair[],
): RowFile<'rows'> => ({
    forms: {
        rows: {
            type: '(Term × Term × Bool × Bool)',
            check: '(Alg.Term.disjoint pair0 p.1 p.2.1 == p.2.2.1) &&\n      (viewsDisjoint p.1 p.2.1 == p.2.2.2)',
        },
    },
    rows: (shapes) =>
        pairs.map((pair) => {
            const [disjointly, views] = disjointAnswers(pair)
            const { l, r } = shapes.pair(pair.left, pair.right, pair.name)
            return {
                name: leanIdent(pair.name),
                form: 'rows',
                row: `(${l}, ${r}, ${disjointly}, ${views})`,
            }
        }),
})

/**
 * The disjointness pairs in the row form: each row is the two terms and the two answers of
 * {@link leanDisjoint}, and the checker of a list states both answers at each row.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanDisjointRowModule = (
    pairs: readonly DisjointPair[],
    subject: Subject = 'pool',
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(disjointRows(pairs), shapes).map(
        (one) => one.text,
    )
    return leanNumeralsOnce(`import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.Disjoint
import Calculus.Dynamo.Lang.Store

/-!
# Disjointness of the ${subject}, proposed to the model

**Generated — do not edit.** One row per pair of ${subject} terms: the two terms, the answer of
\`src/\`'s \`disjoint\` on the two terms, and the answer of \`src/\`'s \`viewsDisjoint\` on the two pairs
of views. The checker of a list states that \`Calculus.Alg.Term.disjoint\` and
\`Calculus.viewsDisjoint\` give the same answers at each row.

${rowForm(subject)}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists.join('\n\n')}

end Calculus
`)
}

/** The kernel's check of a row list of each form, and the lemma of `Calculus.Bridge.Rows` that lifts it. */
const separationLists = {
    accepted: {
        type: '(Term × Term × Term × Term)',
        check: 'Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1 &&\n      Alg.compatPair dynOracle p.2.2.1 p.2.2.2',
        caller: ' (κ : Callers)',
        verdict: `(Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1) = true ∧
    ((∀ t ∈ [p.2.2.1, p.2.2.2], Lawful (denote (libTable κ) t)) →
      PairwiseCompat (libTable κ) [p.2.2.1, p.2.2.2])`,
        lift: (list: string) => `accepted_of_rows (${list}_check ρ π) κ`,
    },
    refused: {
        type: '(Term × Term × Term × Term)',
        check: 'Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1 &&\n      !Alg.compatPair dynOracle p.2.2.1 p.2.2.2',
        caller: '',
        verdict: `(Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1) = true ∧
    Alg.compatPair dynOracle p.2.2.1 p.2.2.2 = false`,
        lift: (list: string) => `refused_of_rows (${list}_check ρ π)`,
    },
    guardRefused: {
        type: '(Term × Term)',
        check: '!(Alg.Term.guarded p.1 && Alg.Term.guarded p.2)',
        caller: '',
        verdict: '(Alg.Term.guarded p.1 && Alg.Term.guarded p.2) = false',
        lift: (list: string) => `guardRefused_of_rows (${list}_check ρ π)`,
    },
} as const satisfies Record<SeparationForm, unknown>

/**
 * The declaration verdicts as rows, one form per {@link SeparationForm}. A row of an accepted pair
 * or of a pair refused at compatibility is the two rooted terms that the guard reads, then the two
 * open terms that compatibility reads. A row of a pair refused at the guard is the two rooted terms.
 */
export const separationRows = (
    separations: readonly Separation[],
): RowFile<SeparationForm> => ({
    forms: separationLists,
    rows: (shapes) =>
        separations.map((one) => {
            const { l, r, gl, gr } = shapes.pair(one.left, one.right, one.name)
            const form = separationForm(one)
            return {
                name: leanIdent(one.name),
                form,
                row:
                    form === 'guardRefused'
                        ? `(${gl}, ${gr})`
                        : `(${gl}, ${gr}, ${l}, ${r})`,
            }
        }),
})

/**
 * The declaration verdicts in the row form: one row list per {@link SeparationForm}. Each list
 * carries the checker, and the verdict of {@link leanSeparation} at each row, lifted from the
 * checker.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanSeparationRowModule = (
    separations: readonly Separation[],
    subject: Subject = 'pool',
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(separationRows(separations), shapes).map(
        ({ form, name, text }) => {
            const { caller, verdict, lift } = separationLists[form]
            return [
                text,
                '',
                `theorem ${name}_verdicts ${rowBinders}${caller} :`,
                `    ∀ p ∈ ${name} ρ π,`,
                `    ${verdict} :=`,
                `  ${lift(name)}`,
            ].join('\n')
        },
    )
    return leanNumeralsOnce(`import Calculus.Bridge.Rows
import Calculus.Bridge.Vectors

/-!
# Declaration verdicts of the ${subject}, both ways

**Generated — do not edit.** One row per option pair of the ${subject}, in one list per form. A pair
that \`src/\`'s \`union\` accepts carries the model's guard on both options and the model's proof
that the pair is compatible. A pair that \`src/\` refuses at compatibility carries the model's
guard and \`compatPair dynOracle x y = false\`. A pair that \`src/\` refuses at the guard carries
the model's guard refusal. The lemmas of \`Calculus.Bridge.Rows\` lift each checker to the verdict
of each row.

${rowForm(subject)}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists.join('\n\n')}

end Calculus
`)
}

/* ── the legacy read gate ─────────────────────────────────────────────────────────────────── */

/**
 * **An older reader, as the variable of the theorem with the answers of the host pinned.** `Attr`
 * has no decidable equality, so each pin tests `aeq` at the attribute that the host asked. Any
 * other attribute goes to the variable, so the claim holds at every reader that gives these answers.
 */
const pinned = (bound: Bound, r: unknown): string =>
    pinText(bound.pins?.get(r), boundName(bound.readers, r, 'r'))

/** A reader, given as `name`, with the answers of the host pinned. */
const pinText = (
    pins: readonly (readonly [string, string])[] | undefined,
    name: string,
): string =>
    pins === undefined || pins.length === 0
        ? name
        : `(fun b => ${pins.map(([test, answer]) => `if ${test} then ${answer} else `).join('')}${name} b)`

/**
 * **A copy of the term whose older readers record each answer.** The copy denotes what the term
 * denotes: each reader answers as before. A thunk copies to one thunk, so a cycle stays a cycle.
 */
const recording = (
    t: Term,
    log: Map<unknown, [AttributeValue, unknown][]>,
): Term =>
    throughThunks((t, copy) => {
        switch (t.kind) {
            case 'held':
                return { ...t, inner: copy(t.inner), outer: copy(t.outer) }
            case 'refine':
                return { ...t, inner: copy(t.inner) }
            case 'legacy': {
                const answers = log.get(t.r) ?? []
                log.set(t.r, answers)
                const r = t.r
                return {
                    ...t,
                    inner: copy(t.inner),
                    r: (attribute) => {
                        try {
                            const out = r(attribute)
                            answers.push([attribute, out])
                            return out
                        } catch (thrown) {
                            answers.push([attribute, undefined])
                            throw thrown
                        }
                    },
                }
            }
            default:
                return mapChildren(t, copy)
        }
    })(t)

/** One read of a codec with an older reader, addressed by the attribute. */
export type LegacyRead = {
    readonly name: string
    readonly codec: AnyCodec
    readonly attribute: AttributeValue
}

/**
 * **The legacy read gate, as one read.** The host decodes through a copy of the term whose older
 * readers record each answer. The theorem binds each reader as a variable, and pins the variable
 * at each attribute that the host asked. A reader that threw, failed, or answered `undefined`
 * pins to `none`. The model reads the older answer only where the current term writes the answer.
 */
export const leanLegacyRead = (one: LegacyRead): string => {
    const { name, attribute } = one
    const { read, term, binders } = legacyReadOf(one)
    const head = [
        `/-- \`${name}\` — the older reader pinned where \`src/\` asked it -/`,
        `theorem ${leanIdent(name)} ${binders} :`,
    ]
    return failed(read)
        ? [
              ...head,
              `    (denote (libTable noCallers) (${term})).p`,
              `      (${leanAttrOf(attribute, name)}) = none := kernel_rfl%`,
          ].join('\n')
        : [
              ...head,
              `    vcheck ${fuelForValue(read)}`,
              `      ((denote (libTable noCallers) (${term})).p`,
              `        (${leanAttrOf(attribute, name)}))`,
              `      (some (${leanValueOf(read, name)})) = .same := kernel_rfl%`,
          ].join('\n')
}

/**
 * **One legacy read, decided here**: what the host read, the answers of each older reader that the
 * host asked, and the term with each reader pinned. The refusals of {@link leanLegacyRead} are made
 * here.
 */
const legacyReadOf = (
    one: LegacyRead,
): {
    readonly read: unknown
    readonly pins: ReadonlyMap<unknown, readonly (readonly [string, string])[]>
    readonly term: string
    readonly binders: string
} => {
    const { name, codec, attribute } = one
    const def = codec.def
    if ('mark' in def) {
        return refuse(
            name,
            'a §4 *field*, not a term — `optional`/`fallback` denote `Field`, and no `Term` position accepts one',
        )
    }
    const log = new Map<unknown, [AttributeValue, unknown][]>()
    let read: unknown
    try {
        read = codecOfTerm(recording(def, log)).decode(attribute as never)
    } catch (thrown) {
        read = new CodecError(String(thrown))
    }
    const pins = new Map(
        [...log].map(([r, answers]) => [
            r,
            answers.map(
                ([asked, answer]) =>
                    [
                        `aeq ${fuelFor(asked)} b (${leanAttrOf(asked, name)}) = .same`,
                        failed(answer) || answer === undefined
                            ? 'none'
                            : `some (${leanValueOf(answer, name)})`,
                    ] as const,
            ),
        ]),
    )
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
        pins,
    }
    const term = leanTermOf(codec, name, bound)
    if (bound.closures.size > 0 || bound.adapters.size > 0) {
        return refuse(
            name,
            "a caller's predicate or adapter: the read binds the older readers alone, under `libTable noCallers`",
        )
    }
    return { read, pins, term, binders: leanBinders(bound) }
}

/* ── the slice ───────────────────────────────────────────────────────────────────────────── */

/**
 * A union or a dissection, with the slice that `src/` runs on it.
 *
 * The public `extract` is generic over the clauses that the options admit. This is the erased
 * form, as {@link AnyCodec} is the erased form of a codec.
 */
export type Sliceable = AnyCodec & {
    readonly extract: (clause: Readonly<Record<string, AnyCodec>>) => AnyCodec
}

/**
 * A union and the clauses put to it: `src/`'s `extract`, against the model's `AltClause.admits`.
 *
 * `keys` names the discriminators of a dissection. Each option then adds one row per key: the
 * one-key clause at the tag that `assignmentOf` reads off the option. The row keeps each option
 * that the host assigns the same tag at that key, the option itself included.
 */
export type Slice = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: Sliceable
    readonly clauses: readonly Readonly<Record<string, AnyCodec>>[]
    readonly keys?: readonly string[]
}

/**
 * **The reading of the host that the model's slice does not make.**
 *
 * At a row with this reading, the two sides answer two different questions, so the emitter refuses
 * the row. The pool measured the agreement at every other row.
 */
const numberForm =
    'the clause is a `number` literal: the host reads the literal under the float adapter of `number`, and the model names no float adapter'

/** One clause, and the options that `src/` keeps under the clause, in the order of the union. */
type SliceRow = { readonly clause: string; readonly keeps: readonly boolean[] }

/** One clause key: the name, the adapter word, and the alternatives under the word. */
type ClauseEntry = readonly [string, string, Alternatives]

/**
 * **The adapter word a pin goes through**, as `Calculus.pinOf` reads it: `[]` for a literal, and the
 * generator of the `held` that `leanTermOfTerm` prints, under the same bound, for an adapter.
 */
const leanWord = (t: Term, bound: Bound): string =>
    t.kind === 'refine'
        ? leanWord(t.inner, bound)
        : t.kind !== 'held'
          ? '[]'
          : t.via === 'decimalText'
            ? '[(.decimalText, false)]'
            : `[(.caller ${boundName(bound.adapters, t.via ?? t.f, '')}, false)]`

/** A clause, as an `AltClause` over the names, and the word and the alternatives at each name. */
const leanClause = (entries: readonly ClauseEntry[], at: string): string =>
    `(AltClause.mk ${leanFinset(entries.map(([name]) => name))} (${leanKeyFunction(
        entries.map(([name, word, alts]) => [
            leanString(name),
            `((${word}, ⟨.${alts.base}, ${leanNonEmptySet(
                (alts.ls as readonly LiteralValue[]).map((one) =>
                    leanAlternative(alts.base, one),
                ),
                at,
            )}⟩) : Pin)`,
        ]),
    )}))`

/** The options that `src/`'s `extract` keeps under one clause. */
const keptBy = (
    codec: Sliceable,
    options: readonly Term[],
    clause: Readonly<Record<string, AnyCodec>>,
    at: string,
): readonly boolean[] => {
    let result: AnyCodec
    try {
        result = codec.extract(clause)
    } catch (error) {
        // the host refuses a clause key that no member pins, and a clause at a base that no
        // member carries: each keeps nothing whatever the values, and so does the model
        if (error instanceof CodecError) return options.map(() => false)
        throw error
    }
    const def = result.def
    if ('mark' in def) throw new Error(`${at}: a slice returned a field`)
    const kept =
        def.kind === 'never' ? [] : def.kind === 'union' ? def.options : [def]
    if (kept.some((t) => !options.includes(t))) {
        throw new Error(`${at}: a slice returned an option the union lacks`)
    }
    return options.map((t) => kept.includes(t))
}

/** One clause of the caller, with the host's verdict, or a refusal that names the reading. */
const sliceRow = (
    codec: Sliceable,
    options: readonly Term[],
    clause: Readonly<Record<string, AnyCodec>>,
    bound: Bound,
    at: string,
): SliceRow => {
    const entries = Object.entries(clause).map(([key, value]): ClauseEntry => {
        const def = value.def
        const form = 'mark' in def ? undefined : clauseForm(def)
        if ('mark' in def || form === undefined) {
            return refuse(
                at,
                `the clause at '${key}' is no literal codec: \`src/\` refuses the clause, and \`AltClause\` has no clause to state`,
            )
        }
        if (form.form === 'number') refuse(at, numberForm)
        return [key, leanWord(def, bound), form.alts]
    })
    return {
        clause: leanClause(entries, at),
        keeps: keptBy(codec, options, clause, at),
    }
}

/**
 * The rows of the discriminator assignment: one per option and key.
 *
 * The verdict comes from `assignmentOf` alone, and not from `extract`. A wrong tag then states a
 * clause that the option fails, and the kernel refuses the row.
 */
const assignmentRows = (
    options: readonly Term[],
    keys: readonly string[],
    bound: Bound,
    at: string,
): readonly SliceRow[] => {
    const assigned = options.map((t, i) => {
        if (t.kind !== 'object') {
            return refuse(
                `${at}.option${i}`,
                'no object: `assignmentOf` reads a tag off an object body',
            )
        }
        const tags = assignmentOf(keys, t.body)
        if (failed(tags)) {
            return refuse(
                `${at}.option${i}`,
                `\`src/\` assigns no tag: ${tags.message}`,
            )
        }
        // past `assignmentOf`, a tag is a `req` field that stores one alternative
        const entryAt = (key: string): ClauseEntry => {
            const field = t.body.fields[key]
            const alts = field && storedAlternatives(field.t)
            if (field === undefined || alts === undefined) {
                throw new Error(
                    `${at}.option${i}: the tag at '${key}' stores no literal`,
                )
            }
            if (clauseForm(field.t)?.form === 'number') {
                refuse(`${at}.option${i}`, numberForm)
            }
            return [key, leanWord(field.t, bound), alts]
        }
        return keys.map((key) => [entryAt(key), tags[key]] as const)
    })
    return assigned.flatMap((mine, i) =>
        mine.map(([entry, tag], k) => ({
            clause: leanClause([entry], `${at}.option${i}`),
            keeps: assigned.map((other) => {
                const [[, , alts], t] = other[k] as (typeof other)[number]
                return alts.base === entry[2].base && t === tag
            }),
        })),
    )
}

/**
 * One union, as a Lean `theorem`: the verdict of each clause at each option, as `src/` gives it.
 *
 * One theorem per union and not per row, so the file prints each option one time. A caller's
 * function is a variable of the theorem, and the goal closes as {@link closing} says.
 */
export const leanSlice = (
    { name, codec, clauses, keys = [] }: Slice,
    /** The name of a `def` that holds the clause list, where the module shares the list. */
    named?: (list: string) => string,
): string => {
    const def = codec.def
    if ('mark' in def || def.kind !== 'union') {
        return refuse(
            name,
            'no union: a slice selects among the options of a union',
        )
    }
    const options = def.options
    // one bound for the clauses and the options, so one adapter is one generator in both
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const rows = [
        ...clauses.map((clause, i) =>
            sliceRow(codec, options, clause, bound, `${name}.clause${i}`),
        ),
        ...assignmentRows(options, keys, bound, name),
    ]
    const printed = options.map((t, i) =>
        leanTermOfTerm(t, `${name}.option${i}`, { ...topScope(t), bound }),
    )
    const binders = leanBinders(bound)
    const list = `[${rows.map((row) => row.clause).join(',\n      ')}]`
    return [
        `/-- \`${name}\` — the options \`src/\` keeps under each clause -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        `    ${named === undefined ? list : named(list)}.map`,
        `      (fun c => [${printed.map((t) => `(${t})`).join(',\n        ')}].map c.admits) =`,
        `    [${rows.map((row) => `[${row.keeps.join(', ')}]`).join(',\n      ')}] := ${closing(binders)}`,
    ].join('\n')
}

/* ── the path ──────────────────────────────────────────────────────────────────────────────── */

/** One step of a path: a name, a position, or the clause of a `narrow`. */
export type PathStep =
    | string
    | number
    | { readonly narrow: Readonly<Record<string, AnyCodec>> }

/**
 * **What `at` decides at one path**, read from outside the host.
 *
 * The walk refuses (`refused`), or no codec stands at the path (`vacant`), or some options admit
 * no value at the path (`someVariants`), or the options declare the path differently
 * (`ambiguous`), or one codec stands at the path (`resolved`). The first and the second each
 * happen at the call or on use. The model's frontier carries no such moment, so the vector reads
 * neither moment.
 */
export type HostAt =
    | { readonly kind: 'refused' | 'vacant' | 'someVariants' | 'ambiguous' }
    | { readonly kind: 'resolved'; readonly codec: AnyCodec }

/**
 * The recorder that `at` hands its selector, as a loop drives it. The path type names the steps
 * that a selector literal writes, and a loop computes its steps, so the one cast is at
 * {@link wrapperOf}.
 */
type Recorder = { readonly [name: string]: Recorder } & {
    readonly at: (index: number) => Recorder
    readonly narrow: (clause: Readonly<Record<string, AnyCodec>>) => Recorder
}

/** The item codec that holds a codec at {@link wrapped}, with `at` over a loop's steps. */
type Wrapper = AnyCodec & {
    readonly at: (select: (path: Recorder) => Recorder) => AnyCodec
}

/** The name at which the wrapper holds the codec under test. */
const wrapped = 'r'

/**
 * **A path enters a codec through an item.** `at` belongs to the item of an object, so the codec
 * sits at an optional name, which takes every codec and `never` too. The type of `at` follows the
 * spec, and the spec here is a variable, so the item is cast one time to the erased signature.
 */
const wrapperOf = (codec: AnyCodec): Wrapper =>
    object({ [wrapped]: optional(codec) }).item as unknown as Wrapper

/** Every term that the walk can reach from a root, through each thunk that resolves. */
export const reachable = (root: Term): ReadonlySet<Term> => {
    const seen = new Set<Term>()
    const walk = (t: Term): void => {
        if (seen.has(t)) return
        seen.add(t)
        switch (t.kind) {
            case 'lazy': {
                const target = force(t)
                if (target !== undefined) walk(target)
                return
            }
            case 'list':
                for (const one of [...t.pre, ...t.suf]) walk(one)
                if (t.spread !== undefined) walk(t.spread)
                return
            case 'object':
                for (const field of Object.values(t.body.fields)) walk(field.t)
                if (t.body.rest !== undefined) walk(t.body.rest)
                return
            case 'union':
                return t.options.forEach(walk)
            case 'set':
                return walk(t.elem)
            case 'held':
                walk(t.inner)
                return walk(t.outer)
            case 'refine':
            case 'legacy':
                return walk(t.inner)
            default:
                return
        }
    }
    walk(root)
    return seen
}

/** One step of the recorder. */
const stepOf = (path: Recorder, step: PathStep): Recorder =>
    typeof step === 'number'
        ? path.at(step)
        : typeof step === 'string'
          ? (path[step] as Recorder)
          : path.narrow(step.narrow)

/**
 * **The decision of `at` at a path under {@link wrapped}.** A throw of the call is a refusal at the
 * call. A codec whose term the root does not reach is a refusal on use, and its message names the
 * reading. Any other codec is the resolved codec. A throw that is no `CodecError` propagates.
 */
export const hostAt = (codec: AnyCodec, steps: readonly PathStep[]): HostAt => {
    const item = wrapperOf(codec)
    let reached: AnyCodec
    try {
        reached = item.at((path) =>
            steps.reduce(stepOf, path[wrapped] as Recorder),
        )
    } catch (error) {
        if (!(error instanceof CodecError)) throw error
        return {
            kind: error.message.startsWith('no attribute is declared')
                ? 'vacant'
                : 'refused',
        }
    }
    if (reachable(item.def as Term).has(reached.def as Term))
        return { kind: 'resolved', codec: reached }
    const refusal = reached.decode({ NULL: true })
    const message = refusal instanceof CodecError ? refusal.message : ''
    if (message.includes('is declared by some variants only'))
        return { kind: 'someVariants' }
    if (message.includes('is declared differently in different variants'))
        return { kind: 'ambiguous' }
    // a clause that separates every option leaves no codec at the path
    if (message.startsWith('the clause on')) return { kind: 'vacant' }
    return { kind: 'refused' }
}

/** The paths of one codec, each as its steps under {@link wrapped}. */
export type PathVectors = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly paths: readonly (readonly PathStep[])[]
}

/** A segment of the model's path. */
const leanSeg = (step: string | number): string =>
    typeof step === 'number' ? `.pos ${step}` : `.name ${leanString(step)}`

/**
 * **The depth of a term as it prints**: a thunk that closes a cycle prints a variable, and any
 * other thunk prints its target. The comparator of two declarations reads two frames as similar
 * (`frameSim`) to the depth of the deepest term that the theorem resolves, and two more steps.
 * Similarity is one shape, not one meaning: `frameSim` reads no predicate. A deeper
 * step reads one more unfolding of a binder that the print already holds. A bound of the
 * constructor count reads a recursive term with two recursive children to an exponential size.
 */
const depthOf = (root: Term): number => {
    const walk = (t: Term, stack: readonly Term[]): number => {
        const on = [...stack, t]
        const max = (ts: readonly Term[]) =>
            1 + Math.max(0, ...ts.map((one) => walk(one, on)))
        switch (t.kind) {
            case 'lazy': {
                const target = force(t)
                return target === undefined || on.includes(target)
                    ? 1
                    : walk(target, on)
            }
            case 'list':
                return max([
                    ...t.pre,
                    ...t.suf,
                    ...(t.spread ? [t.spread] : []),
                ])
            case 'object':
                return max([
                    ...Object.values(t.body.fields).map((field) => field.t),
                    ...(t.body.rest ? [t.body.rest] : []),
                ])
            case 'union':
                return max(t.options)
            case 'set':
                return max([t.elem])
            case 'held':
                return max([t.inner, t.outer])
            case 'refine':
            case 'legacy':
                return max([t.inner])
            default:
                return 1
        }
    }
    return walk(root, [])
}

/** The term of a codec with each thunk resolved, as the walk of `narrow` reads it. */
const resolved = (t: Term): Term | undefined =>
    t.kind === 'lazy'
        ? ((u) => (u === undefined ? undefined : resolved(u)))(force(t))
        : t

/**
 * **A decision where a row can narrow**: one codec, and a union under its thunks that is no
 * binder. The walk of `narrow` narrows the options of such a union, and a row states that narrowing.
 *
 * A recursive union has no row. Its options read the union through a variable, and `narrow` reads
 * the variable open, where the host reads the thunk closed. The model has no substitution that
 * closes the options, so no row states the narrowing that the host does.
 */
export const unionAt = (host: HostAt): boolean => {
    if (host.kind !== 'resolved' || 'mark' in host.codec.def) return false
    const u = resolved(host.codec.def)
    return u?.kind === 'union' && !bindersOf(host.codec.def).has(u)
}

/** A frame of the model's walk: a term object at one position, and the binders above it. */
type Walked = {
    readonly t: Term
    readonly scope: At
    readonly above: readonly string[]
}

/** The frame of a walk, as the model's `Frame` prints. */
const leanFrame = (w: Walked, at: string): string =>
    `(${leanTermOfTerm(w.t, at, w.scope)}, [${w.above.join(', ')}])`

/** The term `never`, the frame of a name that an object neither declares nor leaves open. */
const nothingAt: Term = { kind: 'never' }

/**
 * **The model's frontier at one segment, over the printed term**: `Alg.Frame.child`. A binder
 * enters its body under its own print, a thunk that closes a cycle enters its binder again over the
 * binders outside the binder, and any other thunk is its target. A union gives the children of each
 * option. `undefined` is a refusal, and a segment that a term does not read gives no frame. The
 * kernel checks each frame against `Term.at`, so a step that reads otherwise fails the row.
 */
const childOf = (
    w: Walked,
    s: string | number,
    at: string,
): Walked[] | undefined => {
    const { t, scope, above } = w
    if (scope.binds.has(t) && !scope.inside.includes(t)) {
        const self = leanTermOfTerm(t, at, scope)
        const inside = { ...scope, inside: [...scope.inside, t] }
        return childIn({ t, scope: inside, above: [self, ...above] }, s, at)
    }
    return childIn(w, s, at)
}

/** {@link childOf} past the binder of the term. */
const childIn = (
    w: Walked,
    s: string | number,
    at: string,
): Walked[] | undefined => {
    const { t, scope, above } = w
    const here = (u: Term): Walked[] => [{ t: u, scope, above }]
    switch (t.kind) {
        case 'never':
            return []
        case 'opaq':
            return here(t)
        case 'lazy': {
            const target = force(t)
            if (target === undefined) return []
            const k = scope.inside.lastIndexOf(target)
            if (k === -1) return childOf({ t: target, scope, above }, s, at)
            const outer = { ...scope, inside: scope.inside.slice(0, k) }
            const i = scope.inside.length - 1 - k
            return childOf(
                { t: target, scope: outer, above: above.slice(i + 1) },
                s,
                at,
            )
        }
        case 'union': {
            const all: Walked[] = []
            for (const option of t.options) {
                const some = childOf({ t: option, scope, above }, s, at)
                if (some === undefined) return undefined
                all.push(...some)
            }
            return all
        }
        case 'object': {
            if (typeof s !== 'string') return []
            const field = t.body.fields[s]
            return here(field ? field.t : (t.body.rest ?? nothingAt))
        }
        case 'list': {
            if (typeof s !== 'number') return []
            const one = t.pre[s]
            if (one !== undefined) return here(one)
            if (t.suf.length > 0) return undefined
            return here(t.spread ?? nothingAt)
        }
        default:
            return []
    }
}

/** The frontier of a walk at each segment of a path. */
const walkOf = (
    start: readonly Walked[],
    segs: readonly (string | number)[],
    at: string,
): Walked[] | undefined => {
    let ws: Walked[] = [...start]
    for (const s of segs) {
        const next: Walked[] = []
        for (const w of ws) {
            const some = childOf(w, s, at)
            if (some === undefined) return undefined
            next.push(...some)
        }
        ws = next
    }
    return ws
}

/** The options of a union that a clause keeps: the host's narrowing, on the stored views. */
const narrowedBy = (
    clause: Readonly<Record<string, AnyCodec>>,
    options: readonly Term[],
): Term[] => {
    const fields: Record<string, TermField> = {}
    for (const [key, one] of Object.entries(clause)) {
        if ('mark' in one.def) continue
        fields[key] = { mark: 'req', t: one.def }
    }
    const phi = storedView({
        kind: 'object',
        body: { fields, rest: { kind: 'opaq' } },
    })
    return options.filter((o) => !disjoint(phi, storedView(o)))
}

/**
 * **The paths of one codec, as one Lean `theorem`.** Each path without a clause is a row of
 * `PathRows`: the model's `Term.at` at the path, read against the decision of the host. A path
 * with a clause is a row of `NarrowRows` at the union that the host resolves before the clause:
 * the model's `narrow` over the options of the union, then the frontier of the rest of the path.
 *
 * One bound for every term of the theorem, so one adapter is one generator in each.
 *
 * **A resolved row states the frontier.** The host resolves a node of the term graph of the root.
 * The printer records each position of each node, with the binders above the position. The walk
 * of the model's frontier, over the same print, names the position of each frame, and the row
 * states each frame as the recorded frame of the resolved node at that position. Equal frames have
 * one meaning, so the row certifies the meaning of the host's decision. A frame at a position of
 * another node, or at a position that the resolved node does not hold, refuses the path.
 *
 * **A caller's function is a variable of the theorem**, so a frame equals the resolved frame only
 * where the two hold the same function. The theorem binds each closure and each older reader.
 *
 * **The kernel decides the goal**, by `kernel_rfl%` on each conjunct. A frame holds a function, so
 * the equation has no decision, and the kernel compares the two sides by definitional equality.
 *
 * `decide` is the decision of the host. Every caller but one test reads {@link hostAt}. The test
 * gives a wrong decision, so the refusal of a frame at no position of the resolved node fires.
 */
export const leanPath = (
    { name, codec, paths }: PathVectors,
    decide: typeof hostAt = hostAt,
): string => {
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const item = wrapperOf(codec)
    const rootFrames = new Map<Term, Position[]>()
    const root = leanTermOf(item, `${name}.root`, bound, rootFrames)
    const rootWalk: Walked = {
        t: item.def as Term,
        scope: { ...topScope(item.def as Term), bound },
        above: [],
    }
    let fuel = 1
    // a long term of a frame prints one time per theorem, as a `let` that the rows name: the term
    // can hold a variable of the theorem, so it is no declaration
    const terms = new Map<string, string>()
    const named = (printed: string): string => {
        if (printed.length <= 80) return printed
        const known = terms.get(printed)
        if (known !== undefined) return known
        const made = `t${terms.size}`
        terms.set(printed, made)
        return made
    }
    /**
     * The decision of the host at a path. A resolved row states the frontier of the walk, each
     * frame at a recorded position of the resolved node.
     */
    const host = (
        steps: readonly PathStep[],
        at: string,
        frontier: () => Walked[] | undefined,
        recorded: Map<Term, Position[]>,
    ): string => {
        const decided = decide(codec, steps)
        if (decided.kind !== 'resolved') return `.${decided.kind}`
        fuel = Math.max(fuel, depthOf(decided.codec.def as Term))
        const own = new Set(
            (recorded.get(decided.codec.def as Term) ?? []).map(
                (p) =>
                    `(${p.term}, [${p.above.map((c) => c.text).join(', ')}])`,
            ),
        )
        const walked = frontier() ?? []
        if (
            walked.length === 0 ||
            walked.some((w) => !own.has(leanFrame(w, at)))
        )
            return refuse(
                at,
                'the model reaches a frame that is no position of the resolved node',
            )
        const [first, ...others] = walked.map(
            (w) =>
                `(${named(leanTermOfTerm(w.t, at, w.scope))}, [${w.above.map(named).join(', ')}])`,
        )
        return `.resolved ${first} [${others.join(', ')}]`
    }
    const plain: string[] = []
    const unions = new Map<string, Map<string, string[]>>()
    paths.forEach((steps, i) => {
        const at = `${name}.path${i}`
        const clauses = steps.flatMap((step, k) =>
            typeof step === 'object' ? [k] : [],
        )
        if (clauses.length === 0) {
            const segs = [wrapped, ...(steps as readonly (string | number)[])]
            const frontier = () => walkOf([rootWalk], segs, at)
            plain.push(
                `([${segs.map(leanSeg).join(', ')}], ${host(steps, at, frontier, rootFrames)})`,
            )
            return
        }
        const [k] = clauses
        if (clauses.length > 1 || k === undefined) {
            return refuse(at, 'a path of two clauses: a row narrows once')
        }
        const before = decide(codec, steps.slice(0, k))
        if (before.kind !== 'resolved' || !unionAt(before)) {
            return refuse(
                at,
                'no union stands before the clause: a row narrows the options of one union',
            )
        }
        const uFrames = new Map<Term, Position[]>()
        const u = leanTermOf(before.codec, `${at}.union`, bound, uFrames)
        const clause = (steps[k] as Exclude<PathStep, string | number>).narrow
        const entries = Object.entries(clause).map(
            ([key, one]) =>
                [
                    leanString(key),
                    `(${leanTermOf(one, `${at}.narrow.${key}`, bound)})`,
                ] as const,
        )
        const phi = `(Alg.clauseTerm ${leanFinset(Object.keys(clause))} (${leanKeyFunction(entries)}))`
        const rest = steps.slice(k + 1) as readonly (string | number)[]
        const uDef = before.codec.def as Term
        const scope = { ...topScope(uDef), bound }
        const options = resolved(uDef)
        const frontier = () =>
            options?.kind === 'union'
                ? walkOf(
                      narrowedBy(clause, options.options).map((t) => ({
                          t,
                          scope,
                          above: [],
                      })),
                      rest,
                      at,
                  )
                : undefined
        const byClause = unions.get(u) ?? new Map<string, string[]>()
        const rows = byClause.get(phi) ?? []
        rows.push(
            `([${rest.map(leanSeg).join(', ')}], ${host(steps, at, frontier, uFrames)})`,
        )
        byClause.set(phi, rows)
        unions.set(u, byClause)
    })
    const conjuncts = [
        `PathRows ${fuel + 2} (${root})\n      [${plain.join(',\n       ')}]`,
        ...[...unions].map(
            ([u, byClause]) =>
                `NarrowRows ${fuel + 2} (${u})\n      [${[...byClause]
                    .map(
                        ([phi, rows]) =>
                            `(${phi},\n        [${rows.join(',\n         ')}])`,
                    )
                    .join(',\n       ')}]`,
        ),
    ]
    const proof =
        conjuncts.length === 1
            ? 'kernel_rfl%'
            : `⟨${conjuncts.map(() => 'kernel_rfl%').join(', ')}⟩`
    const binders = leanBinders(bound)
    // one theorem per codec: the cost of a declaration outweighs the parallel check of small ones
    return [
        `/-- \`${name}\` — the decision of \`at\` at each path, and under each \`narrow\` -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        ...[...terms].map(
            ([printed, ident]) => `    let ${ident} : Term := ${printed}`,
        ),
        `    ${conjuncts.join(' ∧\n    ')} := ${proof}`,
    ].join('\n')
}

/** The imports of a slice module. A path module imports `Calculus.Bridge.Paths` too. */
const sliceImports = `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.Slice
import Calculus.Dynamo.Lang.Store
import Calculus.Lang.Path`

/**
 * The slices as a module of their own.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanSliceModule = (slices: readonly Slice[]): string => {
    // one clause list is one `def`, so the file prints each list one time
    const lists = new Map<string, string>()
    const named = (list: string): string => {
        const known = lists.get(list)
        if (known !== undefined) return known
        const made = `clauses${lists.size}`
        lists.set(list, made)
        return made
    }
    const theorems = slices.map((slice) => leanSlice(slice, named))
    const defs = [...lists].map(
        ([list, name]) => `def ${name} : List AltClause := ${list}`,
    )
    return leanNumeralsOnce(`${sliceImports}

/-!
# Slices, proposed to the model

**Generated — do not edit.** One theorem per union. Each row is a clause, and the row lists the
options that \`src/\` keeps under the clause: \`extract\` gives the verdict of a clause of the caller,
and \`assignmentOf\` gives the verdict of a clause at the tag of a dissection's option. The theorem
states that \`Calculus.AltClause.admits\` gives the same verdict at each option. Each distinct
clause list is one \`def\`, which each theorem with that list reads.
-/

/-! The emitted key function is total on a membership subtype, so a one-name clause binds a \`k\`
it never reads; the binder cannot be \`_\` because a clause of several names reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${[...defs, ...theorems].join('\n\n')}

end Calculus
`)
}

/**
 * **The path theorems, in \`files\` modules of near one size.** The kernel checks the theorems of
 * one file in sequence, so the gate checks the files in parallel. The emitter measures a theorem
 * by its printed length, and gives each theorem, longest first, to the file with the least length.
 * A file keeps the theorems in the order of the pool. The readings that the rows read are
 * `Calculus/Bridge/Paths.lean`, which states the frontier that each decision of the host names.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanPathModules = (
    paths: readonly PathVectors[],
    files: number,
): string[] => {
    const printed = paths.map((one) => leanPath(one))
    const size = Array.from({ length: files }, () => 0)
    const owner = new Map<number, number>()
    const longestFirst = printed
        .map((text, i) => [text.length, i] as const)
        .sort(([a, i], [b, j]) => b - a || i - j)
    for (const [length, i] of longestFirst) {
        const least = size.indexOf(Math.min(...size))
        owner.set(i, least)
        size[least] = (size[least] ?? 0) + length
    }
    return size.map((_, file) =>
        leanNumeralsOnce(`${sliceImports}
import Calculus.Bridge.Paths

/-!
# Paths, proposed to the model

**Generated — do not edit.** File ${file} of ${files}. A path theorem states the decision of
\`at\` at each path into one codec, and under each \`narrow\` at a union on the path. The model
gives the frontier by \`Alg.Term.at\`, and after a clause by \`Alg.narrow\` and the frontier of
the rest of the path.
-/

/-! The emitted key function is total on a membership subtype, so a one-name clause binds a \`k\`
it never reads; the binder cannot be \`_\` because a clause of several names reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

set_option maxRecDepth 8192

${printed.filter((_, i) => owner.get(i) === file).join('\n\n')}

end Calculus
`),
    )
}

/**
 * One read verdict, as a Lean `theorem`; `src/`'s answer is taken by running `decode`.
 *
 * **A caller's predicate at the top is a variable `q0` of the theorem.** The model's `refine` row
 * reads the attribute with the inner term, then applies `q0` to the value read. Where the inner
 * term refuses, the verdict is `false` at every `q0`. Where the inner term reads `v`, the theorem
 * assumes `q0 v` equals the answer of the caller's closure at the value that the host read. The
 * kernel then checks that the model applies `q0` at that value, and that `decode` answers the same.
 * A caller's predicate below the top is refused, because the emitter computes the value that the
 * predicate reads at the top only. A caller's adapter and an older reader are refused, because the
 * row reads under `libTable noCallers`.
 */
export const leanReadVerdict = (one: ReadVerdict): string => {
    const { name, attribute } = one
    const { decodes, term, quantified, pin } = readVerdictOf(one)
    const head = [
        `/-- \`${name}\` — \`src/\` ${decodes ? 'decodes' : 'refuses'} this attribute -/`,
        `    AdmA (libTable noCallers) (${term})`,
        `      (${leanAttrOf(attribute, name)}) = ${decodes}`,
    ] as const
    if (!quantified) {
        return [
            head[0],
            `theorem ${leanIdent(name)} :`,
            head[1],
            `${head[2]} := kernel_rfl%`,
        ].join('\n')
    }
    if (pin === undefined) {
        return [
            head[0],
            `theorem ${leanIdent(name)} (q0 : Value → Bool) :`,
            head[1],
            `${head[2]} := kernel_rfl%`,
        ].join('\n')
    }
    const { v, answer } = pin
    return [
        head[0],
        `theorem ${leanIdent(name)} (q0 : Value → Bool) (h0 : q0 (${v}) = ${answer}) :`,
        head[1],
        `${head[2]} := show q0 (${v}) = ${answer} from h0`,
    ].join('\n')
}

/**
 * **One read verdict, decided here**: `src/`'s answer, the term, whether a caller's predicate at the
 * top is a variable, and the answer of that predicate at the value that the inner term reads, where
 * the inner term reads one. The refusals of {@link leanReadVerdict} are made here.
 */
const readVerdictOf = (
    one: ReadVerdict,
): {
    readonly decodes: boolean
    readonly term: string
    readonly quantified: boolean
    readonly pin?: {
        readonly is: unknown
        readonly v: string
        readonly answer: boolean
        readonly fuel: number
    }
} => {
    const { name, codec, attribute } = one
    const decodes = readsBack(codec, attribute)
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const term = leanTermOf(codec, name, bound)
    if (bound.adapters.size > 0 || bound.readers.size > 0) {
        return refuse(
            name,
            "a caller's adapter or older reader: the read row reads under `libTable noCallers`, which names no caller",
        )
    }
    if (bound.closures.size === 0) return { decodes, term, quantified: false }
    const def = codec.def
    const inner =
        !('mark' in def) && def.kind === 'refine' && def.q.kind === 'closure'
            ? { term: def.inner, holds: def.q.q.is }
            : undefined
    // the inner term must print no closure, so the theorem binds the top predicate alone
    const below: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    if (inner !== undefined) {
        leanTermOfTerm(inner.term, name, {
            ...topScope(inner.term),
            bound: below,
        })
    }
    if (inner === undefined || below.closures.size > 0) {
        return refuse(
            name,
            "a caller's predicate below the top: the emitter computes the value that the predicate reads at the top only",
        )
    }
    const read: unknown = codecOfTerm(inner.term).decode(attribute as never)
    if (failed(read)) return { decodes, term, quantified: true }
    return {
        decodes,
        term,
        quantified: true,
        pin: {
            is: inner.holds,
            v: leanValueOf(read, name),
            answer: inner.holds(read as never),
            fuel: fuelForValue(read),
        },
    }
}

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
        `      (some (${leanValueOf(read, name)})) = .same := kernel_rfl%`,
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
    return leanNumeralsOnce(`import Calculus.Bridge.Vectors
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
`)
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

/** What the union wrote for the value, or that it wrote nothing. */
const writeOf = (
    u: AnyCodec,
    value: unknown,
):
    | { readonly wrote: true; readonly written: AttributeValue }
    | { readonly wrote: false; readonly written?: undefined } => {
    try {
        const out = u.encode(value as never)
        return failed(out)
            ? { wrote: false }
            : { wrote: true, written: out as AttributeValue }
    } catch {
        return { wrote: false }
    }
}

/** One read-side resolution, addressed by the attribute rather than the value. */
export type ReadResolution = {
    readonly name: string
    readonly union: AnyCodec
    readonly attribute: AttributeValue
}

/** One read-side resolution: what the union read, or that it read nothing. */
export const leanReadResolution = (one: ReadResolution): string =>
    statedRead(one.name, one.union, one.attribute, () =>
        one.union.decode(one.attribute as never),
    )

/**
 * A dissection, with the read of a whole item that `src/` runs through the index of its tags.
 *
 * The index is the host's, and no term carries it. The model's `Term.union` of the members reads
 * `Attr.m` of the item, so the statement is the read resolution of that union.
 */
export type Dissection = AnyCodec & {
    readonly item: {
        readonly decode: (item: StoredItem) => ReturnType<AnyCodec['decode']>
    }
}

/** One read through the index of a dissection, addressed by the item. */
export type ItemRead = {
    readonly name: string
    readonly dissection: Dissection
    readonly item: Readonly<Record<string, AttributeValue>>
}

/** One read through the index: what the index read from the item, or that it read nothing. */
export const leanItemReadResolution = (one: ItemRead): string =>
    statedRead(one.name, one.dissection, carrying('M', one.item), () =>
        one.dissection.item.decode(one.item),
    )

/** What the union read, or that it read nothing. */
const readOf = (
    decode: () => unknown,
): { readonly did: boolean; readonly read: unknown } => {
    try {
        const out = decode()
        return { did: !failed(out), read: out }
    } catch {
        return { did: false, read: undefined }
    }
}

/** The theorem that the model's union reads `attribute` as the host read it, or reads nothing. */
const statedRead = (
    name: string,
    u: AnyCodec,
    attribute: AttributeValue,
    decode: () => unknown,
): string => {
    const { did, read } = readOf(decode)
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
              `      (some (${leanValueOf(read, name)})) = .same := kernel_rfl%`,
          ].join('\n')
        : [
              ...head,
              `    (denote (libTable noCallers) (${leanTermOf(u, name)})).p`,
              `      (${leanAttrOf(attribute, name)}) = none := kernel_rfl%`,
          ].join('\n')
}

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
const preamble = `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Denote
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
     * written in the `equation` protocol at all, and the `equation` sample states each vector as an
     * equation on `denote` — putting a `vcheck` in it would cost that.
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
            : `\n\n/-! ### Read back, through the same term\n\nThe model's \`p\`, given the attribute the library wrote, against the value the library read. Only\nthe \`check\` sample carries these: a read vector's answer is a \`Value\`, so it needs \`vcheck\`, and\nthe \`equation\` sample states each vector as an equation on \`denote\` by design. -/\n\n${reads
                  .filter((one) => readVectorIsUnstatable(one) === undefined)
                  .map(leanReadVector)
                  .join('\n\n')}`
    const guarded =
        guards.length === 0
            ? ''
            : `\n\n/-! ### The guard of a binder -/\n\n${guards.map(leanGuard).join('\n\n')}`
    const body = `${written}${readBack}${guarded}`
    if (refusals.length === 0) {
        return leanNumeralsOnce(
            `${protocol === 'equation' ? preamble : checkPreamble}\n${body}\n\nend Calculus\n`,
        )
    }
    const refused = refusals.map(leanRefusal).join('\n\n')
    const heading = [
        '',
        '/-! ## Refusals — neither side writes anything for these',
        '',
        `${refusals.length} of ${refusalsChecked} shown; \`scripts/gate.sh\` elaborates all`,
        `${refusalsChecked}. One \`kernel_rfl%\` each, no comparator and no fuel: the answer is \`none\`,`,
        'which carries no function for the funext gap to open under.',
        '-/',
        '',
    ].join('\n')
    return leanNumeralsOnce(
        `${protocol === 'equation' ? preamble : checkPreamble}\n${body}\n${heading}\n${refused}\n\nend Calculus\n`,
    )
}

/* ── the corpus in the row form ────────────────────────────────────────────────────────────── */

/**
 * The forms of the evaluation vectors. Each check is a `Bool` whose truth is the former statement:
 * `beq_iff_eq` makes `(v == w) = true` the equation `v = w` at `Verdict` and at `Bool`, and
 * `Option.isNone_iff_eq_none` makes `x.isNone = true` the equation `x = none`. `Attr` and `Value`
 * hold a function, so neither has decidable equality, and a `some` answer keeps `check` or `vcheck`.
 */
const evaluationForms = {
    writes: {
        type: '(Nat × Term × Value × Attr)',
        check: 'check p.1 ((denote (libTable noCallers) p.2.1).e p.2.2.1) (some p.2.2.2) == Verdict.same',
    },
    writesNothing: {
        type: '(Term × Value)',
        check: '((denote (libTable noCallers) p.1).e p.2).isNone',
    },
    reads: {
        type: '(Nat × Term × Attr × Value)',
        check: 'vcheck p.1 ((denote (libTable noCallers) p.2.1).p p.2.2.1) (some p.2.2.2) == Verdict.same',
    },
    readsNothing: {
        type: '(Term × Attr)',
        check: '((denote (libTable noCallers) p.1).p p.2).isNone',
    },
    guards: {
        type: '(Term × Bool)',
        check: 'Alg.Term.guarded p.1 == p.2',
    },
    admits: {
        type: '(Term × Attr × Bool)',
        check: 'AdmA (libTable noCallers) p.1 p.2.1 == p.2.2',
    },
} as const satisfies Record<string, RowForm>

/** The equivalence that turns the checker of a list into the former statement of each row. */
const rowChecks = `The checker of a list states \`List.all … = true\`, which \`List.all_eq_true\` makes the check at
each row. A check is a \`Bool\` whose truth is the former statement of the row: \`beq_iff_eq\` makes
\`(v == Verdict.same) = true\` the equation \`v = .same\`, and \`(b == c) = true\` the equation \`b = c\`
at \`Bool\`. \`Option.isNone_iff_eq_none\` makes \`x.isNone = true\` the equation \`x = none\`. \`Attr\` and
\`Value\` have no decidable equality, because a map holds a function, so a \`some\` answer keeps \`check\` or
\`vcheck\`.`

/** A module of corpus rows: the imports, the title, the statement, and the rows. */
const leanCorpusRowModule = <F extends string>(
    imports: string,
    title: string,
    states: string,
    file: RowFile<F>,
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(file, shapes).map((one) => one.text)
    return leanNumeralsOnce(`${imports}

/-!
# ${title}

**Generated — do not edit.** ${states}

${rowChecks}

${rowForm('corpus')}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists.join('\n\n')}

end Calculus
`)
}

/**
 * **The cross product of the corpus as rows**: each admission of {@link leanVector} in the `check`
 * protocol, with the guard of a recursive term, each guard verdict of {@link leanGuard}, and each
 * refusal of {@link leanRefusal}. The term of each row is a closed term, as the former theorem
 * printed it.
 */
export const vectorRows = (
    admissions: readonly Vector[],
    refusals: readonly Refusal[],
    guards: readonly Guard[],
): RowFile<'writes' | 'writesNothing' | 'guards'> => ({
    forms: {
        writes: evaluationForms.writes,
        guards: evaluationForms.guards,
        writesNothing: evaluationForms.writesNothing,
    },
    rows: (shapes) => [
        ...admissions.flatMap(({ name, codec, value }) => {
            const term = leanTermOf(codec, name)
            const attribute = codec.unsafeEncode(value as never)
            const t = shapes.closed(term)
            const row = {
                name: leanIdent(name),
                form: 'writes' as const,
                row: `(${fuelFor(attribute)}, ${t}, ${leanValueOf(value, name)}, ${leanAttrOf(attribute, name)})`,
            }
            return guardedToo(term)
                ? [
                      row,
                      {
                          name: leanIdent(`${name}__guarded`),
                          form: 'guards' as const,
                          row: `(${t}, true)`,
                      },
                  ]
                : [row]
        }),
        ...guards.map(({ name, codec, guarded }) => ({
            name: leanIdent(name),
            form: 'guards' as const,
            row: `(${shapes.closed(leanTermOf(codec, name))}, ${guarded})`,
        })),
        ...refusals.map(({ name, codec, value }) => {
            refusedBoth(name, codec, value)
            return {
                name: leanIdent(name),
                form: 'writesNothing' as const,
                row: `(${shapes.closed(leanTermOf(codec, name))}, ${leanValueOf(value, name)})`,
            }
        }),
    ],
})

/** The cross product of the corpus in the row form. Generated at gate time, never committed. */
export const leanVectorRowModule = (
    admissions: readonly Vector[],
    refusals: readonly Refusal[],
    guards: readonly Guard[],
): string =>
    leanCorpusRowModule(
        `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store`,
        'Differential-testing vectors, the full cross product',
        `Emitted by \`src/codec/lean.ts\` from the shipped TypeScript codecs. A \`writes\`
row is one \`encode\` that this library performed, \`check n ((denote t).e v) (some a) = .same\`. A
\`writesNothing\` row is a value that this library refuses, \`(denote t).e v = none\`. A \`guards\` row
is the model's guard on a term, \`Alg.Term.guarded t = b\`. ${admissions.length} admissions,
${refusals.length} refusals.`,
        vectorRows(admissions, refusals, guards),
    )

/**
 * The union resolutions as rows: each write that {@link writeOf} decides, then each read of
 * {@link leanReadResolution}, then each read of {@link leanItemReadResolution}.
 */
export const resolutionRows = (
    writes: readonly Resolution[],
    reads: readonly ReadResolution[],
    items: readonly ItemRead[],
): RowFile<'writes' | 'writesNothing' | 'reads' | 'readsNothing'> => ({
    forms: {
        writes: evaluationForms.writes,
        writesNothing: evaluationForms.writesNothing,
        reads: evaluationForms.reads,
        readsNothing: evaluationForms.readsNothing,
    },
    rows: (shapes) => {
        const read = (
            name: string,
            u: AnyCodec,
            attribute: AttributeValue,
            decode: () => unknown,
        ) => {
            const t = shapes.closed(leanTermOf(u, name))
            const a = leanAttrOf(attribute, name)
            const { did, read } = readOf(decode)
            return did
                ? {
                      name: leanIdent(name),
                      form: 'reads' as const,
                      row: `(${fuelForValue(read)}, ${t}, ${a}, ${leanValueOf(read, name)})`,
                  }
                : {
                      name: leanIdent(name),
                      form: 'readsNothing' as const,
                      row: `(${t}, ${a})`,
                  }
        }
        return [
            ...writes.map(({ name, union: u, value }) => {
                const t = shapes.closed(leanTermOf(u, name))
                const v = leanValueOf(value, name)
                const { wrote, written } = writeOf(u, value)
                return wrote
                    ? {
                          name: leanIdent(name),
                          form: 'writes' as const,
                          row: `(${fuelFor(written)}, ${t}, ${v}, ${leanAttrOf(written, name)})`,
                      }
                    : {
                          name: leanIdent(name),
                          form: 'writesNothing' as const,
                          row: `(${t}, ${v})`,
                      }
            }),
            ...reads.map((one) =>
                read(one.name, one.union, one.attribute, () =>
                    one.union.decode(one.attribute as never),
                ),
            ),
            ...items.map((one) =>
                read(one.name, one.dissection, carrying('M', one.item), () =>
                    one.dissection.item.decode(one.item),
                ),
            ),
        ]
    },
})

/** The union resolutions in the row form. Generated at gate time, never committed. */
export const leanResolutionRowModule = (
    writes: readonly Resolution[],
    reads: readonly ReadResolution[],
    items: readonly ItemRead[],
): string =>
    leanCorpusRowModule(
        `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store`,
        'Union resolution, model against library',
        `One row per (union, value) and (union, attribute) pair: the option
the model's \`select\` resolves to, against the one this library's resolver picked.
${writes.length} on the write side, ${reads.length} on the read side, and ${items.length} read through the
index of a dissection's tags. A read row states \`vcheck\`, the \`Value\` twin of \`check\`.`,
        resolutionRows(writes, reads, items),
    )

/**
 * The read verdicts as rows: the term, the attribute, and whether `src/` decodes it. A caller's
 * predicate at the top takes an index of `π`. Where the former theorem assumed `q0 v = b`, the row
 * pins the predicate: `fun x => if veq n x v = .same then b else π k x`. `veq_pin` proves that a
 * `q0` with `q0 v = b` equals its own pin, so the row at `π k := q0` is the former theorem at `q0`.
 */
export const readVerdictRows = (
    verdicts: readonly ReadVerdict[],
): RowFile<'admits'> => ({
    forms: { admits: evaluationForms.admits },
    rows: (shapes) =>
        verdicts.map((one) => {
            const { decodes, pin } = readVerdictOf(one)
            const t = shapes.row((fn, made) =>
                pin !== undefined && fn === pin.is
                    ? `(fun x => if veq ${pin.fuel} x (${pin.v}) = .same then ${pin.answer} else ${made} x)`
                    : made,
            )(one.codec, one.name)
            return {
                name: leanIdent(one.name),
                form: 'admits' as const,
                row: `(${t}, ${leanAttrOf(one.attribute, one.name)}, ${decodes})`,
            }
        }),
})

/** The read verdicts in the row form. Generated at gate time, never committed. */
export const leanReadRowModule = (verdicts: readonly ReadVerdict[]): string =>
    leanCorpusRowModule(
        `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.ExactA
import Calculus.Dynamo.Lang.Store`,
        "Read verdicts, proposed to the model's read row",
        `One row per (codec, attribute) pair: \`AdmA t a\` equals whether
\`src/\`'s \`decode\` accepted it. All ${verdicts.length} pairs are asserted here. A caller's predicate is
\`π k\`, pinned at the value that the inner term reads where the host answered the predicate there.
\`veq_pin\` proves that a predicate with that answer equals its own pin, so the row at
\`π k := q0\` states the former theorem at each such \`q0\`.`,
        readVerdictRows(verdicts),
    )

/**
 * The legacy reads as rows. The older reader is `ρ k`, pinned at each attribute that `src/` asked
 * it, as {@link leanLegacyRead} pins the variable of the former theorem.
 */
export const legacyReadRows = (
    reads: readonly LegacyRead[],
): RowFile<'reads' | 'readsNothing'> => ({
    forms: {
        reads: evaluationForms.reads,
        readsNothing: evaluationForms.readsNothing,
    },
    rows: (shapes) =>
        reads.map((one) => {
            const { read, pins } = legacyReadOf(one)
            const t = shapes.row((fn, made) => pinText(pins.get(fn), made))(
                one.codec,
                one.name,
            )
            const a = leanAttrOf(one.attribute, one.name)
            return failed(read)
                ? {
                      name: leanIdent(one.name),
                      form: 'readsNothing' as const,
                      row: `(${t}, ${a})`,
                  }
                : {
                      name: leanIdent(one.name),
                      form: 'reads' as const,
                      row: `(${fuelForValue(read)}, ${t}, ${a}, ${leanValueOf(read, one.name)})`,
                  }
        }),
})

/** The legacy reads in the row form. Generated at gate time, never committed. */
export const leanLegacyReadRowModule = (reads: readonly LegacyRead[]): string =>
    leanCorpusRowModule(
        `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store`,
        'The legacy read gate, model against library',
        `One row per (codec, attribute) pair, ${reads.length} in all. Each older
reader is \`ρ k\`, pinned at each attribute that \`src/\` asked it. The model reads the older answer
only where the current term writes the answer, and \`src/\` checks the same.`,
        legacyReadRows(reads),
    )

/** The sentinel that the gate reads: the only line of a clean run of the corpus pre-check. */
export const corpusSentinel = (count: number): string =>
    `corpus: ${count} vectors checked`

/**
 * **The pre-check of the corpus**: the rows of the six corpus files, at one instance of each caller
 * function, each row with the name of its former theorem. An `#eval` runs the check of each row,
 * and prints the name where the check fails. A printed line proves nothing: the kernel rows are the
 * check, and this file names the vector that a failing list holds.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanCorpusEval = (files: readonly RowFile[]): string => {
    const shapes = leanShapes((kind) =>
        kind === 'closure' ? '(fun _ => true)' : '(fun _ => none)',
    )
    let count = 0
    const lists = files
        .flatMap((file) => {
            const lists = rowLists(file, shapes)
            for (const { rows } of lists) count += rows.length
            return lists.map(({ form, rows }) => ({
                ...file.forms[form],
                rows,
            }))
        })
        .map(
            (
                { type, check, rows },
                i,
            ) => `def rows${i} : List (String × ${type}) := [
  ${rows.map((one) => `(${leanString(one.name)}, ${one.row})`).join(',\n  ')}]

#eval rows${i}.forM fun (nm, p) => unless (${check}) do IO.println s!"mismatch {nm}"`,
        )
    return leanNumeralsOnce(`import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.Compat
import Calculus.Dynamo.Analysis.ExactA
import Calculus.Dynamo.Lang.Store

/-!
# The pre-check of the corpus

**Generated — do not edit.** The rows of the six corpus files, at one instance of each caller
function, each with the name of its former theorem. A row prints only a mismatch, with the name. One
\`#eval\` runs each list of rows, and the last line counts the rows.
-/

set_option maxRecDepth 8192
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists.join('\n\n')}

#eval IO.println ${leanString(corpusSentinel(count))}

end Calculus
`)
}
