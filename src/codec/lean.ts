/**
 * Test vectors for the Lean model, emitted as Lean source.
 *
 * `formal/` is a mechanization of the codec calculus; this library is what it is supposed to
 * certify. The correspondence between the two is a *paper* obligation — somebody reads `Closed.meaning`
 * and reads `src/codec/codec.ts` and believes they agree — and no instrument closes it, which is
 * the third of the three warranties `docs/architecture.md` keeps apart. This module is the
 * machine-checkable half of that belief.
 *
 * ── why the traffic goes this way ───────────────────────────────────────────────────────────────
 *
 * The obvious design is the other one: let Lean produce the expected attribute and compare it here.
 * `#eval` runs `Closed.meaning`, so Lean can produce it, but a printed value certifies nothing, and
 * `native_decide` adds an axiom of its own for each proof, outside the model's axiom base. The model declares no
 * axiom: `N` is carried exactly, as `WFNumeral`.
 *
 * What Lean *can* do is check. `(Closed.meaning α t).e v = some a` is a closed proposition, and for every
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
 * the bridge. See {@link leanTermCore}. A JS number is one of them: it is a binary64 float, and
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
import type {
    AnyCodec,
    ClausePattern,
    Itemable,
    LiteralValue,
    ObjectSlot,
    Precondition,
    Refinement,
} from './codec'
import {
    at,
    clauseOf,
    exclude,
    extract,
    item as itemOf,
    narrow,
    object,
    optional,
    preconditions as preconditionsOf,
    type Segment,
    union,
} from './codec'
import { accepts, assignmentOf, codecOfTerm, readsBack } from './denote'
import { CodecError, failed, type Result } from './result'
import {
    agrees,
    agreesApart,
    disjoint,
    type FlatScope,
    flatOf,
    sharedFlatOf,
    storedApart,
    viewsDisjoint,
} from './scoped'
import type {
    Alternatives,
    Body,
    Literal,
    Term,
    Field as TermField,
} from './term'
import {
    clauseForm,
    componentsOf,
    entryOrder,
    mapChildren,
    openRefusal,
    recursionUse,
    storedAlternatives,
    targetOf,
    throughRefs,
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
const leanString = (value: string): string => {
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
            'an empty wire set — the attribute domain types SS/NS/BS as ℘⁺fin, so `NEFinset` has no empty inhabitant',
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

/** A byte string, as the `List UInt8` that the attribute domain calls `Bytes`. */
const leanBytes = (bytes: Uint8Array): string =>
    `[${Array.from(bytes).join(', ')}]`

/* ── values ──────────────────────────────────────────────────────────────────────────────── */

const isRecord = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value)

/**
 * A `Value` — the value language, as the `e` of `Closed.meaning` consumes it.
 *
 * Directed by the *value*, not by the codec, which is sound because a value and the
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
        // the `optional` of a field is about presence, and emitting `null` would test a different vector
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

/** A numeral, with its well-formedness discharged by `by decide` where it is written. */
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
const leanNumeralsOnce = (module: string): string => {
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
 * **A module checks the axioms of the theorems that the module declares.** No module imports a
 * generated file, so `#assert_axioms_all` reads no vector. The last command of each module checks
 * each theorem of the module against the sanctioned base, and prints nothing when each passes.
 * Apply this once to a whole module, after {@link leanNumeralsOnce}.
 */
const leanModule = (module: string): string =>
    `${leanNumeralsOnce(module)}\n#assert_axioms_module\n`

/**
 * An `Attr` — the attribute domain, one member per attribute.
 *
 * `N` carries `WFNumeral`, a subtype, so `WFNumeral.of` runs the numeral grammar at elaboration time with
 * its `by decide` default argument. A numeral this library will happily write but the grammar refuses does
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

/** The position of the printer, and the functions that the theorem binds where the vector is quantified. */
type At = {
    readonly bound?: Bound
    readonly placed: Placed
}

/** **One entry of a closed codec**: its index in the one scope of the codec. */
type Entry = {
    readonly index: number
}

/**
 * **Where the scoped printer is**: the entries of the closed codec, the entry that it prints,
 * whether it prints the top of the entry, and whether the position is a child of a container, below
 * a guard, or below a wall.
 */
type Placed = {
    /** A closed codec: one ordered scope. A graph: one flat system, with no order on its entries. */
    readonly form: 'closed' | 'graph'
    /** The entries that a position above every guard names. */
    readonly entries: ReadonlyMap<Term, Entry>
    /** The entry of each child of a container, in a closed codec. */
    readonly children: ReadonlyMap<Term, Entry>
    readonly index: number
    readonly top: boolean
    /** The position is a child of a container. */
    readonly down: boolean
    readonly guarded: boolean
    readonly wall: boolean
}

/**
 * The namespace of the builders: the scoped builders where the printer prints a closed codec, and
 * the flat builders where it prints a graph or a closed term below a wall.
 */
const pre = (scope: At): string =>
    scope.placed.form === 'graph' || scope.placed.wall
        ? 'Scoped.Graph.'
        : 'Scoped.'

/** The position below a container, which is a guard, or below a wall. */
const below = (scope: At, kind: 'guard' | 'wall'): At => ({
    ...scope,
    placed: {
        ...scope.placed,
        down: kind === 'guard',
        guarded: scope.placed.guarded || kind === 'guard',
        wall: scope.placed.wall || kind === 'wall',
    },
})

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
 * **A closed codec** — the codec as one flat scope, for the families whose analysis reads only the
 * meaning.
 *
 * The entries of the scope are the entries of {@link flatOf}: the entries of each cycle of the term
 * graph, cycle by cycle in the order of {@link componentsOf}, then the root where no cycle holds it,
 * then each child of a container. A cycle comes after each cycle that it reaches, and the entries of
 * a cycle are in the order of {@link entryOrder}. So an entry reads an entry of an earlier cycle
 * above every guard, and the scope needs no constant. A child of a container prints as the index of
 * its entry, and a term below a wall prints as a closed graph term. The top of each entry states its
 * indices, because the elaborator needs them before it reads a list of options. A term with no
 * scoped form, an unguarded cycle, a wall that reaches a cycle, or an open fragment, is refused,
 * with the reason.
 */
export const leanClosedOf = (
    declared: ObjectSlot,
    at = 'codec',
    bound?: Bound,
): string => {
    const def = declared.def
    if ('mark' in def) {
        return refuse(
            at,
            'a *field*, not a term — `optional`/`fallback` denote `Field`, and no `Term` position accepts one',
        )
    }
    return leanClosedOfTerm(def, at, bound)
}

/** The closed codec of a term, as {@link leanClosedOf} prints it. */
export const leanClosedOfTerm = (
    def: Term,
    at: string,
    bound?: Bound,
): string => closedPrint(def, at, bound).text

/**
 * A printed closed codec, with the entry of each term that prints as an entry: an entry is its index
 * in the scope, and the root is the entry of the term. `entries` holds the entries that a position
 * above every guard names, and `children` the entry of each child of a container.
 */
type ClosedPrint = {
    readonly text: string
    readonly entries: ReadonlyMap<Term, Entry>
    readonly children: ReadonlyMap<Term, Entry>
    readonly root: number
}

/**
 * The print of {@link leanClosedOfTerm}: the flat scope of the host ({@link flatOf}). The last arm
 * refutes each index past the entries, because the elaborator does not find the match on `Fin n`
 * exhaustive from sixteen literal arms up.
 */
const closedPrint = (def: Term, at: string, bound?: Bound): ClosedPrint => {
    const flat = flatOf(def)
    if (flat.kind === 'refused') return refuse(at, flat.reason)
    const { scope, entries, children } = scopePrint(flat, at, bound)
    return {
        text: `(⟨${scope}, ${flat.root}⟩ : Closed)`,
        entries,
        children,
        root: flat.root,
    }
}

/**
 * **Two options of one scope**, the model's `Closed.Shared`: the entries of the flat scope that holds
 * both options ({@link sharedFlatOf}), and the two roots. A node that both options hold prints once.
 */
const leanSharedOf = (
    left: AnyCodec,
    right: AnyCodec,
    at: string,
    bound?: Bound,
): string => {
    const flat = sharedFlatOf(left.def, right.def)
    if (flat.kind === 'refused') return refuse(at, flat.reason)
    return `(⟨${scopePrint(flat, at, bound).scope}, ${flat.root}, ${flat.other}⟩ : Closed.Shared)`
}

/** The scope of a flat scope as the model's `Closed` reads it: the count of the entries, then the bodies. */
const scopePrint = (flat: FlatScope, at: string, bound?: Bound) => {
    const entryMap = (m: ReadonlyMap<Term, number>) =>
        new Map<Term, Entry>([...m].map(([t, index]) => [t, { index }]))
    const entries = entryMap(flat.cycles)
    const children = entryMap(flat.index)
    const arms = flat.bodies
        .map((t, index) => {
            const body = leanTermOfTerm(t, at, {
                bound,
                placed: {
                    form: 'closed',
                    entries,
                    children,
                    index,
                    top: true,
                    down: false,
                    guarded: false,
                    wall: false,
                },
            })
            return `| ⟨${index}, _⟩ => (${body} : Scoped.Term ${flat.bodies.length} ${index})`
        })
        .join(' ')
    return {
        scope: `${flat.bodies.length}, (fun i => match i with ${arms} | ⟨_ + ${flat.bodies.length}, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left _ _)))`,
        entries,
        children,
    }
}

/**
 * **The graph of a codec** — one flat system over the term container, for the guard rows. Each cycle
 * point of the term graph is an entry: each entry of each cycle, a `ref` of a cycle of `ref`s, and
 * the root. The graph has no order on its entries, so it prints a codec that has no scoped form as
 * well, and the graph guard decides it.
 */
export const leanGraphOf = (
    declared: ObjectSlot,
    at = 'codec',
    bound?: Bound,
): string => {
    const def = declared.def
    if ('mark' in def) {
        return refuse(
            at,
            'a *field*, not a term — `optional`/`fallback` denote `Field`, and no `Term` position accepts one',
        )
    }
    return leanGraphOfTerm(def, at, bound)
}

/** The graph of a term, as {@link leanGraphOf} prints it. */
const leanGraphOfTerm = (def: Term, at: string, bound?: Bound): string => {
    const points: Term[] = []
    for (const { members, keys } of componentsOf([def])) {
        const [first] = members
        if (keys.size > 0) points.push(...keys.keys())
        else if (first !== undefined) points.push(first)
    }
    if (!points.includes(def)) points.push(def)
    const entries = new Map<Term, Entry>(
        points.map((t, index) => [t, { index }]),
    )
    const arms = points
        .map((t, index) => {
            const body = leanTermOfTerm(t, at, {
                bound,
                placed: {
                    form: 'graph',
                    entries,
                    children: entries,
                    index,
                    top: true,
                    down: false,
                    guarded: false,
                    wall: false,
                },
            })
            return `| ⟨${index}, _⟩ => (${body} : Scoped.Graph.Term ${points.length})`
        })
        .join(' ')
    return `(⟨${points.length}, fun i => match i with ${arms}⟩ : Graph)`
}

/** The meaning of a closed codec at the library table, as a vector reads it. */
const leanMeaningOf = (
    declared: ObjectSlot,
    at: string,
    bound?: Bound,
): string =>
    `(Closed.meaning (libTable noCallers) ${leanClosedOf(declared, at, bound)})`

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
 * The rule `(refine)`'s predicate, as the model's `Pred.closure`.
 *
 * The predicate comes back parenthesised, because it is an application and `Term.refine` takes its
 * second argument juxtaposed.
 *
 * A closure is a caller's JavaScript function; the registry below recognises two of them **by
 * reference**, and everything else is refused. `refine` still carries an arbitrary predicate.
 */
const leanPredicate = (q: Refinement, at: string, bound?: Bound): string => {
    // recognised by reference against the function this package exported, so a rename or a
    // reimplementation of the predicate is a type error here rather than a silent misemission
    const known = shippedPredicates.get(q.is)
    // a caller's closure in a quantified vector is a variable of the theorem
    if (!known && bound)
        return bound.standIn
            ? '(Pred.closure (fun _ => true))'
            : `(Pred.closure ${boundName(bound.closures, q.is, 'q')})`
    if (!known) {
        return refuse(
            at,
            `\`Pred.closure\` carries \`q : Value → Bool\`, and this predicate is not one this library ships: it is the caller's closure for ${JSON.stringify(q.what)}, a JS closure. A quantified verdict binds it as a variable, and no evaluation vector prints one. The model names two predicates that this library ships, \`isNumeral\` and \`isStoredNumeral\` from \`src/codec/attribute.ts\`, passed by reference`,
        )
    }
    return `(Pred.closure ${known.lean})`
}

/**
 * The object payload, as the model's `Body.mk`.
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
    return `(${pre(scope)}Body.mk ${leanFinset(names)} (${fields}) ${restTerm})`
}

const leanTermOfTerm = (t: Term, at: string, scope: At): string =>
    leanPlaced(t, at, scope, scope.placed)

/**
 * **A term of a closed codec.** A child of a container prints as the index of its entry. Above every
 * guard an entry of a cycle prints as `ref` of an earlier entry. Below a wall the term names no
 * entry, and prints as a closed graph term. Each other term prints in place.
 */
const leanPlaced = (t: Term, at: string, scope: At, placed: Placed): string => {
    if (placed.form === 'closed' && placed.down && !placed.wall) {
        const child = placed.children.get(t)
        if (child !== undefined) return `${child.index}`
        if (t.kind !== 'ref')
            throw new Error(
                'the flat scope holds no entry for a child of a container: flatOf missed the child',
            )
        const target = targetOf(t)
        if (target === undefined)
            return refuse(
                at,
                'an open fragment: a thunk names a codec not yet declared, so the term has no scoped form',
            )
        return leanPlaced(target, at, scope, placed)
    }
    const entry = placed.entries.get(t)
    if (entry !== undefined && !placed.top && placed.form === 'graph')
        return `Scoped.Graph.Term.ref ${entry.index}`
    if (entry !== undefined && !placed.top) {
        if (placed.wall)
            return refuse(
                at,
                'a wall reaches a cycle: a wall reads its term at any depth, so the term has no scoped form',
            )
        if (!placed.guarded && entry.index >= placed.index)
            return refuse(
                at,
                'an unguarded cycle: an entry reads its own input above every guard, so the term has no scoped form',
            )
        return `Scoped.Term.ref ${entry.index}`
    }
    return leanTermCore(t, at, {
        ...scope,
        placed: { ...placed, top: false, down: false },
    })
}

/**
 * A term of a closed codec or of a graph, from what the codec says it is.
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
 * - **A `ref` that no scope binds.** The `ref` names a codec not yet declared, so the term is an
 *   open fragment and has no scoped form.
 *
 * `Rest.drop` vs `Rest.refuse` used to be a fourth entry here: `Def` recorded the rest *codec*
 * and nothing when the policy was a string, so this wrote `Rest.drop` for either. It was sound for
 * the vectors this module writes and only for them — `objectCodec`'s `e` is `objWrite`, which takes
 * `rc?` and not the `kn` filter, and `rcOf` is `none` for both policies, so the two denote the
 * same `e` and differ only under `p`. A decode-direction
 * vector would have needed them apart and would have been silently wrong. The `attributes` term
 * carries the policy now rather than only its codec, and this emits all three.
 */
const leanTermCore = (t: Term, at: string, scope: At): string => {
    switch (t.kind) {
        case 'string':
            return `${pre(scope)}Term.string`
        case 'boolean':
            return `${pre(scope)}Term.boolean`
        case 'binary':
            return `${pre(scope)}Term.binary`
        case 'null':
            return `${pre(scope)}Term.null`
        /**
         * **Emittable, and it took refusal vectors to see that.** `Term.number` is a closed term.
         * A `Value.num` is a closed term too, over a `WFNumeral`. What {@link leanValueOf} refuses
         * is a JS number, which is a float, and this row used to refuse on its behalf one level
         * too early.
         */
        case 'number':
            return `${pre(scope)}Term.number`
        case 'literal':
            return `${pre(scope)}Term.literal ${leanLiteral(t)}`
        /** `Term.set` takes its element term, as the host term does. */
        case 'set':
            return `${pre(scope)}Term.set (${leanTermOfTerm(t.elem, `${at}.elem`, below(scope, 'guard'))})`
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
            const inner = below(scope, 'guard')
            const positions = (
                ts: readonly Term[],
                part: (index: number) => string,
            ) =>
                ts
                    .map((element, index) =>
                        leanTermOfTerm(element, part(index), inner),
                    )
                    .join(', ')
            const spread = t.spread
            if (t.suf.length === 0) {
                if (t.pre.length === 0 && spread)
                    return `${pre(scope)}Term.array (${leanTermOfTerm(spread, `${at}.element`, inner)})`
                const tail = spread
                    ? `(some (${leanTermOfTerm(spread, `${at}.tail`, inner)}))`
                    : 'none'
                return `${pre(scope)}Term.tuple [${positions(t.pre, (index) => `${at}[${index}]`)}] ${tail}`
            }
            const middle = spread
                ? `(some (${leanTermOfTerm(spread, `${at}.spread`, inner)}))`
                : 'none'
            return `${pre(scope)}Term.list [${positions(t.pre, (index) => `${at}[${index}]`)}] ${middle} [${positions(t.suf, (index) => `${at}.suffix[${index}]`)}]`
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
            return `${pre(scope)}Term.object ${leanBodyOf(t.body, at, below(scope, 'guard'))}`
        }
        case 'never':
            return `${pre(scope)}Term.never`
        case 'union':
            return `${pre(scope)}Term.union [${t.options
                .map((variant, index) =>
                    leanTermOfTerm(variant, `${at}[${index}]`, scope),
                )
                .join(', ')}]`
        // The model's `opaq` is the exact codec: its number option is `numberCodec`, so it is this
        // total term. The two policies are `held` over this term, and the `held` row refuses them
        case 'opaq':
            return `${pre(scope)}Term.opaq`
        // a `ref` prints its target, and an entry prints as its reference. A `ref` with no target
        // names a codec not yet declared, so the term is an open fragment
        case 'ref': {
            const target = targetOf(t)
            if (target === undefined)
                return refuse(
                    at,
                    'an open fragment: a thunk names a codec not yet declared, so the term has no scoped form',
                )
            return leanTermOfTerm(target, `${at}.inner`, scope)
        }
        /**
         * The rule `(refine)`. The predicate is printed by {@link leanPredicate}, and the side condition
         * below applies to a **shipped closure** only. A caller's closure in a quantified vector
         * is a variable, and the claim holds at every function, so no coercion can part the two.
         *
         * `writesOnlyStrings` exists because the two shipped predicates take a `string` and a
         * `Value → Bool` takes anything: they disagree where JavaScript coerces, so the emission is
         * confined to inner terms that write nowhere else.
         */
        case 'refine': {
            const q = leanPredicate(t.q, at, scope.bound)
            if (shippedPredicates.has(t.q.is) && !writesOnlyStrings(t.inner)) {
                return refuse(
                    at,
                    `${shippedPredicates.get(t.q.is)?.what ?? 'this predicate'} decides a *string*, and this refinement's inner term writes values that are not strings — where JavaScript would coerce and the model would not, so the two predicates would part company`,
                )
            }
            // the stored predicate is the top of the store universe: the truth, which is `()`
            return `${pre(scope)}Term.refine (${leanTermOfTerm(t.inner, `${at}.inner`, scope)}) ${q} ()`
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
                return `(${pre(scope)}Term.held false (${leanTermOfTerm(t.inner, at, below(scope, 'wall'))}) (${leanTermOfTerm(t.outer, at, below(scope, 'wall'))}) (.caller ${boundName(scope.bound.adapters, t.via ?? t.f, '')}, false) [])`
            return t.via === 'decimalText'
                ? `(${pre(scope)}Term.held false (${leanTermOfTerm(t.inner, at, below(scope, 'wall'))}) (${leanTermOfTerm(t.outer, at, below(scope, 'wall'))}) (.decimalText, false) [])`
                : refuse(
                      at,
                      "`Term.held` carries a word of adapter generators, and a table gives each generator two `Value → Value` functions: a quantified verdict binds an adapter that the model does not name as a generator `caller n`, and no evaluation vector prints one. An evaluation vector would have to run the adapter: a caller's closure has no name in the model, and a float adapter's content is binary64 rounding, the host axiom this development deleted. The model names one generator that this library ships, `decimalText`, whose pair is `numeralOfStoredText`/`textOfNumeral`",
                  )
        // the older reader is caller code: a quantified verdict binds it as a variable, and an
        // evaluation vector would have to run it
        case 'legacy':
            return scope.bound
                ? `(${pre(scope)}Term.legacy (${leanTermOfTerm(t.inner, at, below(scope, 'wall'))}) ${scope.bound.standIn ? '(fun _ => none)' : pinned(scope.bound, t.r)})`
                : refuse(
                      at,
                      '`Term.legacy` carries `r : Attr → Option Value`, a JS closure: a quantified verdict binds it as a variable, and no evaluation vector prints one',
                  )
    }
}

/**
 * An `ObjectSlot` — the field stratum, which is a *position* in a map and not a codec.
 *
 * **The slot has three constructors.** A name is required, optional, or filled: a fill is required
 * on the write and reads an absent name as its stand-in. The presence lattice reads the rest.
 */
const leanSlotOf = (field: TermField, at: string, scope: At): string => {
    switch (field.mark) {
        case 'optional':
            return `${pre(scope)}ObjectSlot.optional (${leanTermOfTerm(field.t, at, scope)})`
        /**
         * `ObjectSlot.fill`: the stand-in is data, so it prints as a `Value`. An older reader of a
         * present value stays in the term, as `Term.legacy`.
         */
        case 'fallback':
            return `${pre(scope)}ObjectSlot.fill (${leanTermOfTerm(field.t, at, scope)}) (${leanValueOf(field.v, at)})`
        case 'req':
            return `${pre(scope)}ObjectSlot.req (${leanTermOfTerm(field.t, at, scope)})`
        /**
         * `ObjectSlot.optional`, because that is what it denotes rather than an approximation of
         * it.
         *
         * `Value` has no `undefined` and `Value.map` is a key set with a total function on it, so
         * `{ k: undefined }` and `{}` are one `Value` and there is no second thing to mean. The
         * quotient that rests on is {@link leanValueOf}'s, which was already there for `optional`.
         */
        case 'undefinable':
            return `${pre(scope)}ObjectSlot.optional (${leanTermOfTerm(field.t, at, scope)})`
    }
}

/* ── vectors ─────────────────────────────────────────────────────────────────────────────── */

/**
 * How a vector states its claim to the kernel.
 *
 * `'check'` writes `check n ((Closed.meaning α t).e v) (some a) = .same := kernel_rfl%` and is the default. It
 * depends on `Calculus/Bridge/Vectors.lean` — a fuelled three-valued comparator with `check_same` and
 * `check_differ` proved about it, so a passing line cashes to `(Closed.meaning α t).e v = some a` as a
 * theorem. No tactic, no `funext` gymnastics, an order of magnitude faster on maps, and it can
 * state a **negative** vector (`= .differ`), which an equation cannot. The `n` is fuel, because
 * only structural recursion reduces in the kernel; {@link leanVector} computes it from the
 * attribute, and under-fuelling reduces to `.exhausted`, which matches neither side and fails the
 * build rather than passing quietly.
 *
 * `'equation'` writes `(Closed.meaning α t).e v = some a` and proves it with a tactic the generated file
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
    const meaning = leanMeaningOf(codec, name)
    const attribute = codec.unsafeEncode(value as never)
    const head = [`/-- \`${name}\` -/`, `theorem ${leanIdent(name)} :`]
    const guard = recursive(codec)
        ? `\n\n${leanGuard({ name: `${name}__guarded`, codec, guarded: true })}`
        : ''
    const vector =
        protocol === 'equation'
            ? [
                  ...head,
                  `    ${meaning}.e`,
                  `      (${leanValueOf(value, name)})`,
                  `    = some (${leanAttrOf(attribute, name)}) := by`,
                  '  vector',
              ].join('\n')
            : [
                  ...head,
                  `    check ${fuelFor(attribute)}`,
                  `      (${meaning}.e`,
                  `        (${leanValueOf(value, name)}))`,
                  `      (some (${leanAttrOf(attribute, name)})) = .same := kernel_rfl%`,
              ].join('\n')
    return `${vector}${guard}`
}

/** A recursive codec that the library wrote through is a codec that the guard accepts. */
const recursive = (codec: AnyCodec): boolean =>
    !('mark' in codec.def) && componentsOf([codec.def]).length > 0

/**
 * **A guard verdict**: whether the graph guard accepts the graph of a codec (`Graph.guarded`).
 * A recursive schema below a list or an object is guarded. A `ref` that names its own term reads
 * its own input, and the guard refuses it: the graph has no stratified form.
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
        `    (${leanGraphOf(codec, name)}).guarded = ${guarded} := kernel_rfl%`,
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
 * **And it reaches `number`**: `Term.number` is a closed term, so at its closed codec `t`,
 * `(Closed.meaning α t).e (Value.str "x") = none` is `rfl`. A numeric `literal` is closed too, its
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
        `    ${leanMeaningOf(codec, name)}.e`,
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
 * - `src/` **accepts** the pair: the pair prints as two closed codecs, and a closed codec exists
 *   only for a codec that the model's guard accepts. Where {@link agrees} holds, the host decided
 *   the model's `Closed.compatPair`, and `Closed.compat_of_compatPair` gives `Compat` in each
 *   order over two lawful meanings. A host warrant that the model does not prove stops the file.
 * - `src/` **accepts** two options that share a node, where two scopes refuse the pair: the two
 *   options sit in one term, so {@link agrees} reads one scope that holds both. The pair prints as
 *   one scope with two roots, and the model's `Closed.Shared.compatPair` decides the pair over one
 *   scope. `Closed.Shared.compat_of_compatPair` gives `Compat` in each order over two lawful
 *   meanings. A pair that two scopes accept prints as two closed codecs, so a spelling that makes
 *   two terms of one codec prints the same row.
 * - `src/` **refuses** the pair at its compatibility test: the pair prints as two closed codecs,
 *   and the model's decision refuses the pair, `Closed.compatPair x y = false`. A decision that
 *   starts to accept a pair `src/` turns down stops the file.
 * - `src/` **refuses** the pair **at the guard**: an option reads the input of its own binder, or
 *   holds an adapter on a recursive path. The pair prints as two graphs, and the graph guard must
 *   refuse a graph too.
 *
 * A union over a `ref` that no scope binds is an open fragment: the scope that binds the name
 * decides it, so such a pair holds no decision of the host, and the emitter refuses the pair.
 *
 * Compatibility is not decidable, so a refused pair carries no theorem that it is incompatible:
 * `Closed.not_compat_flip` and `Closed.not_compat_shout` are the model's witnesses of that class.
 */
export type Separation = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly left: AnyCodec
    readonly right: AnyCodec
}

/**
 * **The form of a separation verdict**: accepted, accepted over one scope, refused at compatibility, or
 * refused at the guard.
 * The host's guard runs before its compatibility test, and reads each option on its own. The
 * emitter refuses a pair that the host accepts on no warrant that the model proves.
 *
 * **The form reads each host answer that a row states.** A row of a form states the guard and the
 * compatibility of the pair, so the host's union decision, its guard (`recursionUse`) and its
 * compatibility test (`agrees`) each decide the form. Where the union decision disagrees with the
 * guard or with `agrees`, no form states the host, and the emitter refuses the pair. Otherwise a row
 * checks the union decision alone, and a guard or `agrees` that drifts from the decision passes.
 */
type SeparationForm = 'accepted' | 'acceptedShared' | 'refused' | 'guardRefused'

/** The form of one separation verdict, with the `src/` side decided here. */
const separationForm = ({ name, left, right }: Separation): SeparationForm => {
    const guarded = [left, right].every(
        (option) => recursionUse(option.def) < 2,
    )
    let declared: AnyCodec | undefined
    try {
        declared = union([left, right] as never)
    } catch {
        declared = undefined
    }
    // the union of an open fragment decides at the scope that binds each name, so the pair holds
    // no decision of the host
    if (declared !== undefined && openRefusal(declared.def) !== undefined) {
        return refuse(
            name,
            'the union reads a `ref` that no scope binds, so the host decides the pair at the scope',
        )
    }
    if (declared === undefined) {
        if (!guarded) return 'guardRefused'
        return agrees(left.def, right.def)
            ? refuse(
                  name,
                  '`src/` refuses this pair at compatibility, and `agrees` accepts it: no form states the host',
              )
            : 'refused'
    }
    if (!guarded) {
        return refuse(
            name,
            '`src/` accepts this pair, and its guard refuses an option: no form states the host',
        )
    }
    if (agreesApart(left.def, right.def)) return 'accepted'
    // two options that share a node are one scope, and the decision over one scope accepts where
    // two scopes refuse
    return agrees(left.def, right.def)
        ? 'acceptedShared'
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
    const form = separationForm({ name, left, right })
    // a pair that the guard refuses has no closed codec, so it prints as two graphs
    const print = form === 'guardRefused' ? leanGraphOf : leanClosedOf
    // two options of one scope print as one closed scope with two roots, which `l` holds
    const shared = form === 'acceptedShared'
    const l = shared
        ? leanSharedOf(left, right, name, bound)
        : print(left, name, bound)
    const r = shared ? '' : print(right, name, bound)
    const binders = leanBinders(bound)
    const head = `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`}`
    const reduce = closing(binders)
    if (form === 'guardRefused') {
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair at the guard; the graph guard refuses a graph too -/`,
            `${head} :`,
            `    ((${l}).guarded &&`,
            `      (${r}).guarded) = false :=`,
            `  ${reduce}`,
        ].join('\n')
    }
    // the host's guard accepted before its compatibility test refused, and a closed codec states the guard
    if (form === 'refused') {
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair; the model's decision refuses it -/`,
            `${head} :`,
            `    Closed.compatPair (${l})`,
            `      (${r}) = false :=`,
            `  ${reduce}`,
        ].join('\n')
    }
    // two options that share a node are one scope, and the decision over one scope states the pair
    if (form === 'acceptedShared') {
        return [
            `/-- \`${name}\` — \`src/\` accepts two options of one scope; the model proves them compatible -/`,
            `${head} (κ : Callers) :`,
            `    let s := ${l}`,
            `    Lawful (s.meaning (libTable κ) s.left) → Lawful (s.meaning (libTable κ) s.right) →`,
            `      Alg.Compat (s.meaning (libTable κ) s.left) (s.meaning (libTable κ) s.right) ∧`,
            `        Alg.Compat (s.meaning (libTable κ) s.right) (s.meaning (libTable κ) s.left) :=`,
            `  Closed.Shared.compat_of_compatPair (${reduce}) (libTable κ)`,
        ].join('\n')
    }
    // the host's union verdict is the guard and the compatibility test, and a closed codec states the guard
    return [
        `/-- \`${name}\` — \`src/\` accepts this pair; the model proves it compatible -/`,
        `${head} (κ : Callers) :`,
        `    Lawful ((${l}).meaning (libTable κ)) → Lawful ((${r}).meaning (libTable κ)) →`,
        `      Alg.Compat ((${l}).meaning (libTable κ)) ((${r}).meaning (libTable κ)) ∧`,
        `        Alg.Compat ((${r}).meaning (libTable κ)) ((${l}).meaning (libTable κ)) :=`,
        `  Closed.compat_of_compatPair (${reduce}) (libTable κ)`,
    ].join('\n')
}

/**
 * **A guard verdict on a term that a former refused.** Each former refuses a term where the host's
 * guard reads a recursion at its own input or an adapter on a recursive path, and the refusal
 * carries the term. No union reads such a term, so no {@link Separation} states the model's guard
 * on the term. This vector states the guard half of a separation on the term alone: the model's
 * guard refuses the term too.
 */
export type FormerGuard = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly term: Term
}

/** One guard verdict on a refused term, as a Lean `theorem`, with the `src/` side decided here. */
export const leanFormerGuard = ({ name, term }: FormerGuard): string => {
    // a `ref` in the term can name a codec that is declared now, and the host's guard then reads
    // the term again with another answer. A vector about a term that the host accepts asserts a
    // refusal that the host does not make
    if (recursionUse(term) < 2) {
        return refuse(
            name,
            "the host's guard accepts this term now, so a vector that the model's guard refuses it states no host refusal",
        )
    }
    // a caller's function is a variable of the theorem; the guard reads the graph and no function
    const bound: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    const printed = leanGraphOfTerm(term, name, bound)
    const binders = leanBinders(bound)
    return [
        `/-- \`${name}\` — a former refuses this term; the graph guard refuses its graph too -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        `    ${printed}.guarded = false :=`,
        `  ${closing(binders)}`,
    ].join('\n')
}

/**
 * The guard verdicts on refused terms as a module of their own. A verdict spells the graph of a
 * term and its guard, which `Bridge.Vectors` reaches. The header imports `Store` as well.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanFormerGuardModule = (guards: readonly FormerGuard[]): string =>
    leanModule(`import Calculus.Bridge.Vectors
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
 * read side a decision through a port of `Closed.AdmA`.
 * Measured
 * first: over 864 (codec, attribute) pairs the two agree at **861 of 861 checkable** ones and
 * disagree at none. `decode` validates — it parses data somebody else wrote, which is its job —
 * where `encode` trusted its argument's *type*, and that asymmetry is the whole reason wiring
 * `admits` into the write side changed real answers and a read-side port would change none. So a
 * def-reading port would be a second description of what `decode` already computes exactly, and
 * two descriptions of one thing need a guard between them. **The guard is what landed.**
 *
 * `#eval` runs `Closed.AdmA`, but a printed verdict proves nothing. The kernel unfolds it, which is the
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
 * both ways, at every pair: `Calculus.Closed.disjoint` and {@link disjoint} are the *same
 * function* stated twice over one graph, so a disagreement in either direction is a defect on one
 * side. Each side prints as a closed codec, so a term with no scoped form has no pair to state. The
 * test of the raw terms and the test of the two pairs of views are asserted apart, because the
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
            'a *field*, not a term — no `Term` position accepts one, so the test has no pair to state',
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
    const l = leanClosedOf(left, name, bound)
    const r = leanClosedOf(right, name, bound)
    const binders = leanBinders(bound)
    return [
        `/-- \`${name}\` — the answers \`src/\` computes, put to the model -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        `    Closed.disjoint (${l})`,
        `        (${r}) = ${disjointly} ∧`,
        `      Closed.viewsDisjoint (${l})`,
        `        (${r}) = ${views} := ⟨${closing(binders)}, ${closing(binders)}⟩`,
    ].join('\n')
}

/* ── the row form ──────────────────────────────────────────────────────────────────────────── */

/** The two terms that the tests and the guard read, as a row prints them. */
export type RowTerms = {
    readonly l: string
    readonly r: string
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
    readonly pair: (
        left: AnyCodec,
        right: AnyCodec,
        at: string,
        printer: Printer,
    ) => RowTerms
    readonly shared: (left: AnyCodec, right: AnyCodec, at: string) => string
    readonly row: (
        pin: Pin | undefined,
        printer: Printer,
    ) => (codec: AnyCodec, at: string) => string
    readonly closed: (printed: string, printer: Printer) => string
    readonly defs: () => string
} => {
    const names = new Map<string, string>()
    const defs: string[] = []
    const nameOf = (printed: string, binders: string, type: string): string => {
        const known = names.get(printed)
        if (known !== undefined) return known
        const name = `t${names.size}`
        names.set(printed, name)
        defs.push(
            `def ${name}${binders === '' ? '' : ` ${binders}`} : ${type} := ${printed}`,
        )
        return name
    }
    const session = (pin: Pin = (_, made) => made) => {
        const adapters = new Map<unknown, string>()
        const given = new Map<unknown, string>()
        const argumentOf = (fn: unknown, kind: 'closure' | 'reader') => {
            const known = given.get(fn)
            if (known !== undefined) return known
            const made = pin(fn, argument(kind))
            given.set(fn, made)
            return made
        }
        return (print: (bound: Bound) => string, type: string): string => {
            const bound: Bound = {
                closures: new Map(),
                adapters,
                readers: new Map(),
            }
            const printed = print(bound)
            const name = nameOf(printed, leanBinders(bound), type)
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
    const row = (pin: Pin | undefined, printer: Printer) => {
        const apply = session(pin)
        return (codec: AnyCodec, at: string): string =>
            apply(
                (bound) => printers[printer].print(codec, at, bound),
                printers[printer].type,
            )
    }
    const pair = (
        left: AnyCodec,
        right: AnyCodec,
        at: string,
        printer: Printer,
    ): RowTerms => {
        const one = row(undefined, printer)
        const l = one(left, at)
        const r = one(right, at)
        return { l, r }
    }
    const shared = (left: AnyCodec, right: AnyCodec, at: string): string =>
        session()(
            (bound) => leanSharedOf(left, right, at, bound),
            'Closed.Shared',
        )
    return {
        pair,
        shared,
        row,
        closed: (printed, printer) =>
            nameOf(printed, '', printers[printer].type),
        defs: () => defs.join('\n'),
    }
}

/**
 * **The two printers of a codec**: the closed codec, and the graph. A family that reads the meaning
 * reads the closed codec. The guard rows read the graph.
 */
const printers = {
    closed: { type: 'Closed', print: leanClosedOf },
    graph: { type: 'Graph', print: leanGraphOf },
} as const

/** A printer of a codec. */
type Printer = keyof typeof printers

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
const listsOf = <T>(rows: readonly T[]): readonly (readonly T[])[] =>
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

/** A list of named rows of `type` as a `def` over the functions, and the kernel's check of the list. */
const leanRowList = (
    name: string,
    type: string,
    rows: readonly Row<string>[],
    ok: string,
): string =>
    [
        `def ${name} ${rowBinders} : List (String × ${type}) := [`,
        `  ${rows.map((one) => `(${leanString(one.name)}, ${one.row})`).join(',\n  ')}]`,
        '',
        `theorem ${name}_check ${rowBinders} :`,
        `    failing ${ok} (${name} ρ π) = [] := kernel_rfl%`,
    ].join('\n')

/**
 * **The diagnostic of a row module**: one `#eval` that prints the name of each row whose
 * comparator answers `false`, at one instance of the caller functions: each reader answers `none`,
 * and each predicate answers `true`.
 * The kernel theorem of each list reads the same `failing` and the same comparator.
 */
const leanDiagnostic = (
    lists: readonly { readonly name: string; readonly ok: string }[],
): string =>
    lists.length === 0
        ? ''
        : `#eval ([${lists
              .map(
                  ({ name, ok }) =>
                      `failing ${ok} (${name} (fun _ _ => none) (fun _ _ => true))`,
              )
              .join(',\n  ')}].flatten).forM IO.println`

/** What a row module states: the generated pool, or the corpus. */
type Subject = 'pool' | 'corpus'

/** The unit of a row of each subject, as the header names it. */
const unitOf = { pool: 'pair', corpus: 'vector' } as const satisfies Record<
    Subject,
    string
>

/** The header of a row module: how a row names its vector, and how the file names a failure. */
const rowForm = (
    subject: Subject,
) => `Each distinct term is one \`def\`, and a caller's function of the term is a parameter of the \`def\`.
A row applies the \`def\` to \`ρ n\` or \`π n\`, and each function of each ${unitOf[subject]} has an index of its own.
A row is the name of its ${unitOf[subject]}, then the data. A list holds ${rowsPerList} rows, and the kernel decides
\`failing ok rows = []\` for the comparator \`ok\` of each list by \`kernel_rfl%\`. The last \`#eval\` prints
\`failing ok rows\` of each list at one instance of the caller functions, so the file names each failing
${unitOf[subject]}, and prints nothing when each row passes.`

/** A form of row list: the Lean type of a row, and the comparator of `Calculus.Bridge.Rows` that answers one row. */
type RowForm = { readonly type: string; readonly ok: string }

/** One vector as a row: the name of its former theorem, its form, and the row as Lean prints it. */
type Row<F extends string> = {
    readonly name: string
    readonly form: F
    readonly row: string
}

/**
 * **The vectors of one file in the row form.** The rows print through the shapes that the reader
 * gives: the kernel module gives each caller function an index of `ρ` or `π`.
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
    readonly ok: string
    readonly text: string
}[] =>
    rowLists(file, shapes).map(({ form, index, rows }) => {
        const name = `${form}${index}`
        const { type, ok } = file.forms[form]
        return { form, name, ok, text: leanRowList(name, type, rows, ok) }
    })

/** The disjointness pairs as rows: the two closed codecs and the two answers of {@link leanDisjoint}. */
export const disjointRows = (
    pairs: readonly DisjointPair[],
): RowFile<'rows'> => ({
    forms: {
        rows: {
            type: '(Closed × Closed × Bool × Bool)',
            ok: 'disjointOk',
        },
    },
    rows: (shapes) =>
        pairs.map((pair) => {
            const [disjointly, views] = disjointAnswers(pair)
            const { l, r } = shapes.pair(
                pair.left,
                pair.right,
                pair.name,
                'closed',
            )
            return {
                name: leanIdent(pair.name),
                form: 'rows',
                row: `(${l}, ${r}, ${disjointly}, ${views})`,
            }
        }),
})

/**
 * The disjointness pairs in the row form: each row is the two closed codecs and the two answers of
 * {@link leanDisjoint}, and the checker of a list states both answers at each row.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanDisjointRowModule = (
    pairs: readonly DisjointPair[],
    subject: Subject = 'pool',
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(disjointRows(pairs), shapes)
    return leanModule(`import Calculus.Bridge.Rows

/-!
# Disjointness of the ${subject}, proposed to the model

**Generated — do not edit.** One row per pair of ${subject} terms: the two closed codecs, the answer
of \`src/\`'s \`disjoint\` on the two terms, and the answer of \`src/\`'s \`viewsDisjoint\` on the two
pairs of views. The checker of a list states that \`Calculus.Closed.disjoint\` and
\`Calculus.Closed.viewsDisjoint\` give the same answers at each row: \`disjointOk_iff\` makes
\`disjointOk\` the two equations.

${rowForm(subject)}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists.map((one) => one.text).join('\n\n')}

${leanDiagnostic(lists)}

end Calculus
`)
}

/** The kernel's check of a row list of each form, and the lemma of `Calculus.Bridge.Rows` that lifts it. */
const separationLists = {
    accepted: {
        type: '(Closed × Closed)',
        ok: 'acceptedOk',
        caller: ' (κ : Callers)',
        verdict: `Lawful (p.2.1.meaning (libTable κ)) → Lawful (p.2.2.meaning (libTable κ)) →
      Alg.Compat (p.2.1.meaning (libTable κ)) (p.2.2.meaning (libTable κ)) ∧
        Alg.Compat (p.2.2.meaning (libTable κ)) (p.2.1.meaning (libTable κ))`,
        lift: (list: string) => `accepted_of_rows (${list}_check ρ π) κ`,
    },
    acceptedShared: {
        type: 'Closed.Shared',
        ok: 'acceptedSharedOk',
        caller: ' (κ : Callers)',
        verdict: `Lawful (p.2.meaning (libTable κ) p.2.left) → Lawful (p.2.meaning (libTable κ) p.2.right) →
      Alg.Compat (p.2.meaning (libTable κ) p.2.left) (p.2.meaning (libTable κ) p.2.right) ∧
        Alg.Compat (p.2.meaning (libTable κ) p.2.right) (p.2.meaning (libTable κ) p.2.left)`,
        lift: (list: string) => `acceptedShared_of_rows (${list}_check ρ π) κ`,
    },
    refused: {
        type: '(Closed × Closed)',
        ok: 'refusedOk',
        caller: '',
        verdict: 'p.2.1.compatPair p.2.2 = false',
        lift: (list: string) => `refused_of_rows (${list}_check ρ π)`,
    },
    guardRefused: {
        type: '(Graph × Graph)',
        ok: 'guardRefusedOk',
        caller: '',
        verdict: '(p.2.1.guarded && p.2.2.guarded) = false',
        lift: (list: string) => `guardRefused_of_rows (${list}_check ρ π)`,
    },
} as const satisfies Record<SeparationForm, unknown>

/**
 * The declaration verdicts as rows, one form per {@link SeparationForm}. A row of an accepted pair
 * or of a pair refused at compatibility is the two closed codecs: a closed codec exists only for a
 * guarded codec, so the row states the guard by its type. A row of two options of one scope is the
 * one scope with two roots. A row of a pair refused at the guard is the two graphs, because such a pair has no
 * closed codec.
 */
export const separationRows = (
    separations: readonly Separation[],
): RowFile<SeparationForm> => ({
    forms: separationLists,
    rows: (shapes) =>
        separations.map((one) => {
            const form = separationForm(one)
            if (form === 'acceptedShared')
                return {
                    name: leanIdent(one.name),
                    form,
                    row: shapes.shared(one.left, one.right, one.name),
                }
            const { l, r } = shapes.pair(
                one.left,
                one.right,
                one.name,
                form === 'guardRefused' ? 'graph' : 'closed',
            )
            return {
                name: leanIdent(one.name),
                form,
                row: `(${l}, ${r})`,
            }
        }),
})

/**
 * **A pair over an open fragment states no guard row.** A union over a `ref` that no scope binds
 * is judged on the closed copy of a scope, so the host decides no guard and no compatibility on
 * the pair, and no caller observes a verdict on the open term. The term has no graph to print
 * either. The rule is the rule of {@link separationForm}. The answer is the reason, or nothing.
 */
export const pairGuardRefusal = ({
    left,
    right,
}: Separation): string | undefined =>
    [left, right].some((option) => openRefusal(option.def) !== undefined)
        ? 'the union reads a `ref` that no scope binds, so the host decides the pair at the scope'
        : undefined

/**
 * **The guard column of a pair, alone**: the two graphs, and whether `src/`'s guard accepts both
 * options. A pair with a fill on each side has no separation verdict, and this row states the
 * column of the pair that the model decides. A pair over an open fragment states no row
 * ({@link pairGuardRefusal}).
 */
export const pairGuardRows = (
    pairs: readonly Separation[],
): RowFile<'pairGuards'> => ({
    forms: {
        pairGuards: { type: '(Graph × Graph × Bool)', ok: 'pairGuardOk' },
    },
    rows: (shapes) =>
        pairs.flatMap((one) => {
            if (pairGuardRefusal(one) !== undefined) return []
            const { l, r } = shapes.pair(one.left, one.right, one.name, 'graph')
            const guarded = [one.left, one.right].every(
                (option) => recursionUse(option.def) < 2,
            )
            return [
                {
                    name: leanIdent(one.name),
                    form: 'pairGuards' as const,
                    row: `(${l}, ${r}, ${guarded})`,
                },
            ]
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
    guardOnly: readonly Separation[] = [],
): string => {
    const shapes = kernelShapes()
    const separated = kernelLists(separationRows(separations), shapes)
    const guarded = kernelLists(pairGuardRows(guardOnly), shapes)
    const lists = [
        ...separated.map(({ form, name, text }) => {
            const { caller, verdict, lift } = separationLists[form]
            return [
                text,
                '',
                `theorem ${name}_verdicts ${rowBinders}${caller} :`,
                `    ∀ p ∈ ${name} ρ π,`,
                `    ${verdict} :=`,
                `  ${lift(name)}`,
            ].join('\n')
        }),
        ...guarded.map((one) => one.text),
    ]
    const guardText =
        guardOnly.length === 0
            ? ''
            : ` A pair with a fill on each side carries the
guard column alone, in the \`pairGuards\` lists: the model refuses two fills at one name whatever their
constants, and \`src/\` accepts two fills with equal constants, so the pair has no separation verdict.`
    return leanModule(`import Calculus.Bridge.Rows

/-!
# Declaration verdicts of the ${subject}, both ways

**Generated — do not edit.** One row per option pair of the ${subject}, in one list per form. A pair
that \`src/\`'s \`union\` accepts holds two closed codecs, which exist only for guarded codecs, and
carries the model's proof that the pair is compatible. A pair that \`src/\` refuses at
compatibility holds two closed codecs and carries \`Closed.compatPair x y = false\`. A pair that
\`src/\` refuses at the guard holds two graphs and carries the guard's refusal. The lemmas of \`Calculus.Bridge.Rows\` lift each checker to the verdict
of each row.${guardText}

${rowForm(subject)}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists.join('\n\n')}

${leanDiagnostic([...separated, ...guarded])}

end Calculus
`)
}

/* ── the meet cover ───────────────────────────────────────────────────────────────────────── */

/**
 * **One pair of a meet**: the two factors, the codec that `src/`'s `meet` built from them, and one
 * value with the attribute that one factor writes from the value.
 */
export type MeetCover = {
    readonly name: string
    readonly left: AnyCodec
    readonly right: AnyCodec
    readonly meet: AnyCodec
    readonly value: unknown
    readonly attribute: AttributeValue
}

/**
 * The meet pairs as rows: the fuel of the attribute, the three closed codecs, the value, and the
 * attribute. The checker of a list states that the model's meaning of the meet writes the
 * attribute from the value wherever the meanings of both factors do.
 */
export const meetCoverRows = (
    covers: readonly MeetCover[],
): RowFile<'meetCovers'> => ({
    forms: {
        meetCovers: {
            type: '(Nat × Closed × Closed × Closed × Value × Attr)',
            ok: 'meetCoversOk',
        },
    },
    rows: (shapes) =>
        covers.map((one) => {
            const [l, r, m] = [one.left, one.right, one.meet].map((codec) =>
                shapes.closed(leanClosedOf(codec, one.name), 'closed'),
            )
            return {
                name: leanIdent(one.name),
                form: 'meetCovers',
                row: `(${fuelFor(one.attribute)}, ${l}, ${r}, ${m}, ${leanValueOf(one.value, one.name)}, ${leanAttrOf(one.attribute, one.name)})`,
            }
        }),
})

/**
 * The meet pairs in the row form. Each list carries the checker, and the cover of the model's
 * `Codec.meet` of the two factors by the meet that `src/` built, lifted from the checker.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanMeetCoverModule = (
    covers: readonly MeetCover[],
    subject: Subject = 'pool',
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(meetCoverRows(covers), shapes)
    return leanModule(`import Calculus.Bridge.Rows

/-!
# The meets of the ${subject}, covered in the model

**Generated — do not edit.** One row per sampled pair of a meet of two ${subject} terms: the fuel,
the two closed factors, the closed codec of \`src/\`'s \`meet\` of the two, a value, and the attribute
that one factor writes from the value. The checker of a list states that the model's meaning
of the meet writes the attribute from the value wherever the meanings of both factors do, and each
check settles. \`meetCovers_of_rows\` lifts the checker to the cover of \`Codec.meet\` of the two
meanings at each row. A row reads each factor as written, and \`src/\` reads each factor open, so
the row states the cover and not the equation.

${rowForm(subject)}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists
    .map(({ name, text }) =>
        [
            text,
            '',
            `theorem ${name}_covers [DecidableEq Attr] ${rowBinders} :`,
            `    ∀ x n A B M v s, (x, n, A, B, M, v, s) ∈ ${name} ρ π →`,
            '      (Alg.Codec.meet (A.meaning (libTable noCallers)) (B.meaning (libTable noCallers))).e v =',
            '        some s → (M.meaning (libTable noCallers)).e v = some s :=',
            `  meetCovers_of_rows (${name}_check ρ π)`,
        ].join('\n'),
    )
    .join('\n\n')}

${leanDiagnostic(lists)}

end Calculus
`)
}

/* ── the fit rows ─────────────────────────────────────────────────────────────────────────── */

/**
 * **One row of a fit**: the option, the pattern as `src/` opens it, one value that the option
 * writes with its attribute, and whether `src/` writes the value through the opened pattern.
 */
export type FitRow = {
    readonly name: string
    readonly option: AnyCodec
    readonly pattern: Term
    readonly value: unknown
    readonly attribute: AttributeValue
    readonly holds: boolean
}

/**
 * The fit rows: the fuel of the attribute, the two closed codecs, the value, the attribute, and
 * the flag. The checker of a list states that the model's meaning of the option writes the
 * attribute from the value, and that the model's meaning of the opened pattern writes from the
 * value exactly where the flag is `true`.
 */
export const fitRows = (fits: readonly FitRow[]): RowFile<'fits'> => ({
    forms: {
        fits: {
            type: '(Nat × Closed × Closed × Value × Attr × Bool)',
            ok: 'fitsOk',
        },
    },
    rows: (shapes) =>
        fits.map((one) => {
            const o = shapes.closed(
                leanClosedOf(one.option, one.name),
                'closed',
            )
            const p = shapes.closed(
                leanClosedOfTerm(one.pattern, one.name),
                'closed',
            )
            return {
                name: leanIdent(one.name),
                form: 'fits',
                row: `(${fuelFor(one.attribute)}, ${o}, ${p}, ${leanValueOf(one.value, one.name)}, ${leanAttrOf(one.attribute, one.name)}, ${one.holds})`,
            }
        }),
})

/**
 * The fit rows in the row form. Each list carries the checker, and the statement about the model's
 * meaning of the opened pattern at each row, lifted from the checker.
 *
 * Generated at gate time and elaborated, never committed.
 */
export const leanFitModule = (
    fits: readonly FitRow[],
    subject: Subject = 'pool',
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(fitRows(fits), shapes)
    return leanModule(`import Calculus.Bridge.Rows

/-!
# The fits of the ${subject}, checked in the model

**Generated — do not edit.** One row per sampled value of an option of a ${subject} pair: the fuel,
the closed codec of the option, the closed codec of the pattern as \`src/\` opens it, the value, the
attribute that the option writes from the value, and the flag. The flag is \`true\` where
\`src/\`'s \`fits\` says that the option fits the pattern, and \`false\` where \`src/\` refuses the
value through the opened pattern. The checker of a list states that the model's meaning of the
option writes the attribute from the value, and that the model's meaning of the opened pattern
writes from the value exactly where the flag is \`true\`. \`fits_of_rows\` lifts the checker to that
statement at each row. A row reads a sampled value, so the row states a witness of the value order
and not the order.

${rowForm(subject)}
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false

namespace Calculus

${shapes.defs()}

${lists
    .map(({ name, text }) =>
        [
            text,
            '',
            `theorem ${name}_fits ${rowBinders} :`,
            `    ∀ x n A P v s holds, (x, n, A, P, v, s, holds) ∈ ${name} ρ π →`,
            '      (A.meaning (libTable noCallers)).e v = some s ∧',
            '        ((P.meaning (libTable noCallers)).e v).isSome = holds :=',
            `  fits_of_rows (${name}_check ρ π)`,
        ].join('\n'),
    )
    .join('\n\n')}

${leanDiagnostic(lists)}

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
 * denotes: each reader answers as before. A `ref` copies to one `ref`, so a cycle stays a cycle.
 */
const recording = (
    t: Term,
    log: Map<unknown, [AttributeValue, unknown][]>,
): Term =>
    throughRefs((t, copy) => {
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
              `    (Closed.meaning (libTable noCallers) ${term}).p`,
              `      (${leanAttrOf(attribute, name)}) = none := kernel_rfl%`,
          ].join('\n')
        : [
              ...head,
              `    vcheck ${fuelForValue(read)}`,
              `      ((Closed.meaning (libTable noCallers) ${term}).p`,
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
            'a *field*, not a term — `optional`/`fallback` denote `Field`, and no `Term` position accepts one',
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
    const term = leanClosedOf(codec, name, bound)
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
 * A union or a dissection, with the two slices that `src/` runs on it.
 *
 * The public `extract` and `exclude` are generic over the patterns that the options admit. This is
 * the erased form, as {@link AnyCodec} is the erased form of a codec.
 */
export type Sliceable = AnyCodec & {
    readonly extract: (pattern: AnyCodec) => AnyCodec
    readonly exclude: (pattern: AnyCodec) => AnyCodec
}

/** A codec, with the two slices of `src/` erased on it. */
export const sliceableOf = (codec: AnyCodec): Sliceable => ({
    ...codec,
    extract: (pattern) => extract(codec, pattern),
    exclude: (pattern) => exclude(codec, pattern),
})

/**
 * A union and the clauses put to it: `src/`'s `extract`, against the model's `AltClause.admitsC`.
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

/** One clause: the options that `src/` keeps under the clause, in the order of the union. */
type SliceRow = {
    readonly clause: string
    readonly keeps: readonly boolean[]
}

/** One clause key: the name, the adapter word, and the alternatives under the word. */
type ClauseEntry = readonly [string, string, Alternatives]

/**
 * **The adapter word a pin goes through**, as `Calculus.pinOfG` reads it: `[]` for a literal, and the
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
): Omit<SliceRow, 'clause'> => {
    const def = codec.extract(object(clause)).def
    if ('mark' in def) throw new Error(`${at}: a slice returned a field`)
    const kept =
        def.kind === 'never' ? [] : def.kind === 'union' ? def.options : [def]
    if (kept.some((t) => !options.includes(t))) {
        throw new Error(`${at}: a slice returned an option the union lacks`)
    }
    return { keeps: options.map((t) => kept.includes(t)) }
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
        ...keptBy(codec, options, clause, at),
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
 * Each option prints as a closed codec of its own, rooted at its entry, as narrowing roots the
 * options, so an option with no scoped form refuses the union.
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
    // the slice of an open fragment refuses each clause, until a scope binds each name
    if (openRefusal(def) !== undefined) {
        return refuse(
            name,
            'the union reads a `ref` that no scope binds, so the host keeps no option under a clause',
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
    const printed = options.map(
        (t, i) => closedPrint(t, `${name}.option${i}`, bound).text,
    )
    const binders = leanBinders(bound)
    const list = `[${rows.map((row) => row.clause).join(',\n      ')}]`
    return [
        `/-- \`${name}\` — the options \`src/\` keeps under each clause -/`,
        `theorem ${leanIdent(name)}${binders === '' ? '' : ` ${binders}`} :`,
        `    ${named === undefined ? list : named(list)}.map`,
        `      (fun c => let os := [${printed.map((t) => `(${t})`).join(',\n        ')}]`,
        '        os.map c.admitsC) =',
        `    [${rows.map((row) => `[${row.keeps.join(', ')}]`).join(',\n      ')}] := ${closing(binders)}`,
    ].join('\n')
}

/* ── the path ──────────────────────────────────────────────────────────────────────────────── */

/** One step of a path: a name, a position, or the clause of a `narrow`. */
export type PathStep = string | number | { readonly narrow: ClausePattern }

/**
 * **What `at` decides at one path**, read from outside the host.
 *
 * The walk refuses (`refused`), or no codec stands at the path (`vacant`), or some options admit
 * no value at the path (`someVariants`), or the options declare the path differently
 * (`ambiguous`), or one codec stands at the path (`resolved`). The first and the second each
 * happen at the call or on use. The model's frontier carries no such moment, so the vector reads
 * neither moment.
 */
export type HostAt = {
    /** The preconditions of the call, where the call of `at` returned a codec. */
    readonly preconditions?: Result<readonly Precondition[]>
} & (
    | { readonly kind: 'refused' | 'vacant' | 'someVariants' | 'ambiguous' }
    | { readonly kind: 'resolved'; readonly codec: AnyCodec }
)

/** The name at which the wrapper holds the codec under test. */
const wrapped = 'r'

/**
 * **A path enters a codec through an item.** The codec sits at an optional name of an item, which
 * takes every codec and `never` too, so a path of the model reads the codec one level down.
 */
const wrapperOf = (codec: AnyCodec) =>
    itemOf(object({ [wrapped]: optional(codec) }))

/** Every term that the walk can reach from a root, through each `ref` that has a target. */
export const reachable = (root: Term): ReadonlySet<Term> => {
    const seen = new Set<Term>()
    const walk = (t: Term): void => {
        if (seen.has(t)) return
        seen.add(t)
        switch (t.kind) {
            case 'ref': {
                const target = targetOf(t)
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

/**
 * **The codec at a path under {@link wrapped}**: each run of segments is one `at`, and each clause
 * is one `narrow`. A loop computes the steps, so the path is no tuple that the type can check.
 */
const reach = (
    item: ReturnType<typeof wrapperOf>,
    steps: readonly PathStep[],
): AnyCodec => {
    let run: Segment[] = [wrapped]
    let reached = at(item, run)
    run = []
    for (const step of steps) {
        if (typeof step !== 'object') {
            run.push(step)
            continue
        }
        reached = narrow(at(reached, run), step.narrow)
        run = []
    }
    return at(reached, run)
}

/**
 * **The decision of `at` at a path under {@link wrapped}.** A throw of the call is a refusal at the
 * call. A codec whose term the root does not reach is a refusal on use, and its message names the
 * reading. Any other codec is the resolved codec. A throw that is no `CodecError` propagates.
 */
export const hostAt = (codec: AnyCodec, steps: readonly PathStep[]): HostAt => {
    const item = wrapperOf(codec)
    let reached: AnyCodec
    try {
        reached = reach(item, steps)
    } catch (error) {
        if (!(error instanceof CodecError)) throw error
        return {
            kind: error.message.startsWith('no attribute is declared')
                ? 'vacant'
                : 'refused',
        }
    }
    if (reachable(item.def as Term).has(reached.def as Term))
        return {
            kind: 'resolved',
            codec: reached,
            preconditions: preconditionsOf(reached),
        }
    const refusal = reached.decode({ NULL: true })
    const message = refusal instanceof CodecError ? refusal.message : ''
    const preconditions = preconditionsOf(reached)
    if (message.includes('is declared by some variants only'))
        return { kind: 'someVariants', preconditions }
    if (message.includes('is declared differently in different variants'))
        return { kind: 'ambiguous', preconditions }
    // a clause that separates every option leaves no codec at the path
    if (message.startsWith('the clause on'))
        return { kind: 'vacant', preconditions }
    return { kind: 'refused', preconditions }
}

/** The order of `compare` on `String` in the model: by code point. */
const nameOrder = (a: string, b: string): number => {
    const points = (name: string) =>
        Array.from(name, (one) => one.codePointAt(0) ?? 0)
    const [x, y] = [points(a), points(b)]
    for (let i = 0; i < Math.min(x.length, y.length); i++) {
        const d = (x[i] ?? 0) - (y[i] ?? 0)
        if (d !== 0) return d
    }
    return x.length - y.length
}

/** One stored literal, as the base and the inhabitant of the carrier that `Test.in` takes. */
const leanStoredLiteral = (
    stored: Extract<Precondition, { readonly in: unknown }>['in'][number],
): readonly [string, string] => {
    if (stored.S !== undefined) return ['string', leanString(stored.S)]
    if (stored.N !== undefined)
        return ['number', `(WFNumeral.of ${leanString(stored.N)})`]
    if (stored.BOOL !== undefined) return ['boolean', String(stored.BOOL)]
    if (stored.B !== undefined) return ['binary', leanBytes(stored.B)]
    throw new Error('a stored literal holds no member')
}

/** One precondition of the host, as the model's `Cond`. */
const leanCond = (p: Precondition): string => {
    const path = `[${p.segments.map(leanSeg).join(', ')}]`
    if ('exists' in p) return `⟨${path}, .exists⟩`
    if ('type' in p) return `⟨${path}, .type .${p.type}⟩`
    const [first, ...rest] = p.in.map(leanStoredLiteral)
    const [base, x] = first as readonly [string, string]
    return `⟨${path}, .in GroundKind.${base} ${x} [${rest.map(([, y]) => y).join(', ')}]⟩`
}

/**
 * **The claim of the host about the precondition of a clause**, as the model's
 * `Option (List Cond)`: a refusal is `none`. The model lists the conditions in pre-order: the `M`
 * of an object, then each name in the order of `compare`, each with its own conditions. A clause
 * lists them as declared, so the claim sorts the conditions by the full path, where a prefix
 * comes before its extensions.
 */
const leanPreconditionClaim = (
    claim: Result<readonly Precondition[]>,
): string => {
    if (failed(claim)) return 'none'
    const preOrder = (a: Precondition, b: Precondition): number => {
        for (
            let i = 0;
            i < Math.min(a.segments.length, b.segments.length);
            i++
        ) {
            const d = nameOrder(String(a.segments[i]), String(b.segments[i]))
            if (d !== 0) return d
        }
        return a.segments.length - b.segments.length
    }
    return `(some [${[...claim].sort(preOrder).map(leanCond).join(', ')}])`
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
 * **A decision where a row can narrow**: one codec, and a union under its `ref`s. The walk of
 * `narrow` narrows the options of the union, and a row states that narrowing.
 *
 * A recursive union narrows as any union does. Each option prints as a closed codec of its own,
 * where a `ref` that returns to the union is an entry of the option, so the row reads `narrowC`
 * over the options and needs no binder.
 */
export const unionAt = (host: HostAt): boolean => {
    if (host.kind !== 'resolved' || 'mark' in host.codec.def) return false
    return underRefs(host.codec.def)?.kind === 'union'
}

/** The term `never`, the frame of a name that an object neither declares nor leaves open. */
const nothingAt: Term = { kind: 'never' }

/** The options of a union that a clause keeps: the host's narrowing, on the graph. */
const narrowedBy = (phi: Term, options: readonly Term[]): Term[] =>
    options.filter((o) => !storedApart(phi, o))

/**
 * **A frame of the graph walk of a narrowing row**: the option whose closed codec holds the frame,
 * the term at the frame, and whether the frame is a child of a container. A frame at a position of
 * the print is the body of the entry `j` and the steps `path`, as `Closed.frameAt` reads them. The
 * frame of a root is the root entry.
 */
type GraphWalked = {
    readonly option: number
    readonly t: Term
    readonly down: boolean
    readonly at:
        | { readonly kind: 'root' }
        | {
              readonly kind: 'position'
              readonly j: number
              readonly path: readonly string[]
          }
}

/** A term under its `ref`s, as the walk of `narrow` reads it, or nothing where a `ref` has no target. */
const underRefs = (t: Term): Term | undefined =>
    t.kind === 'ref'
        ? ((u) => (u === undefined ? undefined : underRefs(u)))(targetOf(t))
        : t

/**
 * **The model's frontier at one segment, over the graph of a printed option**: `childG`. A term
 * that prints as an entry is a leaf, and a step past it enters the body of the entry. Each child of
 * a container prints as an entry, and above every guard an entry of a cycle does. A union gives
 * the children of each option. `undefined` is a refusal, and a segment that a term does not read
 * gives no frame. The kernel checks each frame against `Rooted.at`, so a step that reads otherwise
 * fails the row.
 */
const graphChildOf = (
    w: GraphWalked,
    s: string | number,
    print: Pick<ClosedPrint, 'entries' | 'children'>,
): GraphWalked[] | undefined => {
    const u = underRefs(w.t)
    if (u === undefined) return []
    const entry = (w.down ? print.children : print.entries).get(u)
    const top = w.at.kind === 'position' && w.at.path.length === 0
    if (
        entry !== undefined &&
        !(top && w.at.kind === 'position' && w.at.j === entry.index)
    )
        return graphChildOf(
            {
                option: w.option,
                t: u,
                down: false,
                at: { kind: 'position', j: entry.index, path: [] },
            },
            s,
            print,
        )
    if (w.at.kind !== 'position') return []
    const { j, path } = w.at
    const step = (t: Term, sel: string, down: boolean): GraphWalked => ({
        option: w.option,
        t,
        down,
        at: { kind: 'position', j, path: [...path, sel] },
    })
    switch (u.kind) {
        case 'never':
            return []
        case 'opaq':
            return [w]
        case 'union': {
            const all: GraphWalked[] = []
            for (const [p, option] of u.options.entries()) {
                const some = graphChildOf(
                    step(option, `.opt ${p}`, false),
                    s,
                    print,
                )
                if (some === undefined) return undefined
                all.push(...some)
            }
            return all
        }
        case 'object': {
            if (typeof s !== 'string') return []
            const field = u.body.fields[s]
            return [
                step(
                    field ? field.t : (u.body.rest ?? nothingAt),
                    `.name ${leanString(s)}`,
                    true,
                ),
            ]
        }
        case 'list': {
            if (typeof s !== 'number') return []
            const one = u.pre[s]
            if (one !== undefined) return [step(one, `.pos ${s}`, true)]
            if (u.suf.length > 0) return undefined
            return [step(u.spread ?? nothingAt, `.pos ${s}`, true)]
        }
        default:
            return []
    }
}

/** The frontier of a graph walk at each segment of a path, each frame over the entries of its option. */
const graphWalkOf = (
    start: readonly GraphWalked[],
    segs: readonly (string | number)[],
    printOf: (
        option: number,
    ) => Pick<ClosedPrint, 'entries' | 'children'> | undefined,
): GraphWalked[] | undefined => {
    let ws: GraphWalked[] = [...start]
    for (const s of segs) {
        const next: GraphWalked[] = []
        for (const w of ws) {
            const some = graphChildOf(
                w,
                s,
                printOf(w.option) ?? {
                    entries: new Map(),
                    children: new Map(),
                },
            )
            if (some === undefined) return undefined
            next.push(...some)
        }
        ws = next
    }
    return ws
}

/**
 * **The paths of one codec, as one Lean `theorem`.** The root prints as a closed codec. Each path
 * without a clause is a row of `PathRowsC`: the model's `Rooted.at` at the path, read against the
 * decision of the host. A path with a clause is a row of `NarrowRowsC` at the union that the host
 * resolves before the clause: each option and the clause print as a closed codec of their own, and
 * the row reads the model's `narrowC` over the options, then the frontier of the rest of the path
 * over the graph of each kept option. A frame of the graph is the body of an entry and the steps
 * from it (`Closed.frameAt`), so the kernel reduces the recorded frame to the frame that the walk
 * reaches.
 *
 * One bound for every term of the theorem, so one adapter is one generator in each.
 *
 * **A resolved row states the frontier.** The host resolves a node of the term graph of the root.
 * The walk of the model's frontier, over the graph of the print, names the position of each frame,
 * and the row states each frame at that position. A frame holds the resolved node where the frame
 * prints as the node prints, so the row certifies the meaning of the host's decision. A frame that
 * prints otherwise refuses the path.
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
    const def = item.def as Term
    // a closed codec prints one time per theorem, as a `let` that the rows name
    const closedLets = new Map<string, string>()
    const closedNamed = (printed: string): string => {
        const known = closedLets.get(printed)
        if (known !== undefined) return known
        const made = `c${closedLets.size}`
        closedLets.set(printed, made)
        return made
    }
    const rootPrint = closedPrint(def, `${name}.root`, bound)
    const root = closedNamed(rootPrint.text)
    /** A frame of the graph walk, over the closed codec `c`. */
    const frameText =
        (c: string | undefined) =>
        (w: GraphWalked): string =>
            w.at.kind === 'root'
                ? `(Alg.Scoped.Rooted.frame (Closed.rooted ${c}))`
                : `(Closed.frameAt ${c} ${w.at.j} [${w.at.path.join(', ')}])`
    /**
     * The decision of the host at a path. A resolved row states the frontier of the graph walk,
     * each frame at a position that holds the resolved node.
     */
    const hostC = (
        decided: HostAt,
        at: string,
        frontier: () => GraphWalked[] | undefined,
        frameText: (w: GraphWalked) => string,
    ): string => {
        if (decided.kind !== 'resolved') return `.${decided.kind}`
        const node = underRefs(decided.codec.def as Term)
        const walked = frontier() ?? []
        // a frame holds the resolved node where it prints as the node prints
        const same = (t: Term): boolean => {
            const u = underRefs(t)
            if (u === undefined || node === undefined) return false
            return (
                u === node ||
                closedPrint(u, at, bound).text ===
                    closedPrint(node, at, bound).text
            )
        }
        if (walked.length === 0 || walked.some((w) => !same(w.t)))
            return refuse(
                at,
                'the model reaches a frame that is no position of the resolved node',
            )
        const [first, ...others] = walked.map(frameText)
        return `.resolved ${first} [${others.join(', ')}]`
    }
    const plain: string[] = []
    const unions = new Map<string, Map<string, string[]>>()
    const preconditions = new Map<string, Set<string>>()
    paths.forEach((steps, i) => {
        const at = `${name}.path${i}`
        const clauses = steps.flatMap((step, k) =>
            typeof step === 'object' ? [k] : [],
        )
        if (clauses.length === 0) {
            const segs = [wrapped, ...(steps as readonly (string | number)[])]
            const frontier = () =>
                graphWalkOf(
                    [{ option: 0, t: def, down: false, at: { kind: 'root' } }],
                    segs,
                    () => rootPrint,
                )
            plain.push(
                `([${segs.map(leanSeg).join(', ')}], ${hostC(decide(codec, steps), at, frontier, frameText(root))})`,
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
        const clause = (steps[k] as Exclude<PathStep, string | number>).narrow
        const rest = steps.slice(k + 1) as readonly (string | number)[]
        const options = underRefs(before.codec.def as Term)
        if (options?.kind !== 'union')
            return refuse(
                at,
                'no union stands before the clause: a row narrows the options of one union',
            )
        // each option and the clause print as a closed codec of their own, as `narrowC` roots them
        const printed = options.options.map((o, i) =>
            closedPrint(o, `${at}.option${i}`, bound),
        )
        const names = printed.map((one) => closedNamed(one.text))
        const os = `[${names.join(', ')}]`
        const phiTerm = clauseOf(clause)
        const phi = closedNamed(
            closedPrint(phiTerm, `${at}.clause`, bound).text,
        )
        const frontier = () => {
            const kept = new Set(narrowedBy(phiTerm, options.options))
            return graphWalkOf(
                options.options.flatMap((t, option) =>
                    kept.has(t)
                        ? [
                              {
                                  option,
                                  t,
                                  down: false,
                                  at: { kind: 'root' } as const,
                              },
                          ]
                        : [],
                ),
                rest,
                (option) => printed[option],
            )
        }
        const decidedAll = decide(codec, steps)
        const claim = decidedAll.preconditions
        const prefix = [
            wrapped,
            ...(steps.slice(0, k) as readonly (string | number)[]),
        ]
        if (claim) {
            const row = `([${prefix.map(leanSeg).join(', ')}], ${leanPreconditionClaim(claim)})`
            const known = preconditions.get(phi) ?? new Set<string>()
            preconditions.set(phi, known.add(row))
        }
        const byClause = unions.get(os) ?? new Map<string, string[]>()
        const rows = byClause.get(phi) ?? []
        rows.push(
            `([${rest.map(leanSeg).join(', ')}], ${hostC(decidedAll, at, frontier, (w) => frameText(names[w.option])(w))})`,
        )
        byClause.set(phi, rows)
        unions.set(os, byClause)
    })
    const conjuncts = [
        `PathRowsC ${root}\n      [${plain.join(',\n       ')}]`,
        ...[...unions].map(
            ([u, byClause]) =>
                `NarrowRowsC ${u}\n      [${[...byClause]
                    .map(
                        ([phi, rows]) =>
                            `(${phi},\n        [${rows.join(',\n         ')}])`,
                    )
                    .join(',\n       ')}]`,
        ),
        ...[...preconditions].map(
            ([phi, rows]) =>
                `PreRowsC ${phi}\n      [${[...rows].join(',\n       ')}]`,
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
        ...[...closedLets].map(
            ([printed, ident]) => `    let ${ident} : Closed := ${printed}`,
        ),
        `    ${conjuncts.join(' ∧\n    ')} := ${proof}`,
    ].join('\n')
}

/** The imports of a slice module. A path module imports `Calculus.Bridge.ScopePaths` too. */
const sliceImports = `import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.ScopeSlice
import Calculus.Dynamo.Lang.Store`

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
    return leanModule(`${sliceImports}

/-!
# Slices, proposed to the model

**Generated — do not edit.** One theorem per union. Each row is a clause: the options that \`src/\`
keeps under it. \`extract\` gives the verdict of a clause of the caller, and \`assignmentOf\` gives
the verdict of a clause at the tag of a dissection's option. Each option is a closed codec of its
own. The theorem states that \`Calculus.AltClause.admitsC\` gives the same verdict at each option.
Each distinct clause list is one \`def\`, which each theorem with that list reads.
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
 * `Calculus/Bridge/ScopePaths.lean`, which states the frontier that each decision of the host names.
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
        leanModule(`${sliceImports}
import Calculus.Bridge.ScopePaths

/-!
# Paths, proposed to the model

**Generated — do not edit.** File ${file} of ${files}. A path theorem states the decision of
\`at\` at each path into one codec, and under each \`narrow\` at a union on the path. The model
gives the frontier of a closed codec by \`Rooted.at\`, and after a clause by \`narrowC\` and the
frontier of the rest of the path.
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
 * proof rewrites `q0` to its pin at that value (`veq_pin`), and the kernel checks that `decode`
 * answers as the meaning reads under the pin.
 * A caller's predicate below the top is refused, because the emitter computes the value that the
 * predicate reads at the top only. A caller's adapter and an older reader are refused, because the
 * row reads under `libTable noCallers`.
 */
export const leanReadVerdict = (one: ReadVerdict): string => {
    const { name, attribute } = one
    const { decodes, term, quantified, pin } = readVerdictOf(one)
    const head = [
        `/-- \`${name}\` — \`src/\` ${decodes ? 'decodes' : 'refuses'} this attribute -/`,
        `    Closed.AdmA (libTable noCallers) ${term}`,
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
        `${head[2]} := by`,
        `  rw [← veq_pin (n := ${pin.fuel}) h0]; exact kernel_rfl%`,
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
    const term = leanClosedOf(codec, name, bound)
    if (bound.adapters.size > 0 || bound.readers.size > 0) {
        return refuse(
            name,
            "a caller's adapter or older reader: the read row reads under `libTable noCallers`, which names no caller",
        )
    }
    if (bound.closures.size === 0) return { decodes, term, quantified: false }
    const def = codec.def
    const inner =
        !('mark' in def) && def.kind === 'refine'
            ? { term: def.inner, holds: def.q.is }
            : undefined
    // the inner term must print no closure, so the theorem binds the top predicate alone
    const below: Bound = {
        closures: new Map(),
        adapters: new Map(),
        readers: new Map(),
    }
    if (inner !== undefined) {
        leanClosedOfTerm(inner.term, name, below)
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
 * The write vectors assert `(Closed.meaning α t).e v = some a` and the refusal vectors assert `= none`, so
 * one half of every pair was proposed to the model and the other half was not — for the corpus at
 * large. The read side *was* asserted, but only where a union had to choose:
 * {@link leanReadResolution} states `(Closed.meaning α t).p a = some v` for each read resolution. This is
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
        `      (${leanMeaningOf(codec, name)}.p`,
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
 * an unknown lower-case name, so the missing import leaves `Closed.meaning` stuck on a free variable and
 * each vector reports a failed definitional equality rather than an unknown identifier.
 */
export const leanReadVectorModule = (vectors: readonly Vector[]): string => {
    const blocked = vectors
        .map((one) => [one, readVectorIsUnstatable(one)] as const)
        .filter(([, why]) => why !== undefined)
    const live = vectors.filter(
        (one) => readVectorIsUnstatable(one) === undefined,
    )
    return leanModule(`import Calculus.Bridge.Vectors
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
export type Dissection = AnyCodec &
    Itemable<{
        readonly decode: (item: StoredItem) => ReturnType<AnyCodec['decode']>
    }>

/** One read through the index of a dissection, addressed by the item. */
export type ItemRead = {
    readonly name: string
    readonly dissection: Dissection
    readonly item: Readonly<Record<string, AttributeValue>>
}

/** One read through the index: what the index read from the item, or that it read nothing. */
export const leanItemReadResolution = (one: ItemRead): string =>
    statedRead(one.name, one.dissection, carrying('M', one.item), () =>
        itemOf(one.dissection).decode(one.item),
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
              `      (${leanMeaningOf(u, name)}.p`,
              `        (${leanAttrOf(attribute, name)}))`,
              `      (some (${leanValueOf(read, name)})) = .same := kernel_rfl%`,
          ].join('\n')
        : [
              ...head,
              `    ${leanMeaningOf(u, name)}.p`,
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
 * would close a vector line. So the budget is the emitter's job, and it is exactly the
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
import Calculus.Dynamo.Alg.Frontier
import Calculus.Dynamo.Lang.Store
import Mathlib.Tactic.FinCases

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by \`src/codec/lean.ts\` from the shipped TypeScript codecs: each
theorem below is one \`encode\` this library actually performed, proposed to the model as an
equation. A failure here is a disagreement between \`src/codec/codec.ts\` and \`Calculus.Closed.meaning\`, and the
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

    The three wire-set alternatives are the second surprise. The attribute domain types \`SS\`/\`NS\`/\`BS\` as
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
here is a disagreement between \`src/codec/codec.ts\` and \`Calculus.Closed.meaning\`, and the theorem's name says
which vector.

The verdict is \`Calculus.check\`'s, and \`check_same\` is what makes it worth having: \`.same\`
*implies* the two attributes are equal, so a line that reduces to \`.same\` is a proof and not a
comparator's opinion. The fuel on each line is the attribute's own nesting, computed by the
emitter — an under-fuelled line reduces to \`.exhausted\`, which matches neither \`.same\` nor
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
     * equation on `Closed.meaning` — putting a `vcheck` in it would cost that.
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
            : `\n\n/-! ### Read back, through the same term\n\nThe model's \`p\`, given the attribute the library wrote, against the value the library read. Only\nthe \`check\` sample carries these: a read vector's answer is a \`Value\`, so it needs \`vcheck\`, and\nthe \`equation\` sample states each vector as an equation on \`Closed.meaning\` by design. -/\n\n${reads
                  .filter((one) => readVectorIsUnstatable(one) === undefined)
                  .map(leanReadVector)
                  .join('\n\n')}`
    const guarded =
        guards.length === 0
            ? ''
            : `\n\n/-! ### The guard of a binder -/\n\n${guards.map(leanGuard).join('\n\n')}`
    const body = `${written}${readBack}${guarded}`
    if (refusals.length === 0) {
        return leanModule(
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
    return leanModule(
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
        type: '(Nat × Closed × Value × Attr)',
        ok: 'writesOk',
    },
    writesNothing: {
        type: '(Closed × Value)',
        ok: 'writesNothingOk',
    },
    reads: {
        type: '(Nat × Closed × Attr × Value)',
        ok: 'readsOk',
    },
    readsNothing: {
        type: '(Closed × Attr)',
        ok: 'readsNothingOk',
    },
    guards: {
        type: '(Graph × Bool)',
        ok: 'guardsOk',
    },
    admits: {
        type: '(Closed × Attr × Bool)',
        ok: 'admitsOk',
    },
} as const satisfies Record<string, RowForm>

/** The equivalence that turns the checker of a list into the former statement of each row. */
const rowChecks = `The checker of a list states \`failing ok rows = []\`, which \`ok_of_failing\` makes the
comparator at each row. The law of each comparator of \`Calculus.Bridge.Rows\` (\`writesOk_iff\` and the
rest) makes the comparator the former statement of the row. \`Attr\` and \`Value\` have no decidable
equality, because a map holds a function, so a \`some\` answer keeps \`check\` or \`vcheck\`.`

/** A module of corpus rows: the title, the statement, and the rows. */
const leanCorpusRowModule = <F extends string>(
    title: string,
    states: string,
    file: RowFile<F>,
): string => {
    const shapes = kernelShapes()
    const lists = kernelLists(file, shapes)
    return leanModule(`import Calculus.Bridge.Rows

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

${lists.map((one) => one.text).join('\n\n')}

${leanDiagnostic(lists)}

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
            const attribute = codec.unsafeEncode(value as never)
            const t = shapes.closed(leanClosedOf(codec, name), 'closed')
            const row = {
                name: leanIdent(name),
                form: 'writes' as const,
                row: `(${fuelFor(attribute)}, ${t}, ${leanValueOf(value, name)}, ${leanAttrOf(attribute, name)})`,
            }
            return recursive(codec)
                ? [
                      row,
                      {
                          name: leanIdent(`${name}__guarded`),
                          form: 'guards' as const,
                          row: `(${shapes.closed(leanGraphOf(codec, name), 'graph')}, true)`,
                      },
                  ]
                : [row]
        }),
        ...guards.map(({ name, codec, guarded }) => ({
            name: leanIdent(name),
            form: 'guards' as const,
            row: `(${shapes.closed(leanGraphOf(codec, name), 'graph')}, ${guarded})`,
        })),
        ...refusals.map(({ name, codec, value }) => {
            refusedBoth(name, codec, value)
            return {
                name: leanIdent(name),
                form: 'writesNothing' as const,
                row: `(${shapes.closed(leanClosedOf(codec, name), 'closed')}, ${leanValueOf(value, name)})`,
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
        'Differential-testing vectors, the full cross product',
        `Emitted by \`src/codec/lean.ts\` from the shipped TypeScript codecs. A \`writes\`
row is one \`encode\` that this library performed, \`check n ((t.meaning (libTable noCallers)).e v) (some a) = .same\`. A
\`writesNothing\` row is a value that this library refuses, \`(t.meaning (libTable noCallers)).e v = none\`. A \`guards\` row
is the graph guard on the graph of a codec, \`g.guarded = b\`. ${admissions.length} admissions,
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
            const t = shapes.closed(leanClosedOf(u, name), 'closed')
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
                const t = shapes.closed(leanClosedOf(u, name), 'closed')
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
                    itemOf(one.dissection).decode(one.item),
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
            const t = shapes.row(
                (fn, made) =>
                    pin !== undefined && fn === pin.is
                        ? `(fun x => if veq ${pin.fuel} x (${pin.v}) = .same then ${pin.answer} else ${made} x)`
                        : made,
                'closed',
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
 * it, as {@link leanLegacyRead} pins the variable of the former theorem. `aeq_pin` proves that a
 * reader with the pinned answers equals its own pin.
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
            const t = shapes.row(
                (fn, made) => pinText(pins.get(fn), made),
                'closed',
            )(one.codec, one.name)
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
        'The legacy read gate, model against library',
        `One row per (codec, attribute) pair, ${reads.length} in all. Each older
reader is \`ρ k\`, pinned at each attribute that \`src/\` asked it. \`aeq_pin\` proves that a reader
with those answers equals its own pin, so the row at \`ρ k := r\` states the read at each such \`r\`.
The model reads the older answer only where the current term writes the answer, and \`src/\` checks
the same.`,
        legacyReadRows(reads),
    )
