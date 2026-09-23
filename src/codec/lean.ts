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
 * That is not available, and the reason is structural rather than a missing feature.
 *
 * `denote` is `noncomputable` — `funImage` is a `dite` on a `Decidable` instance the kernel does
 * not evaluate for free. So `#eval` fails on every denoted codec, and Lean can generate nothing.
 * The model declares no axiom: `N` is carried exactly, as `WFNumeral`.
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
import { meetTerms } from './term'
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
 * **no** `refine`, `held`, `legacy` or `custom` internally — every one of the four is a combinator
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
 * and all of them closed by `rfl`. `inD` is deliberately *not* used for `isNumeral`: it decides
 * `Numeral.WF d.toDec` for a **double**, which is a different predicate on a different carrier, and
 * it is `noncomputable`, so a vector mentioning it would not reduce.
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
    // an adapter answers from what it declared: `decimal` hands the caller text, so a refinement
    // outside it tests a string even though the base beneath writes a numeral
    if (t.kind === 'held') {
        return t.writes?.every((slot) => slot === 'string') ?? false
    }
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
 * - **`number` and a numeric `literal` are *not* here.** `Term.number` is a closed term, and a
 *   numeric alternative is `WFNumeral.of`, so both emit. A JS number *value* is what has no
 *   exact image, and `leanValueOf` refuses it, so the refusal is reported where it lives.
 * - **`held`, `legacy`, `custom`.** Three of §3's constructors carry *functions* —
 *   `f g : Value → Value`, `r : Attr → Option Value`, `ce`/`cp` — and this library carries
 *   JavaScript closures in the same positions. There is no expression in Lean for an arbitrary
 *   closure. `legacy` used to be the worst of the three for a second reason, and is not any more:
 *   the definition dropped the older readers entirely, so there was nothing to be refused about.
 *   It carries `older` now, and the refusal below names it.
 * - **`refine`, unless the predicate is one this library shipped.** The fourth
 *   function-carrying constructor, and the one where the line has moved. See
 *   {@link ShippedPredicate}: `isNumeral` and `isStoredNumeral` are recognised by reference and
 *   emitted as the model's own predicates, and everything else is still refused, by name. The
 *   boundary is no longer "all refinements" but "refinements this library did not build", which is
 *   the honest line — and it is only two predicates wide, because `src/` constructs none of these
 *   four internally.
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
    forced = 0,
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
    return leanTermOfTerm(def, at, forced)
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
 * **The two sides are one shape now.** {@link Predicate} is `members | each | closure` and
 * `Calculus.Pred` is the same three constructors, so this is a rename and not a translation:
 * `members` to `Pred.members`, `each` to `Pred.each`, a recognised closure to `Pred.closure`.
 * The emitter used to print the *meaning* — `inL k ls`, `liftQ p` — because `Term.refine` carried
 * a `Value → Bool` and a constructor was not available to print. `Pred.eval` is where those two
 * expressions live in the model now, and this prints the data instead.
 *
 * Every case comes back parenthesised, because each is an application and `Term.refine` takes its
 * second argument juxtaposed. That includes the recognised closures, which used to come back bare
 * because they were identifiers and are now wrapped.
 *
 * The third case has no data and never will. A `closure` is a caller's JavaScript function; the
 * registry below recognises two of them **by reference**, and everything else is refused. That is
 * the case `Pred` keeps rather than removes: `refine` still carries an arbitrary predicate.
 */
const leanPredicate = (q: Predicate, at: string, forced: number): string => {
    switch (q.kind) {
        case 'members':
            return `(Pred.members ${leanGround(q.literal, at)})`
        case 'each':
            return `(Pred.each ${leanPredicate(q.of, at, forced)})`
        case 'closure': {
            // recognised by reference against the function this package exported, so a rename or a
            // reimplementation of the predicate is a type error here rather than a silent misemission
            const known = shippedPredicates.get(q.q.is)
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
const leanBodyOf = (body: Body, at: string, forced: number): string => {
    const declared = Object.entries(body.fields)
    const names = declared.map(([name]) => name)
    const fields = leanKeyFunction(
        declared.map(
            ([name, field]) =>
                [
                    leanString(name),
                    leanSlotOf(field, `${at}.${name}`, forced),
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
            : `(some (${leanTermOfTerm(rest, `${at}.rest`, forced)}))`
    return `(Body.mk ${leanFinset(names)} (${fields}) ${restTerm})`
}

const leanTermOfTerm = (t: Term, at: string, forced: number): string => {
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
        /**
         * `Term.set` is indexed by a **`SetBase`**, and by the time the printer sees one it holds a
         * base rather than an element term.
         *
         * The refusal for a restricted element — `refine(b, q).set()`, `string.set('a','b')` — used
         * to live here, and it lives at `.set()` now, because it is not a fact
         * about emission. Such a codec is lawful and simply has no `set` term:
         * `setCodec_restrict` and `setCodec_restrict_p` prove the set of a restriction and the
         * restriction of a set are one pair on both halves, and that is an equation between codecs
         * rather than a term.
         */
        case 'set':
            return `Term.set SetBase.${t.base}`
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
                        leanTermOfTerm(element, part(index), forced),
                    )
                    .join(', ')
            const spread = t.spread
            if (t.suf.length === 0) {
                if (t.pre.length === 0 && spread)
                    return `Term.array (${leanTermOfTerm(spread, `${at}.element`, forced)})`
                const tail = spread
                    ? `(some (${leanTermOfTerm(spread, `${at}.tail`, forced)}))`
                    : 'none'
                return `Term.tuple [${positions(t.pre, (index) => `${at}[${index}]`)}] ${tail}`
            }
            const middle = spread
                ? `(some (${leanTermOfTerm(spread, `${at}.spread`, forced)}))`
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
            return `Term.object ${leanBodyOf(t.body, at, forced)}`
        }
        case 'never':
            return 'Term.never'
        case 'union':
            return `Term.union [${t.options
                .map((variant, index) =>
                    leanTermOfTerm(variant, `${at}[${index}]`, forced),
                )
                .join(', ')}]`
        // The model's `opaq` is the exact codec: its number option is `numberCodec`, so it is this
        // total term. The two policies are `held` over this term, and the `held` row refuses them
        case 'opaq':
            return 'Term.opaq'
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
            return `Term.lazy (${leanTermOfTerm(t.get(), `${at}.inner`, forced + 1)})`
        }
        /**
         * §3 `(refine)`. The predicate is printed by {@link leanPredicate}, and the side condition
         * below applies to a **closure** only.
         *
         * `writesOnlyStrings` exists because the two shipped predicates take a `string` and a
         * `Value → Bool` takes anything: they disagree where JavaScript coerces, so the emission is
         * confined to inner terms that write nowhere else. `members` and `each` are `Pred`
         * constructors over data the term carries, and `Pred.eval` sends them to the model's own
         * `inL` and `liftQ`, so they agree at every value by construction and the gate has nothing
         * to say about them.
         */
        case 'refine': {
            const q = leanPredicate(t.q, at, forced)
            if (t.q.kind === 'closure' && !writesOnlyStrings(t.inner)) {
                return refuse(
                    at,
                    `${shippedPredicates.get(t.q.q.is)?.what ?? 'this predicate'} decides a *string*, and this refinement's inner term writes values that are not strings — where JavaScript would coerce and the model would not, so the two predicates would part company`,
                )
            }
            return `Term.refine (${leanTermOfTerm(t.inner, `${at}.inner`, forced)}) ${q}`
        }
        /**
         * **An adapter this library ships is printed by name**, the way a recognised predicate
         * is. `decimal` is `number` under the text adapter now, so refusing every `held` would
         * take every decimal vector with it.
         *
         * A caller's pair is still refused, and so is the float adapter, for a reason that is not
         * about closures: `Value` carries no float, so the conversion would be numeral to numeral
         * and its content is binary64 rounding. That is the host axiom this development deleted.
         */
        case 'held':
            return t.via === 'decimalText'
                ? `(Term.held (${leanTermOfTerm(t.inner, at, forced)}) numeralOfStoredText textOfNumeral)`
                : refuse(
                      at,
                      "`Term.held` carries two `Value → Value` functions. The library ships one pair the model names, `numeralOfStoredText`/`textOfNumeral`, and this is not it — a caller's closure has no name in the model, and the adapter carrying a JS float has none either, because writing binary64 rounding down is the host axiom this development deleted",
                  )
        case 'legacy':
            return refuse(
                at,
                '`Term.legacy` carries `r : Attr → Option Value`; the definition carries the older reading now, and it is a JS closure, which no `Term` prints — the same wall `custom` meets',
            )
    }
}

/**
 * An `ObjectSlot` — §4's stratum, which is a *position* in a map and not a codec.
 *
 * **`Field` is gone and the slot has two constructors.** A name is required or it is optional, and
 * the presence lattice reads the rest. This emitted `Field.req` and `Field.optional` against a
 * model that stopped having them.
 */
const leanSlotOf = (field: TermField, at: string, forced: number): string => {
    switch (field.mark) {
        case 'optional':
            return `ObjectSlot.optional (${leanTermOfTerm(field.t, at, forced)})`
        /**
         * **A field's alternate reader has no slot, and that is deliberate in the model.**
         *
         * The model states an older reader as `Codec.extendRead`, a codec over the current term's
         * codec and outside `Term`, so a `Body` has no alternate-reader row to put this in —
         * `ExactA.lean` states exactly that. A field-level fallback is not a slot the model declined to add; it
         * is a stratum the model put somewhere else, and nothing here can name it.
         */
        case 'fallback':
            return refuse(
                at,
                '`withLegacyRead` on a field has no `ObjectSlot`: the model carries an older reader as `Codec.extendRead`, which is a codec outside `Term`, so a body has no alternate-reader slot to print',
            )
        case 'req':
            return `ObjectSlot.req (${leanTermOfTerm(field.t, at, forced)})`
        /**
         * `ObjectSlot.optional`, because that is what it denotes rather than an approximation of
         * it.
         *
         * `Value` has no `undefined` and `Value.map` is a key set with a total function on it, so
         * `{ k: undefined }` and `{}` are one `Value` and there is no second thing to mean. The
         * quotient that rests on is {@link leanValueOf}'s, which was already there for `optional`.
         */
        case 'undefinable':
            return `ObjectSlot.optional (${leanTermOfTerm(field.t, at, forced)})`
    }
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
        `    (denote (${leanTermOf(codec, name)})).e`,
        `      (${leanValueOf(value, name)}) = none := rfl`,
    ].join('\n')
}

/**
 * One proposed **separation verdict**: `src/` refuses this pair at the declaration, and the model
 * must not certify it.
 *
 * **The bridge from `src/`'s declaration-time guard to `Orth`, and it runs one way only.** `Orth`
 * is a *sufficient* decidable condition for a fragment of (U) — `docs/architecture.md`'s own
 * by-phase table puts it at six of twenty-five hand discharges directly — so `Orth x y = false`
 * does **not** mean the model cannot separate the pair. It means the cheap syntactic test
 * declines. Measured over the corpus, 66 of 351 pairs are exactly that and every one is
 * legitimate, each landing in one of the guard's three documented exemptions: a literal (which
 * identifies its own values), an object option (chosen by names), or an option whose kind is
 * unknown (`opaque`, `lazy`, an adapter).
 *
 * So the checkable law is the converse. **If the model certifies a pair, `src/` must accept it** —
 * refusing a declaration the model *proves* separable is `src/` rejecting a union that works.
 * Stated as a theorem per refusal: `certPair x y = false`, which stops compiling the moment the
 * certificate starts certifying a pair `src/` turns down. `certPair` is `Orth`, or a meet at the
 * bottom, and it is what the model's `unionOk` reads. Zero counterexamples today, and the pair that
 * motivated `ff75c6b` is the reason the law is worth gating rather than asserting once:
 * `Orth (Term.set .string) (Term.set .number) = true`, which `src/` refused until that commit.
 *
 * **That law holds of a pair the model TYPES, and a refusal has one of two warrants.** `never` is
 * the pair it does not reach. `Orth` certifies it on slots alone — `Orth Term.string Term.never`
 * is `true`, `never` occupying no slot — so `Orth x y = false` is false about it. The model types
 * the union as well: `HNever` is disjoint from every held set, being empty, and §5's (D) holds on
 * that disjunct.
 *
 * **So a `never` pair is the one place the two sides diverge, and the artifact states the
 * divergence rather than hiding it.** `src/` refuses the pair as a *lint*: `restricts` answers
 * that an option admitting nothing can never be chosen, which is true and is worth saying. The
 * model answers that the union is *well formed*, which is also true. Well formed and useful are
 * different claims, so a pair with `never` on a side carries the permits-form — what the model
 * does say about it — and the other side appears in the name and the docstring only: the warrant
 * does not depend on it.
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
    // the same test `restricts` makes, which is what put the pair in this list
    const isNever = (declared: AnyCodec): boolean => {
        const def = declared.def
        return !('mark' in def) && def.kind === 'never'
    }
    if (isNever(left) || isNever(right)) {
        // the permits-form: `src/` refuses on usefulness, the model answers well-formedness, and
        // the theorem records what the model says rather than asserting a refusal it does not make
        const [held, warrant] = isNever(left)
            ? (['[HNever, T]', 'dincomp_never_left'] as const)
            : (['[T, HNever]', 'dincomp_never_right'] as const)
        return [
            `/-- \`${name}\` — \`src/\` refuses this pair as a lint: an option admitting nothing can`,
            `    never be chosen. The model permits it, an empty option being the unit of the sum. -/`,
            `theorem ${leanIdent(name)} : ∀ T : Held, DIncomp ${held} :=`,
            `    ${warrant}`,
        ].join('\n')
    }
    return [
        `/-- \`${name}\` — \`src/\` refuses this pair; the model must not certify it -/`,
        `theorem ${leanIdent(name)} :`,
        `    certPair (${leanTermOf(left, name)})`,
        `      (${leanTermOf(right, name)}) = false := by decide`,
    ].join('\n')
}

/**
 * The separation verdicts as a module of their own, because they need `certPair`.
 *
 * `Calculus.Vectors` reaches `Denote` and not `Orthogonality`, and adding the import to the
 * committed vector samples would make them depend on a module they have nothing to say about.
 *
 * The header imports `Calculus.DynamoDB` as well, because a `held` term spells
 * `numeralOfStoredText` and `textOfNumeral`, which the DynamoDB port defines, and
 * `Meet` does not reach them. Lean
 * auto-binds an unknown lower-case name, so the missing import reports a free variable in the
 * expected type of every verdict rather than an unknown identifier.
 *
 * Generated at gate time and elaborated, never committed — the counts are in
 * `docs/architecture.md`, which is where the verdict this checks is written down.
 */
export const leanSeparationModule = (
    separations: readonly Separation[],
): string =>
    `import Calculus.Meet
import Calculus.DynamoDB

/-!
# Declaration-guard verdicts, proposed to the classifier

**Generated — do not edit.** One theorem per option pair \`src/\`'s \`union\` refuses at the
declaration. \`certPair\` is *sufficient* and not necessary, so this runs one way: a pair the model
certifies must not be refused by \`src/\`. A refusal carries one of two warrants: \`certPair\` declines
the pair, or — where the pair has \`never\` on a side — the model permits it and the theorem says
so. That second one is a divergence, and a deliberate one: the model answers whether the union is
well formed, \`src/\` answers whether it is useful, and an option admitting nothing is well formed
and useless at once. See \`src/codec/lean.ts\`'s \`Separation\`.
-/

/-! The emitted key function is total on a membership subtype, so a single-name object binds a
\`k\` it never reads; the binder cannot be \`_\` because a multi-name object reads \`k.1\`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries \`__\`. -/
set_option linter.style.nameCheck false

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
 * `AdmA` is `noncomputable`, so this cannot be `#eval`. The kernel unfolds it anyway, which is
 * the same fact `Vectors.lean` opens with, so the verdict is asserted and elaboration is the test.
 */
export type ReadVerdict = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly codec: AnyCodec
    readonly attribute: AttributeValue
}

/**
 * A pair of corpus terms, put to the model's meet with the answer `src/` computes.
 *
 * The separations bridge runs one way, because `Orth` is sufficient and not necessary. This one
 * runs both: `Term.meet` and {@link meetTerms} are the *same function* stated twice, so a
 * disagreement in either direction is a defect on one side. It is the only check that measures the
 * meet at all — the host's `unionOk` reads `separable`, which exempts what the model's `Orth` does
 * not, and nothing else holds that divergence.
 */
export type MeetPair = {
    /** A Lean identifier; anything else is sanitized, because a bad name loses the whole file. */
    readonly name: string
    readonly left: AnyCodec
    readonly right: AnyCodec
}

/**
 * One meet, as a Lean `theorem`: the two terms, and the answer this library gives.
 *
 * A refusal emits `= none` and is as much of an assertion as an answer is. The two are the
 * distinction the meet exists to keep — `none` says no term states the intersection and `.never`
 * says the intersection is empty — so a port that confused them would fail here on the pair it
 * confused, which is the whole reason to emit the refusals rather than skip them.
 */
export const leanMeet = ({ name, left, right }: MeetPair): string => {
    const one = left.def
    const other = right.def
    if ('mark' in one || 'mark' in other) {
        throw new LeanUnemittable(
            name,
            'a §4 *field*, not a term — no `Term` position accepts one, so the meet has no pair to state',
        )
    }
    const answer = meetTerms(one, other)
    const pair = `Term.meet (${leanTermOf(left, name)})\n      (${leanTermOf(right, name)})`
    const objects =
        answer?.kind === 'object'
            ? [answer]
            : answer?.kind === 'union' &&
                answer.options.every((o) => o.kind === 'object')
              ? (answer.options as readonly Extract<Term, { kind: 'object' }>[])
              : undefined
    if (objects) return leanMeetObjects(name, pair, objects, [one, other])
    const rhs =
        answer === undefined
            ? 'none'
            : `some (${leanTermOfTerm(answer, `${name}.meet`, 0)})`
    return [
        `/-- \`${name}\` — the meet \`src/\` computes, put to the model -/`,
        `theorem ${leanIdent(name)} :`,
        `    ${pair} = ${rhs} := by meet_pair`,
    ].join('\n')
}

/**
 * **An object answer, stated pointwise**, and a union of object answers option by option. A body is
 * a total function from the key space to a slot, presented as its declared slots and its block, so
 * two bodies are one body exactly when their slots agree at every name either declares and their
 * blocks agree. The model builds its body through a field function that \`rfl\` cannot compare with
 * the emitted one under the binder, and the pointwise statement is closed at every name, so each
 * conjunct reduces.
 *
 * The names are every field name either operand mentions, which covers every name either answer
 * can declare. One more position past the last option states that no option follows.
 */
const leanMeetObjects = (
    name: string,
    pair: string,
    options: readonly Extract<Term, { kind: 'object' }>[],
    operands: readonly Term[],
): string => {
    const names = new Set<string>()
    for (const o of options)
        for (const k of Object.keys(o.body.fields)) names.add(k)
    for (const t of operands) fieldNamesOf(t, names, 3)
    const conjuncts = options.flatMap((answer, i) => {
        const block = answer.body.rest
        const at = `${name}.meet[${i}]`
        const blockTerm = block
            ? leanTermOfTerm(block, `${at}.rest`, 0)
            : undefined
        const option = `(${pair}).bind (·.optionAt ${i})`
        const slot = (k: string): string => {
            const field = answer.body.fields[k]
            return field
                ? leanSlotOf(field, `${at}.${k}`, 0)
                : `ObjectSlot.optional (${blockTerm ?? 'Term.never'})`
        }
        return [
            ...[...names]
                .sort()
                .map(
                    (k) =>
                        `(${option}).bind (·.slotAt ${leanString(k)}) = some (${slot(k)})`,
                ),
            `(${option}).bind (·.blockOf) = some (${blockTerm ? `some (${blockTerm})` : 'none'})`,
        ]
    })
    if (options.length > 1)
        conjuncts.push(`(${pair}).bind (·.optionAt ${options.length}) = none`)
    return [
        `/-- \`${name}\` — the meet \`src/\` computes, put to the model, name by name -/`,
        `theorem ${leanIdent(name)} :`,
        `    ${conjuncts.join(' ∧\n    ')} :=`,
        conjuncts.length === 1
            ? '  rfl'
            : `  ⟨${conjuncts.map(() => 'rfl').join(', ')}⟩`,
    ].join('\n')
}

/** Every field name a term mentions, at any depth. A thunk is forced to a bounded depth. */
const fieldNamesOf = (t: Term, into: Set<string>, forced: number): void => {
    switch (t.kind) {
        case 'object':
            for (const [k, field] of Object.entries(t.body.fields)) {
                into.add(k)
                fieldNamesOf(field.t, into, forced)
            }
            if (t.body.rest) fieldNamesOf(t.body.rest, into, forced)
            return
        case 'union':
            for (const o of t.options) fieldNamesOf(o, into, forced)
            return
        case 'list':
            for (const e of [...t.pre, ...t.suf]) fieldNamesOf(e, into, forced)
            if (t.spread) fieldNamesOf(t.spread, into, forced)
            return
        case 'refine':
        case 'held':
        case 'legacy':
            fieldNamesOf(t.inner, into, forced)
            return
        case 'lazy':
            if (forced > 0) fieldNamesOf(t.get(), into, forced - 1)
            return
        default:
            return
    }
}

/**
 * The meets as a module of their own, carrying the tactic that discharges them.
 *
 * **The tactic is generated and not a declaration of `Calculus/`.** `Term.meet` is compiled by
 * well-founded recursion, so it does not reduce: `decide` and `rfl` both fail, and `Term` carries
 * functions at `held`, `custom` and a `Body`'s field map, so it has no `DecidableEq` for `decide`
 * to use even where it did reduce. What is left is the equation compiler, which is what `simp` on
 * the definition reaches. The lemma set below is the union of the sets `Meet.lean`'s own worked
 * examples use, and the three alternatives are ordered by cost. A wrong answer does not close:
 * measured on two planted controls, one claiming a refusal where the model answers and one
 * claiming an answer where the model refuses.
 */
export const leanMeetModule = (
    meets: readonly MeetPair[],
    deferred: readonly string[] = [],
): string =>
    `import Calculus.Meet
import Calculus.DynamoDB

/-!
# The meet, proposed to the model

**Generated — do not edit.** One theorem per pair of corpus terms, asserting that
\`Calculus.Term.meet\` answers what \`src/\`'s \`meetTerms\` answered. Unlike the separation
verdicts this runs in both directions, the two being one function written twice.

\`none\` is not the bottom. It says no term states the intersection, where \`.never\` says the
intersection is empty, and both are asserted here.

**An object answer is stated name by name.** A body is a total function from the key space to a
slot, so two bodies are one body exactly when their slots agree at every name either declares and
their blocks agree. The model's field function does not reduce under its binder, and each
pointwise conjunct is closed, so each one reduces. A union of object answers is stated option by
option.

**The pairs this module defers.** A deferred pair is named here and asserted nowhere, which is the
honest form: a gap that is counted and read, not one that is skipped in silence. The count is pinned
in \`lean.spec.ts\`, so a *new* deferral fails the suite.
${deferred.length === 0 ? '\nNone today.\n' : deferred.map((name) => `\n* \`${name}\``).join('')}
-/

namespace Calculus

set_option maxHeartbeats 1000000
-- the emitted key function is total on a membership subtype, so a single-name object binds a
-- variable it never reads, and the generated names carry the corpus vector names
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

/-- Reduction first: \`Term.meet\` is structural, so the kernel evaluates a closed pair. The
    unfolding alternatives stay for a pair whose answer carries a field function. -/
local macro "meet_pair" : tactic => \`(tactic|
  first
    | rfl
    | decide
    | (simp [${MEET_LEMMAS}] <;> decide)
    | (simp [${MEET_LEMMAS}] <;> rfl))

${meets.map(leanMeet).join('\n\n')}

end Calculus
`

/** The union of the lemma sets `Meet.lean`'s worked examples use to reduce a meet. */
const MEET_LEMMAS = [
    'Term.meet',
    'Term.meetLit',
    'Pred.isData',
    'allSome',
    'Term.ofOptions',
    'unionOk',
    'certAll',
    'Term.isNever',
    'Term.isOpenObject',
    'MapOf.at',
    'Term.tupleOf',
    'Term.listOf',
    'Term.refineOf',
    'ObjectSlot.meet',
    'ObjectSlot.isReq',
    'ObjectSlot.isBottom',
    'objSlot',
    'ObjectSlot.through',
    'ObjectSlot.isAbsentOpt',
    'Body.block',
    'meetSRight',
    'meetSRightL',
    'famString',
    'famNumber',
    'famBoolean',
    'famBinary',
    'famNull',
    'famLit',
    'famSet',
    'famOpaq',
    'famList',
    'famObj',
    'objObj',
    'zipF',
    'listMeetRow',
    'rowOfG',
    'dominates',
    'Term.meetSL',
    'Term.meetSTs',
].join(', ')

/** One read verdict, as a Lean `theorem`; `src/`'s answer is taken by running `decode`. */
export const leanReadVerdict = (one: ReadVerdict): string => {
    const { name, codec, attribute } = one
    const decodes = readsBack(codec, attribute)
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
 * Generated at gate time and elaborated, never committed.
 */
export const leanReadModule = (verdicts: readonly ReadVerdict[]): string =>
    `import Calculus.DynamoDB

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
        `      ((denote (${leanTermOf(codec, name)})).p`,
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
 * The header imports `Calculus.DynamoDB` as well, because a `held` term spells
 * `numeralOfStoredText` and `textOfNumeral`, which the DynamoDB port defines, and `Vectors`
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
    return `import Calculus.Vectors
import Calculus.DynamoDB

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
 * `docs/architecture.md`, beside the classifier this is the other half of.
 */
export const leanResolutionModule = (
    writes: readonly Resolution[],
    reads: readonly ReadResolution[],
): string =>
    `import Calculus.Vectors
import Calculus.DynamoDB

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
const preamble = `import Calculus.Denote
import Calculus.Frontier
import Calculus.DynamoDB
import Mathlib.Tactic.FinCases

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by \`src/codec/lean.ts\` from the shipped TypeScript codecs: each
theorem below is one \`encode\` this library actually performed, proposed to the model as an
equation. A failure here is a disagreement between \`src/codec/codec.ts\` and \`Calculus.denote\`, and the
theorem's name says which vector.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a \`k\` it never reads. \`Calculus/\` itself builds warning-free and so should this file; the
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
import Calculus.DynamoDB

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
binds a \`k\` it never reads. \`Calculus/\` itself builds warning-free and so should this file; the
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
    const body = `${written}${readBack}`
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
