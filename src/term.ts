/**
 * §3's term language, and the five functions of a term that the model computes.
 *
 * Derived from `formal/Calculus/Term.lean`, with `member` from `Denote.lean`'s `μSyn`, `specOf`
 * and `tagsOf` from `Denote.lean`, and {@link occV}/{@link occA} from `Orthogonality.lean`. One
 * variant per model constructor, under the model's own names, so a reader holding the two files
 * side by side is reading one language twice rather than two languages that agree.
 *
 * **Why the term is its own module.** Every constructor in `codec.ts` writes one of these as its
 * `def`, and `denote.ts` reads one to build the pair. The type is the model's, so a state the model
 * cannot represent — a `set` indexed by an element term, a literal whose alternatives are not
 * indexed by their base, a field where a term is wanted — is unreachable rather than checked for.
 *
 * The one place this language is **wider** than the model is `lazy`, and the row says why.
 */

import type { AttributeName, AttributeValue } from './attribute'
import type {
    LiteralBase,
    Refinement,
    Result,
    Rng,
    SetBase,
    Slot,
} from './codec'

/* ── the term ─────────────────────────────────────────────────────────────────────────── */

/**
 * A nonempty list, which is what `NEFinset` buys the model at a literal.
 *
 * Two of `NEFinset`'s three guarantees are here: the element type, from the base that indexes
 * {@link Literal}, and non-emptiness, from the tuple's head. **Pairwise distinctness is not**, and
 * TypeScript cannot say it — so it stays a refusal at the constructor, with a test that pins it and
 * the reason written above the refusal.
 */
export type NonEmpty<T> = readonly [T, ...T[]]

/**
 * §3 `(literal)`: a ground base, and a nonempty set of that base's alternatives.
 *
 * **Five variants rather than one with a `base` field**, and that is the whole content. One
 * variant with `base: LiteralBase` beside `ls: readonly LiteralValue[]` admits
 * `{ base: 'decimal', ls: [1, 2] }` — a decimal literal whose alternatives are numbers, which
 * nothing can encode. The model has no such term: `ls` is a `NEFinset k.Carrier`, so the base
 * *indexes* the alternatives. This is that indexing, in the one form TypeScript has for it.
 *
 * `decimal` carries text, which is the reason the base is recorded at all: a decimal literal's
 * alternatives are strings and it stores `N`, so neither the member nor the JS type of the values
 * recovers the base.
 */
export type Literal =
    | {
          readonly kind: 'literal'
          readonly base: 'string'
          readonly ls: NonEmpty<string>
      }
    | {
          readonly kind: 'literal'
          readonly base: 'decimal'
          readonly ls: NonEmpty<string>
      }
    | {
          readonly kind: 'literal'
          readonly base: 'number'
          readonly ls: NonEmpty<number>
      }
    | {
          readonly kind: 'literal'
          readonly base: 'boolean'
          readonly ls: NonEmpty<boolean>
      }
    | {
          readonly kind: 'literal'
          readonly base: 'binary'
          readonly ls: NonEmpty<Uint8Array>
      }

/**
 * §3 `(refine)`'s `q`, as the term carries it.
 *
 * The model's `q` is a bare `Value → Bool` and the host's used to be the caller's closure. Neither
 * is enough, because **`identifies` has to read the predicate as data**: §5's fourth discharger row
 * is about a term deciding which values are its own, and a closure decides nothing a declaration
 * can see. `Exactness.lean` writes the case that forced this — `liftQ (inL k ls)`, where `ls` is a
 * `NEFinset` and not a function.
 *
 * So three cases. `members` is membership of a {@link Literal}'s alternatives — the whole literal
 * and not a base beside a list, so a `decimal` membership over numeric alternatives is
 * unrepresentable here for the same reason it is unrepresentable as a term. `each` is
 * `liftQ`: every element of a wire set satisfies the element's predicate, which is what makes
 * `set(literal …)` expressible as a refinement of the set — the equation `setCodec_restrict` and
 * `setCodec_restrict_p` prove on both halves of the pair. `closure` is the caller's function, which
 * no declaration reads and no `Term` prints.
 */
export type Predicate =
    | { readonly kind: 'members'; readonly literal: Literal }
    | { readonly kind: 'each'; readonly of: Predicate }
    | { readonly kind: 'closure'; readonly q: Refinement }

/** §3's terms. One variant per `Term.lean` constructor, under the model's names. */
export type Term =
    | { readonly kind: 'string' }
    | { readonly kind: 'number' }
    | { readonly kind: 'decimal' }
    | { readonly kind: 'boolean' }
    | { readonly kind: 'binary' }
    | { readonly kind: 'null' }
    | Literal
    /**
     * §3 `(set)`, indexed by its element **base** and not by an element term.
     *
     * The premise `setMember μ = some μS` was partial, so a constructor over element terms accepted
     * terms the rule then refused. Four bases survive it, so the base is an index and the refusal is
     * a type error. `set(refine(b, q))` and `set(literal k ls)` are not lost as *codecs* —
     * `setCodec_restrict` and `setCodec_restrict_p` prove the set of a restriction and the
     * restriction of a set are one pair, on both halves — so `.set()` spells them as
     * `refine(set(b), each(…))`, with {@link elementPredicates} naming the restriction.
     */
    | { readonly kind: 'set'; readonly base: SetBase }
    | { readonly kind: 'array'; readonly elem: Term }
    /** `(tuple)` and `(tuple-tail)` in one variant; no tail is the plain tuple. */
    | {
          readonly kind: 'tuple'
          readonly elems: readonly Term[]
          readonly tail?: Term
      }
    | { readonly kind: 'record'; readonly val: Term }
    /** §3 `(held)`: the iso, both halves, as the caller supplied them. */
    | {
          readonly kind: 'held'
          readonly inner: Term
          readonly f: (value: never) => unknown
          readonly g: (held: never) => unknown
      }
    /**
     * §3 `(refine)`. The model carries `q : Value → Bool`; this carries a {@link Predicate}, so a
     * declaration can read the ones that are data. The caller's closure rides in `closure`, with
     * `what` as the refusal text and `arbitrary` as what a generator derived from the term reads.
     */
    | { readonly kind: 'refine'; readonly inner: Term; readonly q: Predicate }
    /** §3 `(legacy)`: `r : Attr ⇀ Value`, the older reading, which widens `p` and never `e`. */
    | {
          readonly kind: 'legacy'
          readonly inner: Term
          readonly r: (attribute: AttributeValue) => unknown
      }
    | { readonly kind: 'nullable'; readonly inner: Term }
    /**
     * §3 `(lazy)`, and **the one row where this language is wider than the model's.**
     *
     * `Term.lazy` carries a plain `Term`, and `Term.lean` says why in as many words: a closure adds
     * no constructible term, every `Term` being finite either way, and recursive codecs are not
     * modelled and cannot be — `union`'s admission is anti-monotone, so a genuinely recursive union
     * has no fixpoint semantics in any system.
     *
     * This library supports a recursive entity through a thunk, and `codec.recursive.spec.ts`
     * declares one. So the thunk stays, the emitter refuses a `lazy`, and {@link occV} and
     * {@link occA} answer `undefined` here rather than the subterm's — because reading through
     * forces a binding that may not exist at declaration time, and a declaration-time guard that
     * forces is a guard that throws on the entity it exists to allow.
     */
    | { readonly kind: 'lazy'; readonly get: () => Term }
    /** §3 `(custom)`: the pair as data. The two generators are the caller's and ride here too. */
    | {
          readonly kind: 'custom'
          readonly ce: (value: never) => Result<AttributeValue>
          readonly cp: (attribute: AttributeValue) => unknown
          readonly arbitrary?: (rng: Rng, size: number) => unknown
          readonly shrink?: (value: never) => readonly unknown[]
      }
    /** §3 `(opaque)`: `lossy = false` is the `refuse` policy — the absence of the `number` option. */
    | { readonly kind: 'opaq'; readonly lossy: boolean }
    | { readonly kind: 'object'; readonly body: Body }
    | { readonly kind: 'union'; readonly options: readonly Term[] }
    | {
          readonly kind: 'dunion'
          readonly d: string
          readonly options: readonly Term[]
      }

/**
 * §4's object payload: the declared names with the field at each, and the policy for the rest.
 *
 * A record from name to {@link Field} **is** the model's `Finset Name` paired with a function on
 * it: no repeats, no ordering for a statement to have to ignore. The model spends a paragraph
 * arguing that shape against a list of pairs, and TypeScript gives it for nothing.
 */
export type Body = {
    readonly fields: Readonly<Record<string, Field>>
    readonly rest: Rest
}

/**
 * §4's field: a term with a presence mark, and **not a term**.
 *
 * No member of {@link Term} holds one, which is §4's stratification as a type rather than a check.
 * `array(optional(c))` is not a thing this type can express.
 */
export type Field =
    | { readonly mark: 'req'; readonly t: Term }
    | { readonly mark: 'optional'; readonly t: Term }
    /** `fallback` concludes `req` (§4): the absence is in the row, never in the value. */
    | { readonly mark: 'fallback'; readonly t: Term; readonly v: unknown }

/** §4's rest policy. `codec` is the one that holds an undeclared name; the two others refuse it. */
export type Rest =
    | 'drop'
    | 'refuse'
    | { readonly kind: 'codec'; readonly t: Term }

/* ── the member index ─────────────────────────────────────────────────────────────────── */

/** Which member each ground base stores. Not injective: `number` and `decimal` both store `N`. */
const baseMember: { readonly [B in LiteralBase]: AttributeName } = {
    string: 'S',
    number: 'N',
    decimal: 'N',
    boolean: 'BOOL',
    binary: 'B',
}

/** …and which member a set of that base stores. Four bases onto three wire members. */
const setMember: { readonly [B in SetBase]: AttributeName } = {
    string: 'SS',
    number: 'NS',
    decimal: 'NS',
    binary: 'BS',
}

/**
 * §5 `(union)`'s member: `μ` where every option agrees, and `⊤` otherwise.
 *
 * An empty list answers `⊤`, as the model's `unanimous` does. A list of `⊤`s answers `⊤` too, and
 * by agreement rather than by default — which is the same answer and not the same reason.
 */
export const unanimous = (
    members: readonly (AttributeName | undefined)[],
): AttributeName | undefined => {
    const [first, ...rest] = members
    return first !== undefined && rest.every((one) => one === first)
        ? first
        : undefined
}

/**
 * `μSyn`: the member a term stores, read off the term.
 *
 * `undefined` is the model's `⊤` — *not determined by the term* — and the four rows that answer it
 * do so for four different reasons (§3): `nullable` writes its subterm's member or `NULL` and so
 * names neither, `lazy` could be asked but answering forces the thunk, `custom` is a pair of opaque
 * functions with nothing to ask, and `opaque` writes whatever the value turns out to be.
 */
export const member = (t: Term): AttributeName | undefined => {
    switch (t.kind) {
        case 'string':
            return 'S'
        case 'number':
        case 'decimal':
            return 'N'
        case 'boolean':
            return 'BOOL'
        case 'binary':
            return 'B'
        case 'null':
            return 'NULL'
        case 'literal':
            return baseMember[t.base]
        case 'set':
            return setMember[t.base]
        case 'array':
        case 'tuple':
            return 'L'
        case 'record':
        case 'object':
        case 'dunion':
            return 'M'
        // a wrapper preserves the member (§6), which is what keeps a key's attribute type stable
        case 'held':
        case 'refine':
        case 'legacy':
            return member(t.inner)
        case 'nullable':
        case 'lazy':
        case 'custom':
        case 'opaq':
            return undefined
        case 'union':
            return unanimous(t.options.map(member))
    }
}

/* ── occupancy ────────────────────────────────────────────────────────────────────────── */

/** A ground base's value slot. `decimal` is held as text, which is why it lands on `string`. */
const baseSlot: { readonly [B in LiteralBase]: Slot } = {
    string: 'string',
    number: 'number',
    decimal: 'string',
    boolean: 'boolean',
    binary: 'binary',
}

/**
 * …and a set base's. Four bases onto three slots, colliding at `string`/`decimal`, where
 * {@link setMember} collides at `number`/`decimal` instead. The two collisions are disjoint, which
 * is why the pair of families separates all four bases and neither family does alone.
 */
const setSlot: { readonly [B in SetBase]: Slot } = {
    string: 'strSet',
    number: 'numSet',
    decimal: 'strSet',
    binary: 'binSet',
}

const everySlot: readonly Slot[] = [
    'string',
    'number',
    'boolean',
    'binary',
    'null',
    'strSet',
    'numSet',
    'binSet',
    'array',
    'map',
]

const everyMember: readonly AttributeName[] = [
    'S',
    'N',
    'B',
    'BOOL',
    'NULL',
    'SS',
    'NS',
    'BS',
    'L',
    'M',
]

/** `⊤` is `undefined`, so a union of occupancies is `undefined` as soon as one side is. */
const joined = <A>(
    parts: readonly (readonly A[] | undefined)[],
): readonly A[] | undefined => {
    const out: A[] = []
    for (const part of parts) {
        if (part === undefined) return undefined
        for (const one of part) if (!out.includes(one)) out.push(one)
    }
    return out
}

const withOne = <A>(
    one: A,
    rest: readonly A[] | undefined,
): readonly A[] | undefined => joined([[one], rest])

/**
 * `occV`: which value constructors a term may write, or `undefined` for every one of them.
 *
 * An over-approximation on purpose. If `X ⊆ X′`, `Y ⊆ Y′` and `X′ ∩ Y′ = ∅` then `X ∩ Y = ∅`, so a
 * coarse answer costs a certificate and never buys a wrong one.
 *
 * The `undefined` rows, and why each: `held`'s `f` runs *before* the subterm and can move a value
 * into any constructor; `custom` is arbitrary in both directions; `opaque` at `lossy` accepts every
 * kind by design, and at `refuse` every kind but `number`.
 *
 * **`lazy` diverges from the model, deliberately.** `occV (.lazy t)` is the subterm's there, because
 * the model's thunk carries a finite `Term`. Here it carries a closure over a binding that may not
 * exist when a declaration asks, so reading through would force it. `undefined` is the sound
 * direction: an over-approximation costs a certificate and never buys a wrong one, and the
 * alternative throws on the recursive entity the thunk exists to allow.
 */
export const occV = (t: Term): readonly Slot[] | undefined => {
    switch (t.kind) {
        case 'string':
        case 'decimal':
            return ['string']
        case 'number':
            return ['number']
        case 'boolean':
            return ['boolean']
        case 'binary':
            return ['binary']
        case 'null':
            return ['null']
        case 'literal':
            return [baseSlot[t.base]]
        case 'set':
            return [setSlot[t.base]]
        case 'array':
        case 'tuple':
            return ['array']
        case 'record':
        case 'object':
        case 'dunion':
            return ['map']
        case 'held':
        case 'custom':
        case 'lazy':
            return undefined
        case 'refine':
        case 'legacy':
            return occV(t.inner)
        case 'nullable':
            return withOne<Slot>('null', occV(t.inner))
        case 'union':
            return joined(t.options.map(occV))
        case 'opaq':
            return t.lossy
                ? undefined
                : everySlot.filter((slot) => slot !== 'number')
    }
}

/**
 * `occA`: which members a term may read, or `undefined` for every one of them.
 *
 * The mirror of {@link occV}, and **not a symmetric mirror**: `held` and `legacy` swap sides.
 * `held`'s `g` sits *behind* `p`, so it changes which value comes out and never which attributes go
 * in, and the read occupancy is the subterm's. `legacy`'s `r` is arbitrary data the term carries and
 * widens exactly the reading, so it is `⊤` here where it was the subterm's on the write side.
 *
 * A lawful `r` does respect the member, and the model records that this is the one place `μSyn` is
 * sharper than `occA` — sharper only under an obligation no declaration-time certificate takes as a
 * premise.
 *
 * `lazy` diverges from the model for the reason {@link occV} gives.
 */
export const occA = (t: Term): readonly AttributeName[] | undefined => {
    switch (t.kind) {
        case 'string':
            return ['S']
        case 'number':
        case 'decimal':
            return ['N']
        case 'boolean':
            return ['BOOL']
        case 'binary':
            return ['B']
        case 'null':
            return ['NULL']
        case 'literal':
            return [baseMember[t.base]]
        case 'set':
            return [setMember[t.base]]
        case 'array':
        case 'tuple':
            return ['L']
        case 'record':
        case 'object':
        case 'dunion':
            return ['M']
        case 'legacy':
        case 'custom':
        case 'lazy':
            return undefined
        case 'refine':
        case 'held':
            return occA(t.inner)
        case 'nullable':
            return withOne<AttributeName>('NULL', occA(t.inner))
        case 'union':
            return joined(t.options.map(occA))
        case 'opaq':
            return t.lossy
                ? undefined
                : everyMember.filter((one) => one !== 'N')
    }
}

/* ── the name spec, and the discriminator ─────────────────────────────────────────────── */

/**
 * The names an object option answers to, each with whether the item must carry it.
 *
 * `undefined` for a non-object, which is what makes an object option the one kind chosen by names
 * rather than by being attempted. An `optional` binding is declared and not required, and that is
 * the ambiguity §5 names in the same words: two objects declaring only optional names both admit
 * the empty map, however disjoint their names.
 */
export const specOf = (
    t: Term,
): Readonly<Record<string, boolean>> | undefined => {
    if (t.kind !== 'object') return undefined
    const spec: Record<string, boolean> = {}
    for (const [name, field] of Object.entries(t.body.fields)) {
        spec[name] = field.mark !== 'optional'
    }
    return spec
}

/**
 * The tags an object option answers to on discriminator `d` — empty for everything else.
 *
 * **`req` only, and a string literal only.** A `fallback` discriminator would fill an absent tag
 * with an arbitrary value the tag sets never vouched for, and (C) would then re-encode a variant no
 * tag selects; an `optional` one would let the tag be absent altogether. So four facts are read off
 * one question, exactly as the model's `tagsOf` reads them: the term is an object, `d` is declared,
 * the field is `req`, and its term is a literal at the string base.
 */
export const tagsOf = (d: string, t: Term): readonly string[] => {
    if (t.kind !== 'object') return []
    const field = t.body.fields[d]
    if (field === undefined || field.mark !== 'req') return []
    const inner = field.t
    return inner.kind === 'literal' && inner.base === 'string' ? inner.ls : []
}

/* ── the declaration guard ────────────────────────────────────────────────────────────── */

/**
 * Whether a term decides which values are its own.
 *
 * §5's fourth discharger row: two refinements of one base read an attribute to the *same* value, so
 * at most one predicate accepts it and both sides separate. A literal is that with the predicate
 * written as data, which is why `union([string('A'), string('B')])` is not ambiguous and never was.
 *
 * **It propagates through the containers**, which is what keeps
 * `union([array(string('A')), array(string('B'))])` declarable — lawful where the union acts, and
 * proved so. Note what that costs: the pair fails `UAtCan` outright at `[]`
 * (`not_uAtCan_array_literals`) and meets only `UAtAct` (`uAtAct_array_literals`), because a
 * container admits its empty case whatever its element admits. So the warrant for the flat case and
 * the warrant for the container case are two different theorems, and only the first is about
 * literals.
 *
 * A bare `set` answers `false`: {@link Term}'s `set` carries a **base** and has no element to read.
 * `string.set('a','b')` is `refine(set(string), each(members …))`, so this row sees the literal
 * through the `refine`.
 *
 * `nullable` is left out deliberately: two nullable literals both accept `null`, so the wrapper
 * admits a value neither literal decides. `held` is left out because the conversion is a caller's
 * function and there is nothing to read.
 */
const decidesOwn = (q: Predicate): boolean =>
    q.kind === 'members' ? true : q.kind === 'each' ? decidesOwn(q.of) : false

export const identifies = (t: Term): boolean => {
    switch (t.kind) {
        case 'literal':
        // a tag lookup fails for a value carrying no tag it knows, which is the same evidence
        case 'dunion':
            return true
        case 'array':
            return identifies(t.elem)
        case 'tuple':
            return t.elems.every(identifies)
        case 'record':
            return identifies(t.val)
        case 'union':
            return t.options.every(identifies)
        // a predicate that is data decides on its own — `refine(set(b), each(members …))` is how
        // `set(literal …)` is spelled, and the literal is inside the predicate rather than inside
        // a subterm, so reading only `inner` would miss it
        case 'refine':
            return decidesOwn(t.q) || identifies(t.inner)
        case 'legacy':
            return identifies(t.inner)
        default:
            return false
    }
}

/**
 * **Whether a union may hold these two options**, asked at the declaration.
 *
 * **This is not a port of `Orth`, and the difference is the direction.** `Orth` is a *certificate*:
 * `true` means the model proved the two cannot both admit one input. This is the complement of a
 * *refutation*: it answers `false` only where both occupancies are known, they meet on a side, and
 * no exemption applies. Where `Orth` declines for want of a proof, this accepts. One row is shared
 * — `Orth1`, below — and the law that ties them is what `formal/.separations.lean` pins, one
 * theorem per pair this function refuses: **it never answers `false` where `Orth` answers `true`.**
 * Refusing a declaration the model proves separable would be refusing a union that works.
 *
 * Four rows, and each carries its own warrant.
 *
 * **An object option, either side.** A union admits an object by the names present, never by being
 * attempted, and the collision check is `Collides` — which is `OrthM` written in the type:
 * `[Exclude<RequiredKeysOf<A>, keyof B>] extends [never]` on both sides is exactly "neither side
 * requires a name the other does not declare". So the model's certificate for objects already runs,
 * one level up, and the type-level snapshot pins it. Answering `true` here is deferring to it, not
 * skipping it.
 *
 * **An option that identifies its own values.** {@link identifies}, whose two warrants are on it.
 *
 * **An occupancy that is unknown.** `held`'s `f` runs before the subterm and can move a value into
 * any constructor, `custom` is arbitrary both ways, and a host `lazy` cannot be read without
 * forcing a binding that may not exist. The model takes the same direction for the same reason:
 * over-approximating an occupancy is safe, so a pair involving one is not certified rather than
 * A term the model cannot spell at all takes the same answer by the same argument, and the caller
 * owns that case: `union` skips a pair with an absent term before it asks, so this takes two terms
 * and has no row for one that is missing.
 *
 * **An `opaque` option.** §5 separates the two things a `⊤` covers: *unknown* — `held`, `custom`
 * and a host `lazy`, whose answer exists and cannot be read — and *everything*, which is
 * `opaque`, accepting every kind by design. The model takes the second as a **closed form**:
 * `occV (.opaq lossy)` is `occTop` at `lossy` and `occBut .num` at `refuse`, which is sharper than
 * `⊤` and sharp enough for `Orth1` to find a meeting. The host has always read it as `⊤`.
 *
 * Measured when the model's row was ported without this exemption: the corpus's refusal set moved
 * from 17 pairs to 32, and all fifteen new ones have `opaque` on a side. Every one of the fifteen
 * theorems would hold — `Orth (Term.opaq false) Term.string` evaluates to `false`, so the
 * one-directional law is untouched either way — and every one is a declaration this library
 * accepts today. The model's reading is that no value resolves such a union. That is a finding for
 * §10 and the owner's to triage, not a change this guard makes on its own, so the row answers
 * `true` and (U) guards each input as it does for the other three exemptions.
 *
 * **Otherwise `Orth1`, both sides conjoined.** A pair separated on one side only is not separated:
 * the loosened form ships `union([decimal, number])`, which writes `'1.5'` to an `N` and cannot read
 * back what it wrote, because `decimal` takes a string and `number` a number while both store `N`.
 */
export const separable = (x: Term, y: Term): boolean => {
    if (x.kind === 'object' || y.kind === 'object') return true
    if (identifies(x) || identifies(y)) return true
    if (x.kind === 'opaq' || y.kind === 'opaq') return true
    const writable = meet(occV(x), occV(y))
    const readable = meet(occA(x), occA(y))
    return writable === undefined && readable === undefined
}

/**
 * Where two occupancies meet, or nothing — and `⊤` on either side means "not compared".
 *
 * The label is what a refusal reports, so this answers the meeting rather than a boolean. `union`
 * asks again on the path it is about to throw on, which costs one walk of a term nobody will use
 * and keeps {@link separable} the `Bool` the model's `Orth` is.
 */
export const meet = <A>(
    one: readonly A[] | undefined,
    other: readonly A[] | undefined,
): A | undefined =>
    one && other ? one.find((label) => other.includes(label)) : undefined
/**
 * Which of the four set bases a term's values sit at, or `undefined` where the term is not one.
 *
 * `member` cannot answer this: `decimal.set()` and `number.set()` both write `NS`. This reads the
 * term, and reads through `refine` and a literal only — both are *restrictions* of a base, so the set
 * they build is a restriction of the base's set (`setCodec_restrict`). An adapter (`held`), a read
 * widening (`legacy`) or a union is not a restriction of anything, and gets `undefined`.
 */
export const setBaseOf = (t: Term): SetBase | undefined => {
    switch (t.kind) {
        case 'string':
        case 'number':
        case 'decimal':
        case 'binary':
            return t.kind
        case 'literal':
            return t.base === 'boolean' ? undefined : t.base
        case 'refine':
            return setBaseOf(t.inner)
        default:
            return undefined
    }
}

/**
 * What a set's element restricts by, outermost first — empty where the element restricts by nothing.
 *
 * The element of a `set` is a bare base, a literal at that base, or a refinement over either. The
 * first restricts nothing and the set is a plain `Term.set`. The other two restrict, and the set
 * is a refinement of the plain one — which is what `setCodec_restrict` and `setCodec_restrict_p`
 * license, on both halves of the pair. `.set()` wraps the plain set in one `refine(…, each(p))`
 * per predicate listed here, so a refinement over a literal contributes **both** the closure and
 * the membership, conjoined the way `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)` conjoins them.
 */
export const elementPredicates = (elem: Term): readonly Predicate[] => {
    switch (elem.kind) {
        case 'literal':
            return [{ kind: 'members', literal: elem }]
        case 'refine':
            return [elem.q, ...elementPredicates(elem.inner)]
        default:
            return []
    }
}
