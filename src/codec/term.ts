/**
 * §3's term language, and the five functions of a term that the model computes.
 *
 * Derived from `formal/Calculus/Term.lean`, with `member` from `Denote.lean`'s `μSyn`, `specOf`
 * from `Denote.lean`, and {@link occV}/{@link occA} from `Orthogonality.lean`. {@link tagsOf} has
 * no counterpart there: the tag table is a host index, and no term carries it. One
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
 * can see. `ExactV.lean` writes the case that forced this — `liftQ (inL k ls)`, where `ls` is a
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
    /**
     * §5's bottom: the term that admits no value.
     *
     * A constructor rather than a union over no options. The empty option list is a term a caller
     * can build by accident, and a rule that reads it as the bottom reads that accident as intent.
     */
    | { readonly kind: 'never' }

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
    /** The absence is in the row *and* in the value, and the key is still there. */
    | { readonly mark: 'undefinable'; readonly t: Term }

/** Whether the row always carries this field's attribute. */
export const alwaysWritten = (field: Field): boolean =>
    field.mark === 'req' || field.mark === 'fallback'

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
        // nothing is written, so there is no member stored
        case 'never':
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
        // **A closed form, not `⊤`.** §5 separates the two things a `⊤` covers: *unknown*, which is
        // `held`, `custom` and a host `lazy`, and *everything*, which is `opaque` by design. The
        // model takes the second as data — `occV (.opaq lossy)` is `occTop` and `occBut .num` at
        // `refuse` — so answering `undefined` here would say "cannot be read" about the one term
        // whose occupancy is fully known, and {@link separable} would then decline to compare it.
        case 'opaq':
            return t.lossy
                ? everySlot
                : everySlot.filter((slot) => slot !== 'number')
        // **Empty, not `undefined`.** `undefined` is the `⊤` that says "cannot be read", and this
        // term's occupancy is fully known: it is nothing. The model spells it `occNone`.
        case 'never':
            return []
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
        // the closed form again, for the reason {@link occV}'s `opaq` row gives
        case 'opaq':
            return t.lossy
                ? everyMember
                : everyMember.filter((one) => one !== 'N')
        // empty and not `undefined`, for the reason {@link occV}'s `never` row gives
        case 'never':
            return []
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
        spec[name] = alwaysWritten(field)
    }
    return spec
}

/**
 * One declared name, as **structural admission** reads it.
 *
 * The model's `NameSpec`: `required` is what `keysOk` reads, `alts` what `literalsOk` reads. Split
 * across two host readers rather than one record, because {@link specOf} already answers the first
 * for every declared name and this answers the second for the few names a literal pins.
 */
export type NameLiteral = {
    readonly required: boolean
    readonly alts: Literal
}

/**
 * The literal each declared name is pinned to — the names with no literal field are absent, and a
 * non-object term answers `undefined`.
 *
 * **Every mark, not `req` alone**, which is where this parts company with {@link tagsOf}. A tag has
 * to be written, so `tagsOf` reads `req` and refuses the other three. A literal *field* constrains
 * exactly the values that carry the name whatever its mark, and admission is present-only, so an
 * `optional` literal is read here and its `required` says `false`. That is the model's
 * `altsOfField`, which has a row for `req`, `optional` and `fallback` alike.
 */
export const literalsOf = (
    t: Term,
): Readonly<Record<string, NameLiteral>> | undefined => {
    if (t.kind !== 'object') return undefined
    const literals: Record<string, NameLiteral> = {}
    for (const [name, field] of Object.entries(t.body.fields)) {
        const alts = pinnedLiteral(field.t)
        if (alts) literals[name] = { required: alwaysWritten(field), alts }
    }
    return literals
}

/**
 * The literal a term is pinned to, reading through a refinement.
 *
 * A refinement of a literal admits a subset of that literal's alternatives, so the literal is a
 * sound upper bound on what the field can carry: a value outside it is outside the field, and a
 * value inside it that the refinement rejects is the option's own error to report. `setBaseOf`
 * reads through `refine` for the same reason.
 */
const pinnedLiteral = (t: Term): Literal | undefined =>
    t.kind === 'literal'
        ? t
        : t.kind === 'refine'
          ? pinnedLiteral(t.inner)
          : undefined

/**
 * The tags an object option answers to on discriminator `d` — empty for everything else.
 *
 * **`req` only, and a string literal only.** A `fallback` discriminator would fill an absent tag
 * with an arbitrary value the tag sets never vouched for, and (C) would then re-encode a variant no
 * tag selects; an `optional` one would let the tag be absent altogether. So four facts are read off
 * one question: the term is an object, `d` is declared, the field is `req`, and its term is a
 * literal at the string base. The model reads none of this, because no term carries the table.
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
 * **`Orth` certifies two of these cases now and this row is still not redundant.** Since `OrthL`,
 * the model certifies two literals at one base with disjoint alternatives, and two
 * `refine(set b, each(members …))` at one base with disjoint alternatives. Measured over the 378
 * corpus pairs, removing this row and porting `OrthL` in its place loses twenty pairs and gains
 * none, in three groups: a `dunion` against anything, which no phase of `Orth` reaches; a literal
 * against an occupancy that is `⊤`, which is the over-approximation refusing to certify; and a
 * literal against its own base, where the union really is ambiguous at the literal's values and
 * the model's decline is correct rather than incomplete. So this row is not an exemption waiting
 * for a certificate. It is a wider rule than `Orth`'s, and the last group is a question about the
 * rule rather than about the proof.
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
        // …and a term that admits nothing turns every value down, which is evidence too
        case 'never':
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
 * **One option's values are all admitted by the other**, so the narrower one can never be chosen.
 *
 * §5's `select` acts only where *exactly one* option admits. If every value `X` admits is also
 * admitted by `Y`, then the union is undefined on all of `X` and is `Y` everywhere else, so `X` is
 * a declared option no value reaches. That is not ambiguity and no discriminator fixes it. The
 * option has to go.
 *
 * `opaque` was the first instance and `f083188` refused it. These are the other two, and they are
 * the same sentence: a **restriction against the thing it restricts**. A literal against its own
 * base's ground term, and a set of a literal against the plain set at that base — which is spelled
 * `refine(set b, each(members …))`, so this reads the predicate rather than a subterm.
 *
 * Two restrictions of one base are a different shape and still declare:
 * `union([string('A'), string('B')])` is two options neither of which contains the other, and
 * `Orth` certifies it since `OrthL`. So this row asks containment, never disjointness.
 *
 * The type level says the same thing already — `Overlaps` fires on a subtype either way round —
 * so a typed caller never reaches this. What reaches it is a cast, a JavaScript caller, or an
 * erased path. This is the runtime agreeing with the type rather than a new refusal.
 */
export const restricts = (x: Term, y: Term): boolean => {
    // the empty set is contained in every set, which is `opaque`'s rule at the opposite width
    if (x.kind === 'never') return true
    // a literal is a refinement of its base: every value it admits, the base admits
    if (x.kind === 'literal' && y.kind === x.base) return true
    // …and a set of a literal is a restriction of the plain set at that base
    return (
        x.kind === 'refine' &&
        x.inner.kind === 'set' &&
        x.q.kind === 'each' &&
        x.q.of.kind === 'members' &&
        y.kind === 'set' &&
        y.base === x.inner.base
    )
}

/**
 * Whether two bodies' name intervals meet: neither requires a name the other does not declare.
 *
 * A body admits every name set between its required names and its declared names, so the two
 * intervals intersect exactly on that condition. `Calculus.OrthM` read positively, and the same
 * rule `Collides` states in the type.
 */
const namesMeet = (x: Body, y: Body): boolean => {
    for (const [name, field] of Object.entries(x.fields)) {
        if (alwaysWritten(field) && !(name in y.fields)) return false
    }
    for (const [name, field] of Object.entries(y.fields)) {
        if (alwaysWritten(field) && !(name in x.fields)) return false
    }
    return true
}

/**
 * Whether two literals at one base admit nothing in common.
 *
 * Different bases answer `false` and not `true`. `string('a')` and `decimal('a')` are read from two
 * different attribute members, so they never meet on the stored side — but they meet on the value
 * side, where both are the text `'a'`, and a pair separated on one side only is not separated.
 */
const altsApart = (x: Literal, y: Literal): boolean =>
    x.base === y.base &&
    !(x.ls as readonly unknown[]).some((one) =>
        (y.ls as readonly unknown[]).some((other) =>
            one instanceof Uint8Array
                ? other instanceof Uint8Array &&
                  one.length === other.length &&
                  one.every((byte, at) => byte === other[at])
                : one === other,
        ),
    )

/**
 * **Whether some value satisfies both object structures** — the runtime half of `StructuralMeet`.
 *
 * Two clauses, and the second is what pass 7 added: the name intervals meet, and no shared
 * **required** name is pinned to literals with nothing in common. `required` on both sides is the
 * rule `Calculus.OrthS` states, because two objects sharing an *optional* literal name with
 * disjoint alternatives both admit the map that omits the name.
 */
export const structuralMeet = (
    x: Extract<Term, { kind: 'object' }>,
    y: Extract<Term, { kind: 'object' }>,
): boolean => {
    if (!namesMeet(x.body, y.body)) return false
    const theirs = literalsOf(y) ?? {}
    for (const [name, mine] of Object.entries(literalsOf(x) ?? {})) {
        const other = theirs[name]
        if (!mine.required || !other?.required) continue
        if (altsApart(mine.alts, other.alts)) return false
    }
    return true
}

/**
 * The object members a term offers: itself, or a union's options where every one is an object.
 *
 * **A dissection is a union of objects**, so a union option that is one has members to compare
 * rather than an occupancy to meet. Without this, `union([discriminatedUnion(…),
 * discriminatedUnion(…)])` is two terms that both write `M`, and the occupancy meet refuses it —
 * which it did not do while a dissection was a term of its own, because `identifies` answered for
 * it. Deleting the second sum moved that fact here, where it is a statement about structures
 * rather than a claim that a whole union decides its own values.
 */
const objectMembers = (
    t: Term,
): readonly Extract<Term, { kind: 'object' }>[] | undefined => {
    if (t.kind === 'object') return [t]
    if (t.kind !== 'union' || t.options.length === 0) return undefined
    return t.options.every((o) => o.kind === 'object')
        ? (t.options as readonly Extract<Term, { kind: 'object' }>[])
        : undefined
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
 * Four rows, and each carries its own warrant. A fifth exempted an `opaque` option and is gone;
 * the paragraph below the fourth says why.
 *
 * **Two object options: the structural meet, which is the same question the type asks.** A union
 * admits an object by its structure, never by being attempted — the names present, and then every
 * literal field the value carries. Two such options are separable exactly where no value satisfies
 * both structures: either their name intervals do not meet (`OrthM`, and `Collides` is that written
 * in the type) or some shared required name is pinned to literals with nothing in common (`OrthS`).
 * This answers that, so the runtime and the declaration decide by one rule rather than two.
 *
 * **One object option beside a non-object is separable outright**, and that is not this rule
 * declining. An object writes a map and nothing else does, so the two never meet on either side.
 *
 * **An option that is a restriction of another.** {@link restricts}, and it *refuses* where every
 * other row accepts, so it sits ahead of them. `opaque` was the first instance of the rule and had
 * its own paragraph below; a literal against its base and a literal set against its base's plain
 * set are the other two.
 *
 * **An option that identifies its own values.** {@link identifies}, whose warrants are on it, and
 * the row is permanent rather than pending. `Orth` carries a phase `OrthL` now, so the flat
 * literal case and the literal-set case are certified. Porting `OrthL` here would be dead code:
 * every pair it certifies, this row already accepts, and the row accepts twenty corpus pairs the
 * model does not certify. {@link identifies} names the three groups.
 *
 * **An occupancy that is unknown.** `held`'s `f` runs before the subterm and can move a value into
 * any constructor, `custom` is arbitrary both ways, and a host `lazy` cannot be read without
 * forcing a binding that may not exist. The model takes the same direction for the same reason:
 * over-approximating an occupancy is safe, so a pair involving one is not certified rather than
 * A term the model cannot spell at all takes the same answer by the same argument, and the caller
 * owns that case: `union` skips a pair with an absent term before it asks, so this takes two terms
 * and has no row for one that is missing.
 *
 * **There is no `opaque` row, and its removal is the rule this function most recently learned.**
 * §5 separates the two things a `⊤` covers: *unknown* — `held`, `custom` and a host `lazy`, whose
 * answer exists and cannot be read — and *everything*, which is `opaque`, accepting every kind by
 * design. The model states the second as a **closed form**, `occTop` at `lossy` and `occBut .num`
 * at `refuse`, so it can be compared; this library read it as `⊤` and exempted it instead, which
 * meant `union([opaque, X])` declared.
 *
 * **JH ruled that union unacceptable, and the model says why.** It is not equal to `opaque`: it is
 * *undefined* wherever `X` admits, because `opaque` admits every value `X` does and `select` acts
 * only where exactly one option does. Everywhere else it is `opaque`. So `X` is a declared option
 * that no value can ever choose — §5's failure, not a rank. `occV` and `occA` answer the closed
 * form now, `Orth1` finds the meeting, and the pair is refused at the declaration.
 *
 * **Otherwise `Orth1`, both sides conjoined.** A pair separated on one side only is not separated:
 * the loosened form ships `union([decimal, number])`, which writes `'1.5'` to an `N` and cannot read
 * back what it wrote, because `decimal` takes a string and `number` a number while both store `N`.
 */
export const separable = (x: Term, y: Term): boolean => {
    // **Containment before the object exemption.** The three {@link restricts} rows name a literal,
    // a set of a literal and `never`, and an object option is none of them — so the only pair
    // whose answer this order changes is an object option beside `never`.
    if (restricts(x, y) || restricts(y, x)) return false
    const xs = objectMembers(x)
    const ys = objectMembers(y)
    if (xs && ys) {
        return xs.every((a) => ys.every((b) => !structuralMeet(a, b)))
    }
    if (x.kind === 'object' || y.kind === 'object') return true
    if (identifies(x) || identifies(y)) return true
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
 * `member` cannot answer this: `decimal.set()` and `number.set()` both write `NS`, so the member
 * cannot tell them apart and the term can — which is why `SetBase` indexes
 * a set by a base rather than by a `Member`. Reads through `refine` and a literal only — both are *restrictions* of a base, so the set
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
