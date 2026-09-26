/**
 * §3's term language, and the five functions of a term that the model computes.
 *
 * Derived from `formal/Calculus/Dynamo/Lang/Term.lean`, with `member` from `Denote.lean`'s `μSyn`, `specOf`
 * from `Denote.lean`. {@link occV}, {@link occA} and {@link tagsOf} have no counterpart there: the
 * two occupancies serve the host's union dispatch, and the tag table is a host index that no term
 * carries. One
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

import type { AttributeName, AttributeValue, DynamoNumber } from './attribute'
import type {
    LiteralBase,
    LiteralValue,
    Refinement,
    Rng,
    SetSlot,
} from './codec'
import { sameLiteral } from './value'

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
 * §3 `(literal)`: a ground base, and **one** inhabitant of that base's carrier.
 *
 * **Five variants rather than one with a `base` field**, and that is the whole content. One
 * variant with `base: LiteralBase` beside `v: LiteralValue` admits
 * `{ base: 'decimal', v: 1 }` — a decimal literal whose value is a number, which nothing can
 * encode. The model has no such term: `v` is a `k.Carrier`, so the base *indexes* the value. This
 * is that indexing, in the one form TypeScript has for it.
 *
 * `decimal` carries text, which is the reason the base is recorded at all: a decimal literal's
 * value is a string and it stores `N`, so neither the member nor the JS type of the value recovers
 * the base.
 *
 * **One value, and several values are a `union`.** `string('a', 'b')` builds
 * `union([string('a'), string('b')])`, whose members are separated because the values differ. The
 * builder stays because the union form costs the type checker linearly in the number of
 * alternatives where this form is flat; {@link Alternatives} is what a reader gets back from
 * either shape.
 */
export type Literal =
    | { readonly kind: 'literal'; readonly base: 'string'; readonly v: string }
    | {
          readonly kind: 'literal'
          readonly base: 'number'
          readonly v: DynamoNumber
      }
    | {
          readonly kind: 'literal'
          readonly base: 'boolean'
          readonly v: boolean
      }
    | {
          readonly kind: 'literal'
          readonly base: 'binary'
          readonly v: Uint8Array
      }

/**
 * A base and a nonempty set of that base's values — what a reader gets back from a literal or from
 * a union of literals at one base.
 *
 * This is what {@link Literal} was before a literal carried one value, and it survives for the two
 * places the model keeps a set of alternatives too: `Pred.members`, which is a refinement
 * predicate over a `NEFinset`, and the answer {@link literalsOf} gives for a declared name. The
 * model's split is the same one, `inL` against `inLs`.
 */
export type Alternatives =
    | {
          readonly kind: 'alternatives'
          readonly base: 'string'
          readonly ls: NonEmpty<string>
      }
    | {
          readonly kind: 'alternatives'
          readonly base: 'number'
          readonly ls: NonEmpty<DynamoNumber>
      }
    | {
          readonly kind: 'alternatives'
          readonly base: 'boolean'
          readonly ls: NonEmpty<boolean>
      }
    | {
          readonly kind: 'alternatives'
          readonly base: 'binary'
          readonly ls: NonEmpty<Uint8Array>
      }

/**
 * §3 `(refine)`'s `q`, as the term carries it.
 *
 * The model's `q` is a bare `Value → Bool` and the host's used to be the caller's closure. Neither
 * is enough, because **the meet has to read the predicate as data**: a closure decides nothing a
 * declaration can see. `Pred.members` is the case that forced this: its `ls` is a `NEFinset`
 * and not a function.
 *
 * So two cases. `members` is membership of a {@link Literal}'s alternatives: the whole literal
 * and not a base beside a list, so a `decimal` membership over numeric alternatives is
 * unrepresentable here for the same reason it is unrepresentable as a term. `closure` is the
 * caller's function, which no declaration reads and no `Term` prints.
 */
export type Predicate =
    | { readonly kind: 'members'; readonly literal: Alternatives }
    | { readonly kind: 'closure'; readonly q: Refinement }

/**
 * **The two numeric policies of `opaque`**, as the `via` of the `held` that builds each one.
 *
 * The term `opaq` is total and holds a number as a `DynamoNumber`. A policy converts a JS
 * number, or refuses one, over that term. The name lets a reader find the `opaq` under the
 * adapter: containment, the generator, and the union refusal at the type level each read it.
 */
export type OpaqueSugar = 'opaqueLossy' | 'opaqueRefuse'

/** Whether a `held` is one of the two numeric policies of `opaque`. */
export const isOpaqueSugar = (via: string | undefined): via is OpaqueSugar =>
    via === 'opaqueLossy' || via === 'opaqueRefuse'

/** §3's terms. One variant per `Term.lean` constructor, under the model's names. */
export type Term =
    | { readonly kind: 'string' }
    /**
     * §3 `(number)`, and **the one native numeric term**. Its carrier is {@link DynamoNumber},
     * which is DynamoDB's own `N`. `number` and `decimal` are adapters over it and are no longer
     * terms of their own: a JS float and a decimal string are two ways a caller may hold this,
     * not two things the service stores.
     */
    | { readonly kind: 'number' }
    | { readonly kind: 'boolean' }
    | { readonly kind: 'binary' }
    | { readonly kind: 'null' }
    | Literal
    /**
     * §3 `(set)`: the finite-powerset lift of an element term. A lawful element gives a lawful set
     * (`lawful_setCodec`), and that law reads nothing about the element's base.
     *
     * That a stored set holds elements of one member of `S`, `N` or `B` is the DynamoDB universe's
     * rule, not structure here: {@link set} refuses an element that names no such member, as the
     * model's `SetElem` obligation does. A restricted element, a literal element and an adapter
     * element are each spelled at the element.
     */
    | { readonly kind: 'set'; readonly elem: Term }
    /**
     * §3 `(list)`: the one positional container, as a prefix, at most one spread, and a suffix.
     *
     * A fixed arity, a homogeneous run, and the two together are shapes of one thing, and a fixed
     * position *after* a spread — `[A, B, ...C[], D]` — is one more. A value of length
     * `n` is admitted when `n >= pre.length + suf.length`: `pre` aligns from the left, `suf` from
     * the right, and every position between them goes through the spread. With no spread the arity
     * is exactly `pre.length + suf.length`.
     *
     * **Two spreads have no term**, because `spread` is one optional member and not a list. The
     * constructor keeps its own refusal, because `list` takes its elements as a variadic parameter
     * list and a parameter list can still carry two markers.
     */
    | {
          readonly kind: 'list'
          readonly pre: readonly Term[]
          readonly spread?: Term
          readonly suf: readonly Term[]
      }
    /**
     * §3 `(held)`: a conversion between two restrictions. `inner` restricts the stored side, and
     * `outer` restricts the held side, which is the model's second term.
     */
    | {
          readonly kind: 'held'
          readonly inner: Term
          /**
           * **The held side, as a term.** The write occupancy of a `held` is the occupancy of this
           * term, as the model's `occV (held t P f g) = occV P` states. A library adapter records
           * the base it hands to the caller. A foreign schema records `opaque`, the top, because
           * the library cannot read which kinds of value a foreign schema admits.
           */
          readonly outer: Term
          readonly f: (value: never) => unknown
          readonly g: (held: never) => unknown
          /**
           * **Which adapter this is, where the library ships it**, so a vector can cite the pair
           * by name. The emitter prints `held` only for a pair it recognises, the way it already
           * prints `isNumeral` and `isStoredNumeral` for the predicates: a caller's closure has
           * no name in the model and is refused.
           *
           * Separate from {@link outer} on purpose. That says which slots the conversion lands
           * in and is read by the certificate; this says which named pair the model carries and
           * is read by the emitter. One of them can be known without the other.
           */
          readonly via?: 'decimalText' | OpaqueSugar
          /**
           * **The generators, where the caller supplies them rather than the inner codec.**
           *
           * An adapter derives both from the codec underneath: a value is generated for the inner
           * term and handed out through `g`, and a value is shrunk on the inner side and handed
           * back. That is right whenever the pair is total on the inner codec's values.
           *
           * It is wrong when the adapter is partial. A conversion that refuses some of what the
           * inner codec generates makes the derived generator produce values the pair never
           * makes, and the property then fails on the generator rather than on the codec. So the
           * caller states them, and states them here because a definition carries everything the
           * caller said about a codec. Absent is the honest answer for an adapter nobody has
           * declared, and the derivation stands there.
           */
          readonly arbitrary?: (rng: Rng, size: number) => unknown
          readonly shrink?: (value: never) => readonly unknown[]
      }
    /**
     * §3 `(refine)`. The model carries `q : Value → Bool`; this carries a {@link Predicate}, so a
     * declaration can read the ones that are data. The caller's closure rides in `closure`, with
     * `what` as the refusal text and `arbitrary` as what a generator derived from the term reads.
     */
    | { readonly kind: 'refine'; readonly inner: Term; readonly q: Predicate }
    /** §3 `(withLegacyRead)`: `r : Attr ⇀ Value`, the older reading, which widens `p` and never `e`. */
    | {
          readonly kind: 'legacy'
          readonly inner: Term
          readonly r: (attribute: AttributeValue) => unknown
      }
    /**
     * A thunk, which is how this language spells a recursive schema.
     *
     * The model has no thunk. It states a recursive schema with a binder: `Term.mu` at the term a
     * thunk returns while that term is being read, and `Term.var` at the thunk. Any other thunk is
     * the term it returns. The model's guard accepts the binder
     * when the variable sits under a list or an object, and `opaque` is the same construct at a
     * fixed body.
     *
     * This library supports a recursive entity through a thunk, and `codec.recursive.spec.ts`
     * declares one, so the thunk stays. **Everything else here reads through it.**
     * {@link occV}, {@link occA} and {@link ownsNullOf} answer what the term underneath answers,
     * and `meetTerms` and the emitter read the binder at the term that closes the cycle. Only
     * {@link member} answers `undefined`, because the host cannot force a thunk safely at
     * declaration: forcing a recursive thunk can loop.
     *
     * **The two projections answered `undefined` until it was measured, on the ground that
     * forcing would throw on the entity the thunk exists to allow. Both halves were wrong.**
     * Forcing does not throw: `object()` already forces at the declaration and the recursive
     * entity still round-trips. And `undefined` was the unsound direction rather than the safe
     * one, because the declaration guard then refused a union when two occupancies *met*, so an
     * unknown occupancy made it decline to refuse. `union([lazy(string), string])` was accepted
     * and a write then found two options admitting one value. `lazy` was the only
     * term answering unknown on both projections, which is why it was the only hole.
     */
    | { readonly kind: 'lazy'; readonly get: () => Term }
    /**
     * §3 `(opaque)`: the universal sum, and **total**. It holds a number as {@link DynamoNumber},
     * which is the model's `WFNumeral`, so it writes every wire value. The two numeric policies
     * `'refuse'` and `'lossy'` are not terms of their own: each is a `held` over this term.
     */
    | { readonly kind: 'opaq' }
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
 * §4's object payload: the declared names with the field at each, and the open block.
 *
 * A record from name to {@link Field} **is** the model's `Finset Name` paired with a function on
 * it: no repeats, no ordering for a statement to have to ignore. The model spends a paragraph
 * arguing that shape against a list of pairs, and TypeScript gives it for nothing.
 */
export type Body = {
    readonly fields: Readonly<Record<string, Field>>
    /**
     * **The open block**, the model's `Option Term`: the term every undeclared name
     * holds. A body is a partition of the key space, so a name is declared, or it falls in the
     * block, or the body refuses it. Absent is the one closed state.
     */
    readonly rest?: Term
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
    /** `withLegacyRead` concludes `req` (§4): the absence is in the row, never in the value. */
    | { readonly mark: 'fallback'; readonly t: Term; readonly v: unknown }
    /** The absence is in the row *and* in the value, and the key is still there. */
    | { readonly mark: 'undefinable'; readonly t: Term }

/** Whether the row always carries this field's attribute. */
export const alwaysWritten = (field: Field): boolean =>
    field.mark === 'req' || field.mark === 'fallback'

/* ── the member index ─────────────────────────────────────────────────────────────────── */

/**
 * Which member each ground base stores, and it is injective again. `decimal` was the second base
 * at `N`, and it is an adapter over `number` now rather than a base, so no two bases share a
 * member and nothing downstream has to tell two of them apart by anything but the member.
 */
const baseMember: { readonly [B in LiteralBase]: AttributeName } = {
    string: 'S',
    number: 'N',
    boolean: 'BOOL',
    binary: 'B',
}

/**
 * The member a set stores, from the member its element stores: `setMember`. An element of any
 * other member has no stored set, and answers the model's `none`.
 */
const setMemberOf = (
    element: AttributeName | undefined,
): AttributeName | undefined =>
    element === 'S'
        ? 'SS'
        : element === 'N'
          ? 'NS'
          : element === 'B'
            ? 'BS'
            : undefined

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
 * `undefined` is the model's `⊤`: *not determined by the term*. A thunk answers it for a reason of
 * the host: the host cannot force a thunk safely here, because forcing a recursive thunk can loop,
 * which is a limit of the host's carrier. A caller that needs one member, as a DynamoDB set does,
 * refuses the thunk: a set holding one element member is a fact of the store universe. `opaque`
 * writes whatever the value turns out to be, `never` writes nothing, and a `union` answers it
 * where its options do not agree on one member. `nullable` is such a union.
 */
export const member = (t: Term): AttributeName | undefined => {
    switch (t.kind) {
        case 'string':
            return 'S'
        case 'number':
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
            return setMemberOf(member(t.elem))
        case 'list':
            return 'L'
        case 'object':
            return 'M'
        // a wrapper preserves the member (§6), which is what keeps a key's attribute type stable
        case 'held':
        case 'refine':
        case 'legacy':
            return member(t.inner)
        case 'lazy':
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
const baseSlot: { readonly [B in LiteralBase]: SetSlot } = {
    string: 'string',
    number: 'number',
    boolean: 'boolean',
    binary: 'binary',
}

/**
 * The wire family a set writes for each scalar slot its element writes: `Slot.setElem`, read from
 * the element's side.
 */
const setSlotOf = (slot: SetSlot): SetSlot | undefined =>
    slot === 'string'
        ? 'strSet'
        : slot === 'number'
          ? 'numSet'
          : slot === 'binary'
            ? 'binSet'
            : undefined

/** The three wire set families: the occupancy of a set whose element family is not known. */
const everySetFamily: readonly SetSlot[] = ['strSet', 'numSet', 'binSet']

export const everySlot: readonly SetSlot[] = [
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

/**
 * `occV`: which value constructors a term may write.
 *
 * An over-approximation on purpose. If `X ⊆ X′`, `Y ⊆ Y′` and `X′ ∩ Y′ = ∅` then `X ∩ Y = ∅`, so a
 * coarse answer costs a certificate and never buys a wrong one.
 *
 * A `held` answers the occupancy of its held side, the term `outer`: the held side restricts
 * every value that `f` receives. A foreign schema records `opaque` there, so the answer is every
 * slot. `opaque` accepts every kind by design, and its row answers that closed form, not `undefined`.
 * A thunk reads through to its subterm, as the model reads the term a thunk returns.
 */
export const occV = (t: Term): readonly SetSlot[] => {
    switch (t.kind) {
        case 'string':
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
        // a set writes the wire family of each scalar slot its element writes. **An element slot
        // with no family answers every family, not none.** The model's caller carrier has no
        // set of booleans, so the model drops the slot exactly. The host caller carrier holds
        // sets that the stored universe has no family for: `refine(held(string, boolean, …),
        // isTrue).set()` admits a `Set<boolean>` and writes the set. The occupancy must
        // over-approximate, so the occupancy keeps that slot. Two such sets then overlap, and
        // `union` refuses the pair at construction
        case 'set':
            return [
                ...new Set(
                    occV(t.elem).flatMap(
                        (slot) => setSlotOf(slot) ?? everySetFamily,
                    ),
                ),
            ]
        case 'list':
            return ['array']
        case 'object':
            return ['map']
        // the held side restricts every value `f` receives, as `occV (held t P f g) = occV P`
        case 'held':
            return occV(t.outer)
        // a thunk carries a term, so it answers what that term answers. `Meet.lean` heads the
        // section `lazy` is transparent, and it constrains nothing: the model reads through on
        // both projections and only the member is lost
        case 'lazy':
            return occV(t.get())
        case 'refine':
        case 'legacy':
            return occV(t.inner)
        case 'union':
            return [...new Set(t.options.flatMap(occV))]
        // **A closed form, not `⊤`.** §5 separates the two things a `⊤` covers: *unknown*, which is
        // the read side of a `legacy`, and *everything*, which is `opaque` by design. The
        // model takes the second as data — `occV .opaq` is `occTop` — so answering
        // `undefined` here would say "cannot be read" about the one term whose occupancy is fully
        // known.
        case 'opaq':
            return everySlot
        // **Empty, not `undefined`.** `undefined` is the `⊤` that says "cannot be read", and this
        // term's occupancy is fully known: it is nothing. The model spells it `occNone`.
        case 'never':
            return []
    }
}

/**
 * Whether a term reaches the null point, read off the term.
 *
 * `undefined` is *not determined by the term*, and it is what makes {@link nullable} refuse at
 * construction rather than guess. `withLegacyRead` answers it, because its older reader is the
 * caller's function. `refine` and `union` answer it through their subterms, as the next paragraph
 * says. A `held` answers from the slots it declares, and `lazy` reads through the thunk.
 *
 * `refine` answers `false` through its subterm and `undefined` otherwise: a predicate narrows, so
 * a subterm that does not reach the point keeps not reaching it, while one that does may or may not
 * survive the predicate, and this reads no predicate.
 *
 * A union's options are separated by construction, so at most one admits null and the union reaches
 * the point exactly when one of its options does.
 */
export const ownsNullOf = (t: Term): boolean | undefined => {
    switch (t.kind) {
        case 'null':
        case 'opaq':
            return true
        case 'string':
        case 'number':
        case 'boolean':
        case 'binary':
        case 'literal':
        case 'set':
        case 'list':
        case 'object':
        case 'never':
            return false
        case 'refine':
            return ownsNullOf(t.inner) === false ? false : undefined
        // **Two questions, one per side.** The held side must not reach null, or a caller's
        // null reaches `f`. The inner term must not reach null, or `f` can land a caller's value
        // on `NULL`, as `held(nullable(string), …)` does. `nullable(decimal)` answers `false` on
        // both, and a foreign schema records `opaque` on the held side, so its answer is unknown
        case 'held':
            return ownsNullOf(t.outer) === false &&
                ownsNullOf(t.inner) === false
                ? false
                : undefined
        case 'union': {
            const answers = t.options.map(ownsNullOf)
            return answers.some((one) => one === undefined)
                ? undefined
                : answers.some((one) => one === true)
        }
        case 'legacy':
            return undefined
        case 'lazy':
            return ownsNullOf(t.get())
    }
}

/**
 * `occA`: which members a term may read, or `undefined` for every one of them.
 *
 * The mirror of {@link occV}, and **not a symmetric mirror**: `held` and `withLegacyRead` swap sides.
 * `held`'s `g` sits *behind* `p`, so it changes which value comes out and never which attributes go
 * in, and the read occupancy is the subterm's. `withLegacyRead`'s `r` is arbitrary data the term carries and
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
            return ['N']
        case 'boolean':
            return ['BOOL']
        case 'binary':
            return ['B']
        case 'null':
            return ['NULL']
        case 'literal':
            return [baseMember[t.base]]
        case 'set': {
            const read = occA(t.elem)
            return read && read.flatMap((one) => setMemberOf(one) ?? [])
        }
        case 'list':
            return ['L']
        case 'object':
            return ['M']
        case 'legacy':
            return undefined
        // transparent, as on the write side
        case 'lazy':
            return occA(t.get())
        case 'refine':
        case 'held':
            return occA(t.inner)
        case 'union':
            return joined(t.options.map(occA))
        // the closed form again, for the reason {@link occV}'s `opaq` row gives
        case 'opaq':
            return everyMember
        // empty and not `undefined`, for the reason {@link occV}'s `never` row gives
        case 'never':
            return []
    }
}

/* ── the name spec, and the discriminator ─────────────────────────────────────────────── */

/**
 * The names an object option answers to, each with whether the item must carry it.
 *
 * `undefined` for a non-object. The certificate reads these names and the literals an object
 * pins (the model reads them through the meet of two bodies). Selection itself is by attempt at every option, objects
 * included. An `optional` binding is declared and not required, and that is
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
 * One declared name, as a **slice clause** reads it.
 *
 * The model's `NameSpec`, which `litSubAt` reads: `required` is its presence, `alts` its literal. Split
 * across two host readers rather than one record, because {@link specOf} already answers the first
 * for every declared name and this answers the second for the few names a literal pins.
 */
export type NameLiteral = {
    readonly required: boolean
    readonly alts: Alternatives
}

/**
 * The literal each declared name is pinned to — the names with no literal field are absent, and a
 * non-object term answers `undefined`.
 *
 * **Every mark, not `req` alone**, which is where this parts company with {@link tagsOf}. A tag has
 * to be written, so `tagsOf` reads `req` and refuses the other three. A literal *field* constrains
 * exactly the values that carry the name whatever its mark, and admission is present-only, so an
 * `optional` literal is read here and its `required` says `false`. That is the model's
 * `altsOfField`, which has a row for `req`, `optional` and `withLegacyRead` alike.
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
 * **The form a clause is written at**, which the base alone stopped naming.
 *
 * `extract` asks a clause and a member to agree on *which literal codec* pins a key, and until
 * `8a2eed9` that was the base: `decimal` was a base of its own, so `LiteralBase` had a member per
 * form. `decimal` is an adapter over `number` now, so `decimal('1')` and `number(1)` share a base
 * and share an inner value, and the base can no longer tell a clause at one from a member at the
 * other.
 *
 * The held side of the adapter is what parts them, because it is the slot the caller's value
 * lands in: `decimal` takes text and `number` takes a float over one carrier. So the form is the
 * base everywhere but `number`, and there it is read off the held side.
 */
export type LiteralForm = LiteralBase | 'decimal' | 'dynamoNumber'

/** @see {@link LiteralForm} */
export const literalForm = (
    base: LiteralBase,
    outer: Term | undefined,
): LiteralForm =>
    base !== 'number'
        ? base
        : outer === undefined
          ? 'dynamoNumber'
          : occV(outer).includes('string')
            ? 'decimal'
            : 'number'

/** One declared name as a clause reads it: the literal under any adapter, and the form. */
export type NameForm = {
    readonly required: boolean
    readonly alts: Alternatives
    readonly form: LiteralForm
}

/**
 * The literal each declared name is pinned to, **read through a declared adapter**.
 *
 * **Not {@link literalsOf}, and the two must not become one.** That reader answers at the caller's
 * level: an adapter pins nothing there, so a field under one is absent. This reader
 * descends, because `extract` compares a clause literal against a member literal and both sit
 * under the same kind of adapter, so the pair below is the pair that decides. Merging them makes
 * every object union at a numeric name refuse every value, and the failure is a runtime refusal
 * rather than a type error.
 *
 * An adapter whose held side is `opaque` pins nothing here either, and a clause cannot
 * name it.
 */
export const clauseLiteralsOf = (
    t: Term,
): Readonly<Record<string, NameForm>> | undefined => {
    if (t.kind !== 'object') return undefined
    const literals: Record<string, NameForm> = {}
    for (const [name, field] of Object.entries(t.body.fields)) {
        const pinned = pinnedForm(field.t)
        if (pinned)
            literals[name] = { required: alwaysWritten(field), ...pinned }
    }
    return literals
}

/**
 * **The form a clause names**, reading through a declared adapter and *not* through a refinement.
 *
 * The refinement rule is {@link pinnedLiteral}'s and the reason is the same one stated there: a
 * member's literal survives a narrowing as an upper bound, and a clause is written by the caller
 * and states exactly what it means. So the member side reads through both and the clause side
 * reads through the adapter alone.
 */
export const clauseForm = (
    t: Term,
    outer?: Term,
): { readonly alts: Alternatives; readonly form: LiteralForm } | undefined => {
    // an `opaque` held side admits every kind, so it names no form
    if (t.kind === 'held')
        return t.outer.kind === 'opaq'
            ? undefined
            : clauseForm(t.inner, t.outer)
    const alts = literalAlternatives(t)
    return alts && { alts, form: literalForm(alts.base, outer) }
}

/** …and the member's side, which reads through a refinement too. @see {@link clauseForm} */
export const pinnedForm = (
    t: Term,
): { readonly alts: Alternatives; readonly form: LiteralForm } | undefined =>
    t.kind === 'refine' ? pinnedForm(t.inner) : clauseForm(t)

/**
 * The literal a term is pinned to, reading through a refinement.
 *
 * A refinement of a literal admits a subset of that literal's alternatives, so the literal is a
 * sound upper bound on what the field can carry: a value outside it is outside the field, and a
 * value inside it that the refinement rejects is the option's own error to report.
 */
const pinnedLiteral = (t: Term): Alternatives | undefined =>
    t.kind === 'refine' ? pinnedLiteral(t.inner) : literalAlternatives(t)

/**
 * **The alternatives a term pins, without reading through a refinement.**
 *
 * One literal pins its own value; a union of literals at one base pins theirs, which is what
 * `string('a', 'b')` builds. Everything else pins nothing.
 *
 * Separate from {@link pinnedLiteral} because a tag is written and a refinement is not: a reader
 * that must produce the value the codec writes cannot look through a predicate that narrows it.
 */
export const literalAlternatives = (t: Term): Alternatives | undefined =>
    t.kind === 'literal'
        ? oneAlternative(t)
        : t.kind === 'union'
          ? unionAlternatives(t.options)
          : undefined

/**
 * **The alternatives an adapter stores**, which is not what it pins.
 *
 * {@link literalAlternatives} answers what a term pins at the *caller's* level, because that is
 * what admission compares a caller's value against. An adapter pins nothing there: `decimal('1')`
 * admits the string `'1'` and the literal beneath it holds a numeral, so reading through would
 * answer with a value no caller ever hands in.
 *
 * A tag table wants the other one. `assignmentOf` builds the lookup a *stored* attribute is
 * matched against, so it wants the alternative under the adapter, and this is that reader. The two
 * are different questions and the split is why they are two functions.
 */
export const storedAlternatives = (t: Term): Alternatives | undefined =>
    t.kind === 'held' ? storedAlternatives(t.inner) : literalAlternatives(t)

/** One literal, as the one-alternative set it pins. */
const oneAlternative = (t: Literal): Alternatives =>
    ({ kind: 'alternatives', base: t.base, ls: [t.v] }) as Alternatives

/**
 * A union of literals at one base, as the alternatives it pins.
 *
 * `string('a', 'b')` builds this union, so a reader that stopped at `kind === 'literal'` would see
 * a field pinned to nothing and every gate over it would answer as if the name were free. That is
 * not a fast path over a correct answer: without this the declaration gate refuses every
 * dissection the builder makes, measured.
 *
 * One option that is not a literal, or two at different bases, pins nothing — a union of
 * `string('a')` and `decimal('a')` is told apart by the member and not by the value, and no single
 * base describes it.
 */
const unionAlternatives = (
    options: readonly Term[],
): Alternatives | undefined => {
    const first = options[0]
    if (first === undefined || first.kind !== 'literal') return undefined
    const ls: LiteralValue[] = [first.v]
    for (const option of options.slice(1)) {
        if (option.kind !== 'literal' || option.base !== first.base)
            return undefined
        ls.push(option.v)
    }
    return {
        kind: 'alternatives',
        base: first.base,
        ls,
    } as unknown as Alternatives
}

/**
 * The tags an object option answers to on discriminator `d` — empty for everything else.
 *
 * **`req` only, and a string literal only.** A `withLegacyRead` discriminator would fill an absent tag
 * with an arbitrary value the tag sets never vouched for, and (C) would then re-encode a variant no
 * tag selects; an `optional` one would let the tag be absent altogether. So four facts are read off
 * one question: the term is an object, `d` is declared, the field is `req`, and its term is a
 * literal at the string base. The model reads none of this, because no term carries the table.
 */
export const tagsOf = (d: string, t: Term): readonly string[] => {
    if (t.kind !== 'object') return []
    const field = t.body.fields[d]
    if (field === undefined || field.mark !== 'req') return []
    // a union of string literals is what `string('a', 'b')` builds, and it names those tags
    const alts = literalAlternatives(field.t)
    return alts?.base === 'string' ? alts.ls : []
}

/* ── the declaration guard ────────────────────────────────────────────────────────────── */

/**
 * **Whether two options share no value and no attribute**, the host's certificate: the model's
 * `certPair`, and a meet row where the host has no views.
 *
 * `union` asks it of a pair that {@link compatible} shows by no other warrant. Where it answers
 * `true`, the model proves `PairwiseCompat` through `separates_of_certPair` and
 * `pairwiseCompat_of_separated`. For each pair `union` refuses, `formal/.separations.lean` pins that
 * `certPair` is `false`, so this never answers `false` where `certPair` answers `true`.
 *
 * Two rows. The model's `certPair` is the second row alone: `viewsNever`.
 *
 * **Two options that meet at the bottom**, the model's `meetNever`. `Adm_meet` and `AdmA_meet`
 * make the meet's admission the conjunction of the two, so a meet at `never` admits no common
 * value and reads no common attribute. An option inside another meets the other at the option
 * itself, and not at the bottom, so no row certifies a literal beside its base.
 *
 * **The host keeps this row where the views do not exist.** {@link viewable} refuses a `legacy`
 * with a `held` below it. The meet still answers the bottom at two objects whose tags meet at the
 * bottom, because a slot at the bottom decides before a slot that refuses. The model has no
 * `legacy`, so the model needs no such row.
 *
 * **Two options, one of which holds a `held`: the two views**, the model's `viewsNever`. A `held`
 * writes where its held side does and reads where its inner term does, so the caller views answer
 * the write question and the stored views answer the read question. Both pairs of views must meet
 * at the bottom. The host asks the row only where one option holds a `held`. On a held-free term
 * the caller view is the term itself, so there the first row certifies each pair that the views
 * certify.
 *
 * The meet refuses a closure beside a partner that its inner term does not meet at the bottom, so
 * the first row certifies `union([refine(string, isNumeral), array(decimal)])`.
 */
export const separable = (x: Term, y: Term): boolean =>
    meetsAtBottom(x, y) || viewsApart(x, y)

/** The model's `meetNever`: the meet states the pair, and the meet is the bottom. */
const meetsAtBottom = (x: Term, y: Term): boolean =>
    meetTerms(x, y)?.kind === 'never'

/**
 * **Whether a term reaches a subterm of one of these kinds**, at any depth, or reaches a thunk
 * that the walk cannot read.
 *
 * The walk forces each thunk once and reads through it. A thunk that the walk meets again is
 * recursive, and a thunk that throws names a codec that is not yet declared. Each answers
 * "reaches". {@link heldFree} asks for no adapter, because the model's confluence holds only
 * there.
 */
const reaches = (
    t: Term,
    kinds: readonly Term['kind'][],
    seen: Set<Term> = new Set(),
): boolean => {
    if (kinds.includes(t.kind)) return true
    const on = (one: Term) => reaches(one, kinds, seen)
    switch (t.kind) {
        case 'lazy': {
            if (seen.has(t)) return true
            seen.add(t)
            const forced = force(t)
            return forced === undefined || on(forced)
        }
        case 'held':
        case 'legacy':
        case 'refine':
            return on(t.inner)
        case 'set':
            return on(t.elem)
        case 'list':
            return (
                t.pre.some(on) ||
                (t.spread !== undefined && on(t.spread)) ||
                t.suf.some(on)
            )
        case 'object':
            return (
                Object.values(t.body.fields).some((f) => on(f.t)) ||
                (t.body.rest !== undefined && on(t.body.rest))
            )
        case 'union':
            return t.options.some(on)
        default:
            return false
    }
}

/**
 * The term of a thunk, or nothing where the thunk throws. A thunk is caller code, so its throw
 * crosses the boundary here. At a declaration the throw is a thunk that names the codec being
 * declared, and the caller of this function refuses, declines, or reads the thunk as a free
 * variable.
 */
const force = (t: Term & { readonly kind: 'lazy' }): Term | undefined => {
    try {
        return t.get()
    } catch {
        return undefined
    }
}

/**
 * **Whether a thunk on the spine of a term is recursive, or throws when forced.** The spine is
 * what {@link occV} and {@link occA} force: a thunk, the options of a union, both sides of a
 * `held`, and the inner term of a `refine` or a `legacy`. A union asks this of each option before
 * any occupancy runs, so a recursive spine is refused and does not loop.
 */
export const unreadableSpine = (
    t: Term,
    seen: Set<Term> = new Set(),
): boolean => {
    const on = (one: Term) => unreadableSpine(one, seen)
    switch (t.kind) {
        case 'lazy': {
            if (seen.has(t)) return true
            seen.add(t)
            const forced = force(t)
            return forced === undefined || on(forced)
        }
        case 'held':
            return on(t.inner) || on(t.outer)
        case 'legacy':
        case 'refine':
            return on(t.inner)
        case 'union':
            return t.options.some(on)
        default:
            return false
    }
}

/**
 * **Whether a `held` sits between a recursive thunk and the term the thunk returns**, which is the
 * model's `Term.guarded` refusing a variable at level 3. The walk forces each thunk and keeps the
 * term objects it is inside. A thunk that returns an object on that stack closes a cycle, and the
 * objects between the two are the path of the recursion. A `held` on that path refuses: its
 * conversion can make the input deeper, so no container on the path bounds the depth of a stage.
 *
 * **A thunk that throws under a `held` refuses too.** At the declaration of a recursive schema the
 * thunk names the constant being declared, so it throws, and the walk cannot see the cycle. The
 * spine reads such a thunk as recursive ({@link unreadableSpine}), and a `held` path reads it the
 * same way. The walk ends at each cycle, because a thunk memoizes its codec and every other edge of
 * a term is built before the term.
 */
export const heldOnRecursivePath = (root: Term): boolean => {
    const walk = (t: Term, stack: readonly Term[]): boolean => {
        const on = [...stack, t]
        const next = (one: Term) => walk(one, on)
        switch (t.kind) {
            case 'lazy': {
                const target = force(t)
                if (target === undefined)
                    return on.some((one) => one.kind === 'held')
                const at = on.indexOf(target)
                return at === -1
                    ? next(target)
                    : on.slice(at).some((one) => one.kind === 'held')
            }
            case 'list':
                return (
                    [...t.pre, ...t.suf].some(next) ||
                    (t.spread !== undefined && next(t.spread))
                )
            case 'object':
                return (
                    Object.values(t.body.fields).some((field) =>
                        next(field.t),
                    ) ||
                    (t.body.rest !== undefined && next(t.body.rest))
                )
            case 'union':
                return t.options.some(next)
            case 'set':
                return next(t.elem)
            case 'held':
                return next(t.inner) || next(t.outer)
            case 'refine':
            case 'legacy':
                return next(t.inner)
            default:
                return false
        }
    }
    return walk(root, [])
}

/**
 * **Whether {@link callerView} and {@link storedView} are sound on a term.**
 *
 * The view of a `union` is the union of the views of its options, because a union admits where
 * one of its options admits. A `legacy` with a `held` below it has no view: its `r` reads an
 * attribute to a held value, so the read widens on both sides. A thunk has the view of the term
 * it returns. A thunk that throws is a free variable, and the view of a variable is the variable:
 * {@link meetTerms} reads the view of the thunk as a free variable too.
 *
 * The walk forces each thunk once, so it ends: a thunk memoizes its codec, and every other edge
 * of a term is built before the term.
 */
const viewable = (t: Term, seen: Set<Term> = new Set()): boolean => {
    const on = (one: Term) => viewable(one, seen)
    switch (t.kind) {
        case 'lazy': {
            if (seen.has(t)) return true
            seen.add(t)
            const forced = force(t)
            return forced === undefined || on(forced)
        }
        case 'held':
            return on(t.inner) && on(t.outer)
        case 'refine':
            return on(t.inner)
        case 'set':
            return on(t.elem)
        case 'union':
            return t.options.every(on)
        // `reaches` counts a thunk it cannot read as a `held`, so such a thunk below refuses here too
        case 'legacy':
            return !reaches(t, ['held'])
        case 'list':
            return (
                t.pre.every(on) &&
                (t.spread === undefined || on(t.spread)) &&
                t.suf.every(on)
            )
        case 'object':
            return (
                Object.values(t.body.fields).every((f) => on(f.t)) &&
                (t.body.rest === undefined || on(t.body.rest))
            )
        default:
            return true
    }
}

/** A list, an object or a union with each position, field and option replaced by its view. */
const mapChildren = (t: Term, view: (t: Term) => Term): Term => {
    switch (t.kind) {
        case 'list':
            return {
                kind: 'list',
                pre: t.pre.map(view),
                ...(t.spread === undefined ? {} : { spread: view(t.spread) }),
                suf: t.suf.map(view),
            }
        case 'object': {
            const { rest } = t.body
            return {
                kind: 'object',
                body: {
                    fields: Object.fromEntries(
                        Object.entries(t.body.fields).map(([name, f]) => [
                            name,
                            { ...f, t: view(f.t) },
                        ]),
                    ),
                    ...(rest === undefined ? {} : { rest: view(rest) }),
                },
            }
        }
        case 'union':
            return { kind: 'union', options: t.options.map(view) }
        // a view holds no `held`, so the set of the element's view writes element by element
        case 'set':
            return { kind: 'set', elem: view(t.elem) }
        default:
            return t
    }
}

/**
 * **A view that reads through a thunk**, as the model's views read through `mu`: the view of a
 * thunk is a thunk that returns the view of the term that the first thunk returns. Each term
 * object has one view object, so a cycle of the term is a cycle of the view, closed at the view
 * of the same binder. {@link meetTerms} then reads the view as `mu` of the view of the body, and
 * a variable of the view at the thunk.
 *
 * The build forces no thunk, so it ends: it recurses only through the edges that are not a
 * thunk, and every such edge of a term is built before the term. A thunk of the view forces its
 * thunk when {@link meetTerms} reads it, and {@link viewable} forced each such thunk already. A
 * thunk that throws throws again there, and {@link meetTerms} reads it as a free variable.
 */
const throughThunks =
    (row: (t: Term, view: (t: Term) => Term) => Term) =>
    (root: Term): Term => {
        const views = new Map<Term, Term>()
        const view = (t: Term): Term => {
            const known = views.get(t)
            if (known !== undefined) return known
            const made: Term =
                t.kind === 'lazy'
                    ? { kind: 'lazy', get: () => view(t.get()) }
                    : row(t, view)
            views.set(t, made)
            return made
        }
        return view(root)
    }

/**
 * **The caller view**: each `held` becomes its held side. The view admits each value that the
 * term admits, where {@link viewable} holds. A `refine` above a `held` keeps its predicate,
 * because the caller states the predicate on the held value.
 */
const callerView = throughThunks((t, view) => {
    switch (t.kind) {
        case 'held':
            return view(t.outer)
        case 'refine':
            return { kind: 'refine', inner: view(t.inner), q: t.q }
        default:
            return mapChildren(t, view)
    }
})

/**
 * **The stored view**: each `held` becomes its inner term. The view reads each attribute that
 * the term reads, where {@link viewable} holds.
 *
 * **The view keeps a predicate only where the inner term decodes the same in the view as in the
 * term**: where the inner term reaches no `held` and closes no cycle. A thunk that closes a cycle
 * is a variable of the model, and the variable denotes a stage of its binder, which can hold a
 * `held`. {@link reaches} counts such a thunk as a `held`. Elsewhere the view drops the
 * predicate, because data exists only on the side where it was stated: the stored side meets the
 * predicate only through `g`, and the view keeps no closure.
 */
const storedView = throughThunks((t, view) => {
    switch (t.kind) {
        case 'held':
            return view(t.inner)
        case 'refine':
            return reaches(t.inner, ['held']) ? view(t.inner) : t
        default:
            return mapChildren(t, view)
    }
})

/**
 * **The model's `viewsNever`, where one option holds a `held`**: both are
 * {@link viewable}, the caller views meet at the bottom, and the stored views meet at the bottom.
 * Then no caller value is admitted by both options, and no attribute is read by both.
 */
const viewsApart = (x: Term, y: Term): boolean =>
    (reaches(x, ['held']) || reaches(y, ['held'])) &&
    viewable(x) &&
    viewable(y) &&
    meetsAtBottom(callerView(x), callerView(y)) &&
    meetsAtBottom(storedView(x), storedView(y))

/**
 * **Whether the walk shows a term held-free**, the model's `HF`. A `legacy` counts as an adapter,
 * and so does a thunk that the walk cannot read.
 */
export const heldFree = (t: Term): boolean => !reaches(t, ['held', 'legacy'])

/**
 * **Whether a `withLegacyRead` occurs in the term.** The model has no read widening in `Term`, so a
 * construction that the model states only over `Term`, as `set` is, refuses one.
 */
export const widensRead = (t: Term): boolean => reaches(t, ['legacy'])

/** The terms with no payload, where the kind alone names the term. */
const leaves: readonly Term['kind'][] = [
    'string',
    'number',
    'boolean',
    'binary',
    'null',
    'opaq',
    'never',
]

/**
 * **Whether two `held` terms are one adapter.** A library adapter names its pair in `via`, and the
 * model carries one pair for each name. A caller's adapter is one adapter where both halves are
 * the same function values.
 */
const sameAdapter = (
    x: Extract<Term, { kind: 'held' }>,
    y: Extract<Term, { kind: 'held' }>,
): boolean =>
    (x.via !== undefined && x.via === y.via) || (x.f === y.f && x.g === y.g)

/**
 * **Whether `x` is below `y` by a rule the model proves**: a literal is below its base and below
 * itself, a union is below a term that each of its options is below, a term is below a held-free
 * union where the term is below one option, and a `held` is below the same adapter over a wider
 * stored side and a wider held side (`sub_literal_base`, `sub_union_of`, `sub_union_mem`,
 * `sub_held`). A term with no payload is below itself. Nothing else is shown.
 *
 * The union must be held-free, because the model's proof bounds its options by `opaque`. An option
 * with a `held` has no such bound. The proof then needs each option lawful and the options
 * compatible, and a verdict states lawfulness only of the two terms of the pair.
 */
export const below = (x: Term, y: Term): boolean => {
    if (x.kind === 'union') return x.options.every((one) => below(one, y))
    if (y.kind === 'union')
        return heldFree(y) && y.options.some((one) => below(x, one))
    if (x.kind === 'literal')
        return (
            y.kind === x.base || (y.kind === 'literal' && sameLiteral(x.v, y.v))
        )
    if (x.kind === 'held' && y.kind === 'held')
        return (
            sameAdapter(x, y) &&
            below(x.inner, y.inner) &&
            below(x.outer, y.outer)
        )
    return leaves.includes(x.kind) && x.kind === y.kind
}

/**
 * **Whether the declaration shows two options compatible**, which is what `union` asks of a pair.
 *
 * A union is the join of its options, and the join of two lawful options is lawful exactly when
 * the two are compatible: each reading of one is a reading of the other wherever the other acts.
 * Four warrants show it, as the model's dischargers do. `never` is compatible with every option
 * (`pairwiseCompat_never_left`). Two held-free options sit below one canonical codec
 * (`pairwiseCompat_of_HF`). An option {@link below} the other has the other as that codec
 * (`pairwiseCompat_of_sub`). {@link separable} is the certificate (`pairwiseCompat_of_separated`).
 */
export const compatible = (x: Term, y: Term): boolean =>
    x.kind === 'never' ||
    y.kind === 'never' ||
    (heldFree(x) && heldFree(y)) ||
    below(x, y) ||
    below(y, x) ||
    separable(x, y)

/* ── the meet ─────────────────────────────────────────────────────────────────────────── */

/**
 * **The intersection of two admissions, as a term** — `Calculus.Term.meet`, one row per pair of
 * constructors.
 *
 * `undefined` is the model's `none` and is **not** the bottom. It says no term states this
 * intersection, which happens for two reasons: a factor whose admission is a function nobody can
 * read, and a pair that shares a value or a stored attribute it writes or reads two ways. `never`
 * is the empty intersection alone. Conflating the two is the defect this development found four
 * separate times, each time by writing the homomorphism equation rather than by reading the table.
 *
 * **Where the host could answer and the model has no row, this refuses.** Two `withLegacyRead`
 * fields and an `undefinable` field are each comparable in TypeScript and each answer `undefined`
 * here, because a row the model does not state is a rule this port would be inventing. The model's
 * `Field` has no `undefinable` mark.
 *
 * **A recursive term is met as the model spells it**: `mu` at the term object that a cycle
 * returns to, and a variable at the thunk that closes the cycle ({@link Scope}). Two variables meet
 * where the two binders were met together, and a variable beside any other term refuses. Two
 * recursive terms meet at the recursive term of the two bodies met ({@link meetBinders}). A
 * recursive term beside another term unfolds, and its binder pairs with nothing.
 *
 * **A thunk that throws is a free variable that pairs with nothing.** The thunk names a codec that
 * is not yet declared, so the host cannot read the term that the thunk returns. The model's meet
 * holds under every environment of its variables, so a meet that reads no such variable holds
 * whatever the thunk returns later. The walk reads the variable as the model reads a variable
 * under `pair0`: beside the bottom the meet is the bottom, and beside any other term the meet
 * refuses. A container of the variable beside a constructor of another kind meets at the bottom,
 * and reads no variable.
 */
export const meetTerms = (x: Term, y: Term): Term | undefined => {
    // the bottom absorbs, on either side, before any thunk is read: the model's `never` rows sit
    // first, and a recursive term meets the bottom at the bottom
    if (x.kind === 'never' || y.kind === 'never') return never
    return meetWalk(x, y, {
        left: { binds: bindersOf(x), inside: [] },
        right: { binds: bindersOf(y), inside: [] },
        pairs: [],
        variables: new Set(),
    })
}

/**
 * **Where a walk is in one operand**: the term objects that bind a variable, and the binders the
 * walk is inside, nearest last.
 *
 * A recursive host schema is a cycle of term objects closed by a thunk. The model names the cycle
 * with a binder: `Term.mu` at the object that a thunk returns while that object is on the walk,
 * and `Term.var k` at the thunk, where `k` counts the binders between the two. Any other thunk is
 * the term it returns. The meet and the emitter read one spelling, so both read it through this
 * scope.
 */
export type Scope = {
    readonly binds: ReadonlySet<Term>
    readonly inside: readonly Term[]
}

/**
 * **The binders of a term**: each term object that a thunk returns while that object is on the
 * stack of the walk. A thunk that throws binds nothing, because {@link see} reads the thunk as a
 * free variable. The walk forces each thunk and stops at a cycle, so it ends: a thunk memoizes
 * its codec, and every other edge of a term is built before the term.
 */
export const bindersOf = (root: Term): ReadonlySet<Term> => {
    const binds = new Set<Term>()
    const walk = (t: Term, stack: readonly Term[]): void => {
        const on = [...stack, t]
        const next = (one: Term) => walk(one, on)
        switch (t.kind) {
            case 'lazy': {
                const target = force(t)
                if (target === undefined) return
                if (on.includes(target)) binds.add(target)
                else next(target)
                return
            }
            case 'list':
                for (const one of [...t.pre, ...t.suf]) next(one)
                if (t.spread !== undefined) next(t.spread)
                return
            case 'object':
                for (const field of Object.values(t.body.fields)) next(field.t)
                if (t.body.rest !== undefined) next(t.body.rest)
                return
            case 'union':
                for (const one of t.options) next(one)
                return
            case 'set':
                return next(t.elem)
            case 'held':
                next(t.inner)
                return next(t.outer)
            case 'refine':
            case 'legacy':
                return next(t.inner)
            default:
                return
        }
    }
    walk(root, [])
    return binds
}

/**
 * **A term as the model spells it at a scope**: a binder, a variable, a free variable, or a
 * constructor. A free variable is a thunk that throws, and it pairs with no binder.
 */
type Seen =
    | { readonly kind: 'mu'; readonly body: Term; readonly scope: Scope }
    | { readonly kind: 'var'; readonly binder: Term }
    | { readonly kind: 'free' }
    | { readonly kind: 'term'; readonly t: Term }

/**
 * A binder of the scope that the walk is not inside is `mu` of its body, and the walk is then
 * inside the binder. A thunk that returns a binder the walk is inside is a variable. A thunk that
 * throws is a free variable. Any other thunk is the term it returns.
 */
const see = (t: Term, scope: Scope): Seen => {
    if (scope.binds.has(t) && !scope.inside.includes(t))
        return {
            kind: 'mu',
            body: t,
            scope: { binds: scope.binds, inside: [...scope.inside, t] },
        }
    if (t.kind !== 'lazy') return { kind: 'term', t }
    const target = force(t)
    if (target === undefined) return { kind: 'free' }
    return scope.inside.includes(target)
        ? { kind: 'var', binder: target }
        : see(target, scope)
}

/**
 * **The pairing of binders**, the model's `Pairing`: the scope of each operand, and each pair of
 * binders met together with the variable of the answer's binder.
 */
type Walk = {
    readonly left: Scope
    readonly right: Scope
    readonly pairs: readonly {
        readonly left: Term
        readonly right: Term
        readonly variable: Term
    }[]
    /** Every variable of an answer's binder in this meet. The walk of an answer stops at each. */
    readonly variables: Set<Term>
}

/** The pairing with the two operands exchanged, for a row that meets the right operand first. */
const flip = (w: Walk): Walk => ({
    left: w.right,
    right: w.left,
    pairs: w.pairs.map(({ left, right, variable }) => ({
        left: right,
        right: left,
        variable,
    })),
    variables: w.variables,
})

/**
 * One row per pair of constructors, as the operands spell at the pairing.
 *
 * **The walk ends.** The spelling of each operand is a finite term, because {@link bindersOf}
 * binds the target of every thunk that closes a cycle, and the spelling stops at each variable.
 * Each call meets a strict subterm of one spelling, or of both, with the other spelling unchanged,
 * so the sum of the two sizes falls at each call. An exchange of the operands keeps the sum.
 */
const meetWalk = (x: Term, y: Term, w: Walk): Term | undefined => {
    const one = see(x, w.left)
    const other = see(y, w.right)
    // the bottom absorbs, on either side
    if (
        (one.kind === 'term' && one.t.kind === 'never') ||
        (other.kind === 'term' && other.t.kind === 'never')
    )
        return never
    // a free variable pairs with no binder, so beside any term but the bottom the meet refuses
    if (one.kind === 'free' || other.kind === 'free') return undefined
    // a variable admits what its binder admits, so a variable meets only the variable of the
    // binder that its own binder was met with
    if (one.kind === 'var')
        return other.kind === 'var'
            ? w.pairs.find(
                  (pair) =>
                      pair.left === one.binder && pair.right === other.binder,
              )?.variable
            : undefined
    if (one.kind === 'mu')
        return other.kind === 'mu'
            ? meetBinders(one, other, w)
            : // a recursive term beside another term unfolds, and its binder pairs with nothing
              meetWalk(one.body, y, { ...w, left: one.scope })
    const left = one.t
    // the three whose admission is a function and not data: a reader cannot say what they admit
    // without running them, so no term states the intersection
    if (
        opaqueToReader(left) ||
        (other.kind === 'term' && opaqueToReader(other.t))
    )
        return undefined
    // a certified union distributes, on either side
    if (left.kind === 'union') return distribute(left.options, y, w)
    if (other.kind === 'term' && other.t.kind === 'union')
        return distribute(other.t.options, left, flip(w))
    // a refinement conjoins: a predicate that is data rides on the meet of the inner terms
    if (left.kind === 'refine') return overRefinement(left.inner, left.q, y, w)
    // a constructor beside a variable refuses, and beside a recursive term the recursive term
    // unfolds
    if (other.kind === 'var') return undefined
    if (other.kind === 'mu')
        return meetWalk(left, other.body, { ...w, right: other.scope })
    const right = other.t
    if (right.kind === 'refine')
        return overRefinement(right.inner, right.q, left, flip(w))
    // the ground bases: the same base is itself
    if (left.kind === right.kind && groundBase(left)) return left
    // **`string` and `decimal` part on the stored side.** Both admit text; `string` writes `S` and
    // `decimal` writes `N`, so a value they share is stored two ways and there is no meet. The
    // literal rows repeat it, because a literal at either base inherits the pair
    if (left.kind === 'literal' && right.kind === 'literal')
        return meetLiterals(left, right)
    if (left.kind === 'literal') return literalAgainstBase(left, right)
    if (right.kind === 'literal') return literalAgainstBase(right, left)
    if (left.kind === 'list' && right.kind === 'list')
        return meetLists(left, right, w)
    // **Two sets meet at their elements**, the model's `famSet`. An element meet at the bottom is a
    // set meet at the bottom, because a stored set is not empty. A set is stated only where the
    // three terms are held-free, where each set writes and reads element by element. An element
    // that reads a variable refuses, because the set laws are stated over closed elements
    if (left.kind === 'set' && right.kind === 'set') {
        if (
            spells(left.elem, w.left.inside, []) ||
            spells(right.elem, w.right.inside, [])
        )
            return undefined
        const elem = meetWalk(left.elem, right.elem, w)
        if (elem === undefined) return undefined
        if (elem.kind === 'never') return never
        return spells(left.elem, w.left.inside, ['held']) ||
            spells(right.elem, w.right.inside, ['held']) ||
            spells(elem, [], ['held', 'lazy'])
            ? undefined
            : { kind: 'set', elem }
    }
    if (left.kind === 'opaq' && right.kind === 'opaq') return left
    if (left.kind === 'object' && right.kind === 'object')
        return meetBodies(left.body, right.body, w)
    // **`opaque` against a ground base.** It admits every value of every self-identifying kind, so
    // at `string`, `boolean`, `binary`, `null` and `number` the base is the finer term. `decimal`
    // refuses for the reason `string ∧ decimal` refuses
    if (left.kind === 'opaq') return opaqueAgainst(right)
    if (right.kind === 'opaq') return opaqueAgainst(left)
    // **The `number` family and the `decimal` family never meet.** They write different value kinds,
    // so the bottom is right about the write side, and they read the same member `N`, so the bottom
    // is wrong about the read side: every stored numeral is an attribute both admit
    // everything left is two constructors that write different value kinds
    return never
}

/**
 * **Two recursive terms meet at the recursive term of the two bodies met**, with the two binders
 * paired. The answer is a thunk that returns the met body, and the variable of the pair is a thunk
 * that returns the answer, so the answer closes its own cycle and spells as `mu` of the body.
 *
 * The answer is the bottom where the body is. It is a binder only where the model's guard accepts
 * the binder: the body reads the variable under a container, and under no `held`.
 *
 * **A body that never reads the variable parts from the model.** The model answers `mu z` there.
 * A host binder is a cycle, and such a body closes no cycle, so the host has no spelling for the
 * binder and answers the body `z`. No corpus vector reaches this case.
 */
const meetBinders = (
    one: Extract<Seen, { kind: 'mu' }>,
    other: Extract<Seen, { kind: 'mu' }>,
    w: Walk,
): Term | undefined => {
    let body: Term | undefined
    const binder: Term = {
        kind: 'lazy',
        get: () => {
            // the meet returns the binder only after it fills the body
            if (body === undefined)
                throw new Error('a recursive answer was read before its body')
            return body
        },
    }
    const variable: Term = { kind: 'lazy', get: () => binder }
    w.variables.add(variable)
    const z = meetWalk(one.body, other.body, {
        left: one.scope,
        right: other.scope,
        pairs: [...w.pairs, { left: one.body, right: other.body, variable }],
        variables: w.variables,
    })
    if (z === undefined || z.kind === 'never') return z
    const reads = readsBinder(z, variable, w.variables)
    if (reads === 0) return z
    if (reads > 1) return undefined
    body = z
    return binder
}

/**
 * **How an answer reads the variable of one binder**, the model's `Term.use`: `0` where the
 * variable does not occur, `1` where each occurrence sits under a container and none under a
 * `held`, `2` where an occurrence reads the input itself, and `3` where one sits under a `held`.
 *
 * An answer holds two kinds of thunk: the variable of a binder, where the walk stops, and a binder
 * that the meet filled before, whose body the walk reads. So the walk ends where the answer ends.
 */
const readsBinder = (
    t: Term,
    variable: Term,
    variables: ReadonlySet<Term>,
): number => {
    const on = (one: Term) => readsBinder(one, variable, variables)
    const under = (use: number) => (use === 2 ? 1 : use)
    const most = (ts: readonly Term[]) => Math.max(0, ...ts.map(on))
    switch (t.kind) {
        case 'lazy':
            return variables.has(t) ? (t === variable ? 2 : 0) : on(t.get())
        case 'set':
            return under(on(t.elem))
        case 'list':
            return under(
                most([
                    ...t.pre,
                    ...(t.spread === undefined ? [] : [t.spread]),
                    ...t.suf,
                ]),
            )
        case 'object':
            return under(
                most([
                    ...Object.values(t.body.fields).map((field) => field.t),
                    ...(t.body.rest === undefined ? [] : [t.body.rest]),
                ]),
            )
        case 'union':
            return most(t.options)
        case 'refine':
            return on(t.inner)
        case 'held':
            return most([t.inner, t.outer]) === 0 ? 0 : 3
        default:
            return 0
    }
}

/**
 * **Whether the spelling of a term at a scope reads a variable, or holds a subterm of one of these
 * kinds**, the model's `hasVar` and `hasHeldUnder`. A thunk that returns a term the walk is inside
 * is a variable, and a thunk that throws is a free variable. The walk stops at each, so it ends
 * where the spelling ends.
 */
const spells = (
    t: Term,
    inside: readonly Term[],
    kinds: readonly Term['kind'][],
): boolean => {
    if (kinds.includes(t.kind)) return true
    const on = (one: Term) => spells(one, [...inside, t], kinds)
    switch (t.kind) {
        // a thunk that throws is a free variable
        case 'lazy': {
            const target = force(t)
            return target === undefined || inside.includes(target) || on(target)
        }
        case 'set':
            return on(t.elem)
        case 'list':
            return (
                t.pre.some(on) ||
                (t.spread !== undefined && on(t.spread)) ||
                t.suf.some(on)
            )
        case 'object':
            return (
                Object.values(t.body.fields).some((field) => on(field.t)) ||
                (t.body.rest !== undefined && on(t.body.rest))
            )
        case 'union':
            return t.options.some(on)
        case 'held':
            return on(t.inner) || on(t.outer)
        case 'refine':
        case 'legacy':
            return on(t.inner)
        default:
            return false
    }
}

const never: Term = { kind: 'never' }

const opaqueToReader = (t: Term): boolean =>
    t.kind === 'held' || t.kind === 'legacy'

const groundBase = (t: Term): boolean =>
    t.kind === 'string' ||
    t.kind === 'number' ||
    t.kind === 'boolean' ||
    t.kind === 'binary' ||
    t.kind === 'null'

/**
 * **A refinement over the bottom is the bottom, and two refinements over one term meet.** The
 * model's `Term.refineOf`: a second refinement does not stack where the two predicates meet, and
 * where no value satisfies both the result is the bottom.
 */
const refineOf = (z: Term, q: Predicate): Term => {
    if (z.kind === 'never') return never
    if (z.kind !== 'refine') return { kind: 'refine', inner: z, q }
    const met = meetPredicates(z.q, q)
    return met === undefined
        ? { kind: 'refine', inner: z, q }
        : met === null
          ? never
          : { kind: 'refine', inner: z.inner, q: met }
}

/**
 * **Two predicates, met** — the model's `Pred.meetM`. `undefined` is a refusal to combine,
 * `null` says that no value satisfies both, and a predicate is the combined one. `members` meets
 * `members` at any two bases. A `closure` refuses.
 */
const meetPredicates = (
    q: Predicate,
    p: Predicate,
): Predicate | null | undefined => {
    if (q.kind === 'closure' || p.kind === 'closure') return undefined
    const met = meetAlternatives(q.literal, p.literal)
    return met === null ? null : { kind: 'members', literal: met }
}

/** Two alternative sets: the alternatives of the first that the second holds, or nothing. */
const meetAlternatives = (
    a: Alternatives,
    b: Alternatives,
): Alternatives | null => {
    if (a.base !== b.base) return null
    switch (a.base) {
        case 'string': {
            const ls = kept(a.ls, b.ls)
            return ls ? { kind: 'alternatives', base: 'string', ls } : null
        }
        case 'number': {
            const ls = kept(a.ls, b.ls)
            return ls ? { kind: 'alternatives', base: 'number', ls } : null
        }
        case 'boolean': {
            const ls = kept(a.ls, b.ls)
            return ls ? { kind: 'alternatives', base: 'boolean', ls } : null
        }
        case 'binary': {
            const ls = kept(a.ls, b.ls)
            return ls ? { kind: 'alternatives', base: 'binary', ls } : null
        }
    }
}

/** The members of `ls` that `other` holds, in order, or nothing where none is left. */
const kept = <A extends LiteralValue>(
    ls: NonEmpty<A>,
    other: readonly LiteralValue[],
): NonEmpty<A> | undefined => {
    const [head, ...tail] = ls.filter((one) =>
        other.some((candidate) => sameLiteral(one, candidate)),
    )
    return head === undefined ? undefined : [head, ...tail]
}

/**
 * **A list with a declared position at the bottom is the bottom.**
 *
 * Every value the list admits fills each declared position, so one position holding nothing empties
 * the list. The *spread* is not such a position: a value of exactly the declared length omits every
 * spread position, so a spread at the bottom reads "exactly the declared positions" rather than
 * "nothing". The prefix and the suffix are declared; the spread is not. `Term.listOf` is the
 * model's name for this normalisation, and every list the meet builds goes through it.
 */
const listOf = (
    pre: readonly Term[],
    spread: Term | undefined,
    suf: readonly Term[],
): Term =>
    pre.some((t) => t.kind === 'never') || suf.some((t) => t.kind === 'never')
        ? never
        : spread === undefined
          ? { kind: 'list', pre, suf }
          : { kind: 'list', pre, spread, suf }

/** A union of what survived a distribution: nothing is the bottom, and one survivor is itself. */
const ofOptions = (ts: readonly Term[]): Term =>
    ts.length === 0
        ? never
        : ts.length === 1
          ? (ts[0] as Term)
          : { kind: 'union', options: ts }

const overRefinement = (
    inner: Term,
    q: Predicate,
    other: Term,
    w: Walk,
): Term | undefined => {
    const z = meetWalk(inner, other, w)
    if (z === undefined) return undefined
    // a refinement admits a part of what its inner term admits, so an inner meet at the bottom is
    // the bottom whatever the predicate is. A closure is not data, so any other meet refuses
    if (q.kind === 'closure') return z.kind === 'never' ? never : undefined
    return refineOf(z, q)
}

/**
 * **The meet at a union: the survivors, with no certificate.** Each survivor admits a value where
 * its option and the other term both admit the value. So a value that one option of the union
 * admits is a value that one survivor at most admits, and the model's union row asks nothing more.
 *
 * **A certificate here is a cycle.** The certificate of a union is {@link separable}, which reads
 * this meet. A union that recurses through its own options then asks the certificate of the
 * survivors, the certificate meets the same union again, and the walk does not end.
 */
const distribute = (
    options: readonly Term[],
    other: Term,
    w: Walk,
): Term | undefined => {
    const met: Term[] = []
    for (const option of options) {
        const z = meetWalk(option, other, w)
        if (z === undefined) return undefined
        met.push(z)
    }
    return ofOptions(met.filter((z) => z.kind !== 'never'))
}

/**
 * **A literal against a base is the literal at that base, and the bottom at any other.**
 *
 * There is no pair left that shares values and refuses. `string` and `decimal` were that pair
 * while `decimal` held text, and `number` and `decimal` were the pair that shared a member;
 * `decimal` is an adapter now, so every base is disjoint from every other on both halves and the
 * bottom is right at each cross.
 */
const literalAgainstBase = (lit: Literal, base: Term): Term | undefined => {
    switch (base.kind) {
        case 'string':
            return lit.base === 'string' ? lit : never
        case 'number':
            return lit.base === 'number' ? lit : never
        case 'boolean':
            return lit.base === 'boolean' ? lit : never
        case 'binary':
            return lit.base === 'binary' ? lit : never
        // **`opaque` is not "any other base".** The model enumerates the literal rows against the
        // ground bases and nothing else, so a literal against `opaq` falls through them to the
        // `opaq` row, which refuses. Answering the bottom here would claim the two share no value
        // while `opaque` admits every value the literal does
        case 'opaq':
            return undefined
        default:
            return never
    }
}

/**
 * **Two literals: the same value, or the bottom**, as the model's `Ground.meetLit`. A `number`
 * literal is a {@link DynamoNumber}, normalised at construction, so its digits are the numeral the
 * emitter prints and the equality is the model's.
 */
const meetLiterals = (x: Literal, y: Literal): Term | undefined => {
    if (x.base !== y.base) return never
    if (x.base === 'number' && y.base === 'number')
        return x.v.equals(y.v) ? x : never
    const other = (y as { readonly v: unknown }).v
    return sameValue(x.v, other) ? x : never
}

/** Two literal values, compared the way the base compares them: bytes for `binary`, `===` else. */
const sameValue = (one: unknown, other: unknown): boolean =>
    one instanceof Uint8Array
        ? other instanceof Uint8Array &&
          one.length === other.length &&
          one.every((byte, at) => byte === other[at])
        : one === other

const opaqueAgainst = (other: Term): Term | undefined => {
    switch (other.kind) {
        case 'string':
        case 'boolean':
        case 'binary':
        case 'null':
        case 'number':
            return other
        default:
            return undefined
    }
}

/**
 * **The row a list shape assigns to `n` positions**: the prefix, the spread as often as the middle
 * needs, then the suffix. `undefined` is a length the shape refuses.
 */
const rowOf = (
    t: Extract<Term, { kind: 'list' }>,
    n: number,
): readonly Term[] | undefined => {
    const declared = t.pre.length + t.suf.length
    if (t.spread === undefined)
        return n === declared ? [...t.pre, ...t.suf] : undefined
    if (n < declared) return undefined
    const spread = t.spread
    return [
        ...t.pre,
        ...Array.from({ length: n - declared }, () => spread),
        ...t.suf,
    ]
}

/** Two rows met position for position, or nothing where a position refuses. */
const rowMeet = (
    a: readonly Term[],
    b: readonly Term[],
    w: Walk,
): readonly Term[] | undefined => {
    const row: Term[] = []
    for (const [at, one] of a.entries()) {
        const z = meetWalk(one, b[at] as Term, w)
        if (z === undefined) return undefined
        row.push(z)
    }
    return row
}

/**
 * **One side dominates the other**, in the prefix and in the suffix at once.
 *
 * This is the whole of the list meet's refusal, and it is a fact about lengths alone. With both
 * shapes spreading, the meet admits a value of length `n` exactly when `n >= max (p1+s1) (p2+s2)`,
 * while the widest list the answer can spell admits `n >= max p1 p2 + max s1 s2`. The second is
 * never smaller, and the two are equal exactly when one side's prefix and suffix are both at least
 * the other's. Elsewhere a window of lengths sits in the intersection that no single list states,
 * because a list carries one prefix and one suffix and the window needs two shapes. There the meet
 * refuses. `dominates` and `dominates_max` are the model's pair.
 */
const dominates = (p1: number, s1: number, p2: number, s2: number): boolean =>
    (p2 <= p1 && s2 <= s1) || (p1 <= p2 && s1 <= s2)

/**
 * **Two list shapes met**, which is `listMeetRow` in the model.
 *
 * Three branches, and only the first can refuse. **Both spreading**: the answer is the row at
 * `max p1 p2 + max s1 s2`, split back into that prefix and that suffix, with the spreads met.
 * **Either side without a spread**: that side's arity is fixed, so the answer *flattens* to one
 * prefix of exactly that length with no spread and no suffix; a length the other side cannot reach
 * is the empty intersection, which is the bottom. Flattening rather than keeping the longer prefix
 * and the longer suffix is what the fixed arity needs: the two overhangs can collide, and at a
 * fixed arity there is no spread to meet them against.
 *
 * The rows are zipped left operand first, because every cell of the meet keeps the left operand on
 * the left and two refinements nest in argument order.
 */
const meetLists = (
    x: Extract<Term, { kind: 'list' }>,
    y: Extract<Term, { kind: 'list' }>,
    w: Walk,
): Term | undefined => {
    if (x.spread !== undefined && y.spread !== undefined) {
        const p = Math.max(x.pre.length, y.pre.length)
        const s = Math.max(x.suf.length, y.suf.length)
        if (!dominates(x.pre.length, x.suf.length, y.pre.length, y.suf.length))
            return undefined
        const spread = meetWalk(x.spread, y.spread, w)
        if (spread === undefined) return undefined
        const rows = rowOf(x, p + s)
        const other = rowOf(y, p + s)
        // unreachable under dominance, where `p + s` is at least each side's declared length
        if (rows === undefined || other === undefined) return never
        const row = rowMeet(rows, other, w)
        return row === undefined
            ? undefined
            : listOf(row.slice(0, p), spread, row.slice(p))
    }
    // the side without a spread fixes the arity, and a shape that refuses that length shares no
    // value with it
    const fixed = x.spread === undefined ? x : y
    const n = fixed.pre.length + fixed.suf.length
    const rows = rowOf(x, n)
    const other = rowOf(y, n)
    if (rows === undefined || other === undefined) return never
    const row = rowMeet(rows, other, w)
    return row === undefined ? undefined : listOf(row, undefined, [])
}

/**
 * **Two fields at one name: the meet of the terms, at the stronger mark.**
 *
 * A mark carries two presence bits, whether the name must be present when the object is written and
 * whether it must be present when it is read. `optional` forces neither, `withLegacyRead` forces the write
 * alone, and `req` forces both, so the three are a chain and the meet takes the stronger.
 *
 * **`optional` against `withLegacyRead` refuses, and the presence bits are not why.** Both admit a map
 * omitting the name. They part on what they *read* there: `optional` reads a map without it and
 * `withLegacyRead` reads a map carrying the stand-in, so the pair shares attributes it reads two ways.
 *
 * Two `withLegacyRead` fields refuse because the model has no equality on its stand-ins, and
 * `undefinable` refuses because the model's `Field` has no such mark. Both are refusals this
 * library inherits rather than rules it states.
 */
const meetFields = (a: Field, b: Field, w: Walk): Field | undefined => {
    if (a.mark === 'undefinable' || b.mark === 'undefinable') return undefined
    if (a.mark === 'optional' && b.mark === 'optional')
        return mark(meetWalk(a.t, b.t, w), 'optional')
    if (a.mark === 'fallback' || b.mark === 'fallback')
        return a.mark === 'req' || b.mark === 'req'
            ? mark(meetWalk(a.t, b.t, w), 'req')
            : undefined
    return mark(meetWalk(a.t, b.t, w), 'req')
}

const mark = (
    t: Term | undefined,
    of: 'req' | 'optional',
): Field | undefined => (t === undefined ? undefined : { mark: of, t })

/** Whether a field admits nothing at a name that must be present. */
const isBottomField = (field: Field): boolean =>
    field.mark !== 'optional' && field.t.kind === 'never'

/** Whether every `withLegacyRead` name one body declares is a name the other declares too. */
const fbShared = (a: Body, b: Body): boolean =>
    Object.entries(a.fields).every(
        ([name, field]) => field.mark !== 'fallback' || name in b.fields,
    )

/**
 * **Two bodies, met pointwise**, as `objObj` states it.
 *
 * A body is a total function from the key space to a field: a declared name holds its field, and
 * an undeclared name holds `optional` of the open block, which is `never` where the body is closed.
 * So every name of either body meets at its two fields, a name only the right body declares meets
 * the left body's block, and the blocks meet as the default. A field at the bottom decides before a
 * field that refuses, because a product is the bottom when any factor is.
 *
 * **The normal form drops a name that states the default**, where the default is `never`: in a
 * closed body `optional never` is what an undeclared name already holds. An open default has no
 * equality to test, so there every name is kept as written.
 *
 * A `withLegacyRead` name the other body does not declare refuses. The model's field has no such
 * mark, so the host keeps the refusal it inherits.
 */
const meetBodies = (a: Body, b: Body, w: Walk): Term | undefined => {
    if (!fbShared(a, b) || !fbShared(b, a)) return undefined
    const aBlock = a.rest ?? never
    const bBlock = b.rest ?? never
    const met: [string, Field | undefined][] = [
        ...Object.entries(a.fields).map(
            ([name, field]): [string, Field | undefined] => [
                name,
                meetFields(
                    field,
                    b.fields[name] ?? { mark: 'optional', t: bBlock },
                    w,
                ),
            ],
        ),
        ...Object.entries(b.fields)
            .filter(([name]) => !(name in a.fields))
            .map(([name, field]): [string, Field | undefined] => [
                name,
                meetFields({ mark: 'optional', t: aBlock }, field, w),
            ]),
    ]
    if (met.some(([, field]) => field !== undefined && isBottomField(field)))
        return never
    const block = meetWalk(aBlock, bBlock, w)
    if (block === undefined) return undefined
    const closed = block.kind === 'never'
    const fields: Record<string, Field> = {}
    for (const [name, field] of met) {
        if (field === undefined) return undefined
        if (closed && field.mark === 'optional' && field.t.kind === 'never')
            continue
        fields[name] = field
    }
    return {
        kind: 'object',
        body: closed ? { fields } : { fields, rest: block },
    }
}
