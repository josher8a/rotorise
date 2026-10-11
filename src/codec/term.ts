/**
 * The term language, and the five functions of a term that the model computes.
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
    AnyCodec,
    LiteralBase,
    LiteralValue,
    Refinement,
    Rng,
    SetSlot,
} from './codec'
import { CodecError } from './result'
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
 * The rule `(literal)`: a ground base, and **one** inhabitant of that base's carrier.
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
 * The rule `(refine)`'s `q`, as the term carries it.
 *
 * The model's `q` is a bare `Value → Bool` and the host's used to be the caller's closure. Neither
 * is enough, because **the certificate has to read the predicate as data**: a closure decides nothing a
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
 * adapter: containment, the arbitrary, and the union refusal at the type level each read it.
 */
export type OpaqueSugar = 'opaqueLossy' | 'opaqueRefuse'

/** Whether a `held` is one of the two numeric policies of `opaque`. */
export const isOpaqueSugar = (via: string | undefined): via is OpaqueSugar =>
    via === 'opaqueLossy' || via === 'opaqueRefuse'

/** The terms. One variant per `Term.lean` constructor, under the model's names. */
export type Term =
    | { readonly kind: 'string' }
    /**
     * The rule `(number)`, and **the one native numeric term**. Its carrier is {@link DynamoNumber},
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
     * The rule `(set)`: the finite-powerset lift of an element term. A lawful element gives a lawful set
     * (`lawful_setCodec`), and that law reads nothing about the element's base.
     *
     * That a stored set holds elements of one member of `S`, `N` or `B` is the DynamoDB universe's
     * rule, not structure here: {@link set} refuses an element that names no such member, as the
     * model's `SetElem` obligation does. A restricted element, a literal element and an adapter
     * element are each spelled at the element.
     */
    | { readonly kind: 'set'; readonly elem: Term }
    /**
     * The rule `(list)`: the one positional container, as a prefix, at most one spread, and a suffix.
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
     * The rule `(held)`: a conversion between two restrictions. `inner` restricts the stored side, and
     * `outer` restricts the held side, which is the model's second term.
     */
    | {
          readonly kind: 'held'
          readonly inner: Term
          /**
           * **The held side, as a term.** The write occupancy of a `held` is the occupancy of this
           * term, as the model's `occV (held t P k) = occV P` states. A library adapter records
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
           * **The arbitrary and the shrinker, where the caller supplies them rather than the inner codec.**
           *
           * An adapter derives both from the codec underneath: a value is generated for the inner
           * term and handed out through `g`, and a value is shrunk on the inner side and handed
           * back. That is right whenever the pair is total on the inner codec's values.
           *
           * It is wrong when the adapter is partial. A conversion that refuses some of what the
           * inner codec generates makes the derived arbitrary produce values the pair never
           * makes, and the property then fails on the arbitrary rather than on the codec. So the
           * caller states them, and states them here because a definition carries everything the
           * caller said about a codec. Absent is the honest answer for an adapter nobody has
           * declared, and the derivation stands there.
           */
          readonly arbitrary?: (rng: Rng, size: number) => unknown
          readonly shrink?: (value: never) => readonly unknown[]
      }
    /**
     * The rule `(refine)`. The model carries `q : Value → Bool`; this carries a {@link Predicate}, so a
     * declaration can read the ones that are data. The caller's closure rides in `closure`, with
     * `what` as the refusal text and `arbitrary` as what an arbitrary derived from the term reads.
     */
    | { readonly kind: 'refine'; readonly inner: Term; readonly q: Predicate }
    /** The rule `(withLegacyRead)`: `r : Attr ⇀ Value`, the older reading, which widens `p` and never `e`. */
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
     * and {@link disjoint} and the emitter read the binder at the term that closes the cycle. Only
     * {@link member} answers `undefined`, because the host cannot force a thunk safely at
     * declaration: forcing a recursive thunk can loop.
     *
     * **The two projections answered `undefined` until it was measured, on the ground that
     * forcing would throw on the entity the thunk exists to allow. Both halves were wrong.**
     * Forcing does not throw: `object()` already forces at the declaration and the recursive
     * entity still round-trips. And `undefined` was the unsound direction rather than the safe
     * one, because the declaration guard then refused a union when two occupancies *met*, so an
     * unknown occupancy made it decline to refuse. A union of a thunk of `string` and `string` was
     * accepted, and a write then found two options admitting one value. `lazy` was the only
     * term answering unknown on both projections, which is why it was the only hole.
     */
    | { readonly kind: 'lazy'; readonly get: () => Term }
    /**
     * The rule `(opaque)`: the universal sum, and **total**. It holds a number as {@link DynamoNumber},
     * which is the model's `WFNumeral`, so it writes every wire value. The two numeric policies
     * `'refuse'` and `'lossy'` are not terms of their own: each is a `held` over this term.
     */
    | { readonly kind: 'opaq' }
    | { readonly kind: 'object'; readonly body: Body }
    | { readonly kind: 'union'; readonly options: readonly Term[] }
    /**
     * The bottom: the term that admits no value.
     *
     * A constructor rather than a union over no options. The empty option list is a term a caller
     * can build by accident, and a rule that reads it as the bottom reads that accident as intent.
     */
    | { readonly kind: 'never' }

/**
 * The object payload: the declared names with the field at each, and the open block.
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
 * A field: a term with a presence mark, and **not a term**.
 *
 * No member of {@link Term} holds one, which is the field stratum as a type rather than a check.
 * `array(optional(c))` is not a thing this type can express.
 */
export type Field =
    | { readonly mark: 'req'; readonly t: Term }
    | { readonly mark: 'optional'; readonly t: Term }
    /** `withLegacyRead` concludes `req`: the absence is in the row, never in the value. */
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
 * The rule `(union)`'s member: `μ` where every option agrees, and `⊤` otherwise.
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
        // a wrapper preserves the member, which is what keeps a key's attribute type stable
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
 * A thunk reads through to its subterm, as the model reads the term a thunk returns. A thunk that
 * names a codec not yet declared is a free variable, and a free variable may write every slot.
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
        // the held side restricts every value `f` receives, as `occV (held t P k) = occV P`
        case 'held':
            return occV(t.outer)
        // a thunk carries a term, so it answers what that term answers. The model has no thunk: the
        // emitter prints the term that a thunk returns, so the model reads through on both
        // projections, and only the member is lost
        case 'lazy': {
            const forced = force(t)
            return forced === undefined ? everySlot : occV(forced)
        }
        case 'refine':
        case 'legacy':
            return occV(t.inner)
        case 'union':
            return [...new Set(t.options.flatMap(occV))]
        // **A closed form, not `⊤`.** Separation tells apart the two things a `⊤` covers: *unknown*, which is
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
 * says. A `held` answers from the slots it declares, and `lazy` reads through the thunk. A thunk
 * that names a codec not yet declared is a free variable, and the term does not determine whether a
 * free variable reaches the point.
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
        case 'lazy': {
            const forced = force(t)
            return forced === undefined ? undefined : ownsNullOf(forced)
        }
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
        // transparent, as on the write side. A free variable may read every member
        case 'lazy': {
            const forced = force(t)
            return forced === undefined ? undefined : occA(forced)
        }
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
 * pins (the model reads them through the disjointness of two bodies). Selection itself is by attempt at every option, objects
 * included. An `optional` binding is declared and not required, and that is
 * the ambiguity of the union: two objects declaring only optional names both admit
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
    /**
     * The outermost adapter that the literal sits under, where one does. The form names the kind of
     * the held side and not the conversion, so a clause compares the adapter as well.
     */
    readonly adapter?: Extract<Term, { kind: 'held' }>
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
): Omit<NameForm, 'required'> | undefined => {
    const at = resolvedTerm(t)
    if (at?.kind === 'held') {
        // an `opaque` held side admits every kind, so it names no form
        if (at.outer.kind === 'opaq') return undefined
        const pinned = clauseForm(at.inner, at.outer)
        return pinned && { ...pinned, adapter: at }
    }
    const alts = at && literalAlternatives(at)
    return alts && { alts, form: literalForm(alts.base, outer) }
}

/** …and the member's side, which reads through a refinement too. @see {@link clauseForm} */
export const pinnedForm = (t: Term): Omit<NameForm, 'required'> | undefined => {
    const at = resolvedTerm(t)
    return at?.kind === 'refine' ? pinnedForm(at.inner) : at && clauseForm(at)
}

/**
 * The literal a term is pinned to, reading through a refinement.
 *
 * A refinement of a literal admits a subset of that literal's alternatives, so the literal is a
 * sound upper bound on what the field can carry: a value outside it is outside the field, and a
 * value inside it that the refinement rejects is the option's own error to report.
 */
const pinnedLiteral = (t: Term): Alternatives | undefined => {
    const at = resolvedTerm(t)
    return at?.kind === 'refine'
        ? pinnedLiteral(at.inner)
        : at && literalAlternatives(at)
}

/**
 * **The alternatives a term pins, without reading through a refinement.**
 *
 * One literal pins its own value; a union of literals at one base pins theirs, which is what
 * `string('a', 'b')` builds. Everything else pins nothing.
 *
 * Separate from {@link pinnedLiteral} because a tag is written and a refinement is not: a reader
 * that must produce the value the codec writes cannot look through a predicate that narrows it.
 */
export const literalAlternatives = (t: Term): Alternatives | undefined => {
    const at = resolvedTerm(t)
    return at?.kind === 'literal'
        ? oneAlternative(at)
        : at?.kind === 'union'
          ? unionAlternatives(at.options)
          : undefined
}

/**
 * **The term that a chain of thunks resolves to**, or nothing where a thunk does not resolve.
 *
 * The emitter prints a thunk that closes no cycle as its body, so the model reads a literal behind a
 * thunk as the literal. Each reader of a literal or a tag reads through the chain here, and a chain
 * that returns to a thunk it already passed resolves to nothing.
 */
const resolvedTerm = (t: Term): Term | undefined => {
    const passed = new Set<Term>()
    let at: Term | undefined = t
    while (at?.kind === 'lazy') {
        if (passed.has(at)) return undefined
        passed.add(at)
        at = force(at)
    }
    return at
}

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
export const storedAlternatives = (t: Term): Alternatives | undefined => {
    const at = resolvedTerm(t)
    return at?.kind === 'held'
        ? storedAlternatives(at.inner)
        : at && literalAlternatives(at)
}

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
    const [first, ...rest] = options.map(resolvedTerm)
    if (first?.kind !== 'literal') return undefined
    const ls: LiteralValue[] = [first.v]
    for (const option of rest) {
        if (option?.kind !== 'literal' || option.base !== first.base)
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
 * **Whether the two pairs of views are disjoint**, the model's `viewsDisjoint`.
 *
 * A term denotes a partial isomorphism, the caller view states its domain, and the stored view
 * states its range. Two options whose domains are disjoint and whose ranges are disjoint are
 * orthogonal: no value has two writers, and no attribute has two readers. {@link agrees} asks each
 * half of it apart, where no binder is unfolded, as the model's oracle `dynOracle` does.
 */
export const viewsDisjoint = (x: Term, y: Term): boolean =>
    disjoint(callerView(x), callerView(y)) &&
    disjoint(storedView(x), storedView(y))

/**
 * **Whether a term reaches a subterm of one of these kinds**, at any depth, or reaches a thunk
 * that the walk cannot read.
 *
 * The walk forces each thunk once and reads through it. A thunk that the walk meets again is
 * recursive, and a thunk that throws names a codec that is not yet declared. Each answers
 * "reaches".
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
 * **The throw of a thunk that its own resolution forces again**, the black hole of a lazy runtime.
 * `scope({ Self: nullable(ref('Self')) })` forces the thunk of the `nullable` while the thunk
 * resolves. The thunk has no term yet, so the thunk names the codec being declared, as a `ref` that
 * no scope binds does.
 */
export class ThunkReentered extends Error {
    constructor() {
        super('a thunk was forced again while its own resolution ran')
        this.name = 'ThunkReentered'
    }
}

/**
 * The term of a thunk, or nothing where the thunk names a codec not yet declared. A thunk is
 * caller code, so its throw crosses the boundary here. Two throws name such a codec: the
 * `ReferenceError` of a `ref` that no scope binds yet, and {@link ThunkReentered}. The
 * caller of this function refuses, declines, or reads the thunk as a free variable.
 *
 * **Every other throw propagates.** A `RangeError` is a stack that overflowed, which is a broken
 * invariant of the host and not a free variable. Read as a free variable, an overflow makes each
 * walk back out one level and force again, and a recursive declaration does not end.
 */
export const force = (
    t: Term & { readonly kind: 'lazy' },
): Term | undefined => {
    try {
        return t.get()
    } catch (thrown) {
        if (
            thrown instanceof ReferenceError ||
            thrown instanceof ThunkReentered
        )
            return undefined
        throw thrown
    }
}

/**
 * The slot of a `ref`: the name, the definitions of the scope that binds the name, and waiting
 * checks. A scope that refuses keeps its definitions in the slot, so a reader of the term sees the
 * cycle that the scope refused, and marks the slot \`refused\`, so the name stays free.
 */
export type RefSlot = {
    readonly name: string
    bound?: Readonly<Record<string, AnyCodec>>
    refused?: boolean
    readonly waiting: (() => void)[]
}

/** The slot of each `ref`, by the term of the `ref`. `scope` fills the slot one time. */
export const refSlots = new WeakMap<Term, RefSlot>()

/**
 * The slots of the `ref`s that the terms reach and that no scope binds yet. A bound `ref` belongs
 * to the closed scope that bound it, so the walk stops there.
 */
export const unboundRefs = (roots: readonly Term[]): ReadonlySet<RefSlot> => {
    const slots = new Set<RefSlot>()
    const seen = new Set<Term>()
    const walk = (t: Term): void => {
        if (seen.has(t)) return
        seen.add(t)
        const slot = refSlots.get(t)
        if (slot !== undefined) {
            if (slot.bound === undefined || slot.refused === true)
                slots.add(slot)
            return
        }
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
    for (const root of roots) walk(root)
    return slots
}

/**
 * Each term that {@link freeNamesOf} found closed, with the count of refused scopes at that time.
 * A scope that refuses frees each name that it bound, so the count makes each answer stale.
 */
const closedTerms = new WeakMap<Term, number>()
let refusals = 0

/** Marks the slots of a refused scope: each name stays free. */
export const refuseSlots = (slots: Iterable<RefSlot>): void => {
    for (const slot of slots) slot.refused = true
    refusals += 1
}

/**
 * **The free names of a term**: the names of the `ref`s that the term reaches and that no scope
 * binds. The run-time side of the free names that the type of a codec carries.
 */
export const freeNamesOf = (t: Term): readonly string[] => {
    if (closedTerms.get(t) === refusals) return []
    const names = [...new Set([...unboundRefs([t])].map((slot) => slot.name))]
    if (names.length === 0) closedTerms.set(t, refusals)
    return names
}

/**
 * **A use needs a closed codec.** Nothing, or the refusal of a term that reads a name through a
 * \`ref\` that no scope binds: the codec of such a term has no meaning until a scope binds the name.
 */
export const openRefusal = (t: Term): CodecError | undefined => {
    const names = freeNamesOf(t)
    return names.length === 0
        ? undefined
        : new CodecError(
              `this codec reads ${names.map((name) => `'${name}'`).join(', ')} through a \`ref\` that no scope binds. Place the codec in a \`scope\` that binds each name, and use the entry of that scope`,
          )
}

/**
 * **How a recursion in the term reads its own input**, read from the order of the entries of each
 * cycle ({@link entryOrder}). The level is the model's:
 *
 * - `0`: the term has no recursion;
 * - `1`: each cycle has an order, so each stage reads a shallower input;
 * - `2`: a cycle has no container on its path, so the recursion reads the input of its own binder;
 * - `3`: a cycle has an adapter on its path. Caller code makes the input of the inner term, at any
 *   depth. A `held` converts the value, and a `withLegacyRead` writes the older reader's answer.
 *
 * The model's guard refuses `2` and `3`. **A `ref` that no scope binds is a free variable**, and
 * closes no cycle: an open fragment holds no recursion yet, and the {@link scope} that binds the
 * name runs the walk with every name bound.
 */
export const recursionUse = (root: Term): number => {
    const components = componentsOf([root])
    let use = components.length === 0 ? 0 : 1
    for (const component of components) {
        const order = entryOrder(component)
        if (order.kind === 'refused')
            use = Math.max(use, order.cause === 'wall' ? 3 : 2)
    }
    return use
}

/**
 * **The refusal of a former whose term the model's guard refuses.** The refusal carries the term,
 * so a checker states the model's guard on the term that the host refused. The refusal carries the
 * level of {@link recursionUse}, so a walk that forces the thunk reads the cause.
 */
export class RecursionRefused extends CodecError {
    readonly term: Term
    readonly use: 2 | 3

    constructor(term: Term, use: 2 | 3, reason: string) {
        super(reason)
        this.term = term
        this.use = use
    }
}

/**
 * The term of a thunk, or nothing where {@link force} answers nothing or the thunk throws a
 * {@link CodecError}. **A former refuses inside a thunk where the name it reads is in progress**:
 * the thunk of a `nullable` over a `ref` to its own entry refuses while the entry resolves. The
 * throw leaves no mark, so a later force retries. So the walk reads the refusal as the free
 * variable that a `ref` that no scope binds is.
 */
const forceDeclared = (
    t: Term & { readonly kind: 'lazy' },
): Term | undefined => {
    try {
        return force(t)
    } catch (thrown) {
        if (thrown instanceof CodecError) return undefined
        throw thrown
    }
}

/** A list, an object or a union with each position, field and option replaced by its view. */
export const mapChildren = (t: Term, view: (t: Term) => Term): Term => {
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
 * of the same binder. {@link disjoint} then reads the view as `mu` of the view of the body, and
 * a variable of the view at the thunk.
 *
 * The build forces no thunk, so it ends: it recurses only through the edges that are not a
 * thunk, and every such edge of a term is built before the term. A thunk of the view forces its
 * thunk when {@link disjoint} reads it. A thunk that throws throws there, and {@link disjoint}
 * reads it as a free variable. So the thunk of the view forces its thunk directly and not through
 * {@link force}: the throw must reach the {@link force} of {@link disjoint} at the thunk of the
 * view.
 */
export const throughThunks =
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
 * term admits. A `refine` above a `held` keeps its predicate, because the caller states the
 * predicate on the held value.
 */
const callerView = throughThunks((t, view) => {
    switch (t.kind) {
        case 'held':
            return view(t.outer)
        case 'refine':
            return { kind: 'refine', inner: view(t.inner), q: t.q }
        // a `withLegacyRead` writes what its inner term writes, and the older reader only reads
        case 'legacy':
            return view(t.inner)
        default:
            return mapChildren(t, view)
    }
})

/**
 * **The stored view**: each `held` becomes its inner term. The view reads each attribute that
 * the term reads. A `withLegacyRead` stays as it is, and {@link disjoint} reads it as `opaque`,
 * which is the model's stored view of it: the older reader reads every attribute.
 *
 * **The view keeps a predicate only where the inner term decodes the same in the view as in the
 * term**: where the inner term lies below the top ({@link belowTop}), read at its own scope. An
 * adapter (`held`, `withLegacyRead`, a field with a stand-in) or a free variable can run caller
 * code there. Elsewhere the view drops the predicate, because data exists only on the side where
 * it was stated: the stored side reads the predicate only through `g`, and the view keeps no
 * closure.
 */
export const storedView = throughThunks((t, view) => {
    switch (t.kind) {
        case 'held':
            return view(t.inner)
        case 'refine':
            return belowTop(t.inner, { binds: bindersOf(t.inner), inside: [] })
                ? t
                : view(t.inner)
        default:
            return mapChildren(t, view)
    }
})

/**
 * **Whether a `withLegacyRead` occurs in the term.** The model states the read widening as
 * `Term.legacy`, and the judgement `Typed` has no rule for it, because the pair is not a partial
 * bijection. The law of `set`, `lawful_setCodec`, needs a lawful element, so no law covers a set
 * of a widened element, and `set` refuses one.
 */
export const widensRead = (t: Term): boolean => reaches(t, ['legacy'])

/**
 * **Whether two `held` terms are one adapter**: the tag test of the held row, which mirrors the
 * model's `dynOracle.same`. The tag of a library adapter is its `via` name, and the model carries
 * one generator for each name. The tag of a caller's adapter is the pair of functions that
 * `held` builds once for each call, so two terms of one call are one adapter.
 */
export const sameAdapter = (
    x: Extract<Term, { kind: 'held' }>,
    y: Extract<Term, { kind: 'held' }>,
): boolean =>
    (x.via !== undefined && x.via === y.via) || (x.f === y.f && x.g === y.g)

/**
 * **Whether two terms are one term**: one structure, with each thunk read as its target, and each
 * function that a term holds the same function object. A literal compares by its base, and a
 * stand-in by `Object.is`.
 *
 * Two codecs built by two calls of one constructor are two objects and one term, and the model
 * reads only the term. A thunk that closes a cycle makes the walk meet a pair again, and the walk
 * assumes that pair equal: each test is a conjunction, so a pair that differs makes the answer
 * `false` wherever the walk meets it. A thunk that throws is equal to itself only.
 */
export const sameTerm = (x: Term, y: Term): boolean => {
    const assumed: [Term, Term][] = []
    const same = (a: Term, b: Term): boolean => {
        const l = resolvedTerm(a) ?? a
        const r = resolvedTerm(b) ?? b
        if (l === r) return true
        if (assumed.some(([one, other]) => one === l && other === r))
            return true
        assumed.push([l, r])
        const all = (ls: readonly Term[], rs: readonly Term[]) =>
            ls.length === rs.length &&
            ls.every((one, i) => {
                const other = rs[i]
                return other !== undefined && same(one, other)
            })
        const maybe = (one: Term | undefined, other: Term | undefined) =>
            one === undefined || other === undefined
                ? one === other
                : same(one, other)
        switch (l.kind) {
            case 'literal':
                return (
                    r.kind === 'literal' &&
                    l.base === r.base &&
                    sameLiteral(l.v, r.v)
                )
            case 'set':
                return r.kind === 'set' && same(l.elem, r.elem)
            case 'list':
                return (
                    r.kind === 'list' &&
                    all(l.pre, r.pre) &&
                    maybe(l.spread, r.spread) &&
                    all(l.suf, r.suf)
                )
            case 'held':
                return (
                    r.kind === 'held' &&
                    l.via === r.via &&
                    l.f === r.f &&
                    l.g === r.g &&
                    l.arbitrary === r.arbitrary &&
                    l.shrink === r.shrink &&
                    same(l.inner, r.inner) &&
                    same(l.outer, r.outer)
                )
            case 'refine':
                return (
                    r.kind === 'refine' &&
                    samePredicate(l.q, r.q) &&
                    same(l.inner, r.inner)
                )
            case 'legacy':
                return (
                    r.kind === 'legacy' && l.r === r.r && same(l.inner, r.inner)
                )
            case 'object': {
                if (r.kind !== 'object') return false
                const names = Object.keys(l.body.fields)
                return (
                    names.length === Object.keys(r.body.fields).length &&
                    names.every((name) => {
                        const one = l.body.fields[name]
                        const other = r.body.fields[name]
                        return (
                            one !== undefined &&
                            other !== undefined &&
                            one.mark === other.mark &&
                            (one.mark !== 'fallback' ||
                                (other.mark === 'fallback' &&
                                    Object.is(one.v, other.v))) &&
                            same(one.t, other.t)
                        )
                    }) &&
                    maybe(l.body.rest, r.body.rest)
                )
            }
            case 'union':
                return r.kind === 'union' && all(l.options, r.options)
            // a thunk that throws is equal to itself only, which the identity test above answers
            case 'lazy':
                return false
            default:
                return l.kind === r.kind
        }
    }
    return same(x, y)
}

/** Two predicates: the same alternatives, or the same closure, field by field. */
const samePredicate = (p: Predicate, q: Predicate): boolean => {
    if (p.kind === 'members')
        return (
            q.kind === 'members' &&
            p.literal.base === q.literal.base &&
            p.literal.ls.length === q.literal.ls.length &&
            p.literal.ls.every((one) =>
                q.literal.ls.some((other) => sameLiteral(one, other)),
            )
        )
    return (
        q.kind === 'closure' &&
        p.q.is === q.q.is &&
        p.q.what === q.q.what &&
        p.q.arbitrary === q.q.arbitrary &&
        p.q.onThinSearch === q.q.onThinSearch
    )
}

/* ── the compatibility decision ───────────────────────────────────────────────────────── */

/** One half of agreement. `write`: two writers of one value write one attribute. `read`: two
 * readers of one attribute read one value. */
type Half = 'write' | 'read'

/**
 * **Where the decision is in the two operands**: the scope of each operand, the binders unfolded
 * together, and the context of each operand, the model's. A context holds the binders whose
 * variable is below `opaque`, and a free variable is in none.
 */
type Agreement = {
    readonly left: Scope
    readonly right: Scope
    readonly pairs: Walk['pairs']
    readonly safeL: ReadonlySet<Term>
    readonly safeR: ReadonlySet<Term>
}

/**
 * **Whether each variable that the spelling reads is safe in the context**, the model's
 * `Term.safe`: its binder is in the context, or is a binder of the term itself. A free variable is
 * not safe. With no binder in the context, the term is closed, the model's `Term.closed`.
 */
const safeAt = (t: Term, scope: Scope, safe: ReadonlySet<Term>): boolean => {
    const one = see(t, scope)
    switch (one.kind) {
        case 'mu':
            return safeAt(one.body, one.scope, new Set([...safe, one.body]))
        case 'var':
            return safe.has(one.binder)
        case 'free':
            return false
        case 'term':
            break
    }
    const on = (inner: Term) => safeAt(inner, scope, safe)
    const u = one.t
    switch (u.kind) {
        case 'held':
            return on(u.inner) && on(u.outer)
        case 'legacy':
        case 'refine':
            return on(u.inner)
        case 'set':
            return on(u.elem)
        case 'list':
            return (
                u.pre.every(on) &&
                (u.spread === undefined || on(u.spread)) &&
                u.suf.every(on)
            )
        case 'object':
            return (
                Object.values(u.body.fields).every((field) => on(field.t)) &&
                (u.body.rest === undefined || on(u.body.rest))
            )
        case 'union':
            return u.options.every(on)
        default:
            return true
    }
}

/**
 * **Whether a term is closed at the scope**, the model's `Term.closed`: it reads no variable of a
 * binder outside it. A binder of the term itself is inside it.
 */
const closedAt = (t: Term, scope: Scope): boolean => safeAt(t, scope, new Set())

/**
 * **Whether a term lies below the top at the scope**, the model's `!hasHeld t && t.closed`: it
 * holds no adapter and it is closed. Such a term writes one value to one attribute and reads one
 * attribute to one value, as the top does, so a predicate over it reads the value itself.
 */
const belowTop = (t: Term, scope: Scope): boolean =>
    !holdsAdapter(t, scope) && closedAt(t, scope)

/**
 * **The context with the binder of `y` pushed**, the model's `pushMu`: the binder is below `opaque`
 * where its body holds no adapter and each variable of the recursive term is safe.
 */
const pushBinder = (
    safe: ReadonlySet<Term>,
    binder: Term,
    y: Term,
    scope: Scope,
): ReadonlySet<Term> =>
    !holdsAdapter(y, scope) && safeAt(y, scope, safe)
        ? new Set([...safe, binder])
        : safe

/**
 * **Whether two options agree on both halves**, the model's `compatPair` at `dynOracle`, which
 * holds at every codec that a thunk that throws later names. A union is the join of its options,
 * and the join of two lawful options exists exactly when the two are compatible (Lawson: `s ∨ t`
 * exists iff `s ∼ t`). Compatibility of two partial bijections is two halves of agreement: two
 * writers of one value write one attribute, and two readers of one attribute read one value.
 * The decision reads each operand as the model spells it, as {@link disjoint} does.
 */
export const agrees = (x: Term, y: Term): boolean => {
    const at: Agreement = {
        left: { binds: bindersOf(x), inside: [] },
        right: { binds: bindersOf(y), inside: [] },
        pairs: [],
        safeL: new Set(),
        safeR: new Set(),
    }
    return agreeWalk('write', x, y, at) && agreeWalk('read', x, y, at)
}

/**
 * **Whether the spelling of a term at a scope holds an adapter**, the model's `hasHeld`. A
 * variable is not an adapter. The host reads three more terms as an adapter, because no bound
 * below `opaque` covers each one. A free variable is a thunk that names a codec not yet declared,
 * and that codec can hold a `held`. A `withLegacyRead` reads an attribute through caller code. A
 * field with a fallback reads a map without the name to a value with the name.
 */
const holdsAdapter = (t: Term, scope: Scope): boolean => {
    const one = see(t, scope)
    switch (one.kind) {
        case 'mu':
            return holdsAdapter(one.body, one.scope)
        case 'var':
            return false
        case 'free':
            return true
        case 'term':
            break
    }
    const on = (inner: Term) => holdsAdapter(inner, scope)
    const u = one.t
    switch (u.kind) {
        case 'held':
        case 'legacy':
            return true
        case 'refine':
            return on(u.inner)
        case 'set':
            return on(u.elem)
        case 'list':
            return (
                u.pre.some(on) ||
                (u.spread !== undefined && on(u.spread)) ||
                u.suf.some(on)
            )
        case 'object':
            return (
                Object.values(u.body.fields).some(
                    (field) => field.mark === 'fallback' || on(field.t),
                ) ||
                (u.body.rest !== undefined && on(u.body.rest))
            )
        case 'union':
            return u.options.some(on)
        default:
            return false
    }
}

/** The bottom, as the model spells it at the scope. */
const isNeverAt = (t: Term, scope: Scope): boolean => {
    const one = see(t, scope)
    return one.kind === 'term' && one.t.kind === 'never'
}

/**
 * **The term inside which a `held` acts on one half**, the model's `heldSide`: a `held` writes
 * inside its held side and reads inside its stored side. Where that side is a `held` too, the
 * half acts inside its side in turn, and a binder or a variable stops the walk.
 */
const heldSide = (half: Half, t: Term, scope: Scope): Term | undefined => {
    const one = see(t, scope)
    if (one.kind !== 'term' || one.t.kind !== 'held') return undefined
    const side = half === 'write' ? one.t.outer : one.t.inner
    return heldSide(half, side, scope) ?? side
}

/**
 * **The rows that read no structure**, the model's `cbase`. The bottom agrees with every term.
 * Two terms with no adapter whose variables are safe are bounded by the top. Two disjoint terms
 * share nothing. Two closed terms with disjoint views share nothing on their half. A `held`
 * whose half is disjoint from the partner shares nothing there.
 */
const baseRows = (half: Half, x: Term, y: Term, at: Agreement): boolean => {
    if (isNeverAt(x, at.left) || isNeverAt(y, at.right)) return true
    if (
        !holdsAdapter(x, at.left) &&
        !holdsAdapter(y, at.right) &&
        safeAt(x, at.left, at.safeL) &&
        safeAt(y, at.right, at.safeR)
    )
        return true
    const apart = (a: Term, b: Term) =>
        disjointWalk(a, b, { left: at.left, right: at.right, pairs: [] })
    if (apart(x, y)) return true
    // the caller view states the domain, and the stored view states the range
    const view = half === 'write' ? callerView : storedView
    // two closed terms denote alike at every binder, so their views speak for them
    if (
        closedAt(x, at.left) &&
        closedAt(y, at.right) &&
        disjoint(view(x), view(y))
    )
        return true
    const hx = heldSide(half, x, at.left)
    if (hx !== undefined && apart(hx, y)) return true
    const hy = heldSide(half, y, at.right)
    return hy !== undefined && apart(x, hy)
}

/**
 * **The rows of the right operand**, the model's `cmpR`. The bottom agrees with every term. A
 * union agrees where each option does. A refinement is below its inner term. A recursive term
 * unfolds, and its binder pairs with nothing. `fam` answers every other spelling, and each
 * spelling that it declines.
 */
const agreeRight = (
    half: Half,
    fam: (y: Term, at: Agreement) => boolean,
    y: Term,
    at: Agreement,
): boolean => {
    if (fam(y, at)) return true
    const other = see(y, at.right)
    if (other.kind === 'mu')
        return agreeRight(half, fam, other.body, {
            ...at,
            right: other.scope,
            safeR: pushBinder(at.safeR, other.body, y, at.right),
        })
    if (other.kind !== 'term') return false
    switch (other.t.kind) {
        case 'never':
            return true
        case 'union':
            return other.t.options.every((option) =>
                agreeRight(half, fam, option, at),
            )
        case 'refine':
            return agreeRight(half, fam, other.t.inner, at)
        default:
            return false
    }
}

/** The right operand as the model spells it, where it is a constructor. */
const termAt = (y: Term, at: Agreement): Term | undefined => {
    const other = see(y, at.right)
    return other.kind === 'term' ? other.t : undefined
}

/**
 * **The compatibility decision, one half**, the model's `Term.compat`: one row per constructor of
 * the left operand, as the operands spell at the pairing. The rows are the model's, in the
 * model's order, and the host reads its own terms soundly. A `withLegacyRead` writes what its
 * inner term writes, and its older reading is caller code, so its read half agrees by the rows
 * that read no structure alone.
 *
 * **The walk ends**, for the reason {@link disjointWalk} ends: each call reads a strict subterm
 * of one spelling, or of both, with the other spelling unchanged.
 */
const agreeWalk = (half: Half, x: Term, y: Term, at: Agreement): boolean => {
    const one = see(x, at.left)
    const base = (y1: Term, at1: Agreement) => baseRows(half, x, y1, at1)
    switch (one.kind) {
        case 'mu': {
            if (baseRows(half, x, y, at)) return true
            const other = see(y, at.right)
            const safeL = pushBinder(at.safeL, one.body, x, at.left)
            // two recursive terms: the bodies agree on both halves, with the two binders paired
            if (other.kind === 'mu') {
                const inner: Agreement = {
                    left: one.scope,
                    right: other.scope,
                    pairs: [...at.pairs, { left: one.body, right: other.body }],
                    safeL,
                    safeR: pushBinder(at.safeR, other.body, y, at.right),
                }
                return (
                    agreeWalk('write', one.body, other.body, inner) &&
                    agreeWalk('read', one.body, other.body, inner)
                )
            }
            // a recursive term beside another term unfolds, and its binder pairs with nothing
            return agreeWalk(half, one.body, y, {
                ...at,
                left: one.scope,
                safeL,
            })
        }
        // a variable agrees with the variable of the binder that its own binder was unfolded with
        case 'var':
            return agreeRight(
                half,
                (y1, at1) => {
                    if (base(y1, at1)) return true
                    const other = see(y1, at1.right)
                    return (
                        other.kind === 'var' &&
                        at1.pairs.some(
                            (pair) =>
                                pair.left === one.binder &&
                                pair.right === other.binder,
                        )
                    )
                },
                y,
                at,
            )
        case 'free':
            return agreeRight(half, base, y, at)
        case 'term':
            break
    }
    const t = one.t
    switch (t.kind) {
        case 'never':
            return true
        case 'refine':
            return base(y, at) || agreeWalk(half, t.inner, y, at)
        case 'union':
            return (
                base(y, at) ||
                t.options.every((option) => agreeWalk(half, option, y, at))
            )
        case 'legacy':
            return agreeRight(half, base, y, at)
        case 'set':
            return agreeRight(
                half,
                (y1, at1) => {
                    if (base(y1, at1)) return true
                    const other = termAt(y1, at1)
                    return (
                        other?.kind === 'set' &&
                        agreeWalk(half, t.elem, other.elem, at1)
                    )
                },
                y,
                at,
            )
        case 'list':
            return agreeRight(
                half,
                (y1, at1) => {
                    if (base(y1, at1)) return true
                    const other = termAt(y1, at1)
                    if (other?.kind !== 'list') return false
                    const rights = positionsOf(other)
                    return positionsOf(t).every((left) =>
                        rights.every((right) =>
                            agreeWalk(half, left, right, at1),
                        ),
                    )
                },
                y,
                at,
            )
        case 'object':
            return agreeRight(
                half,
                (y1, at1) => {
                    if (base(y1, at1)) return true
                    const other = termAt(y1, at1)
                    return (
                        other?.kind === 'object' &&
                        bodiesAgree(half, t.body, other.body, at1)
                    )
                },
                y,
                at,
            )
        // two `held`s of one adapter agree where their stored sides agree
        case 'held':
            return agreeRight(
                half,
                (y1, at1) => {
                    if (base(y1, at1)) return true
                    const other = termAt(y1, at1)
                    return (
                        other?.kind === 'held' &&
                        sameAdapter(t, other) &&
                        agreeWalk(half, t.inner, other.inner, at1)
                    )
                },
                y,
                at,
            )
        default:
            return agreeRight(half, base, y, at)
    }
}

/** Every position of a list shape: the prefix, the spread, and the suffix. */
const positionsOf = (t: Extract<Term, { kind: 'list' }>): readonly Term[] => [
    ...t.pre,
    ...(t.spread === undefined ? [] : [t.spread]),
    ...t.suf,
]

/**
 * **Two fields at one name agree on one half**, the model's `ObjectSlot.compat`: the two terms
 * agree, whatever the presence. A field with a fallback reads a map without the name to its
 * stand-in, where every other field reads the map to a value without the name. So on the read
 * half a field with a fallback agrees beside a `req` field, which reads no map without the name,
 * and beside a field with the same stand-in.
 */
const fieldsAgree = (half: Half, a: Field, b: Field, at: Agreement): boolean =>
    (half === 'write' || standInsAgree(a, b)) && agreeWalk(half, a.t, b.t, at)

/** Two fields read a map without the name to one value, or one of the two reads no such map. */
const standInsAgree = (a: Field, b: Field): boolean =>
    a.mark === 'fallback'
        ? b.mark === 'req' || (b.mark === 'fallback' && Object.is(a.v, b.v))
        : b.mark !== 'fallback' || a.mark === 'req'

/**
 * **Two bodies agree on one half**, the model's object row: at each name that either body
 * declares, the two fields agree, and the two open blocks agree. An undeclared name holds
 * `optional` of the open block, which is `never` where the body is closed.
 */
const bodiesAgree = (half: Half, a: Body, b: Body, at: Agreement): boolean => {
    const blockOf = (body: Body): Field => ({
        mark: 'optional',
        t: body.rest ?? never,
    })
    const names = new Set([...Object.keys(a.fields), ...Object.keys(b.fields)])
    return (
        [...names].every((name) =>
            fieldsAgree(
                half,
                a.fields[name] ?? blockOf(a),
                b.fields[name] ?? blockOf(b),
                at,
            ),
        ) &&
        (a.rest === undefined || agreeWalk(half, a.rest, b.rest ?? never, at))
    )
}

/* ── disjointness ─────────────────────────────────────────────────────────────────────── */

/**
 * **Whether two terms share no value and no attribute** — `Calculus.Alg.Term.disjoint` at the
 * closed pairing, one row per constructor of the left operand.
 *
 * `true` says that no value is admitted by both terms and no attribute is read by both.
 * `false` states nothing: the test is sound, not complete. The admission of a term is its domain
 * idempotent, so the test decides that the product of two idempotents is zero.
 *
 * **A `held`, a `withLegacyRead` and `opaque` are disjoint only from the bottom.** The admission
 * of the first two is a function that no reader can read without running it, and `opaque`
 * admits every value. The views read a `held` ({@link viewsDisjoint}).
 *
 * **A recursive term is read as the model spells it**: `mu` at the term object that a cycle
 * returns to, and a variable at the thunk that closes the cycle ({@link Scope}). Two variables are
 * disjoint where the two binders were unfolded together, because the model's environments keep
 * each such pair apart. Two recursive terms are disjoint where their bodies are, with the two
 * binders paired. A recursive term also unfolds, and its binder pairs with nothing. The rows of a
 * left recursive term and a left refinement split the right operand at every depth, so a right
 * refinement or a right recursive term hides no option from the left row.
 *
 * **A thunk that throws is a free variable that pairs with nothing.** The thunk names a codec that
 * is not yet declared, so the host cannot read the term that the thunk returns. The soundness of
 * the model's test holds under every environment of its variables, so a verdict that reads no
 * such variable holds whatever the thunk returns later. Beside the bottom a free variable is
 * disjoint, and beside any other term it is not. A container of the variable beside a
 * constructor of another shape class is disjoint, and reads no variable.
 */
export const disjoint = (x: Term, y: Term): boolean =>
    disjointWalk(x, y, {
        left: { binds: bindersOf(x), inside: [] },
        right: { binds: bindersOf(y), inside: [] },
        pairs: [],
    })

/**
 * **Where a walk is in one operand**: the term objects that bind a variable, and the binders the
 * walk is inside, nearest last.
 *
 * A recursive host schema is a cycle of term objects closed by a thunk. The model names the cycle
 * with a binder: `Term.mu` at the object that a thunk returns while that object is on the walk,
 * and `Term.var k` at the thunk, where `k` counts the binders between the two. Any other thunk is
 * the term it returns. The test and the emitter read one spelling, so both read it through this
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

/** A term that holds no other term. A component of the term graph never holds one. */
export const leafKinds: ReadonlySet<Term['kind']> = new Set([
    'string',
    'number',
    'boolean',
    'binary',
    'null',
    'opaq',
    'never',
])

/**
 * The terms that a term reads one step down, through a thunk that resolves to a declared term.
 *
 * A thunk is the term of a `ref`, or a view of one, and a thunk runs no former and no scope. So a
 * force throws a `CodecError` only where the entry that the `ref` names is a field, and never a
 * refusal of the guard. A thunk that throws holds no cycle. The refusal of a nested scope reaches
 * the guard through the definitions that the refused scope keeps in the slot of each `ref`.
 */
export const childrenOf = (t: Term): readonly Term[] => {
    switch (t.kind) {
        case 'lazy': {
            const target = forceDeclared(t)
            return target === undefined ? [] : [target]
        }
        case 'list':
            return [
                ...t.pre,
                ...t.suf,
                ...(t.spread === undefined ? [] : [t.spread]),
            ]
        case 'object':
            return [
                ...Object.values(t.body.fields).map((field) => field.t),
                ...(t.body.rest === undefined ? [] : [t.body.rest]),
            ]
        case 'union':
            return t.options
        case 'set':
            return [t.elem]
        case 'held':
            return [t.inner, t.outer]
        case 'refine':
        case 'legacy':
            return [t.inner]
        default:
            return []
    }
}

/**
 * **One cycle of a term graph**: its members, and the entries. An entry is a member that a thunk
 * names, that a term outside the component names, that a root names, or that has more than one
 * parent. Each other member has one parent in the component, and prints in place inside that
 * parent. The key of an entry is its name in the print.
 */
export type Component = {
    readonly members: ReadonlySet<Term>
    readonly keys: ReadonlyMap<Term, string>
}

/**
 * **The cycles of a term graph**, as its strongly connected components (Tarjan), in the order that
 * Tarjan closes them: a component comes after each component that it reaches. So an earlier
 * component is an earlier scope. `roots` holds each term that a root names. A term on no cycle is
 * in no component.
 */
export const componentsOf = (roots: readonly Term[]): readonly Component[] => {
    const index = new Map<Term, number>()
    const low = new Map<Term, number>()
    const stack: Term[] = []
    const on = new Set<Term>()
    const comps: Term[][] = []
    const parents = new Map<Term, Term[]>()
    const visit = (t: Term): void => {
        index.set(t, index.size)
        low.set(t, index.get(t) ?? 0)
        stack.push(t)
        on.add(t)
        for (const c of childrenOf(t)) {
            if (leafKinds.has(c.kind)) continue
            parents.set(c, [...(parents.get(c) ?? []), t])
            if (!index.has(c)) {
                visit(c)
                low.set(t, Math.min(low.get(t) ?? 0, low.get(c) ?? 0))
            } else if (on.has(c))
                low.set(t, Math.min(low.get(t) ?? 0, index.get(c) ?? 0))
        }
        if (low.get(t) === index.get(t)) {
            const comp: Term[] = []
            for (let u = stack.pop(); u !== undefined; u = stack.pop()) {
                on.delete(u)
                comp.push(u)
                if (u === t) break
            }
            comps.push(comp)
        }
    }
    for (const r of roots) if (!leafKinds.has(r.kind) && !index.has(r)) visit(r)
    const external = new Set(roots)
    const out: Component[] = []
    for (const comp of comps) {
        const members = new Set(comp)
        const [only] = comp
        if (
            comp.length === 1 &&
            only !== undefined &&
            !childrenOf(only).includes(only)
        )
            continue
        const keys = new Map<Term, string>()
        for (const m of comp) {
            if (m.kind === 'lazy') continue
            const ps = parents.get(m) ?? []
            if (
                external.has(m) ||
                ps.length !== 1 ||
                ps.some((q) => q.kind === 'lazy' || !members.has(q))
            )
                keys.set(m, `k${keys.size}`)
        }
        out.push({ members, keys })
    }
    return out
}

/**
 * **The order of the entries of one component**: an entry names an earlier entry above every
 * guard, and any entry below a guard. A container is a guard. A wall reads its terms at any depth,
 * so an entry below a wall names no entry of its own component. The order is the reason of a
 * refusal where an unguarded cycle or a cycle through a wall has no order.
 */
export type EntryOrder =
    | { readonly kind: 'order'; readonly entries: readonly Term[] }
    | {
          readonly kind: 'refused'
          readonly cause: 'unguarded' | 'wall'
          readonly reason: string
      }

/** The order of the entries of a component, or the reason that it has none. */
export const entryOrder = (component: Component): EntryOrder => {
    const { members, keys } = component
    // a cycle of thunks alone names no term, so it reads its own input with no guard
    if (keys.size === 0)
        return {
            kind: 'refused',
            cause: 'unguarded',
            reason: 'an unguarded cycle: an entry reads its own input above every guard',
        }
    const above = new Map<Term, Term[]>()
    let reason: string | undefined
    for (const entry of keys.keys()) {
        const names: Term[] = []
        const walk = (
            t: Term,
            guarded: boolean,
            wall: boolean,
            top: boolean,
        ): void => {
            if (t.kind === 'lazy') {
                const target = force(t)
                if (target !== undefined) walk(target, guarded, wall, false)
                return
            }
            if (!members.has(t)) return
            if (!top && keys.has(t)) {
                if (wall)
                    reason ??=
                        'a cycle through a wall: a wall reads its term at any depth'
                else if (!guarded) names.push(t)
                return
            }
            const down =
                t.kind === 'list' || t.kind === 'set' || t.kind === 'object'
            const walled = t.kind === 'held' || t.kind === 'legacy'
            for (const c of childrenOf(t))
                walk(c, guarded || down, wall || walled, false)
        }
        walk(entry, false, false, true)
        above.set(entry, names)
    }
    if (reason !== undefined) return { kind: 'refused', cause: 'wall', reason }
    const entries: Term[] = []
    const state = new Map<Term, 'progress' | 'done'>()
    const place = (t: Term): boolean => {
        const now = state.get(t)
        if (now === 'done') return true
        if (now === 'progress') return false
        state.set(t, 'progress')
        for (const u of above.get(t) ?? []) if (!place(u)) return false
        state.set(t, 'done')
        entries.push(t)
        return true
    }
    for (const entry of keys.keys())
        if (!place(entry))
            return {
                kind: 'refused',
                cause: 'unguarded',
                reason: 'an unguarded cycle: an entry reads its own input above every guard',
            }
    return { kind: 'order', entries }
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
 * binders unfolded together.
 */
type Walk = {
    readonly left: Scope
    readonly right: Scope
    readonly pairs: readonly { readonly left: Term; readonly right: Term }[]
}

/**
 * One row per constructor of the left operand, as the operands spell at the pairing. The rows
 * are the model's, in the model's order.
 *
 * **The walk ends.** The spelling of each operand is a finite term, because {@link bindersOf}
 * binds the target of every thunk that closes a cycle, and the spelling stops at each variable.
 * Each call reads a strict subterm of one spelling, or of both, with the other spelling no
 * larger. The split of the right operand hands a left row an option under the refinements that
 * the split keeps, which is no larger than the right spelling, and the left row then reads a
 * strict subterm of the left spelling. So the sum of the two sizes falls at each call.
 */
const disjointWalk = (x: Term, y: Term, w: Walk): boolean => {
    const one = see(x, w.left)
    switch (one.kind) {
        // a free variable pairs with no binder, so it is disjoint from the bottom alone
        case 'free':
            return rightRows(() => false, y, w)
        // a variable admits what its binder admits, so it is disjoint from the variable of the
        // binder that its own binder was unfolded with
        case 'var':
            return rightRows(
                (other, v) =>
                    other.kind === 'var' &&
                    v.pairs.some(
                        (pair) =>
                            pair.left === one.binder &&
                            pair.right === other.binder,
                    ),
                y,
                w,
            )
        // the right operand splits at every depth. Two recursive terms: the bodies, with the two
        // binders paired. A recursive term also unfolds, and its binder pairs with nothing
        case 'mu':
            return splitRight(
                (y1, v) => {
                    const other = see(y1, v.right)
                    return (
                        (other.kind === 'mu' &&
                            disjointWalk(one.body, other.body, {
                                left: one.scope,
                                right: other.scope,
                                pairs: [
                                    ...v.pairs,
                                    { left: one.body, right: other.body },
                                ],
                            })) ||
                        disjointWalk(one.body, y1, { ...v, left: one.scope })
                    )
                },
                y,
                w,
            )
        case 'term':
            return termRow(one.t, y, w)
    }
}

/** The rows of a left operand that is a constructor. */
const termRow = (x: Term, y: Term, w: Walk): boolean => {
    switch (x.kind) {
        case 'never':
            return true
        // the admission is a function, or every value: disjoint from the bottom alone
        case 'held':
        case 'legacy':
        case 'opaq':
        case 'lazy':
            return rightRows(() => false, y, w)
        // **A refinement is disjoint where its inner term is**, or where its data predicate and a
        // data predicate of the partner hold together nowhere. The second reading needs a closed
        // held-free inner term on each side, which reads each attribute as the top reads it
        case 'refine':
            return splitRight(
                (other, v) =>
                    disjointWalk(x.inner, other, v) ||
                    (x.q.kind === 'members' &&
                        belowTop(x.inner, v.left) &&
                        predicateApart(x.q, other, v)),
                y,
                w,
            )
        case 'union':
            return x.options.every((option) => disjointWalk(option, y, w))
        case 'set':
            return rightRows(
                (other, v) =>
                    other.kind === 'term' &&
                    (other.t.kind === 'set'
                        ? closedAt(x.elem, v.left) &&
                          closedAt(other.t.elem, v.right) &&
                          disjointWalk(x.elem, other.t.elem, v)
                        : otherShape(other.t, ['prim', 'list', 'object'])),
                y,
                w,
            )
        case 'list':
            return rightRows(
                (other, v) =>
                    other.kind === 'term' &&
                    (other.t.kind === 'list'
                        ? listsApart(x, other.t, v)
                        : otherShape(other.t, ['prim', 'set', 'object'])),
                y,
                w,
            )
        case 'object':
            return rightRows(
                (other, v) =>
                    other.kind === 'term' &&
                    (other.t.kind === 'object'
                        ? bodiesApart(x.body, other.t.body, v)
                        : otherShape(other.t, ['prim', 'set', 'list'])),
                y,
                w,
            )
        default:
            return rightRows(
                (other) =>
                    other.kind === 'term' &&
                    (isPrim(other.t)
                        ? primsApart(x, other.t)
                        : otherShape(other.t, ['set', 'list', 'object'])),
                y,
                w,
            )
    }
}

/**
 * **Every row that reads the right operand alone**, the model's `disjSRight`. The bottom admits
 * nothing. A union is disjoint from the left operand where each option is. A recursive term
 * unfolds, and its binder pairs with nothing. A refinement admits a part of what its inner term
 * admits, so the inner term bounds it. `fam` answers every other spelling.
 */
const rightRows = (
    fam: (other: Exclude<Seen, { kind: 'mu' }>, w: Walk) => boolean,
    y: Term,
    w: Walk,
): boolean => {
    const other = see(y, w.right)
    if (other.kind === 'mu')
        return rightRows(fam, other.body, { ...w, right: other.scope })
    if (other.kind === 'term')
        switch (other.t.kind) {
            case 'never':
                return true
            case 'refine':
                return rightRows(fam, other.t.inner, w)
            case 'union':
                return other.t.options.every((option) =>
                    rightRows(fam, option, w),
                )
        }
    return fam(other, w)
}

/**
 * **The right operand, split at every depth**, the model's `splitR`. The rows of a left
 * refinement and a left recursive term read the right operand through this split. A union splits
 * into its options. A refinement keeps its predicate on each option below it, through the wrapper
 * `wrap`, where the predicate is data and the inner term lies below the top ({@link belowTop}).
 * Elsewhere the split drops the predicate, and the inner term bounds the refinement: a refined
 * term admits less than its inner term, and a predicate that is not data is read by no row. A recursive term is handed whole to `fam`,
 * and is also unfolded with its binder paired with nothing. So a right refinement or a right
 * recursive term hides no option from the left row.
 */
const splitRight = (
    fam: (other: Term, w: Walk) => boolean,
    y: Term,
    w: Walk,
    wrap: (t: Term) => Term = (t) => t,
): boolean => {
    const other = see(y, w.right)
    if (other.kind === 'mu')
        return (
            fam(wrap(y), w) ||
            splitRight(fam, other.body, { ...w, right: other.scope }, wrap)
        )
    if (other.kind === 'term')
        switch (other.t.kind) {
            case 'never':
                return true
            case 'union':
                return other.t.options.every((option) =>
                    splitRight(fam, option, w, wrap),
                )
            case 'refine': {
                const { inner, q } = other.t
                return q.kind === 'members' && belowTop(inner, w.right)
                    ? splitRight(fam, inner, w, (t) =>
                          wrap({ kind: 'refine', inner: t, q }),
                      )
                    : splitRight(fam, inner, w, wrap)
            }
        }
    return fam(wrap(y), w)
}

/**
 * **A data predicate that no value of the right refinement chain satisfies with `q`**, the
 * model's `predApart`. A refinement of the chain counts only over a closed held-free inner term.
 */
const predicateApart = (q: Predicate, y: Term, w: Walk): boolean => {
    const other = see(y, w.right)
    if (other.kind !== 'term' || other.t.kind !== 'refine') return false
    return (
        (belowTop(other.t.inner, w.right) && predicatesApart(q, other.t.q)) ||
        predicateApart(q, other.t.inner, w)
    )
}

/**
 * **Two predicates that hold together nowhere**, the model's `Pred.apart`.
 * Two `members` sets at two bases share no value, and at one base they share a value where they
 * share an alternative. A `closure` is not data.
 */
const predicatesApart = (q: Predicate, p: Predicate): boolean =>
    q.kind === 'members' &&
    p.kind === 'members' &&
    (q.literal.base !== p.literal.base ||
        !q.literal.ls.some((one: LiteralValue) =>
            p.literal.ls.some((other: LiteralValue) => sameLiteral(one, other)),
        ))

/** The primitives: the ground bases and the literals. */
const isPrim = (t: Term): boolean =>
    t.kind === 'string' ||
    t.kind === 'number' ||
    t.kind === 'boolean' ||
    t.kind === 'binary' ||
    t.kind === 'null' ||
    t.kind === 'literal'

/**
 * **A constructor of another shape class**, which shares no value with the left former: the
 * classes of two formers are disjoint, because the carrier is a coproduct (`Shapes`).
 */
const otherShape = (
    t: Term,
    classes: readonly ('prim' | 'set' | 'list' | 'object')[],
): boolean =>
    (isPrim(t) && classes.includes('prim')) ||
    ((t.kind === 'set' || t.kind === 'list' || t.kind === 'object') &&
        classes.includes(t.kind))

/**
 * **Two primitives apart**, the model's `Ground.apart`: two bases of different kinds,
 * a literal beside another base, and two literals of different values.
 */
const primsApart = (x: Term, y: Term): boolean => {
    const base = (t: Term) => (t.kind === 'literal' ? t.base : t.kind)
    if (base(x) !== base(y)) return true
    return (
        x.kind === 'literal' && y.kind === 'literal' && !sameLiteral(x.v, y.v)
    )
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

/**
 * **One side dominates the other**, in the prefix and in the suffix at once: the model's
 * `dominates`. Where both shapes spread and one dominates, every common length re-spreads the row
 * at `max p1 p2 + max s1 s2` (`dominates_max`).
 */
const dominates = (p1: number, s1: number, p2: number, s2: number): boolean =>
    (p2 <= p1 && s2 <= s1) || (p1 <= p2 && s1 <= s2)

/** Some position of two aligned rows is disjoint, the left row's term on the left. */
const rowsApart = (a: readonly Term[], b: readonly Term[], w: Walk): boolean =>
    a.some((one, at) => disjointWalk(one, b[at] as Term, w))

/**
 * **Two list shapes apart**, the model's `listDisjRow`. Two values of different lengths differ,
 * so the shapes are disjoint where one position of each common length is. **Either side without
 * a spread** fixes the one length, and a length the other side refuses is disjoint outright.
 * **Both spreading**: where one side dominates, one disjoint position of the row at
 * `max p1 p2 + max s1 s2` decides. Where no side dominates, the test answers `false`.
 */
const listsApart = (
    x: Extract<Term, { kind: 'list' }>,
    y: Extract<Term, { kind: 'list' }>,
    w: Walk,
): boolean => {
    if (x.spread !== undefined && y.spread !== undefined) {
        if (!dominates(x.pre.length, x.suf.length, y.pre.length, y.suf.length))
            return false
        const n =
            Math.max(x.pre.length, y.pre.length) +
            Math.max(x.suf.length, y.suf.length)
        const rows = rowOf(x, n)
        const other = rowOf(y, n)
        return (
            rows !== undefined &&
            other !== undefined &&
            rowsApart(rows, other, w)
        )
    }
    const fixed = x.spread === undefined ? x : y
    const n = fixed.pre.length + fixed.suf.length
    const rows = rowOf(x, n)
    const other = rowOf(y, n)
    return (
        rows === undefined || other === undefined || rowsApart(rows, other, w)
    )
}

/**
 * **Two fields at one name apart**, the model's `ObjectSlot.disjoint`: one field requires the
 * name, and the terms are disjoint. Two fields that both admit a map without the name share it.
 * A `withLegacyRead` field reads a map without the name, so only `req` requires the name.
 * An `undefinable` field is the model's `optional`: the row stores `undefined` as an absent name.
 */
const fieldsApart = (a: Field, b: Field, w: Walk): boolean =>
    (a.mark === 'req' || b.mark === 'req') && disjointWalk(a.t, b.t, w)

/**
 * **Two bodies apart at one name**, the model's `famObjD`. A body is a total function from the
 * key space to a field: a declared name holds its field, and an undeclared name holds `optional`
 * of the open block, which is `never` where the body is closed. So two bodies share no map where
 * one name of either body holds two fields apart.
 */
const bodiesApart = (a: Body, b: Body, w: Walk): boolean =>
    Object.entries(a.fields).some(([name, field]) =>
        fieldsApart(
            field,
            b.fields[name] ?? { mark: 'optional', t: b.rest ?? never },
            w,
        ),
    ) ||
    Object.entries(b.fields).some(
        ([name, field]) =>
            !(name in a.fields) &&
            field.mark === 'req' &&
            (a.rest === undefined || disjointWalk(a.rest, field.t, w)),
    )

const never: Term = { kind: 'never' }
