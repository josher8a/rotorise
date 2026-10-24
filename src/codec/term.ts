/**
 * The term language, and the five functions of a term that the model computes.
 *
 * Derived from `formal/Calculus/Dynamo/Lang/Term.lean`, with `member` from `ScopePath.lean`'s `μG`, `specOf`
 * from `ScopeSlice.lean`'s `Closed.spec`. {@link occV}, {@link occA} and {@link tagsOf} have no counterpart there: the
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
 * The one place this language is **wider** than the model is `ref`, and the row says why.
 */

import type { AttributeName, AttributeValue, DynamoNumber } from './attribute'
import type {
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
 * This is what {@link Literal} was before a literal carried one value, and it survives for the
 * place the model keeps a set of alternatives too: the answer {@link literalsOf} gives for a
 * declared name. The model's split is the same one, `inL` against `inLs`.
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
     * The rule `(refine)`. The model carries `q : Value → Bool`; this carries the caller's closure,
     * with `what` as the refusal text and `arbitrary` as what an arbitrary derived from the term
     * reads. A refinement accepts a part of what its inner term accepts, so a declaration reads
     * through it and reads no predicate. A finite set at a ground kind is a union of literals.
     */
    | { readonly kind: 'refine'; readonly inner: Term; readonly q: Refinement }
    /** The rule `(withLegacyRead)`: `r : Attr ⇀ Value`, the older reading, which widens `p` and never `e`. */
    | {
          readonly kind: 'legacy'
          readonly inner: Term
          readonly r: (attribute: AttributeValue) => unknown
      }
    /**
     * A `ref`: the name of an entry of the scope that binds the name, which is how this language
     * spells a recursive schema. The node carries its slot, and the target is one lookup in the
     * slot ({@link targetOf}). The model states a recursive schema as a scope graph: a scope, its
     * entries, and `ref i` at the node that names entry `i`. The model's guard accepts a cycle
     * when a list or an object sits on the cycle. The node is wider than `ref i` in one way: a
     * name that no scope binds yet has no target, and the model has no free variable.
     *
     * **Everything else here reads through the node.** {@link occV}, {@link occA} and
     * {@link ownsNullOf} answer what the target answers, and the emitter prints an entry of a
     * cycle as a `ref`. Only {@link member} answers `undefined`. An unknown occupancy is the
     * unsound direction: the declaration guard refuses a union when two occupancies *meet*, so a
     * union of a `ref` to `string` and `string` would pass, and a write would then find two
     * options admitting one value.
     */
    | { readonly kind: 'ref'; readonly slot: RefSlot }
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
 * `μG`: the member a term stores, read off the term.
 *
 * `undefined` is the model's `⊤`: *not determined by the term*. A `ref` answers it for a reason of
 * the host: the host does not read through a `ref` here, because a walk through a cycle of `ref`s
 * alone can loop, which is a limit of the host's carrier. A caller that needs one member, as a
 * DynamoDB set does, refuses the `ref`: a set holding one element member is a fact of the store
 * universe. `opaque` writes whatever the value turns out to be, `never` writes nothing, and a
 * `union` answers it where its options do not agree on one member. `nullable` is such a union.
 *
 * **This reader runs at construction.** A scope binds its names after the fragments that name them are built, so this reader runs while a `ref` has no target. The reader reads the term, because the flat scope of the root does not exist yet.
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
        case 'ref':
        case 'opaq':
        // nothing is written, so there is no member stored
        case 'never':
            return undefined
        case 'union':
            return unanimous(t.options.map(member))
    }
}

/**
 * **The member that a set element stores**, read at the node that each `ref` names. The type gates
 * `.set()` on the attribute of the element, and the attribute of a scope entry is the attribute of
 * the definition that the entry names, so the run time reads the same node. A stored set holds no
 * recursion, so a node that the read already passed answers nothing.
 */
export const elementMember = (
    t: Term,
    passed: ReadonlySet<Term> = new Set(),
): AttributeName | undefined => {
    const at = resolvedTerm(t)
    if (at === undefined || passed.has(at)) return undefined
    const inside = new Set([...passed, at])
    switch (at.kind) {
        case 'held':
        case 'refine':
        case 'legacy':
            return elementMember(at.inner, inside)
        case 'union':
            return unanimous(
                at.options.map((one) => elementMember(one, inside)),
            )
        default:
            return member(at)
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
 * A `ref` reads through to its target, as the model reads the entry that `ref i` names. A `ref`
 * that no scope binds yet is a free variable, and a free variable may write every slot.
 *
 * **This reader runs at construction.** A scope binds its names after the fragments that name them are built, so this reader runs while a `ref` has no target. The reader reads the term, because the flat scope of the root does not exist yet.
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
        // a `ref` answers what its target answers. The model reads through on both projections,
        // and only the member is lost
        case 'ref': {
            const target = targetOf(t)
            return target === undefined ? everySlot : occV(target)
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
 * says. A `held` answers from the slots it declares, and a `ref` reads through to its target. A
 * `ref` that no scope binds yet is a free variable, and the term does not determine whether a
 * free variable reaches the point.
 *
 * `refine` answers `false` through its subterm and `undefined` otherwise: a predicate narrows, so
 * a subterm that does not reach the point keeps not reaching it, while one that does may or may not
 * survive the predicate, and this reads no predicate.
 *
 * A union's options are separated by construction, so at most one admits null and the union reaches
 * the point exactly when one of its options does.
 *
 * **This reader runs at construction.** A scope binds its names after the fragments that name them are built, so this reader runs while a `ref` has no target. The reader reads the term, because the flat scope of the root does not exist yet.
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
        case 'ref': {
            const target = targetOf(t)
            return target === undefined ? undefined : ownsNullOf(target)
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
 * A lawful `r` does respect the member, and the model records that this is the one place `μG` is
 * sharper than `occA` — sharper only under an obligation no declaration-time certificate takes as a
 * premise.
 *
 * `ref` diverges from the model for the reason {@link occV} gives.
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
        case 'ref': {
            const target = targetOf(t)
            return target === undefined ? undefined : occA(target)
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
 * `Closed.spec`, which reads `pinOfG` at every slot, `req`, `optional` and `withLegacyRead` alike.
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
 * **The node that a term names**: the term itself, or the end of its chain of `ref`s.
 *
 * The emitter prints a `ref` that closes no cycle as its target, so the model reads the node behind
 * a `ref` as the node. Each former that inspects an argument, and each reader of a literal or a tag,
 * reads the node here. A `ref` that no scope binds is its own node, so a caller reads a node of
 * kind `ref` as a free name. A chain that returns to a `ref` it already passed
 * names no node.
 */
export const resolvedTerm = (t: Term): Term | undefined => {
    const passed = new Set<Term>()
    let at: Term = t
    while (at.kind === 'ref') {
        if (passed.has(at)) return undefined
        passed.add(at)
        const target = targetOf(at)
        if (target === undefined) return at
        at = target
    }
    return at
}

/**
 * **Whether a term holds no value**: the model's empty held set, at each form whose emptiness the
 * term decides. The model gives `never` the held set `HNever`, and a union the union of the held
 * sets of its options. So `never`, and a union whose every option holds no value (`union([])` among
 * them), hold no value.
 *
 * Four forms stay out. A `refine` holds no value where its predicate admits nothing, and no
 * function decides that of a closure. A `withLegacyRead` has no held set in the model, and its older
 * reader reads values that the inner term does not hold. A list, an object or a set over a term
 * that holds no value holds none either, but the judgment refuses each of them where it is built.
 * A `held` over a term that holds no value holds none in the model either, and the host admits it
 * in a declared position: the vectors of a legacy read beside itself use that `held` as a position
 * that admits no value, so that only the write half refuses the pair.
 *
 * A `ref` that no scope binds holds a value for this reader, and the scope reads the closed copy.
 * A node that the read already passed is a cycle with no container, which the guard refuses, so the
 * read answers `false` there.
 *
 * **This reader runs at construction, and in the judgment of a codec that no scope has closed.**
 * A scope binds its names after the fragments that name them are built, so this reader runs while a `ref` has no target. The reader reads the term, because the flat scope of the root does not exist yet. The set `passed` stays, because the guard has not run on a scope that binds its names late.
 */
export const holdsNoValue = (
    t: Term,
    passed: ReadonlySet<Term> = new Set(),
): boolean => {
    const at = resolvedTerm(t)
    if (at === undefined || passed.has(at)) return false
    const inside = new Set([...passed, at])
    switch (at.kind) {
        case 'never':
            return true
        case 'ref':
            return false
        case 'union':
            return at.options.every((one) => holdsNoValue(one, inside))
        default:
            return false
    }
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
export const unionAlternatives = (
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
 * **Whether a term reaches a subterm of one of these kinds**, at any depth, or reaches a `ref`
 * that the walk cannot read.
 *
 * The walk reads through each `ref` once. A `ref` that the walk meets again is recursive, and a
 * `ref` with no target names a codec that is not yet declared. Each answers "reaches".
 */
const reaches = (
    t: Term,
    kinds: readonly Term['kind'][],
    seen: Set<Term> = new Set(),
): boolean => {
    if (kinds.includes(t.kind)) return true
    const on = (one: Term) => reaches(one, kinds, seen)
    switch (t.kind) {
        case 'ref': {
            if (seen.has(t)) return true
            seen.add(t)
            const target = targetOf(t)
            return target === undefined || on(target)
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
 * **The target of a `ref`**: one lookup in the definitions of the scope that binds the name, or
 * nothing while no scope binds the name. The caller refuses, declines, or reads the `ref` as a
 * free variable.
 */
export const targetOf = (
    t: Term & { readonly kind: 'ref' },
): Term | undefined => t.slot.bound?.[t.slot.name]

/**
 * The target of a `ref` that a use reads, where only a closed codec has a meaning. A name that no
 * scope binds throws a `ReferenceError`, and each reader that needs a term propagates the throw.
 */
export const usedTargetOf = (t: Term & { readonly kind: 'ref' }): Term => {
    const target = targetOf(t)
    if (target === undefined)
        throw new ReferenceError(
            `ref('${t.slot.name}') is bound by no scope yet`,
        )
    return target
}

/**
 * The slot of a `ref`: the name, and the record of the scope that binds the name. `ref` builds a
 * slot with no record. A scope binds a closed copy of each `ref`, and changes no slot of a caller.
 */
export type RefSlot = {
    readonly name: string
    bound?: Readonly<Record<string, Term>>
}

/**
 * The slots of the `ref`s that the terms reach and that no scope binds yet. A bound `ref` belongs
 * to the closed scope that bound it, so the walk stops there.
 *
 * **This reader defines open.** A term is open where this reader finds a slot, and a flat scope
 * assumes a closed term, so this reader cannot read one.
 */
export const unboundRefs = (roots: readonly Term[]): ReadonlySet<RefSlot> => {
    const slots = new Set<RefSlot>()
    const seen = new Set<Term>()
    const walk = (t: Term): void => {
        if (seen.has(t)) return
        seen.add(t)
        switch (t.kind) {
            case 'ref': {
                const { slot } = t
                if (slot.bound === undefined) slots.add(slot)
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

/** Each term that {@link freeNamesOf} found closed. No slot changes, so a closed term stays closed. */
const closedTerms = new WeakSet<Term>()

/**
 * **The free names of a term**: the names of the `ref`s that the term reaches and that no scope
 * binds. The run-time side of the free names that the type of a codec carries.
 */
export const freeNamesOf = (t: Term): readonly string[] => {
    if (closedTerms.has(t)) return []
    const names = [...new Set([...unboundRefs([t])].map((slot) => slot.name))]
    if (names.length === 0) closedTerms.add(t)
    return names
}

/**
 * **A read of a closed term, kept for each root.** A closed term stays closed, so the read of a
 * closed root does not change. A read of an open term is not kept.
 */
export const memoClosed = <V>(read: (root: Term) => V): ((root: Term) => V) => {
    const known = new WeakMap<Term, { readonly value: V }>()
    return (root) => {
        if (freeNamesOf(root).length > 0) return read(root)
        const hit = known.get(root)
        if (hit !== undefined) return hit.value
        const value = read(root)
        known.set(root, { value })
        return value
    }
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
 * - `2`: a cycle has no container on its path, so the recursion reads the input of its own entry;
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
 * level of {@link recursionUse}, so a walk that reads through the `ref` reads the cause.
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
 * **The closed copy of the terms of a scope.** The copy shares each closed subterm, and copies each
 * node on a path to a free `ref`. Each `ref` copy is bound in `record`, so a cycle stays a `ref`.
 * The map holds each copy, keyed by the node that the copy replaces.
 *
 * **Lexical scope.** `record` is the recursive binding of the scope (`letrec`): the record holds
 * the copy of each entry, and each `ref` of a copy binds in that record. No slot of an input term
 * changes, so a fragment stays open, and a cycle is a `ref` into the record.
 */
export const closedCopy = (
    record: Readonly<Record<string, Term>>,
): readonly [(t: Term) => Term, ReadonlyMap<Term, Term>] => {
    const copies = new Map<Term, Term>()
    const close = (t: Term): Term => {
        const known = copies.get(t)
        if (known !== undefined) return known
        if (unboundRefs([t]).size === 0) return t
        const made: Term =
            t.kind === 'ref'
                ? { kind: 'ref', slot: { name: t.slot.name, bound: record } }
                : t.kind === 'held'
                  ? { ...t, inner: close(t.inner), outer: close(t.outer) }
                  : t.kind === 'refine' || t.kind === 'legacy'
                    ? { ...t, inner: close(t.inner) }
                    : mapChildren(t, close)
        copies.set(t, made)
        return made
    }
    return [close, copies]
}

/**
 * **A view that reads through a `ref`**, as the model's views read through `ref`: the view of a
 * `ref` is a `ref` whose slot binds the name to the view of the target. Each term object has one
 * view object, so a cycle of the term is a cycle of the view, closed at the view of the same term.
 * The emitter then prints the view as a scope whose entries are the views of the entries, and a
 * `ref` of the view at the `ref`.
 *
 * The build ends: the view of a `ref` is in the table before the build reads the target, so a
 * cycle meets the view that it started. The view of a `ref` with no target has no target.
 */
export const throughRefs =
    (row: (t: Term, view: (t: Term) => Term) => Term) =>
    (root: Term): Term => {
        const views = new Map<Term, Term>()
        const view = (t: Term): Term => {
            const known = views.get(t)
            if (known !== undefined) return known
            if (t.kind !== 'ref') {
                const made = row(t, view)
                views.set(t, made)
                return made
            }
            const slot: RefSlot = { name: t.slot.name }
            const made: Term = { kind: 'ref', slot }
            views.set(t, made)
            const target = targetOf(t)
            if (target !== undefined) slot.bound = { [slot.name]: view(target) }
            return made
        }
        return view(root)
    }

/**
 * **Whether a `withLegacyRead` occurs in the term.** The model states the read widening as
 * `Term.legacy`, and the rule `TOp.rule` of the judgement answers `none` at it, because the pair is not a partial
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
 * **Whether two terms are one term**: one structure, with each `ref` read as its target, and each
 * function that a term holds the same function object. A literal compares by its base, and a
 * stand-in by `Object.is`.
 *
 * Two codecs built by two calls of one constructor are two objects and one term, and the model
 * reads only the term. A `ref` that closes a cycle makes the walk meet a pair again, and the walk
 * assumes that pair equal: each test is a conjunction, so a pair that differs makes the answer
 * `false` wherever the walk meets it. A `ref` with no target is equal to itself only.
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
            // a `ref` with no target is equal to itself only, which the identity test above answers
            case 'ref':
                return false
            default:
                return l.kind === r.kind
        }
    }
    return same(x, y)
}

/** Two predicates: the same closure, field by field. */
const samePredicate = (p: Refinement, q: Refinement): boolean =>
    p.is === q.is &&
    p.what === q.what &&
    p.arbitrary === q.arbitrary &&
    p.onThinSearch === q.onThinSearch

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
 * The terms that a term reads one step down, through a `ref` that has a target.
 *
 * A `ref` with no target holds no cycle. A scope binds each `ref` of its closed copy, so the guard
 * of the scope reads each cycle of the copy.
 */
export const childrenOf = (t: Term): readonly Term[] => {
    switch (t.kind) {
        case 'ref': {
            const target = targetOf(t)
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
 * **One cycle of a term graph**: its members, and the entries. An entry is a member that a `ref`
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
 *
 * **This reader builds the flat scope** ({@link flatOf} runs it), and the guard of `scope` runs it
 * before the flat scope of the entries exists. So this reader reads the term.
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
            if (m.kind === 'ref') continue
            const ps = parents.get(m) ?? []
            if (
                external.has(m) ||
                ps.length !== 1 ||
                ps.some((q) => q.kind === 'ref' || !members.has(q))
            )
                keys.set(m, `k${keys.size}`)
        }
        out.push({ members, keys })
    }
    return out
}

/**
 * **The entry on a cycle that the terms reach**, read through each `ref` that has a target, or
 * nothing where the terms reach no cycle. A cycle of the term graph passes through a `ref`, and
 * the name of that `ref` names the entry.
 */
export const cycleEntryOf = (roots: readonly Term[]): string | undefined =>
    componentsOf(roots)
        .flatMap(({ members }) => [...members])
        .find((m): m is Term & { readonly kind: 'ref' } => m.kind === 'ref')
        ?.slot.name

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

/**
 * The order of the entries of a component, or the reason that it has none.
 *
 * **This reader builds the flat scope**: the order is the order of the entries of the flat scope,
 * and the guard of `scope` runs this reader before that scope exists. So this reader reads the term.
 */
export const entryOrder = (component: Component): EntryOrder => {
    const { members, keys } = component
    // a cycle of `ref`s alone names no term, so it reads its own input with no guard
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
            if (t.kind === 'ref') {
                const target = targetOf(t)
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

/** The primitives: the ground bases and the literals. */
export const isPrim = (t: Term): boolean =>
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
export const otherShape = (
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
export const primsApart = (x: Term, y: Term): boolean => {
    const base = (t: Term) => (t.kind === 'literal' ? t.base : t.kind)
    if (base(x) !== base(y)) return true
    return (
        x.kind === 'literal' && y.kind === 'literal' && !sameLiteral(x.v, y.v)
    )
}
