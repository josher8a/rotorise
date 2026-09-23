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

import type { AttributeName, AttributeValue, DynamoNumber } from './attribute'
import type {
    LiteralBase,
    LiteralValue,
    Refinement,
    Rng,
    SetBase,
    SetSlot,
} from './codec'
import { namedLiteral, sameLiteral } from './value'

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
    | { readonly kind: 'members'; readonly literal: Alternatives }
    | { readonly kind: 'each'; readonly of: Predicate }
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
    /** §3 `(held)`: the iso, both halves, as the caller supplied them. */
    | {
          readonly kind: 'held'
          readonly inner: Term
          readonly f: (value: never) => unknown
          readonly g: (held: never) => unknown
          /**
           * **The value slots the conversion lands in, where the adapter knows them.**
           *
           * `occV` answers the top for an adapter, because `f` is a function this library did not
           * write and cannot read. That is honest for a caller's adapter and wrong for one this
           * library ships: `number` and `decimal` are adapters over the one numeric base now, and
           * an unknown write side costs a union its certificate and `nullable` its null point at
           * every numeric field.
           *
           * So the adapter declares it rather than the reader deriving it — the same split the
           * codebase already uses, where one side owns the fact and the other states an
           * expectancy. Absent is the honest answer for an adapter nobody has declared.
           */
          readonly writes?: readonly SetSlot[]
          /**
           * **Which adapter this is, where the library ships it**, so a vector can cite the pair
           * by name. The emitter prints `held` only for a pair it recognises, the way it already
           * prints `isNumeral` and `isStoredNumeral` for the predicates: a caller's closure has
           * no name in the model and is refused.
           *
           * Separate from {@link writes} on purpose. That says which slots the conversion lands
           * in and is read by the certificate; this says which named pair the model carries and
           * is read by the emitter. One of them can be known without the other.
           */
          readonly via?: 'decimalText' | OpaqueSugar
          /**
           * **The same conversion at one element, where the adapter maps over a set.**
           *
           * `.set()` maps an element's conversion over the wire set, so the set-level `f` and `g`
           * are built *from* an element pair and then hold only the set form. A reader that needs
           * the element view cannot recover it: `restrictedSet` descends to the stored base and
           * the element pair is gone, so a generator handed a set of `decimal` built the native
           * element codec and offered it a caller's string.
           *
           * So the builder records what it already had. This is the same split as {@link writes}:
           * one side owns the fact rather than a reader deriving what was never written down.
           * Absent for every adapter that is not a set, and for a caller's, which is the honest
           * answer there.
           */
          readonly element?: {
              readonly f: (value: never) => unknown
              readonly g: (held: never) => unknown
          }
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
     * §3 `(lazy)`, and **the one row where this language is wider than the model's.**
     *
     * `Term.lazy` carries a plain `Term`, and `Term.lean` says why in as many words: a closure adds
     * no constructible term, every `Term` being finite either way, and the model states no recursive
     * term. `union`'s admission is anti-monotone, so a recursive union has no fixpoint semantics under
     * unique admission in general. `lawful_opaqCodecω` is the exception: `opaque` is a lawful
     * recursive union, because its options are pairwise kind-disjoint.
     *
     * This library supports a recursive entity through a thunk, and `codec.recursive.spec.ts`
     * declares one, so the thunk stays. **Everything else here reads through it.**
     * {@link occV}, {@link occA} and {@link ownsNullOf} answer what the term underneath answers,
     * `meetTerms` reads through on either side, and the emitter forces the chain to a depth and
     * gives up only on a genuinely recursive one. `Meet.lean` heads the matching section
     * "`lazy` is transparent, and it constrains nothing". Only {@link member} is lost, because
     * the model's `μSyn (.lazy t)` is `none`.
     *
     * **The two projections answered `undefined` until it was measured, on the ground that
     * forcing would throw on the entity the thunk exists to allow. Both halves were wrong.**
     * Forcing does not throw: `object()` already forces at the declaration and the recursive
     * entity still round-trips. And `undefined` was the unsound direction rather than the safe
     * one, because the declaration guard refuses a union when two occupancies *meet*, so an
     * unknown occupancy makes it decline to refuse. `union([lazy(string), string])` was accepted
     * and `checkUniqueAdmission` then found two options admitting one value. `lazy` was the only
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

/** …and which member a set of that base stores. Three bases onto three wire members. */
const setMember: { readonly [B in SetBase]: AttributeName } = {
    string: 'SS',
    number: 'NS',
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
 * …and a set base's. Four bases onto three slots, colliding at `string`/`decimal`, where
 * {@link setMember} collides at `number`/`decimal` instead. The two collisions are disjoint, which
 * is why the pair of families separates all four bases and neither family does alone.
 */
const setSlot: { readonly [B in SetBase]: SetSlot } = {
    string: 'strSet',
    number: 'numSet',
    binary: 'binSet',
}

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
 * `occV`: which value constructors a term may write, or `undefined` for every one of them.
 *
 * An over-approximation on purpose. If `X ⊆ X′`, `Y ⊆ Y′` and `X′ ∩ Y′ = ∅` then `X ∩ Y = ∅`, so a
 * coarse answer costs a certificate and never buys a wrong one.
 *
 * The `undefined` rows, and why each: `held`'s `f` runs *before* the subterm and can move a value
 * into any constructor; `custom` is arbitrary in both directions. `opaque` accepts every kind by
 * design, and its row answers that closed form, not `undefined`.
 *
 * **`lazy` diverges from the model, deliberately.** `occV (.lazy t)` is the subterm's there, because
 * the model's thunk carries a finite `Term`. Here it carries a closure over a binding that may not
 * exist when a declaration asks, so reading through would force it. `undefined` is the sound
 * direction: an over-approximation costs a certificate and never buys a wrong one, and the
 * alternative throws on the recursive entity the thunk exists to allow.
 */
export const occV = (t: Term): readonly SetSlot[] | undefined => {
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
        case 'set':
            return [setSlot[t.base]]
        case 'list':
            return ['array']
        case 'object':
            return ['map']
        // an adapter answers with what it declared, and the top where it declared nothing
        case 'held':
            return t.writes
        // a thunk carries a term, so it answers what that term answers. `Meet.lean` heads the
        // section `lazy` is transparent, and it constrains nothing: the model reads through on
        // both projections and only the member is lost
        case 'lazy':
            return occV(t.get())
        case 'refine':
        case 'legacy':
            return occV(t.inner)
        case 'union':
            return joined(t.options.map(occV))
        // **A closed form, not `⊤`.** §5 separates the two things a `⊤` covers: *unknown*, which is
        // `held`, `custom` and a host `lazy`, and *everything*, which is `opaque` by design. The
        // model takes the second as data — `occV .opaq` is `occTop` — so answering
        // `undefined` here would say "cannot be read" about the one term whose occupancy is fully
        // known, and {@link separable} would then decline to compare it.
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
 * construction rather than guess. The rows that answer it are the four whose admission is a
 * function: `held`, `custom` and `withLegacyRead` carry the caller's, and `lazy` could be asked but
 * answering forces the thunk — which at module-evaluation time is a reference to a binding that
 * does not exist yet, so a recursive declaration would throw on the guard that exists to allow it.
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
        // **An adapter that declared its write slots answers**, and one that did not cannot.
        // The null point is a question about which slots the conversion lands in, which is
        // exactly what the declaration states, so `nullable(decimal)` is answerable where
        // `nullable` over a caller's adapter still is not.
        case 'held':
            return t.writes === undefined
                ? undefined
                : !t.writes.includes('null')
                  ? false
                  : undefined
        case 'union': {
            const answers = t.options.map(ownsNullOf)
            return answers.some((one) => one === undefined)
                ? undefined
                : answers.some((one) => one === true)
        }
        case 'held':
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
        case 'set':
            return [setMember[t.base]]
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
 * {@link Held.writes} is what parts them, because it is the slot the caller's value lands in:
 * `decimal` takes text and `number` takes a float over one carrier. So the form is the base
 * everywhere but `number`, and there it is the adapter's declared slot.
 */
export type LiteralForm = LiteralBase | 'decimal' | 'dynamoNumber'

/** @see {@link LiteralForm} */
export const literalForm = (
    base: LiteralBase,
    writes: readonly SetSlot[] | undefined,
): LiteralForm =>
    base !== 'number'
        ? base
        : writes === undefined
          ? 'dynamoNumber'
          : writes.includes('string')
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
 * level, because {@link structuralMeet} compares what a caller hands in: an adapter pins nothing
 * there, so a field under one is absent and the option is compared on its other names. This reader
 * descends, because `extract` compares a clause literal against a member literal and both sit
 * under the same kind of adapter, so the pair below is the pair that decides. Merging them makes
 * every object union at a numeric name refuse every value, and the failure is a runtime refusal
 * rather than a type error.
 *
 * A caller's adapter declares no `writes`, so it pins nothing here either and a clause cannot
 * name it. That is the same honest answer {@link identifies} gives.
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
    writes?: readonly SetSlot[],
): { readonly alts: Alternatives; readonly form: LiteralForm } | undefined => {
    if (t.kind === 'held')
        return t.writes === undefined
            ? undefined
            : clauseForm(t.inner, t.writes)
    const alts = literalAlternatives(t)
    return alts && { alts, form: literalForm(alts.base, writes) }
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
 * value inside it that the refinement rejects is the option's own error to report. `setBaseOf`
 * reads through `refine` for the same reason.
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
        /**
         * **Every part, the spread included**, which is what the two rows this replaced disagreed
         * about: `array` read its element and `tuple` read its declared positions and left the
         * tail alone. A value longer than the declared positions is decided *by the spread*, so a
         * tail whose admission is a caller's function decides nothing a declaration can see — the
         * reason stated above for leaving `held` out. One row cannot hold both readings, and this
         * is the reading the reason gives.
         */
        case 'list':
            return (
                t.pre.every(identifies) &&
                (t.spread === undefined || identifies(t.spread)) &&
                t.suf.every(identifies)
            )
        // every declared name and the open block, for the reason `list` reads every position: a
        // name the open block holds is decided by the open block's term
        case 'object':
            return (
                Object.values(t.body.fields).every((field) =>
                    identifies(field.t),
                ) &&
                (t.body.rest === undefined || identifies(t.body.rest))
            )
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
 * **`opaque` unfolded one time**: the universal sum over each base and each container, with the
 * recursion under `lazy`. The term is total, so the number leaf and the number set are always
 * options. `Calculus.Adm_opaqUnfold` and `Calculus.AdmA_opaqUnfold` prove that the union admits exactly what
 * `opaque` admits, on both sides.
 */
export const unfoldOpaque = (op: Extract<Term, { kind: 'opaq' }>): Term => {
    const self: Term = { kind: 'lazy', get: () => op }
    return {
        kind: 'union',
        options: [
            { kind: 'string' },
            { kind: 'boolean' },
            { kind: 'binary' },
            { kind: 'null' },
            { kind: 'number' },
            { kind: 'list', pre: [], spread: self, suf: [] },
            { kind: 'object', body: { fields: {}, rest: self } },
            { kind: 'set', base: 'string' },
            { kind: 'set', base: 'number' },
            { kind: 'set', base: 'binary' },
        ],
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
 * **A term inside one option of a sum is inside the sum.** `opaque` is the universal sum, so
 * `union([string('a'), opaque])` refuses through the `string` option of {@link unfoldOpaque}. The
 * model's `Orth` declines each such pair already. The pair declared here because `identifies`
 * accepts it, and containment runs first.
 *
 * Two restrictions of one base are a different shape and still declare:
 * `union([string('A'), string('B')])` is two options neither of which contains the other, and
 * `Orth` certifies it since `OrthL`. So this row asks containment, never disjointness.
 *
 * **A union of literals at one base is a restriction of that base**, and reading only the
 * `literal` constructor here would miss it: `string('A', 'B')` builds that union, so the pair
 * `union([string, string('A', 'B')])` would declare and then fail at the first value both admit.
 * Measured — it cost three corpus pairs before this row read the union.
 *
 * The type level says the same thing already — `Overlaps` fires on a subtype either way round —
 * so a typed caller never reaches this. What reaches it is a cast, a JavaScript caller, or an
 * erased path. This is the runtime agreeing with the type rather than a new refusal.
 */
export const restricts = (x: Term, y: Term): boolean => {
    // the empty set is contained in every set, which is `opaque`'s rule at the opposite width
    if (x.kind === 'never') return true
    // a term inside one option of a sum is inside the sum, and `opaque` is the universal sum
    if (y.kind === 'union')
        return y.options.some((option) => restricts(x, option))
    if (y.kind === 'opaq') return restricts(x, unfoldOpaque(y))
    // **A numeric policy of `opaque` holds every value that holds no number, unchanged.** Its `f` is
    // the identity there, so the options of the unfolding that write no number are inside it. A
    // number option is not: the policy holds a JS number or none, and never a `DynamoNumber`
    if (y.kind === 'held' && isOpaqueSugar(y.via) && y.inner.kind === 'opaq') {
        const unfolded = unfoldOpaque(y.inner)
        return (
            unfolded.kind === 'union' &&
            unfolded.options
                .filter(
                    (option) =>
                        !(occV(option) ?? everySlot).some(
                            (slot) => slot === 'number' || slot === 'numSet',
                        ),
                )
                .some((option) => restricts(x, option))
        )
    }
    // a literal, or a union of literals at one base, is a refinement of that base: every value
    // it admits, the base admits
    const alts = literalAlternatives(x)
    if (alts && y.kind === alts.base) return true
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
 * Whether two bodies' name intervals meet: neither requires a name the other refuses.
 *
 * A body admits every name set between its required names and the names it holds, so the two
 * intervals intersect exactly on that condition. A body holds its declared names, and an open
 * block holds every other name: `presenceAt` answers `(true, true)` for an undeclared name under a
 * block. `Calculus.OrthM` read positively, and the same rule `Collides` states in the type.
 */
const namesMeet = (x: Body, y: Body): boolean => {
    const holds = (b: Body, name: string) =>
        name in b.fields || b.rest !== undefined
    for (const [name, field] of Object.entries(x.fields)) {
        if (alwaysWritten(field) && !holds(y, name)) return false
    }
    for (const [name, field] of Object.entries(y.fields)) {
        if (alwaysWritten(field) && !holds(x, name)) return false
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
const altsApart = (x: Alternatives, y: Alternatives): boolean =>
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
 * **Whether two pinned options hold disjoint carrier values** — the equivalence class the two sides
 * collapse onto, as a check.
 *
 * `identifies` is unary, and a unary predicate cannot state this: "each option knows its own
 * values" does not say the two sets of values are *different*. For a pair under one carrier that is
 * the whole question. `number(0, 1)` and `decimal('2', '3')` become `dynamoNumber(0, 1)` and
 * `dynamoNumber(2, 3)`, which are disjoint and so resolvable; `number(0.1)` and `decimal('0.1')`
 * become the same `dynamoNumber(0.1)`, and no stored attribute can ever choose between them.
 *
 * {@link clauseForm} is the descent, so an adapter that declares no `writes` pins nothing here and
 * is never certified.
 */
const carrierDisjoint = (x: Term, y: Term): boolean =>
    sharedLiterals(x, y)?.length === 0

/**
 * **The values two pinned options both carry**, or `undefined` where one of them pins none.
 *
 * `union` asks again on the path it is about to throw on, so a refusal can name the values that
 * caused it rather than the slot they happen to share. That is the same walk {@link meet} is asked
 * to repeat for the same reason.
 */
export const sharedLiterals = (
    x: Term,
    y: Term,
): readonly LiteralValue[] | undefined => {
    const xs = clauseForm(x)
    const ys = clauseForm(y)
    if (!xs || !ys) return undefined
    const theirs = ys.alts.ls as readonly LiteralValue[]
    return (xs.alts.ls as readonly LiteralValue[]).filter((one) =>
        theirs.some((other) => sameLiteral(one, other)),
    )
}

/**
 * **Whether one conversion runs on both sides**, by reference.
 *
 * The write side needs it and the read side does not. A stored attribute lands in at most one of
 * two disjoint alternative sets whatever `g` does, so the read side is decided by the sets alone.
 * A caller's value reaches those sets through `f`, so two *different* `f`s could carry one value
 * into both sets and disjointness would certify nothing. Every `number(…)` shares one `asFloat` and
 * every `decimal(…)` one `storedOnly`, so the identity is the reference.
 *
 * **Two bare terms share the identity**, which is one conversion by the same argument: `string('a')`
 * and `string('b')` carry the caller's value to itself, so disjoint alternatives are disjoint
 * admissions. A bare term beside an adapter does not, because the identity and `f` are two.
 */
const sameConversion = (x: Term, y: Term): boolean =>
    x.kind === 'held' || y.kind === 'held'
        ? x.kind === 'held' && y.kind === 'held' && x.f === y.f
        : true

/**
 * **Whether a union may hold these two options**, asked at the declaration.
 *
 * **This is not a port of `Orth`, and the difference is the direction.** `Orth` is a *certificate*:
 * `true` means the model proved the two cannot both admit one input. This is the complement of a
 * *refutation*: it answers `false` only where both occupancies are known, they meet on a side, and
 * no exemption applies. Where `Orth` declines for want of a proof, this accepts. One row is shared
 * — `Orth1`, below — and the law that ties them is what `formal/.separations.lean` pins, one
 * theorem per pair this function refuses: **it never answers `false` where `certPair` answers `true`.**
 * Refusing a declaration the model proves separable would be refusing a union that works.
 * `union` asks {@link crossing} ahead of this function, because this function can accept a pair
 * that crosses.
 *
 * Five rows, and each carries its own warrant. A sixth exempted an `opaque` option and is gone;
 * the paragraph below the fifth says why.
 *
 * **Two options that meet at the bottom.** The model's certificate is `certPair`: `Orth`, or a
 * meet at `never`. `Adm_meet` and `AdmA_meet` make the meet's admission the conjunction of the
 * two, so a meet at the bottom admits no common value and reads no common attribute. The row asks
 * {@link meetTerms} only where both terms reach no thunk, which {@link reaches} answers. It certifies two lists told apart
 * by a literal position, and two objects whose required slots meet at the bottom.
 *
 * **Two object options: the structural meet, which is the same question the type asks.** A union
 * admits every option by attempt, an object option included, so two object options are separable
 * where no value passes both attempts. This row reads that off the two structures: the names
 * present, and then every required literal field. Two such options are separable where no value
 * satisfies both structures: either their name intervals do not meet (`OrthM`, and `Collides` is
 * that written in the type) or some shared required name is pinned to literals with nothing in
 * common (`OrthS`). The meet row above certifies two objects whose required slots meet at `never`
 * through a field that pins no literal.
 *
 * **One object option beside a non-object meets through the occupancies**, as every other pair
 * does. `opaque` writes and reads a map too, so an object beside it is not separable outright.
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
 * **An occupancy that is unknown.** A `held` that declares no `writes` has an unknown write side,
 * because its `f` runs before the subterm and can move a value into any constructor. A `legacy`
 * has an unknown read side, because its `r` widens exactly the reading. A `lazy` is transparent,
 * so its occupancies are its subterm's. The model certifies no pair on an unknown side. This
 * function takes the other direction, as the first paragraph states: an unknown side is not a
 * meeting, so the known side decides. Every option of a `union` has a term, so this function
 * takes two terms and has no row for one that is missing.
 *
 * **There is no `opaque` row, and its removal is the rule this function most recently learned.**
 * §5 separates the two things a `⊤` covers: *unknown* — the write side of a `held` that declares
 * no `writes` and the read side of a `legacy`, whose answer exists and cannot be read — and *everything*, which is `opaque`, accepting every kind by
 * design. The model states the second as a **closed form**, `occTop` at the total `opaq`, so
 * it can be compared; this library read it as `⊤` and exempted it instead, which
 * meant `union([opaque, X])` declared.
 *
 * **JH ruled that union unacceptable, and the model says why.** It is not equal to `opaque`: it is
 * *undefined* wherever `X` admits, because `opaque` admits every value `X` does and `select` acts
 * only where exactly one option does. Everywhere else it is `opaque`. So `X` is a declared option
 * that no value can ever choose — §5's failure, not a rank. `occV` and `occA` answer the closed
 * form now, `Orth1` finds the meeting, and the pair is refused at the declaration.
 *
 * **Otherwise the two occupancies, both sides conjoined.** A pair separated on one side only is not
 * separated: the loosened form ships `union([decimal, number])`, which writes `'1.5'` to an `N` and
 * cannot read back what it wrote, because `decimal` takes a string and `number` a number while both
 * store `N`. The model's `Orth1` tests the write side alone, because there `occA_le_occV` puts the
 * read occupancy inside the write occupancy. Here a `held` declares its `writes`, and `decimal` writes
 * a string and reads an `N`, so the read side is a second question.
 */
export const separable = (x: Term, y: Term): boolean => {
    // **Containment first.** The three {@link restricts} rows name a literal, a set of a literal
    // and `never`. `never` meets no occupancy, so the rows below would accept it beside anything
    if (restricts(x, y) || restricts(y, x)) return false
    // a meet at the bottom separates, and it runs ahead of the object row, because two objects
    // whose required slots meet at `never` share names and no value
    if (!reaches(x, []) && !reaches(y, []) && meetTerms(x, y)?.kind === 'never')
        return true
    const xs = objectMembers(x)
    const ys = objectMembers(y)
    if (xs && ys) {
        return xs.every((a) => ys.every((b) => !structuralMeet(a, b)))
    }
    const writable = meet(occV(x), occV(y))
    const readable = meet(occA(x), occA(y))
    if (writable === undefined && readable === undefined) return true
    /**
     * **Where both options pin a set of values, the values decide.**
     *
     * The occupancies answer *where* two options write and read, which is right, and they are
     * silent about *what*, which is the question `Orth` asks. Two options that each name their own
     * values meet exactly where those value sets meet, so a pair sharing a slot is separable when
     * the sets are disjoint and is separable by nothing when they are not. That holds under an
     * adapter and over a bare base alike: `number(0, 1)` and `decimal('2', '3')` are
     * `dynamoNumber(0, 1)` and `dynamoNumber(2, 3)` beneath one carrier, and `string('a')` and
     * `string('b')` are already themselves.
     *
     * **The two sides part company, and only the write side needs the conversion.** A stored
     * attribute lies in at most one of two disjoint sets whatever `g` does. A caller's value
     * reaches those sets through `f`, so two different conversions could carry one value into both
     * and disjointness would certify nothing.
     *
     * This runs ahead of {@link identifies}, which is the unary reading of the same idea and
     * cannot state it: "each option knows its own values" does not say the two sets differ. The
     * short-circuit stays for the rows below it, where an option decides its own values through a
     * closure or a subterm and names no set to compare.
     */
    const pinned = clauseForm(x) && clauseForm(y)
    if (pinned) {
        const disjoint = carrierDisjoint(x, y)
        return (
            (writable === undefined || (sameConversion(x, y) && disjoint)) &&
            (readable === undefined || disjoint)
        )
    }
    return identifies(x) || identifies(y)
}

/**
 * **Whether a term reaches a subterm of one of these kinds**, at any depth.
 *
 * The model's `lazy` is transparent, and {@link meetTerms} forces a thunk to read through it. A
 * thunk can be recursive, so a meet of two recursive terms need not end, and {@link separable}
 * asks the meet only of a term that reaches no thunk, which `reaches(t, [])` answers. `held` and `legacy` need no such guard
 * there: the meet answers `undefined` at each, and the model's certificate needs no `HF` premise.
 * {@link crossing} asks for no adapter as well, because the model's confluence holds only there.
 */
const reaches = (t: Term, kinds: readonly Term['kind'][]): boolean => {
    if (kinds.includes(t.kind)) return true
    switch (t.kind) {
        // a thunk cannot be read without forcing it, so it counts as reaching every kind
        case 'lazy':
            return true
        case 'held':
        case 'legacy':
        case 'refine':
            return reaches(t.inner, kinds)
        case 'list':
            return (
                t.pre.some((one) => reaches(one, kinds)) ||
                (t.spread !== undefined && reaches(t.spread, kinds)) ||
                t.suf.some((one) => reaches(one, kinds))
            )
        case 'object':
            return (
                Object.values(t.body.fields).some((f) => reaches(f.t, kinds)) ||
                (t.body.rest !== undefined && reaches(t.body.rest, kinds))
            )
        case 'union':
            return t.options.some((one) => reaches(one, kinds))
        default:
            return false
    }
}

/**
 * **The overlap of two options that cross**, or nothing.
 *
 * Two options cross where their meet is neither `never` nor one of the two. A pair whose meet is
 * `never` is disjoint, and a pair whose meet is one option is nested. A value in the overlap is
 * admitted by both options, so the value does not decide the branch, and no rule names an owner
 * of the overlap. JH ruled that `union` refuses such a pair, and that a caller writes the overlap
 * as an option of its own. Asked only where neither option reaches a thunk or an adapter: there
 * the meet is exact, and two options that both admit a value write one attribute. The overlap
 * must reach no `refine`, because the host meet does not decide whether a refinement holds a
 * value.
 */
export const crossing = (x: Term, y: Term): Term | undefined => {
    const adapters = ['held', 'legacy'] as const
    if (reaches(x, adapters) || reaches(y, adapters)) return undefined
    const overlap = meetTerms(x, y)
    // a `refine` in the overlap can hold no value: two literal sets with disjoint alphabets meet
    // at a set whose each element is in both, and the store has no empty set
    if (
        overlap === undefined ||
        overlap.kind === 'never' ||
        reaches(overlap, ['refine'])
    )
        return undefined
    return sameTerm(overlap, x) || sameTerm(overlap, y) ? undefined : overlap
}

/** Two terms with the same structure. A function compares by reference, and bytes by value. */
const sameTerm = (one: unknown, other: unknown): boolean => {
    if (one === other) return true
    if (one instanceof Uint8Array || other instanceof Uint8Array)
        return sameValue(one, other)
    if (typeof one !== 'object' || typeof other !== 'object') return false
    if (one === null || other === null) return false
    if (Array.isArray(one) !== Array.isArray(other)) return false
    const mine = Object.entries(one)
    const theirs = new Map(Object.entries(other))
    return (
        mine.length === theirs.size &&
        mine.every(
            ([key, value]) =>
                theirs.has(key) && sameTerm(value, theirs.get(key)),
        )
    )
}

/**
 * **A term, spelled with the constructors a caller writes**, for a message that names a term the
 * caller did not write: the overlap that {@link crossing} finds.
 */
export const spelled = (t: Term): string => {
    switch (t.kind) {
        case 'number':
            return 'dynamoNumber'
        case 'null':
            return 'nullValue'
        case 'opaq':
            return 'opaque'
        case 'literal':
            return `${literalForm(t.base, undefined)}(${namedLiteral(t.v)})`
        case 'set':
            return `${literalForm(t.base, undefined)}.set()`
        case 'list':
            return `list(${[
                ...t.pre.map(spelled),
                ...(t.spread === undefined
                    ? []
                    : [`spread(${spelled(t.spread)})`]),
                ...t.suf.map(spelled),
            ].join(', ')})`
        case 'object': {
            const fields = Object.entries(t.body.fields).map(
                ([name, field]) =>
                    `${name}: ${
                        field.mark === 'req'
                            ? spelled(field.t)
                            : `${field.mark === 'fallback' ? 'withLegacyRead' : field.mark}(${spelled(field.t)})`
                    }`,
            )
            const rest =
                t.body.rest === undefined
                    ? ''
                    : `, [string, optional(${spelled(t.body.rest)})]`
            return `object({ ${fields.join(', ')} }${rest})`
        }
        case 'union':
            return `union([${t.options.map(spelled).join(', ')}])`
        case 'refine':
            return `refine(${spelled(t.inner)}, …)`
        default:
            return t.kind
    }
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
 * **Where the host could answer and the model has no row, this refuses.** Two `number` literals,
 * two `withLegacyRead` fields and an `undefinable` field are each comparable in TypeScript and each
 * answer `undefined` here, because a row the model does not state is a rule this port would be
 * inventing. The first two are `docs/defects.md` entries; the third is a mark the model's `Field`
 * does not have.
 */
export const meetTerms = (x: Term, y: Term): Term | undefined => {
    // the bottom absorbs, on either side
    if (x.kind === 'never' || y.kind === 'never') return never
    // a thunk carries a plain term, so the meet reads through it. The model's `.lazy` row sits
    // second on the left and after `held` on the right, and these two keep that precedence
    if (x.kind === 'lazy') return meetTerms(x.get(), y)
    // the three whose admission is a function and not data: a reader cannot say what they admit
    // without running them, so no term states the intersection
    if (opaqueToReader(x) || opaqueToReader(y)) return undefined
    if (y.kind === 'lazy') return meetTerms(x, y.get())
    // a certified union distributes, on either side
    if (x.kind === 'union') return distribute(x.options, y)
    if (y.kind === 'union') return distribute(y.options, x)
    // a refinement conjoins: the predicate is data, so it rides on the meet of the inner terms
    if (x.kind === 'refine') return overRefinement(x.inner, x.q, y)
    if (y.kind === 'refine') return overRefinement(y.inner, y.q, x)
    // the ground bases: the same base is itself
    if (x.kind === y.kind && groundBase(x)) return x
    // **`string` and `decimal` part on the stored side.** Both admit text; `string` writes `S` and
    // `decimal` writes `N`, so a value they share is stored two ways and there is no meet. The
    // literal rows repeat it, because a literal at either base inherits the pair
    if (x.kind === 'literal' && y.kind === 'literal') return meetLiterals(x, y)
    if (x.kind === 'literal') return literalAgainstBase(x, y)
    if (y.kind === 'literal') return literalAgainstBase(y, x)
    if (x.kind === 'list' && y.kind === 'list') return meetLists(x, y)
    if (x.kind === 'set' && y.kind === 'set') {
        // every set base is disjoint from every other on both halves now, so two unequal ones
        // meet at the bottom and none of them refuses. `set string` against `set decimal` was the
        // refusal, while `decimal` held text and both families wrote a `strSet`
        return x.base === y.base ? x : never
    }
    if (x.kind === 'opaq' && y.kind === 'opaq') return x
    if (x.kind === 'object' && y.kind === 'object')
        return meetBodies(x.body, y.body)
    // **`opaque` against a ground base.** It admits every value of every self-identifying kind, so
    // at `string`, `boolean`, `binary`, `null` and `number` the base is the finer term. `decimal`
    // refuses for the reason `string ∧ decimal` refuses
    if (x.kind === 'opaq') return opaqueAgainst(y)
    if (y.kind === 'opaq') return opaqueAgainst(x)
    // **The `number` family and the `decimal` family never meet.** They write different value kinds,
    // so the bottom is right about the write side, and they read the same member `N`, so the bottom
    // is wrong about the read side: every stored numeral is an attribute both admit
    // everything left is two constructors that write different value kinds
    return never
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
 * `members` at any two bases, and `each` meets `each` through the element predicates. A scalar
 * `members` and `each` share no value, because `each` holds only a set. A `closure` refuses.
 */
const meetPredicates = (
    q: Predicate,
    p: Predicate,
): Predicate | null | undefined => {
    if (q.kind === 'closure' || p.kind === 'closure') return undefined
    if (q.kind === 'each' && p.kind === 'each') {
        const met = meetPredicates(q.of, p.of)
        return met === undefined || met === null
            ? met
            : { kind: 'each', of: met }
    }
    if (q.kind === 'members' && p.kind === 'members') {
        const met = meetAlternatives(q.literal, p.literal)
        return met === null ? null : { kind: 'members', literal: met }
    }
    return null
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
): Term | undefined => {
    if (q.kind === 'closure') return undefined
    const z = meetTerms(inner, other)
    return z === undefined ? undefined : refineOf(z, q)
}

/**
 * **The meet at a union: the survivors, where both lists carry the certificate.**
 *
 * The meet is the lattice's meet and an uncertified union is not in the lattice, so the pair has
 * no meet to state. Both lists are tested and not one.
 */
const distribute = (
    options: readonly Term[],
    other: Term,
): Term | undefined => {
    const met: Term[] = []
    for (const option of options) {
        const z = meetTerms(option, other)
        if (z === undefined) return undefined
        met.push(z)
    }
    const survivors = met.filter((z) => z.kind !== 'never')
    return unionOk(options) && unionOk(survivors)
        ? ofOptions(survivors)
        : undefined
}

/**
 * **The certificate a union must carry for its admission to be the join of its options'** —
 * `Calculus.unionOk`.
 *
 * `certAll` is {@link separable} here, which is this library's `certPair` and carries exemptions the
 * model's does not. Every union the builders can construct has already passed it pairwise, so the
 * conjunct bites on the survivor list rather than on the input.
 */
const unionOk = (os: readonly Term[]): boolean =>
    os.every((t, at) =>
        os.every((u, other) => other <= at || separable(t, u)),
    ) && os.every((t) => !isOpenObject(t) && objectNamesAgree(t))

const isOpenObject = (t: Term): boolean =>
    t.kind === 'object' && t.body.rest !== undefined

/**
 * Whether an object option's two halves answer the same question about names. A `withLegacyRead`
 * field is required by the write side and supplied by the read side.
 */
const objectNamesAgree = (t: Term): boolean =>
    t.kind !== 'object' ||
    Object.values(t.body.fields).every((field) => field.mark !== 'fallback')

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
 * **Two literals: the same value, or nothing.**
 *
 * `number` refuses, mirroring the model, whose `Term.meetLit` row at `number` answers `none`,
 * because `WFNumeral` equality is textual and two spellings can name one number. TypeScript can compare two numbers, and answering here would
 * make this library's meet finer than the one the model's theorems are about.
 */
const meetLiterals = (x: Literal, y: Literal): Term | undefined => {
    if (x.base !== y.base) return never
    if (x.base === 'number') return undefined
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
): readonly Term[] | undefined => {
    const row: Term[] = []
    for (const [at, one] of a.entries()) {
        const z = meetTerms(one, b[at] as Term)
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
): Term | undefined => {
    if (x.spread !== undefined && y.spread !== undefined) {
        const p = Math.max(x.pre.length, y.pre.length)
        const s = Math.max(x.suf.length, y.suf.length)
        if (!dominates(x.pre.length, x.suf.length, y.pre.length, y.suf.length))
            return undefined
        const spread = meetTerms(x.spread, y.spread)
        if (spread === undefined) return undefined
        const rows = rowOf(x, p + s)
        const other = rowOf(y, p + s)
        // unreachable under dominance, where `p + s` is at least each side's declared length
        if (rows === undefined || other === undefined) return never
        const row = rowMeet(rows, other)
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
    const row = rowMeet(rows, other)
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
const meetFields = (a: Field, b: Field): Field | undefined => {
    if (a.mark === 'undefinable' || b.mark === 'undefinable') return undefined
    if (a.mark === 'optional' && b.mark === 'optional')
        return mark(meetTerms(a.t, b.t), 'optional')
    if (a.mark === 'fallback' || b.mark === 'fallback')
        return a.mark === 'req' || b.mark === 'req'
            ? mark(meetTerms(a.t, b.t), 'req')
            : undefined
    return mark(meetTerms(a.t, b.t), 'req')
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
const meetBodies = (a: Body, b: Body): Term | undefined => {
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
                ),
            ],
        ),
        ...Object.entries(b.fields)
            .filter(([name]) => !(name in a.fields))
            .map(([name, field]): [string, Field | undefined] => [
                name,
                meetFields({ mark: 'optional', t: aBlock }, field),
            ]),
    ]
    if (met.some(([, field]) => field !== undefined && isBottomField(field)))
        return never
    const block = meetTerms(aBlock, bBlock)
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

/**
 * Which of the four set bases a term's values sit at, or `undefined` where the term is not one.
 *
 * `member` could answer this now that `decimal` is an adapter rather than a second base at `N`,
 * and this stays a function of the term because the term is where the base is recorded. Reads
 * through `refine` and a literal only — both are *restrictions* of a base, so the set
 * they build is a restriction of the base's set (`setCodec_restrict`). An adapter (`held`), a read
 * widening (`withLegacyRead`) or a union is not a restriction of anything, and gets `undefined`.
 */
export const setBaseOf = (t: Term): SetBase | undefined => {
    switch (t.kind) {
        case 'string':
        case 'number':
        case 'binary':
            return t.kind
        case 'literal':
            return t.base === 'boolean' ? undefined : t.base
        case 'refine':
            return setBaseOf(t.inner)
        // **An adapter has a set-level spelling after all, so it is read through.** This refused
        // a `held` element on the ground that a set of one could not be written down. It can:
        // an adapter is elementwise, so mapping it over the wire set is the spelling, and
        // {@link elementAdapter} is what `set` builds it from. The base is the *stored* one,
        // which is the inner term's.
        case 'held':
            return setBaseOf(t.inner)
        // `string.set('a', 'b')` puts a union of literals at the element, and a union of literals
        // at one base is that base narrowed — the same reading a single literal gets
        case 'union': {
            const alts = literalAlternatives(t)
            return alts === undefined || alts.base === 'boolean'
                ? undefined
                : alts.base
        }
        default:
            return undefined
    }
}

/**
 * **The adapter an element carries, if it carries one.** `number` and `decimal` are adapters over
 * the one numeric base, so a set of either is a set of that base with the conversion mapped over
 * it, and this is where `set` reads the pair to map.
 *
 * Innermost wins, because the stack alternates and only the one next to the base converts the
 * value the wire set holds.
 */
export const elementAdapter = (
    elem: Term,
):
    | {
          readonly f: (value: never) => unknown
          readonly g: (held: never) => unknown
      }
    | undefined => {
    switch (elem.kind) {
        case 'held':
            return elementAdapter(elem.inner) ?? { f: elem.f, g: elem.g }
        case 'refine':
            return elementAdapter(elem.inner)
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
            return [{ kind: 'members', literal: oneAlternative(elem) }]
        // `string.set('a', 'b')` puts a union of literals at the element, and the model's
        // `Pred.members` carries a `NEFinset` — so the set is where the alternatives come back
        // together. A union of anything else restricts by nothing this can name.
        case 'union': {
            const alts = unionAlternatives(elem.options)
            return alts ? [{ kind: 'members', literal: alts }] : []
        }
        case 'refine':
            return [elem.q, ...elementPredicates(elem.inner)]
        default:
            return []
    }
}
