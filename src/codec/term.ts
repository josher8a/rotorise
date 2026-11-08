/**
 * The term language, and the functions of a term that the model computes.
 *
 * Derived from `formal/Calculus/Dynamo/Lang/Term.lean`, with `member` from `ScopePath.lean`'s `μG`.
 * {@link occV} has no counterpart there: the occupancy serves the host's union dispatch. One
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

import {
    type AttributeName,
    type AttributeValue,
    DynamoNumber,
} from './attribute'
import type {
    LiteralBase,
    LiteralValue,
    Refinement,
    Rng,
    SetSlot,
} from './codec'
import { CodecError, failed } from './result'
import { asRecord, own, sameLiteral } from './value'

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
 * **Four variants rather than one with a `base` field**, and that is the whole content. One
 * variant with `base: LiteralBase` beside `v: LiteralValue` admits
 * `{ base: 'string', v: 1 }` — a string literal whose value is a number, which nothing can
 * encode. The model has no such term: `v` is a `k.Carrier`, so the base *indexes* the value. This
 * is that indexing, in the one form TypeScript has for it.
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
 * place the model keeps a set of alternatives too: the answer {@link literalAlternatives} gives for a
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

/**
 * **Whether a `via` names one pair of functions**, which the model carries as one generator. The two
 * policies, `decimalText` and `float` each name one pair. `native` names a family: each configuration
 * of the marshaller holds its own closures, so the tag of a `native` is the pair of functions.
 */
export const namesOnePair = (
    via: string | undefined,
): via is 'decimalText' | 'float' | OpaqueSugar =>
    via === 'decimalText' || via === 'float' || isOpaqueSugar(via)

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
           * term, because the held side restricts every value that `f` receives. A library adapter records
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
          readonly via?: 'decimalText' | 'float' | OpaqueSugar | 'native'
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
          readonly arbitrary?: ((rng: Rng, size: number) => unknown) | undefined
          readonly shrink?: ((value: never) => readonly unknown[]) | undefined
      }
    /**
     * The rule `(refine)`. The model carries `q : Value → Bool`; this carries the caller's closure,
     * with `what` as the refusal text and `arbitrary` as what an arbitrary derived from the term
     * reads. A refinement accepts a part of what its inner term accepts, so a declaration reads
     * through it and reads no predicate. A finite set at a ground kind is a union of literals.
     */
    | { readonly kind: 'refine'; readonly inner: Term; readonly q: Refinement }
    /** The rule `(legacy)`: `r : Attr ⇀ Value`, the older reading, which widens `p` and never `e`. */
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
     * **Everything else here reads through the node.** {@link occV} and
     * {@link ownsNullOf} answer what the target answers, and the emitter prints an entry of a
     * cycle as a `ref`. Only {@link member} answers `undefined`. An unknown occupancy is the
     * unsound direction: the declaration guard refuses a union when two occupancies *meet*, so a
     * union of a `ref` to `string` and `string` would pass, and a write would then find two
     * options admitting one value.
     */
    | { readonly kind: 'ref'; readonly slot: RefSlot }
    /**
     * The rule `(opaque)`: the universal sum, and **total**. It holds a number as {@link DynamoNumber},
     * which holds the digits of a `WFNumeral` in the stored form, so it writes every wire value. The two numeric policies
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
    /** `fill` concludes `req`: the absence is in the row, never in the value. */
    | { readonly mark: 'fill'; readonly t: Term; readonly v: unknown }
    /** The absence is in the row *and* in the value, and the key is still there. */
    | { readonly mark: 'undefinable'; readonly t: Term }

/**
 * **Whether two fill values are one value**, as the model reads them: the model states a fill value as a
 * `Value`, so two fills agree where their fill values print as one `Value`. A string, a boolean, a
 * `DynamoNumber`, a byte array, a set, an array and a plain object compare by what they hold, a set
 * without its order and an object without its names that hold `undefined`. `null` and `undefined`
 * are one value. Any other value, a JS number among them, is no `Value`, and compares by `Object.is`.
 */
export const fillEquals = (a: unknown, b: unknown): boolean => {
    if (Object.is(a, b)) return true
    if (a === null || a === undefined) return b === null || b === undefined
    if (a instanceof DynamoNumber || a instanceof Uint8Array)
        return sameLiteral(a, b)
    if (a instanceof Set) {
        if (!(b instanceof Set) || a.size !== b.size) return false
        const rest = [...b]
        return [...a].every((x) => {
            const at = rest.findIndex((y) => fillEquals(x, y))
            if (at < 0) return false
            rest.splice(at, 1)
            return true
        })
    }
    if (Array.isArray(a)) {
        return (
            Array.isArray(b) &&
            a.length === b.length &&
            a.every((x, i) => fillEquals(x, b[i]))
        )
    }
    const mine = asRecord(a)
    if (mine) {
        const theirs = asRecord(b)
        if (!theirs) return false
        const names = (o: Record<string, unknown>) =>
            Object.keys(o).filter((name) => o[name] !== undefined)
        const kept = names(mine)
        return (
            kept.length === names(theirs).length &&
            kept.every((name) => fillEquals(mine[name], theirs[name]))
        )
    }
    return false
}

/**
 * **What the order compares at the absent row of a slot.** `relation` compares pairs of a stored
 * row and a decoded value, so a `fill` slot counts the absent row that its fill value
 * reads. The meet of two codecs reads it. `value` compares decoded values alone, because a pattern
 * has no decode of its own: a `fill` slot always gives a value, so the slot equals a
 * required slot, as the model's `AltClause.admitsC` reads a fill through `slotReq`. `fits`, the
 * slice and the pattern side of {@link meetOrdered} read it. The presence marks give one answer in
 * both orders.
 */
export type Order = 'relation' | 'value'

/**
 * **Whether the pairs of the absent row that the slot `mine` holds are pairs of the slot
 * `wanted`.** A required slot holds no absent row. At the `relation` order, a `fill` slot
 * pairs the absent row with its fill value, so it is below only a slot of the same fill value. At the
 * `value` order, a `fill` slot is a required slot. `undefinable` pairs it with
 * `{ k: undefined }`, which `optional` reads as `{}`. `optional`, and a name that a closed object
 * does not declare, pair it with a value without the key, which `undefinable` refuses.
 */
export const absentBelow = (
    mine: Field,
    wanted: Field,
    order: Order,
): boolean => {
    // at the `value` order a fill value counts no absent row, so the slot reads as a required slot
    const read = (f: Field): Field =>
        order === 'value' && f.mark === 'fill' ? { mark: 'req', t: f.t } : f
    const [m, w] = [read(mine), read(wanted)]
    switch (w.mark) {
        case 'req':
            return m.mark === 'req'
        case 'fill':
            return (
                m.mark === 'req' || (m.mark === 'fill' && fillEquals(m.v, w.v))
            )
        case 'undefinable':
            return m.mark === 'req' || m.mark === 'undefinable'
        case 'optional':
            return m.mark !== 'fill'
    }
}

/** Whether the row always carries this field's attribute. */
export const alwaysWritten = (field: Field): boolean =>
    field.mark === 'req' || field.mark === 'fill'

/* ── the member index ─────────────────────────────────────────────────────────────────── */

/** The ground kinds: the literal bases, and `null`, which has one value and no literal. */
export type GroundKind = LiteralBase | 'null'

/**
 * **The facts of a ground kind, stated once.** `member` is the member that the kind stores, and it
 * is injective: `decimal` was the second base at `N`, and it is an adapter over `number` now rather
 * than a base, so no two kinds share a member. `ctor` is the library constructor that prints the
 * kind, which is `dynamoNumber` for `number` because `number` builds a float adapter over it. The
 * keys of the record are the kinds, so a new kind is an error here before it is anywhere else.
 */
export const ground = {
    string: { member: 'S', ctor: 'string' },
    number: { member: 'N', ctor: 'dynamoNumber' },
    boolean: { member: 'BOOL', ctor: 'boolean' },
    binary: { member: 'B', ctor: 'binary' },
    null: { member: 'NULL', ctor: 'nullValue' },
} as const satisfies {
    readonly [K in GroundKind]: {
        readonly member: AttributeName
        readonly ctor: string
    }
}

/**
 * The member a set stores, from the member its element stores: `setMember`. An element of any
 * other member has no stored set, and answers the model's `none`.
 */
const setMemberOf = (
    element: AttributeName | undefined,
): AttributeName | undefined =>
    element === 'S' || element === 'N' || element === 'B'
        ? setMember[element]
        : undefined

/**
 * **The model's `setMember`, as one table**: the wire set that holds an element of each scalar
 * member. The run time reads it here, the denotation of a set reads it, and the path type reads it
 * by `typeof`.
 */
export const setMember = { S: 'SS', N: 'NS', B: 'BS' } as const

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
        case 'number':
        case 'boolean':
        case 'binary':
        case 'null':
            return ground[t.kind].member
        case 'literal':
            return ground[t.base].member
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
        // the return type allows `undefined`, so an arm left out would answer "no member" with no
        // error. This arm is the build error for a kind that has no row
        default:
            return t satisfies never
    }
}

/**
 * **The member that a term reads**, the bound of the stored side that a union's read filter needs.
 * The model's union reads through the first option that acts (`select`), so the filter keeps each
 * option that can act. A `legacy` reads its older form through caller code, so its read is
 * not bounded by a member. Every other term reads the member that it writes.
 */
export const readMember = (t: Term): AttributeName | undefined => {
    switch (t.kind) {
        case 'legacy':
            return undefined
        case 'held':
        case 'refine':
            return readMember(t.inner)
        case 'union':
            return unanimous(t.options.map(readMember))
        default:
            return member(t)
    }
}

/**
 * **The member that a set element stores**, read at the node that each `ref` names. The type gates
 * `.set()` on the attribute of the element, and the attribute of a scope entry is the attribute of
 * the definition that the entry names, so the run time reads the same node. A stored set holds no
 * recursion, so a node that the read already passed answers nothing. At an entry of a cycle the
 * read gives the member where `printedMember` answers none. A set refuses both answers, because the
 * element is then a container or a union of mixed members.
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

/**
 * The wire family a set writes for each scalar slot its element writes, read from the element's
 * side.
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
        case 'number':
        case 'boolean':
        case 'binary':
        case 'null':
            return [t.kind]
        case 'literal':
            return [t.base]
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
        // the held side restricts every value `f` receives
        case 'held':
            return occV(t.outer)
        // a `ref` answers what its target answers
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
        // the read side of a `legacy`, and *everything*, which is `opaque` by design. Answering
        // `undefined` here would say "cannot be read" about the one term whose occupancy is fully
        // known.
        case 'opaq':
            return everySlot
        // **Empty, not `undefined`.** `undefined` is the `⊤` that says "cannot be read", and this
        // term's occupancy is fully known: it is nothing.
        case 'never':
            return []
    }
}

/**
 * Whether a term reaches the null point, read off the term.
 *
 * `undefined` is *not determined by the term*, and it is what makes {@link nullable} refuse at
 * construction rather than guess. `legacy` answers it, because its older reader is the
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
        // an arm left out would answer "unknown" with no error. This arm is the build error
        default:
            return t satisfies never
    }
}

/* ── the name spec, and the discriminator ─────────────────────────────────────────────── */

/**
 * **The form a clause is written at**, which the base alone stopped naming.
 *
 * `extract` asks a clause and a member to agree on *which literal codec* pins a key, and until
 * `8a2eed9` that was the base: `decimal` was a base of its own, so `LiteralBase` had a member per
 * form. `decimal` is an adapter over `number` now, so `decimal('1')` and `number(1)` share a base
 * and share an inner value, and the base can no longer tell a clause at one from a member at the
 * other.
 *
 * The held side of the adapter is what parts them: `decimal` takes text and `number` takes a float
 * over one carrier. So the form is the base everywhere but `number`, and there it is read off the
 * held side of the adapter.
 */
export type LiteralForm = LiteralBase | 'decimal' | 'dynamoNumber'

/** @see {@link LiteralForm} */
export const literalForm = (
    base: LiteralBase,
    adapter: Extract<Term, { kind: 'held' }> | undefined,
): LiteralForm =>
    base !== 'number'
        ? base
        : adapter === undefined
          ? 'dynamoNumber'
          : occV(adapter.outer).includes('string')
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
 * **The form a clause names**, reading through a declared adapter and *not* through a refinement.
 *
 * A clause is written by the caller and states exactly what it means, so a refinement is no part
 * of it: the clause side reads through the adapter alone.
 */
export const clauseForm = (
    t: Term,
    adapter?: Extract<Term, { kind: 'held' }>,
): Omit<NameForm, 'required'> | undefined => {
    const at = resolvedTerm(t)
    if (at?.kind === 'held') {
        // an `opaque` held side admits every kind, so it names no form
        if (at.outer.kind === 'opaq') return undefined
        const pinned = clauseForm(at.inner, at)
        return pinned && { ...pinned, adapter: at }
    }
    const alts = at && literalAlternatives(at)
    return alts && { alts, form: literalForm(alts.base, adapter) }
}

/**
 * **The alternatives a term pins, without reading through a refinement.**
 *
 * One literal pins its own value; a union of literals at one base pins theirs, which is what
 * `string('a', 'b')` builds. Everything else pins nothing.
 *
 * A reader that must produce the value the codec writes cannot look through a refinement, because
 * a predicate narrows the literal.
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
 * sets of its options. A `held` holds the values of its stored side, as the model's `held` does, so
 * a `held` over a term that holds no value holds none. So `never`, a union whose every option holds
 * no value (`union([])` among them), and a `held` whose inner term holds no value, hold no value.
 *
 * Three forms stay out. A `refine` holds no value where its predicate admits nothing, and no
 * function decides that of a closure. A `legacy` has no held set in the model, and its older
 * reader reads values that the inner term does not hold. A list, an object or a set over a term
 * that holds no value holds none either, but the judgment refuses each of them where it is built.
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
        case 'held':
            return holdsNoValue(at.inner, inside)
        default:
            return false
    }
}

/**
 * The pin of a term, read as the model's `pinOfG` reads it: through each `refine`, then through one
 * `held`, and the term under that `held` pins itself. A second adapter or a refinement under the
 * first adapter pins nothing.
 */
export const storedPin = (t: Term): StoredPin | undefined => {
    const at = resolvedTerm(t)
    if (at?.kind === 'refine') return storedPin(at.inner)
    if (at?.kind !== 'held') return at && { held: undefined, under: at }
    const inner = resolvedTerm(at.inner)
    return inner && { held: at, under: inner }
}

/**
 * What {@link storedPin} reads: the `held` that the walk passed, and the term below it, which is
 * the term of the stored attribute. A `held` of a caller has no `via`.
 */
export type StoredPin = {
    readonly held: Extract<Term, { kind: 'held' }> | undefined
    readonly under: Term
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
    const pin = storedPin(t)
    return pin && literalAlternatives(pin.under)
}

/**
 * A stored literal, put back through the adapter that a pin passed: the literal itself where no
 * adapter holds the pin, and `g` of the literal where one does, because a `held` owes that the pair
 * cancels (`pinOfG` reads the pin, and the value is the one that `g` gives for it). `undefined`
 * where the adapter returns a refusal of its own literal, which breaks the pair that the adapter
 * owes. A throw of `g` is not caught, and each caller decides what the throw means.
 */
const throughAdapter = (
    pin: StoredPin | undefined,
    literal: unknown,
): unknown => {
    if (pin?.held === undefined) return literal
    const value = (pin.held.g as (held: unknown) => unknown)(literal)
    return failed(value) ? undefined : value
}

/**
 * The value that a pin decodes to as a constant: a `literal` under the pin, put back through the
 * adapter. `undefined` where the term below is no literal. A union of literals, one literal
 * included, decides no constant, as the type `ConstantOf` states.
 */
export const pinnedValue = (pin: StoredPin | undefined): unknown =>
    pin?.under.kind === 'literal' ? throughAdapter(pin, pin.under.v) : undefined

/**
 * The value that a tag decodes to: the one literal that {@link storedAlternatives} names for the
 * tag, put back through the adapter. The reader is the one that `assignmentOf` reads the stored
 * text with, so a tag that has a stored text has a decoded value, a union of one literal included.
 * `undefined` where the tag names no one literal.
 */
export const decodedTag = (t: Term): unknown => {
    const stored = storedAlternatives(t)?.ls
    return stored?.length === 1
        ? throughAdapter(storedPin(t), stored[0])
        : undefined
}

/** Whether the adapter that {@link storedPin} passed is the adapter of a caller. */
export const isCallerPin = (pin: StoredPin | undefined): boolean =>
    pin?.held !== undefined && pin.held.via === undefined

/** One literal, as the one-alternative set it pins. */
export const oneAlternative = (t: Literal): Alternatives =>
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
 * `string('1')` and a `dynamoNumber` literal of `1` is told apart by the member and not by the
 * value, and no single base describes it.
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
    if (t.kind === 'ref') {
        if (seen.has(t)) return true
        seen.add(t)
        const target = targetOf(t)
        return target === undefined || on(target)
    }
    return childrenOf(t, 'wire').some(on)
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
        if (t.kind === 'ref') {
            if (t.slot.bound === undefined) slots.add(t.slot)
            return
        }
        for (const child of childrenOf(t)) walk(child)
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
 *   depth. A `held` converts the value, and a `legacy` writes the older reader's answer.
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

/**
 * The term with each child replaced by its view, for the children that {@link childrenOf} lists.
 * A `ref` has no child here, because the view of a `ref` is the choice of the caller. `wire` leaves
 * `held.outer` as it is.
 */
export const mapChildren = (
    t: Term,
    view: (t: Term) => Term,
    side: 'all' | 'wire' = 'all',
): Term => {
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
        case 'set':
            return { kind: 'set', elem: view(t.elem) }
        case 'held':
            return {
                ...t,
                inner: view(t.inner),
                ...(side === 'wire' ? {} : { outer: view(t.outer) }),
            }
        case 'refine':
        case 'legacy':
            return { ...t, inner: view(t.inner) }
        // a term with no child term reads as itself in every view
        case 'string':
        case 'number':
        case 'boolean':
        case 'binary':
        case 'null':
        case 'literal':
        case 'opaq':
        case 'never':
        case 'ref':
            return t
        // the arm for a kind that has no row is the build error, so a new container is not a leaf
        default:
            return t satisfies never
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
 * **Whether a `legacy` occurs in the term.** The model states the read widening as
 * `Term.legacy`, and the rule `TOp.rule` of the judgement answers `none` at it, because the pair is not a partial
 * bijection. The law of `set`, `lawful_setCodec`, needs a lawful element, so no law covers a set
 * of a widened element, and `set` refuses one.
 */
export const widensRead = (t: Term): boolean => reaches(t, ['legacy'])

/**
 * **Whether two `held` terms are one adapter**: the tag test of the held row. The tag of a
 * library adapter that names one pair is its `via` name, and the model carries one generator for each
 * name. The tag of any other adapter is the pair of functions, which `held` and `native` build once
 * for each call, so two terms of one call are one adapter.
 */
export const sameAdapter = (
    x: Extract<Term, { kind: 'held' }>,
    y: Extract<Term, { kind: 'held' }>,
): boolean =>
    (namesOnePair(x.via) && x.via === y.via) || (x.f === y.f && x.g === y.g)

/**
 * **Whether two terms are one term**: one structure, with each `ref` read as its target, and each
 * function that a term holds the same function object. A literal compares by its base, and a
 * fill value by {@link fillEquals}.
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
                    sameAdapter(l, r) &&
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
                        const one = own(l.body.fields, name)
                        const other = own(r.body.fields, name)
                        return (
                            one !== undefined &&
                            other !== undefined &&
                            one.mark === other.mark &&
                            (one.mark !== 'fill' ||
                                (other.mark === 'fill' &&
                                    fillEquals(one.v, other.v))) &&
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
            // a kind that carries nothing is equal to the same kind
            case 'string':
            case 'number':
            case 'boolean':
            case 'binary':
            case 'null':
            case 'opaq':
            case 'never':
                return l.kind === r.kind
            // the arm for a kind that has no row is the build error, so a new kind with a payload
            // is not equal by its kind alone
            default:
                return l satisfies never
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
export const childrenOf = (
    t: Term,
    side: 'all' | 'wire' = 'all',
): readonly Term[] => {
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
        // `wire` drops the held side: the run time calls only `outer.encode`, so no older reader
        // under `outer` runs
        case 'held':
            return side === 'wire' ? [t.inner] : [t.inner, t.outer]
        case 'refine':
        case 'legacy':
            return [t.inner]
        // a ground kind, a literal, `opaque` and `never` hold no child term
        case 'string':
        case 'number':
        case 'boolean':
        case 'binary':
        case 'null':
        case 'literal':
        case 'opaq':
        case 'never':
            return []
        // the arm for a kind that has no row is the build error, so a new container is not a leaf
        default:
            return t satisfies never
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
    t.kind === 'literal' || Object.hasOwn(ground, t.kind)

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
