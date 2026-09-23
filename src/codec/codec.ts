import type {
    Attribute,
    AttributeMap,
    AttributeName,
    AttributeValue,
    B,
    BOOL,
    BS,
    L,
    M,
    N,
    NS,
    NULL,
    S,
    SS,
    StoredItem,
} from './attribute'
import { DynamoNumber, isStoredNumeral } from './attribute'
import { codec } from './build'
import {
    accepts,
    altSem,
    byTagSem,
    codecOfTerm,
    itemSem,
    literalCodec,
    literalShape,
    membersOf,
    opaqueTerms,
    optionOfTerm,
    sameAssignment,
    termOf,
} from './denote'
import {
    andThen,
    asPath,
    CodecError,
    failed,
    orThrow,
    type Result,
} from './result'
import type {
    Body,
    Field,
    LiteralForm,
    NameForm,
    OpaqueSugar,
    Term,
} from './term'
import {
    alwaysWritten,
    clauseForm,
    clauseLiteralsOf,
    elementAdapter,
    elementPredicates,
    literalAlternatives,
    meet,
    member as memberOf,
    occA,
    occV,
    ownsNullOf,
    restricts,
    separable,
    setBaseOf,
    sharedLiterals,
} from './term'

/**
 * Forwarded for the consumers that still name them here.
 *
 * They are `denote.ts`'s now — each answers about a term's *pair* — and this keeps the move to one
 * pass. Six of the eight go in the pass that deletes the readers; `codecOfTerm` and `termOf` stay,
 * and their callers move to the module that owns them there.
 */
export { codecOfTerm, termOf, valueKinds } from './denote'

import type { ErrorMessage, show } from '../utils'
import {
    describeShape,
    namedLiteral,
    namesOf,
    readTags,
    sameLiteral,
} from './value'

// the failure algebra lives in `./result`, and is re-exported because it is part of the surface a
// caller works in: a `Result` is what every direction returns
export {
    andThen,
    CodecError,
    every,
    everyEntry,
    failed,
    orThrow,
    type Result,
} from './result'

/**
 * Marks a codec whose attribute may be absent.
 *
 * Type-level only. Whether an attribute may be absent is read at runtime from the field's
 * {@link Field} — `optional` is one of the two marks — so there is nothing for a symbol to carry
 * and nothing for a wrapper to forget to copy. The declaration stays because the *type* needs a
 * brand: {@link ItemSpec} and {@link ObjectOf} decide required from optional by it.
 */
declare const optionalMarker: unique symbol

/** Type-level only, for the same reason as {@link optionalMarker}: the term carries the fact. */
declare const fallbackMarker: unique symbol

/** Type-level only, for the same reason as {@link optionalMarker}. */
declare const undefinableMarker: unique symbol

/**
 * Marks the codec for a list's repeating positions.
 *
 * Type-level only, and read at runtime from the definition, for the same reason as
 * {@link optionalMarker}. Like `optional`, it is a marker for a *position* rather than a codec in its
 * own right — it says "and then any number of these" — so it is meaningful in exactly one place:
 * among the elements of a {@link list}.
 */
declare const spreadMarker: unique symbol

/**
 * A deterministic source of randomness.
 *
 * Seeded rather than `Math.random`, so a counterexample found in CI reproduces exactly from the
 * seed printed alongside it.
 */
export type Rng = () => number

/**
 * Reads and writes one attribute.
 *
 * `A` is the attribute type produced, not the member name: a codec may write more than one member
 * (see {@link nullable}), and naming the members instead would collapse to a value carrying all of
 * them at once.
 */
export type AttributeCodec<
    T,
    A extends AttributeValue = AttributeValue,
> = CodecShape<T, T, A>

/**
 * The capabilities a codec has, with the two directions named separately.
 *
 * One record, instantiated twice. {@link AttributeCodec} is the concrete form, where both
 * directions are the same `T`; {@link AnyCodec} is the erased one, where `In` is `never` and `Out`
 * is `unknown` so every concrete codec is assignable to it.
 *
 * Written once because it was written twice: the erased form was a field-for-field copy, and a
 * capability added to one and not the other simply stops being visible through the erased form —
 * which is the form `at`, `set` and `keyUpdates` all read through. Nothing would fail; the fact
 * would just never arrive.
 */
type CodecShape<In, Out, A extends AttributeValue> = {
    /**
     * The attribute this value is written as, or why it cannot be.
     *
     * A {@link Result}: the failure is returned, not thrown, because a row is data somebody else
     * wrote and failing to read one is an ordinary outcome rather than an exception. `CodecError`
     * extends `Error`, so a bare union is enough to tell the two apart and `isError` narrows it.
     */
    readonly encode: (value: In) => Result<A>
    /** The value this attribute holds, or why it cannot be read. */
    readonly decode: (attribute: AttributeValue) => Result<Out>
    /**
     * The same, throwing.
     *
     * What every codec calls to compose with another: a nested decode that returned a union would
     * have to be unwrapped at each of the fifty-odd places one codec reaches into the next, and the
     * unwrapping is the part that gets forgotten. So composition throws and the boundary converts,
     * which is why these are the ones the composites are built from.
     */
    readonly unsafeEncode: (value: In) => A
    /** The same, throwing. */
    readonly unsafeDecode: (attribute: AttributeValue) => Out
    /**
     * What this codec is — see {@link Term}.
     *
     * A term and not a declaration: the two field kinds denote a §4 field, a field is not a codec,
     * and so no codec's definition is one. It is what makes each reader total over the kinds it can
     * be handed rather than over the kinds that exist.
     */
    readonly def: Term
}

/**
 * Anything that can sit where an attribute codec is expected — which is every codec.
 *
 * There used to be a second thing: an item, tagged or untagged codec, which *was* one `M` attribute
 * but exposed it as `.attribute`, so specs had to accept both shapes and every combinator had to
 * convert. The distinction was never about attributes. It was about the top-level map, and the top
 * level is the one place a map is not written — so it belongs to the *view*, not to the codec.
 * {@link object} writes its `M` like anything else, and offers `.item` for the one place that does
 * not: the top level.
 */
export type Nestable<T> = AttributeCodec<T>

/**
 * An attribute that may be absent from the item entirely.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A>` intersected with the
 * marker, so it claimed a field has an `encode` and a `decode` — true only because {@link optional}
 * built its answer by spreading the codec it marks. §4 refuses it: a field is a statement about a
 * *name*, the name belongs to the object, and the pair a member is read and written through is the
 * one the field marks. `rest` stopped making the same claim at `931c29c`.
 *
 * The definition is carried because {@link fieldOf} reads the mark off `def.kind` at run time, and a
 * type that did not name it would be a type that does not say what the value holds.
 */
export type OptionalCodec<
    T,
    A extends AttributeValue = AttributeValue,
    C = AttributeCodec<T, A>,
> = {
    readonly [optionalMarker]: true
    readonly codec: C
    // the mark's own case and not the whole of `Field`, so a reader that must tell the two marks
    // apart can, without the symbols — which are `declare const` and reach no consumer
    readonly def: Extract<Field, { readonly mark: 'optional' }>
}

/**
 * Carries {@link optionalMarker} as well as its own: the attribute is omitted either way, so every
 * reader that asks about the stored row is correct for this mark by being unchanged. The second
 * marker is what {@link ObjectOf} reads to keep the key required.
 */
export type UndefinableCodec<
    T,
    A extends AttributeValue = AttributeValue,
    C = AttributeCodec<T, A>,
> = {
    readonly [optionalMarker]: true
    readonly [undefinableMarker]: true
    readonly codec: C
    readonly def: Extract<Field, { readonly mark: 'undefinable' }>
}

/** Any codec, both directions erased — `never` in and `unknown` out, so every codec fits. */
export type AnyCodec = CodecShape<never, unknown, AttributeValue>

/**
 * Anything a {@link spread} produced, whatever it marks — {@link AnyCodec}'s counterpart for the one
 * thing that is a position rather than a codec, and the only element type {@link list} accepts that
 * is not a codec.
 *
 * Written as the marked shape rather than as `SpreadCodec<unknown, AttributeValue>`, for the reason
 * {@link ListWrites} records: `AttributeCodec` names its value on both sides, so it is invariant
 * and the `unknown` instantiation matches no real one.
 */
export type AnySpread = {
    readonly [spreadMarker]: true
    readonly spread: AnyCodec
}

/**
 * Anything an object member can be declared as: a codec, or a §4 field that marks one.
 *
 * `optional` and `withLegacyRead` state that the attribute at a *name* may be absent, and the name belongs
 * to the object rather than to the thing declared at it. So a field is not a codec, and the pair a
 * member is read and written through is the one the field marks.
 *
 * Written as the definition alone, because the definition is the whole of what both cases carry that
 * an object reads: `fieldOf` takes the mark off `def.mark` and the child term out of the same record.
 */
export type ObjectSlot = AnyCodec | { readonly def: Field }

/**
 * The codec a declaration marks, and the declaration itself where it is already one.
 *
 * A body hands out codecs and never fields. The mark is a statement about a name, the name is the
 * body's, and a caller that asked for the attribute at a name wants the thing that reads and writes
 * it — so this is what {@link ItemCodec.field} answers with.
 */
export type Marks<C> = C extends { readonly codec: infer Marked } ? Marked : C

export type Decoded<C> = C extends {
    readonly attribute: AttributeCodec<infer T>
}
    ? T
    : // a field marks a codec and has none of its own, so the value it carries is the marked one's
      C extends { readonly codec: AttributeCodec<infer T> }
      ? T
      : C extends AttributeCodec<infer T, AttributeValue>
        ? T
        : never

/* ── the readers ──────────────────────────────────────────────────────────────────────── */

/*
 * A reader here answers from the **term** and nothing else, which is what makes the term determine
 * the codec rather than describe it. `constantOf` is the one left in this file; `member`, `occV`,
 * `occA`, `specOf`, `tagsOf`, `identifies`, `separable` and `setBaseOf` are `term.ts`'s, and
 * `carries`, `accepts` and `readsBack` ask the pair in `denote.ts`.
 *
 * They take a *codec* and read its term rather than taking the term, and that is the decision
 * rather than a leftover. A child position holds a term, so a reader recursing into one calls
 * `codecOfTerm`, which memoises on the frozen term and answers the codec that was already built.
 * A `Term` parameter instead moves the `.def` read from one place inside each of them out to
 * every call site.
 *
 * This is a section note and deliberately not a docstring: it binds to no declaration, so it
 * opens with one star rather than two. `docstring_anchor.py` is the check a doc comment here
 * would trip.
 */

/**
 * The kinds of value a codec can be given, as coarsely as a runtime check can tell them apart.
 *
 * **The codomain of {@link shapeOf}, which classifies a *value*.** That is what fixes the alphabet
 * and why it cannot be finer: `shapeOf` sees a `Set` and answers `'set'`, because telling `strSet`
 * from `numSet` means inspecting the elements, and **an empty `Set` belongs to no family at all**.
 * The same asymmetry decides which containers separate at `union`.
 *
 * {@link SetSlot} is the finer alphabet and is not a replacement. A term knows its base, so `occV`
 * can answer `strSet`; a value does not carry one, so no total function takes a value to a `SetSlot`.
 * The two are the codomains of two different functions rather than two spellings of one, which is
 * the answer to the question `1060c01` left open.
 */
export type Shape =
    | 'string'
    | 'number'
    | 'boolean'
    | 'binary'
    | 'set'
    | 'array'
    | 'map'
    | 'null'

/**
 * The `Value` **constructor** a term can write — {@link Shape} with the three set families split.
 *
 * The model's `SetSlot`, and the split is the whole of its content: `Kind` collapses `strSet`, `numSet`
 * and `binSet` to one label, so `set(string)` and `set(number)` are indistinguishable to it, while
 * the ten constructors tell them apart. `union(set(string), set(number))` is certified by this and
 * was not by the coarser label — which is the correction §5 recorded when the kind tables went, and
 * this is that correction reaching `src/`.
 *
 * **The codomain of `occV`, which reads a *term*.** The split is available here precisely because a
 * term carries its base. {@link Shape} is the value side's alphabet and stays coarse for the reason
 * written there, so this does not replace it: the two answer different questions.
 */
export type SetSlot = Exclude<Shape, 'set'> | 'strSet' | 'numSet' | 'binSet'

/**
 * What one declared attribute decides, read where the field is held.
 *
 * §4's two marks answer differently and neither is the codec's answer. A name that may be absent
 * decides nothing about a key, because a key built from it would have no value to build from in the
 * rows that omit it. A stand-in is written always, so what it stands in for still decides.
 *
 * A reader of the term alone does not answer this. A term is what a codec has, a field is not a
 * codec, and the body is what holds a field — so this reads the mark first and the term second.
 */
export const constantOf = (declared: ObjectSlot): unknown => {
    const def = declared.def
    if (
        'mark' in def &&
        (def.mark === 'optional' || def.mark === 'undefinable')
    )
        return undefined
    const t = 'mark' in def ? def.t : def
    // **A single-valued literal decides; two admissible values narrow without deciding.** This was
    // `decides`, a reader that walked the definition to answer it, and the term answers the same
    // row — deliberately *not* through the wrappers `member` descends: a constant is a claim about
    // the value, and `refine` can reject it, `withLegacyRead` can decode an older encoding into something
    // else, and `optional` admits absence, which is not the value. `withLegacyRead` is the one that keeps
    // it, always writing the attribute at a value typed to the same alternative.
    //
    // **An adapter is the second that keeps it**, and it has to be: `number` and `decimal` are
    // adapters over the one numeric base now, so a numeric discriminator is a literal under a
    // `held` and reading only the bare row would have lost every one of them. The value is the
    // caller's rather than the carrier's, so it is the inner literal's put back through the
    // adapter — well defined because `held` owes that the pair cancels.
    if (t.kind === 'held' && t.inner.kind === 'literal') {
        return (t.g as (held: unknown) => unknown)(t.inner.v)
    }
    return t.kind === 'literal' ? t.v : undefined
}

/* ── the seam: a definition, as the term it denotes ───────────────────────────────────── */

/**
 * Every codec a segment can reach, which is more than one exactly where a union's variants
 * disagree about it.
 *
 * A union is the only definition that branches, and what it branches into is a *set of codecs* —
 * not a codec. This used to be a `Def` kind, a pseudo-codec whose `encode` and `decode` both
 * threw, which meant every reader of a definition had to know about a definition that was not one.
 * The disagreement belongs to the walk, so it is the walk that carries it.
 */
const childrenOf = (
    codec: AnyCodec,
    segment: string | number,
): readonly AnyCodec[] => {
    const def = codec.def
    const one = (child: AnyCodec | undefined) => (child ? [child] : [])
    switch (def.kind) {
        // a name the body does not declare falls in the open block, where there is one
        case 'object': {
            const { fields, rest } = def.body
            const field = fields[String(segment)]
            return one(field ? codecOfTerm(field.t) : rest && codecOfTerm(rest))
        }
        // a set is unordered, so no document path addresses a member of one — `set` never offered
        // a child either, and refusing here is what keeps a meaningless path from compiling
        case 'list': {
            // **A suffix refuses every position past the prefix.** Which codec holds position `n`
            // depends on how long the value is, because the suffix aligns from the right, and a
            // path is written without a length. The prefix is the part a path can address whatever
            // the value, so that is the part addressed here
            const index = Number(segment)
            const at =
                def.pre[index] ??
                (def.suf.length === 0 ? def.spread : undefined)
            return one(at ? codecOfTerm(at) : undefined)
        }
        case 'union':
            return acrossVariants(
                def.options.map((option) => codecOfTerm(option)),
                segment,
            )
        case 'refine':
        case 'legacy':
            return childrenOf(codecOfTerm(def.inner), segment)
        case 'lazy':
            return childrenOf(codecOfTerm(def.get()), segment)
        default:
            return []
    }
}

/** What the variants reach, deduplicated — `Set` keeps insertion order, so the first declared wins. */
const acrossVariants = (
    variants: readonly AnyCodec[],
    segment: string | number,
): readonly AnyCodec[] => [
    ...new Set(variants.flatMap((variant) => childrenOf(variant, segment))),
]

/**
 * A path several variants declare differently, which is still a path.
 *
 * `path()` and `segments` are as well defined here as anywhere — knowing where an attribute lives
 * does not require knowing what writes it, and that is what `at` is most often for. Only the codec
 * half is missing, so only the codec half fails.
 *
 * It says **`never`**, the term that admits no value, and that is what this is: both halves throw,
 * so no value is written and no attribute is read. It used to be a `Def` kind of its own called
 * `branch`, so a definition language for codecs contained an entry that was not a codec and every
 * reader had to know about it; and it used to carry no definition at all, which stopped being
 * available when `def` became required. It then said `custom`, a pair of functions with no
 * structure beneath them, which is gone: a caller reaches `held` over the codec the values really
 * sit on, and the term left with the constructor. `never` costs no reader a case and states the
 * fact rather than hiding it behind a throw — `member` and `carries` say nothing here, exactly as
 * they said nothing at a missing definition, and `accepts` declines to claim instead of reaching
 * the same `false` by catching.
 */
const unresolvedAt = (path: string): AnyCodec => {
    const unresolved = () => {
        throw new CodecError(
            `'${path}' is declared differently in different variants, so this path cannot say which codec to encode with. Reach for the variant you mean — \`variant(...)\` is an item codec with its own \`at\` — or narrow the entity so only one variant declares it.`,
        )
    }
    return codec<never, AttributeValue>({
        def: { kind: 'never' },
        encode: unresolved,
        decode: unresolved,
    })
}

/** A map of attribute name to codec — what `item`, `map` and each `tagged` variant hold. */
export type Attributes = Readonly<Record<string, AnyCodec>>

/** What {@link refine} narrowed with, for a generator that has to satisfy it. */
export type Refinement = {
    readonly is: (value: never) => boolean
    readonly what: string
    readonly arbitrary?: (rng: Rng, size: number) => unknown
    readonly onThinSearch?: (what: string, rate: number) => void
}

// ── scalars ─────────────────────────────────────────────────────────

/**
 * The ground terms a literal can sit at.
 *
 * **Named by the caller, never guessed.** `literal(...)` read its carrier off the JS type of its
 * arguments — digits meant `N`, text meant `S` — and that was the one place in this library where a
 * term's member followed from its *values* rather than from its name. That constructor is now
 * removed, not merely deprecated: a literal is a capability of the primitive that names the base,
 * so `string('A')`, `number(1)` and `decimal('1')` each say which ground term they narrow.
 *
 * The list is §3's `GroundKind` **minus `null`**. It read "plus `decimal`" while `GroundKind` was
 * `string | number | boolean | binary | null`; `decimal` is a ground base in the model now, so the
 * difference is the other way round and it is a stratification one — `nullValue` is a codec and
 * `nullValue()` is not a literal anyone can write, because the only nonempty subset of `Unit` is
 * `Unit`.
 */
export type LiteralBase = 'string' | 'number' | 'boolean' | 'binary'

/** An alternative, at whichever base carries it. */
export type LiteralValue = string | DynamoNumber | boolean | Uint8Array

/**
 * The bases a native set can be built from — `SetBase`.
 *
 * `boolean` is the one base with no set: DynamoDB has `SS`, `NS` and `BS`, and no `BOOLS`. Four
 * bases onto three wire members, because `number` and `decimal` are both real and neither is a
 * legacy spelling of the other.
 */
export type SetBase = Exclude<LiteralBase, 'boolean'>

/**
 * §3 `(literal)`'s `ℓ`, checked: non-empty and pairwise distinct.
 *
 * **The model gets three guarantees from a type and the host's type gives two.** `ls` is a
 * `NEFinset k.Carrier`, so the base indexes the alternatives, `n ≥ 1` holds, and no two are equal —
 * all three from `NEFinset`. `term.ts`'s {@link Literal} buys the first from a discriminated union
 * over the base and the second from a tuple head. **TypeScript cannot say the third**, so it is a
 * refusal at construction, and this is where it lives.
 *
 * Distinctness is not tidiness. `NEFinset` is a *set*, so `literal(k, {'A','A'})` and
 * `literal(k, {'A'})` are one term in the model and two definitions here — and the second names a
 * cardinality the first does not, which is what {@link constantOf} reads to answer whether a literal
 * has exactly one value. A repeated alternative makes a two-element `ls` that admits one value,
 * and the constant would go unrecognised.
 *
 * Compared with {@link sameLiteral}, which compares the way the base compares: bytes for `binary`,
 * `===` otherwise.
 */
const someAlternatives = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): readonly T[] => {
    if (allowed.length === 0) {
        throw new CodecError(
            `a literal admits one of a non-empty set of values, and \`${base}()\` names none; pass the values, or use \`${base}\` itself if anything is admissible`,
        )
    }
    // the values rather than the indices, so the pair is two `T`s and not two lookups the checker
    // has to be told about; `at` recovers the position the message names
    for (const [i, one] of allowed.entries()) {
        for (const [after, other] of allowed.slice(i + 1).entries()) {
            if (sameLiteral(one, other)) {
                const at = i + 1 + after
                throw new CodecError(
                    `a literal's alternatives are a *set*, and \`${base}()\` names the same value at positions ${i} and ${at}; the model's \`NEFinset\` cannot hold it twice, and a repeat makes a two-value literal that admits one — which stops it reading as a constant`,
                )
            }
        }
    }
    return allowed
}

/**
 * Where a literal is stored, which follows from what it holds.
 *
 * Non-distributive on purpose: `'A' | 'B'` is `S`, `0 | 1` is `N`, and a set mixing the two is
 * `never` — a codec cannot write two members, and the type says so before the constructor has to.
 *
 * The default of {@link ConstantCodec}'s second parameter, and only the default. `decimal('1')`
 * holds a string and stores `N`, so it passes its attribute explicitly: this type is the *guess*
 * the new surface exists to stop making, kept because {@link literal} still makes it.
 */
export type LiteralAttribute<T> = [T] extends [string]
    ? Attribute<'S'>
    : [T] extends [number]
      ? Attribute<'N'>
      : never

/**
 * A literal with exactly one admissible value.
 *
 * Its own type records the value, which is what lets a caller that has no entity in hand — a key
 * being rebuilt, say — read the value off the schema rather than be handed it. A literal of two
 * or more values is an ordinary {@link AttributeCodec}: it narrows what is admissible without
 * deciding it.
 *
 * `constant` is a **type-level** brand and carries no runtime property; {@link constantOf} is what
 * reads the value back at runtime.
 */
export type ConstantCodec<
    T,
    A extends AttributeValue = T extends LiteralValue
        ? LiteralAttribute<T>
        : AttributeValue,
> = AttributeCodec<T, A> & { readonly constant: T }

/**
 * The `.set()` capability, on the four bases that have one.
 *
 * `base.set()` is the whole base; `base.set(...values)` is a set of a literal at it. Both are the
 * same {@link set} underneath, which is what keeps there being one set combinator rather than two.
 */
const setCapability =
    (base: SetBase, ground: () => AnyCodec) =>
    (...allowed: readonly LiteralValue[]) =>
        // the *public* codec, reached through a thunk because it is the constant being defined:
        // `string.set()` and the set of that same base should be the same codec, definition
        // included, and a second element object built from the same closures would compare unequal
        set(
            (allowed.length
                ? literalCodec(base, allowed)
                : ground()) as AnyCodec,
        )

/** The literal capability, on every base. */
const literalCapability =
    (base: LiteralBase) =>
    (...allowed: readonly LiteralValue[]) =>
        literalCodec(base, someAlternatives(base, allowed))

/**
 * A string, as `S`. Exact in both directions: DynamoDB does not normalise strings.
 *
 * ```ts
 * string              // any string
 * string('A')         // exactly 'A', and its type says so
 * string('A', 'B')    // one of two
 * string.set()        // SS
 * string.set('A', 'B')// SS whose members are checked
 * ```
 *
 * Callable *and* a codec, the same {@link opaque} trick and for the same reason: `string.encode`
 * and `string('A')` are one name for one ground term, rather than a codec and a constructor that
 * have to be kept in step.
 */
export type StringCodec = AttributeCodec<string, Attribute<'S'>> & {
    <const T extends string>(only: T): ConstantCodec<T, Attribute<'S'>>
    <const T extends string>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'S'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<string>, SS>
        <const T extends string>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, SS>
    }
}

/* ── §3's terms, denoted ──────────────────────────────────────────────────────────────── */

const stringCodec: AttributeCodec<string, Attribute<'S'>> = codecOfTerm({
    kind: 'string',
})

/** @see {@link StringCodec} */
export const string: StringCodec = Object.assign(
    literalCapability('string'),
    stringCodec,
    { set: setCapability('string', () => string) },
) as unknown as StringCodec

/**
 * **`N` itself, and the one native numeric term.** DynamoDB's own number, held as
 * {@link DynamoNumber}: exact to 38 significant digits, validated once at construction, and
 * already in the spelling the store returns.
 *
 * ```ts
 * dynamoNumber                       // an exact number
 * dynamoNumber(DynamoNumber.from('1.5'))   // …and a literal at it
 * dynamoNumber.set()                 // NS
 * ```
 *
 * **Three carriers write `N`, and the other two are adapters over this one.** They are no longer
 * terms of their own: a JS float and a decimal string are two ways a caller may hold this, not two
 * things the service stores.
 *
 * | codec | holds | exact | what it costs |
 * | --- | --- | --- | --- |
 * | `dynamoNumber` | {@link DynamoNumber} | yes, 38 digits | the caller builds one |
 * | {@link decimal} | `string` | yes, 38 digits | text the caller re-validates, and refuses a denormal spelling |
 * | {@link number} | JS `number` | no, about 15 digits | rounding, by construction |
 */
export const dynamoNumber: AttributeCodec<DynamoNumber, Attribute<'N'>> & {
    <const T extends DynamoNumber>(only: T): ConstantCodec<T, Attribute<'N'>>
    <const T extends DynamoNumber>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'N'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<DynamoNumber>, NS>
        <const T extends DynamoNumber>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, NS>
    }
} = Object.assign(
    literalCapability('number'),
    codecOfTerm({ kind: 'number' }) as AttributeCodec<
        DynamoNumber,
        Attribute<'N'>
    >,
    { set: setCapability('number', () => dynamoNumber) },
) as never

/**
 * An adapter over {@link dynamoNumber}, one conversion wide, on both halves. `held` is defined
 * further down this file, so the term is built directly; the two are the same construction.
 */
const numericAdapter = <T>(
    inner: Term,
    writes: SetSlot,
    into: (value: T) => Result<DynamoNumber>,
    outOf: (held: DynamoNumber) => Result<T>,
    via?: 'decimalText',
): AttributeCodec<T, Attribute<'N'>> =>
    codecOfTerm<T, Attribute<'N'>>({
        kind: 'held',
        inner,
        f: into as (value: never) => unknown,
        g: outOf as (held: never) => unknown,
        writes: [writes],
        ...(via ? { via } : {}),
    })

/** …and the same over a set of them, element by element. */
const numericSetAdapter = <T>(
    inner: Term,
    writes: SetSlot,
    into: (value: T) => Result<DynamoNumber>,
    outOf: (held: DynamoNumber) => Result<T>,
): AttributeCodec<ReadonlySet<T>, NS> =>
    codecOfTerm<ReadonlySet<T>, NS>({
        kind: 'held',
        writes: [writes],
        // what the set-level halves below are built from, kept so a reader that needs one element
        // does not have to rediscover it from a conversion over a whole set
        element: {
            f: into as (value: never) => unknown,
            g: outOf as (held: never) => unknown,
        },
        inner,
        f: ((value: ReadonlySet<T>) => {
            const held = new Set<DynamoNumber>()
            for (const each of value) {
                const one = into(each)
                if (failed(one)) return one
                held.add(one)
            }
            return held
        }) as (value: never) => unknown,
        g: ((held: ReadonlySet<DynamoNumber>) => {
            const out = new Set<T>()
            for (const each of held) {
                const one = outOf(each)
                if (failed(one)) return one
                out.add(one)
            }
            return out
        }) as (held: never) => unknown,
    })

/**
 * The digits a caller wrote, refused rather than re-spelled.
 *
 * **The type is checked here and not by `isStoredNumeral`.** That predicate tests a pattern, and a
 * pattern coerces: `['1']` and any object whose `toString` spells a numeral both match it, so
 * `decimal` admitted values its own type excludes and wrote them as `N`. The predicate is right to
 * stay a predicate on `string` — the emitter recognises it by reference — so the boundary is here.
 */
const storedOnly = (value: string): Result<DynamoNumber> =>
    typeof value !== 'string'
        ? new CodecError(
              `${describeShape(value)} is not a string, and \`decimal\` holds the digits as text — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
          )
        : isStoredNumeral(value)
          ? DynamoNumber.from(value)
          : new CodecError(
                `'${value}' is not a numeral DynamoDB stores unchanged; it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
            )

/**
 * A decimal held as a string, stored as `N`. The codec for money — nothing becomes a JS number, so
 * nothing rounds.
 *
 * **An adapter over {@link dynamoNumber}, not a base of its own.** `decimal` was a second ground
 * base at `N` and is a change of carrier now: the same number, handed to the caller as text.
 *
 * **Only the form DynamoDB stores.** It normalises what it accepts — `'1.50'` becomes `'1.5'`,
 * `'007'` becomes `'7'`, `'1e5'` becomes `'100000'` — and this codec hands back the digits, so
 * anything else would come back as a different string from the one written. That is a round trip
 * failing across the database, where neither the type nor the law suite can see it, so it is
 * refused at the point where it is still local: `encode` rejects a denormal numeral rather than
 * quietly rewriting it, because rewriting is how you lose track of which value was meant.
 *
 * That refusal is this codec's and not the carrier's. {@link DynamoNumber} normalises, because it
 * holds a number; this hands back text, so it refuses instead.
 *
 * `'1.50'` is not a price this codec will write. `'1.5'` is. Where exact digits matter more than
 * numeric ordering — trailing zeros that mean something — use {@link string}.
 */
export const decimal: AttributeCodec<string, Attribute<'N'>> & {
    <const T extends string>(only: T): ConstantCodec<T, Attribute<'N'>>
    <const T extends string>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'N'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<string>, NS>
        <const T extends string>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, NS>
    }
} = Object.assign(
    (...allowed: readonly string[]) =>
        numericAdapter<string>(
            termOf(
                literalCapability('number')(
                    ...allowed.map((one) => orThrow(storedOnly(one))),
                ) as AnyCodec,
            ),
            'string',
            storedOnly,
            (held) => held.toString(),
            'decimalText',
        ),
    numericAdapter<string>(
        { kind: 'number' },
        'string',
        storedOnly,
        (held) => held.toString(),
        'decimalText',
    ),
    {
        set: (...allowed: readonly string[]) =>
            numericSetAdapter<string>(
                termOf(
                    (allowed.length
                        ? dynamoNumber.set(
                              ...allowed.map((one) => orThrow(storedOnly(one))),
                          )
                        : dynamoNumber.set()) as AnyCodec,
                ),
                'strSet',
                storedOnly,
                (held) => held.toString(),
            ),
    },
) as never

/** A JS number, as the carrier refuses it. */
const asFloat = (value: number): Result<DynamoNumber> =>
    DynamoNumber.fromNumber(value)

/**
 * The alternatives a numeric literal names, refused at the caller's level first.
 *
 * **Two refusals, and the adapter owes both.** A value that is not a number at all is
 * `literalTerm`'s sentence one base down, and it is about the caller's type. A number outside what
 * `N` holds is the carrier's. The conversion runs before the native literal is built, so without
 * this the carrier would answer for the type and `number(0, 'A')` would report a `NaN` rule.
 *
 * **Every value outside the range is named, not the first.** A caller who writes three bad
 * alternatives fixes three. One bad alternative keeps the carrier's own sentence, which already
 * says which rule it broke.
 */
const numericAlternatives = (
    allowed: readonly number[],
): readonly DynamoNumber[] => {
    const held: DynamoNumber[] = []
    const outside: number[] = []
    let firstRefusal: CodecError | undefined
    for (const one of allowed) {
        if (typeof one !== 'number') {
            throw new CodecError(
                `\`number(...)\` admits ${literalShape.number} values, and ${namedLiteral(one)} is not one`,
            )
        }
        const carried = asFloat(one)
        if (failed(carried)) {
            outside.push(one)
            firstRefusal ??= carried
        } else {
            held.push(carried)
        }
    }
    if (outside.length === 1 && firstRefusal) throw firstRefusal
    if (outside.length > 1) {
        throw new CodecError(
            `${outside.map(namedLiteral).join(', ')} are not numbers DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN and no Infinity`,
        )
    }
    return held
}

/**
 * …and back, refused where the rounding leaves the range `N` holds.
 *
 * `N` carries 38 significant digits and a JS `number` about 15, so reading rounds. Rounding is this
 * codec's declared cost and not a failure. Rounding *out of the range DynamoDB stores* is a
 * different fact: the value read back is one this same codec would refuse to write, so the round
 * trip breaks on a numeral the service genuinely returns. The write half already refuses it, and
 * this half says the same thing rather than hand back a number that cannot go home.
 */
const asJsNumber = (held: DynamoNumber): Result<number> => {
    const value = held.toNumber()
    return failed(DynamoNumber.fromNumber(value))
        ? new CodecError(
              `'${held.toString()}' rounds to ${String(value)}, which is outside what DynamoDB stores, so \`number\` cannot write it back; read this attribute with \`dynamoNumber\` or \`decimal\`, which do not round`,
          )
        : value
}

/**
 * A JS number, stored as `N`. Lossy by construction — `N` carries 38 digits, `number` about 15.
 * Right for enums, counts and flags; wrong for money, which is {@link decimal}.
 *
 * **An adapter over {@link dynamoNumber}, not a base of its own**, and the conversion is where the
 * loss is: the float has already rounded before this codec sees it. `number.set()` and
 * `decimal.set()` are two carriers over one wire set rather than two set bases, which is why
 * `SetBase` no longer has a `decimal`.
 */
export const number: AttributeCodec<number, Attribute<'N'>> & {
    <const T extends number>(only: T): ConstantCodec<T, Attribute<'N'>>
    <const T extends number>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'N'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<number>, NS>
        <const T extends number>(
            ...allowed: readonly T[]
        ): AttributeCodec<ReadonlySet<T>, NS>
    }
} = Object.assign(
    (...allowed: readonly number[]) =>
        numericAdapter<number>(
            termOf(
                literalCapability('number')(
                    ...numericAlternatives(allowed),
                ) as AnyCodec,
            ),
            'number',
            asFloat,
            asJsNumber,
        ),
    numericAdapter<number>({ kind: 'number' }, 'number', asFloat, asJsNumber),
    {
        set: (...allowed: readonly number[]) =>
            numericSetAdapter<number>(
                termOf(
                    (allowed.length
                        ? dynamoNumber.set(...numericAlternatives(allowed))
                        : dynamoNumber.set()) as AnyCodec,
                ),
                'numSet',
                asFloat,
                asJsNumber,
            ),
    },
) as never

/**
 * A boolean, as `BOOL`.
 *
 * `boolean(true)` is a literal at `BOOL`, which nothing on the old surface could spell —
 * `literal(...)` took a string or a number and there was no third option. There is deliberately no
 * `boolean.set()`: DynamoDB has `SS`, `NS` and `BS`, and no set of booleans.
 */
export type BooleanCodec = AttributeCodec<boolean, Attribute<'BOOL'>> & {
    <const T extends boolean>(only: T): ConstantCodec<T, Attribute<'BOOL'>>
    <const T extends boolean>(
        ...allowed: readonly T[]
    ): AttributeCodec<T, Attribute<'BOOL'>>
}

const booleanCodec: AttributeCodec<boolean, Attribute<'BOOL'>> = codecOfTerm({
    kind: 'boolean',
})

/** @see {@link BooleanCodec} */
export const boolean: BooleanCodec = Object.assign(
    literalCapability('boolean'),
    booleanCodec,
) as unknown as BooleanCodec

/**
 * The `NULL` point: the one value `null`, stored as `⟨NULL, ∗⟩`.
 *
 * Named `nullValue` because `null` is a keyword and `NULL` is already the attribute type. It says
 * what it holds, which is the whole of it — one value.
 *
 * What it is for: a tombstone, and a payload-free option of a discriminated union. Before it, a
 * schema could say "this attribute is a string" or "this attribute is optional", and could not say
 * "this attribute is exactly `NULL`" — the value language had `null` and the attribute domain had
 * `NULL`, and no codec denoted either. That gap was found by asking whether `nullable(c)` could be
 * written as `union(c, nullValue)`; it could not, because the right-hand side was not expressible.
 *
 * Distinct from {@link nullable}, which *adds* `null` to another codec's held set. This holds
 * nothing else.
 *
 * Not callable, and there is nothing for it to be: the model's `GroundKind.null` has carrier `Unit`,
 * so `literal .null` can say nothing this codec does not already say.
 */
export const nullValue: AttributeCodec<null, Attribute<'NULL'>> = codecOfTerm({
    kind: 'null',
})

/**
 * Binary, as `B`.
 *
 * `binary(bytes)` compares **by bytes**, not by reference — two `Uint8Array`s holding the same
 * octets are the same alternative, and a decoded value comes back as the member of `ℓ` rather than
 * as the array that was read off the wire.
 */
export type BinaryCodec = AttributeCodec<Uint8Array, Attribute<'B'>> & {
    (only: Uint8Array): ConstantCodec<Uint8Array, Attribute<'B'>>
    (
        ...allowed: readonly Uint8Array[]
    ): AttributeCodec<Uint8Array, Attribute<'B'>>
    readonly set: {
        (): AttributeCodec<ReadonlySet<Uint8Array>, BS>
        (
            ...allowed: readonly Uint8Array[]
        ): AttributeCodec<ReadonlySet<Uint8Array>, BS>
    }
}

const binaryCodec: AttributeCodec<Uint8Array, Attribute<'B'>> = codecOfTerm({
    kind: 'binary',
})

/** @see {@link BinaryCodec} */
export const binary: BinaryCodec = Object.assign(
    literalCapability('binary'),
    binaryCodec,
    { set: setCapability('binary', () => binary) },
) as unknown as BinaryCodec

// ── collections ─────────────────────────────────────────────────────

/**
 * A non-empty set, stored as the native set its members belong to.
 *
 * **The one set builder, and it is internal.** Every set in the surface comes through here:
 * `string.set()` and the other three bases via {@link setCapability}, and everything that reduces
 * to a base via {@link setCapable} — `amount.set()` where `amount = refine(decimal, isAmount)`.
 * It was exported as `set(element)` and is not any more: the capability propagates, so a
 * free-standing form said nothing `.set()` cannot, and having two spellings of one combinator on
 * the surface meant two things to keep in step. It stays a function rather than being inlined
 * because it is where both halves of §3 `(set)`'s premise are checked, and they are checked once.
 *
 * Which set follows from the element's member: `SS`, `NS` or `BS`. Taking a codec rather than being
 * fixed to strings is what makes `price.set()` decode back as prices.
 *
 * **Order is not preserved.** A DynamoDB set comes back in an order the service chooses, so both
 * directions sort. `decode ∘ encode = id` therefore holds only for canonical values; for the rest
 * the law is {@link checkStable}. If order carries meaning use `array(...)`.
 *
 * **Empty is not representable** — encode throws rather than writing what the service refuses.
 */
const set = <const C extends AnyCodec>(
    element: C,
): AttributeCodec<ReadonlySet<Decoded<C>>, SetOf<C>> => {
    type T = Decoded<C>
    const inner = element as unknown as AttributeCodec<T>
    // the member the element stores, read off its term — the deleted reader asked the definition and the
    // two answer the same rows, but only the term's answer survives the reader going
    const member = memberOf(inner.def)
    if (member !== 'S' && member !== 'N' && member !== 'B') {
        throw new CodecError(
            `a set holds strings, numbers or binary, and this element writes ${member ? `'${member}'` : 'no single member'}`,
        )
    }
    /**
     * …and the element reduces to one of the four bases a stored set is built from.
     *
     * The member check above is §3 `(set)`'s premise as it *was* — `setMember μ = some μS` — and it
     * is not enough, because `member` reads through wrappers that a set has no way to record.
     * a set of `held(string, f, g)` passed it: `held` writes where its inner term does, so the member
     * was `'S'`, and the adapter's two functions then ran per member of an attribute that stores no
     * such thing. The model closed this by indexing `Term.set` with a `SetBase`
     * and says outright what that gives up — a set of a `withLegacyRead`, which has no set-level
     * spelling. A set of a `held` was given up on the same ground and is not: an adapter is
     * elementwise, so mapping it over the wire set IS the spelling, and `decimal.set()` needs it
     * now that `decimal` is an adapter rather than a base.
     *
     * `refine` and a literal are **not** given up: a restriction of the elements is a restriction of
     * the set, and `setCodec_restrict` and `setCodec_restrict_p` prove the two are one pair on both
     * halves. So the walk reads through those two and nothing else.
     *
     * **Asked of the element's term, not of the element's codec.** `set` takes a base now, and the
     * base is a fact about the term — the same walk that decides how the conversion spells this
     * set, so the guard and the spelling cannot answer differently.
     */
    const base = setBaseOf(inner.def)
    if (base === undefined) {
        throw new CodecError(
            `a set's element must be one of the four bases a stored set is built from — \`string\`, \`number\`, \`decimal\` or \`binary\`, narrowed by \`refine\` or by a literal — and this element is a \`${inner.def?.kind ?? 'codec with no definition'}\`, which writes '${member}' by reading through to something else. A set of it has nothing DynamoDB stores`,
        )
    }
    /**
     * §3 `(set)` is indexed by the **base**, so a restricted element is spelled as a restriction of
     * the *set*: `string.set('a','b')` is `refine(set(string), each(members …))` and
     * `refine(decimal, q).set()` is `refine(set(decimal), each(closure q))`. `each` is `liftQ` at
     * the term level — every element of the wire set satisfies the element's own predicate — and
     * `setCodec_restrict` and `setCodec_restrict_p` prove the two spellings are one pair on both
     * halves. One `refine` per predicate the element carries, outermost first.
     */
    const bare: Term = { kind: 'set', base }
    /**
     * **An adapter on the element is mapped over the set**, which is the set-level spelling this
     * used to say did not exist. `number` and `decimal` are adapters over the one numeric base
     * now, so `decimal.set()` and `refine(decimal, q).set()` both arrive here carrying one, and
     * refusing them would take two published capabilities.
     *
     * The order is forced and is the alternating stack's: the wire set is converted first, then
     * the element predicates run, because a predicate a caller wrote tests the value the caller
     * holds and not the one the table does.
     */
    const adapter = elementAdapter(inner.def)
    const adapted: Term = adapter
        ? {
              kind: 'held',
              inner: bare,
              // the pair the two halves below are built from, kept so a reader that needs one
              // element does not have to rediscover it from a conversion over a whole set
              element: adapter,
              f: ((value: ReadonlySet<unknown>) => {
                  const held = new Set<unknown>()
                  for (const each of value) {
                      const one = (adapter.f as (v: unknown) => unknown)(each)
                      if (failed(one)) return one
                      held.add(one)
                  }
                  return held
              }) as (value: never) => unknown,
              g: ((held: ReadonlySet<unknown>) =>
                  new Set(
                      [...held].map(adapter.g as (v: unknown) => unknown),
                  )) as (held: never) => unknown,
          }
        : bare
    const term = elementPredicates(inner.def).reduceRight<Term>(
        (restricted, of) => ({
            kind: 'refine',
            inner: restricted,
            q: { kind: 'each', of },
        }),
        adapted,
    )
    return codecOfTerm<ReadonlySet<T>, SetOf<C>>(term)
}

/**
 * A homogeneous positional container, as `L`.
 *
 * `list(spread(c))` says the same thing, and this says it in one word for the common case. A
 * `never` element is admitted rather than refused: the spread is not a slot, so an array of
 * nothing is the empty list, which is a value.
 */
export const array = <const C extends AnyCodec>(
    element: C,
): AttributeCodec<readonly Decoded<C>[], L<AttributeOf<C>>> => {
    type T = Decoded<C>
    return codecOfTerm<readonly T[], L<AttributeOf<C>>>({
        kind: 'list',
        pre: [],
        spread: termOf(element as unknown as AnyCodec),
        suf: [],
    })
}

/**
 * A declaration that fills a **slot** with a term holding no value.
 *
 * A slot is a position a value must fill: a declared element of a list, and a `req` or `withLegacyRead`
 * field. `optional` and `undefinable` are not slots, because the key may be absent. A list's
 * spread is not one either, because a value of the declared length omits it.
 */
type IsNeverSlot<D> = [D] extends [{ readonly [optionalMarker]: true }]
    ? false
    : [D] extends [
            { readonly codec: { readonly def: { readonly kind: 'never' } } },
        ]
      ? true
      : [D] extends [{ readonly def: { readonly kind: 'never' } }]
        ? true
        : false

/**
 * Whether any **declared** position of a list is `never`.
 *
 * The spread is not asked, because the spread is not a slot: a value of exactly the declared
 * length omits every spread position, so a spread at the bottom is the list of its declared
 * positions and that is a value. `Term.listOf` normalises the declared positions for the same
 * reason and leaves the spread alone.
 */
type ListNeverSlot<Cs extends readonly unknown[]> = Cs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? H extends AnySpread
        ? ListNeverSlot<T>
        : IsNeverSlot<H> extends true
          ? true
          : ListNeverSlot<T>
    : false

/**
 * Nothing, or why this list can hold no value.
 *
 * **The model types a list with a `never` position and gives it an empty held set, which is
 * correct there.** The host refuses it instead, because a position nothing fills makes the whole
 * list unconstructible and `never` already names that term: a declaration with two spellings, one
 * of them a trap, is the shape a constructor should not have.
 *
 * The spread is exempt, and that is the same rule read the other way: it is not a slot, so a list
 * whose spread is `never` is the list of its declared positions, and that is a value.
 */
type NoNeverSlot<Cs extends readonly unknown[]> = ListNeverSlot<Cs> extends true
    ? ErrorMessage<'[list] a declared position is `never`, so nothing fills it and the list holds no value at all. Use `never` itself if that is what you meant'>
    : unknown

/**
 * A positional container: the elements in order, with at most one {@link spread} among them.
 *
 * The call reads as the type it builds. `list(string, spread(decimal), boolean)` is
 * `readonly [string, ...string[], boolean]`, position for position, so a reader checks the
 * declaration against the type without splitting it into parts first.
 *
 * **A spread may sit anywhere, and only once.** It used to have to go last, because the only
 * container that took one was a tuple and a tuple had no suffix. A list has one, so "last" was
 * never the rule: the rule is *once*, and {@link SpreadOnce} states it. Every position after the
 * spread is a fixed element aligned from the right.
 *
 * A value of length `n` is held when `n` is at least the declared positions: the prefix aligns
 * from the left, the suffix from the right, and the middle goes through the spread.
 *
 * @example
 * ```ts
 * list(string, decimal, spread(boolean))  // readonly [string, string, ...boolean[]]
 * list(string, spread(decimal), boolean)  // readonly [string, ...string[], boolean]
 * list(string, decimal)                   // readonly [string, string]
 * list(spread(string))                    // readonly string[], as `array` gives
 * ```
 */
export const list = <const Cs extends readonly (AnyCodec | AnySpread)[]>(
    // asked of the union of the elements rather than mapped over them: one instantiation instead
    // of one per position, and the diagnostic lands on the call either way. Mapping cost +10%
    // across this repo, measured
    ...elements: Cs & SpreadOnce<Cs> & NoNeverSlot<Cs>
): AttributeCodec<ListOf<Cs>, L<ListWrites<Cs>>> => {
    const all = elements as readonly unknown[]

    /**
     * `SpreadOnce` refuses a second spread in the *type*, and a cast defeats the type.
     *
     * The cast is the path that matters: with two spreads the first was read as the spread and
     * the second as a fixed element, so the declaration held a shape nobody wrote.
     */
    const spreads = all.filter(isSpread)
    if (spreads.length > 1) {
        throw new CodecError(
            'a list has at most one spread, and this one has ' +
                `${spreads.length} — the positions after the spread are fixed elements`,
        )
    }

    const at = all.findIndex(isSpread)
    const marked = at === -1 ? undefined : (all[at] as AnySpread)
    const declared = (
        at === -1 ? all : [...all.slice(0, at), ...all.slice(at + 1)]
    ) as readonly AnyCodec[]

    /**
     * **A declared position nothing fills makes the whole list unconstructible.**
     *
     * The model types a list with a `never` position and gives it an empty held set, which is
     * correct as a model. Here it is a declaration with a second spelling for `never`, and one of
     * the two is a trap. `NoNeverSlot` refuses it in the *type*, and a cast defeats the type.
     *
     * The **spread** is not asked, and that is the rule rather than an omission: a value of
     * exactly the declared length omits every spread position, so `list(spread(never))` is the
     * empty list and the empty list is a value. `Term.listOf` draws the same line.
     */
    const deadAt = declared.findIndex((item) => termOf(item).kind === 'never')
    if (deadAt !== -1) {
        throw new CodecError(
            `position ${deadAt} of the declared positions is \`never\`, so nothing fills it and the list holds no value at all — use \`never\` itself if that is what you meant`,
        )
    }

    // as with `map`, the cast keeps the shape each position writes, which
    // `Attribute<'L'>` would flatten to "some list"
    return codecOfTerm({
        kind: 'list',
        pre: (at === -1 ? all : all.slice(0, at)).map((c) =>
            termOf(c as AnyCodec),
        ),
        ...(marked ? { spread: termOf(marked.spread) } : {}),
        suf: (at === -1 ? [] : all.slice(at + 1)).map((c) =>
            termOf(c as AnyCodec),
        ),
    }) as unknown as AttributeCodec<ListOf<Cs>, L<ListWrites<Cs>>>
}

/**
 * The elements split at the one spread: what comes before it, what it marks, and what comes after.
 *
 * Accumulated into `Pre` rather than inferred at a fixed position, because the spread may sit
 * anywhere. The accumulator makes the recursion tail-recursive, which is the form TypeScript
 * unrolls to a thousand elements instead of fifty.
 */
type Split<
    Cs extends readonly unknown[],
    Pre extends readonly unknown[] = [],
> = Cs extends readonly [infer H, ...infer T]
    ? H extends AnySpread
        ? H extends { readonly spread: infer S }
            ? { pre: Pre; spread: S; suf: T }
            : never
        : Split<T, [...Pre, H]>
    : { pre: Pre; spread: undefined; suf: [] }

/**
 * What a list holds: the prefix by position, the spread by repetition, then the suffix by position.
 *
 * Written as two branches on the spread rather than as one type with an empty rest, because
 * `...never[]` in the middle of a tuple type is not the empty middle — it is a tuple no value
 * inhabits.
 */
export type ListOf<Cs extends readonly unknown[]> = Split<Cs> extends {
    pre: infer P extends readonly unknown[]
    spread: infer S
    suf: infer F extends readonly unknown[]
}
    ? S extends AnyCodec
        ? readonly [
              ...{ [I in keyof P]: Decoded<P[I]> },
              ...Decoded<S>[],
              ...{ [I in keyof F]: Decoded<F[I]> },
          ]
        : readonly [
              ...{ [I in keyof P]: Decoded<P[I]> },
              ...{ [I in keyof F]: Decoded<F[I]> },
          ]
    : never

/**
 * The same split, on the stored side.
 *
 * Both sides match the *marker* and then extract with {@link Decoded} and {@link AttributeOf},
 * rather than inferring through `SpreadCodec<…>`. Inferring is the trap: `AttributeCodec` names
 * its value on both sides, so `SpreadCodec<unknown, infer A>` matches nothing and this fell to the
 * fixed-arity branch — a list with a spread typed as though the spread were one element. Silently,
 * because a fixed `[S, N, N]` *is* assignable to `readonly [S, N, ...N[]]`, so an assignment could
 * not tell.
 */
export type ListWrites<Cs extends readonly unknown[]> = Split<Cs> extends {
    pre: infer P extends readonly unknown[]
    spread: infer S
    suf: infer F extends readonly unknown[]
}
    ? S extends AnyCodec
        ? readonly [
              ...{ [I in keyof P]: AttributeOf<P[I]> },
              ...(AttributeOf<S> & AttributeValue)[],
              ...{ [I in keyof F]: AttributeOf<F[I]> },
          ]
        : readonly [
              ...{ [I in keyof P]: AttributeOf<P[I]> },
              ...{ [I in keyof F]: AttributeOf<F[I]> },
          ]
    : never

/**
 * Nothing, or why a spread is not an attribute.
 *
 * An item's members are reached by *name*, so `optional` and `withLegacyRead` belong here — both are
 * statements about a name. `spread` is a statement about a *position*, and there are no positions
 * in a map, so it is the one marker an object member cannot be.
 */
type NoSpreadMember<Spec> = [
    Extract<Spec[keyof Spec], { readonly [spreadMarker]: true }>,
] extends [never]
    ? unknown
    : ErrorMessage<'`spread(...)` is a position in a list, not an attribute: an item has names and not positions'>

/** A field whose mark makes it a slot, declared at a term that holds no value. */
type NoNeverField<Spec> = [
    {
        [K in keyof Spec]: IsNeverSlot<Spec[K]> extends true ? K : never
    }[keyof Spec],
] extends [never]
    ? unknown
    : ErrorMessage<`[object] '${{
          [K in keyof Spec]: IsNeverSlot<Spec[K]> extends true ? K : never
      }[keyof Spec] &
          string}' is declared at \`never\` and the row always writes it, so the object holds no value at all. Mark it \`optional\`, or use \`never\` itself`>

/**
 * Nothing, or why a list carries more than one spread.
 *
 * A spread says "and then any number of these", and a second one has no reading: the positions
 * between the two belong to both. Checked by splitting at the first spread and asking whether
 * anything *after* it is marked, which is one instantiation over the tail rather than one per
 * position.
 */
export type SpreadOnce<Cs extends readonly unknown[]> = Split<Cs> extends {
    suf: infer F extends readonly unknown[]
}
    ? [Extract<F[number], { readonly [spreadMarker]: true }>] extends [never]
        ? unknown
        : ErrorMessage<'a list has at most one `spread(...)` — the positions after it are fixed elements'>
    : unknown

/**
 * A list's repeating positions: *and then any number of these*.
 *
 * The counterpart of `...T[]` in a tuple type, and restricted the same way — it is meaningful only
 * among the elements of a {@link list}, and only once, because the positions between two spreads
 * belong to both. Every other place refuses it, and the type says so rather than a runtime check
 * discovering it.
 *
 * @example
 * ```ts
 * list(string, decimal, spread(boolean))  // readonly [string, string, ...boolean[]]
 * list(string, spread(decimal), boolean)  // readonly [string, ...string[], boolean]
 * list(spread(string))                    // readonly string[], stored as L with no minimum
 * ```
 */
export const spread = <const C extends AnyCodec>(
    element: C,
): SpreadCodec<Decoded<C>, AttributeOf<C> & AttributeValue> =>
    ({ spread: element as unknown as AnyCodec }) as unknown as SpreadCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue
    >

/**
 * Whether this is a spread marker rather than an element — the runtime half of `spreadMarker`.
 *
 * `spreadMarker` is a `declare const` symbol, so it exists in the type and nowhere else, and
 * {@link list} needs an answer at run time. One own property, checked by name.
 */
const isSpread = (element: unknown): element is AnySpread =>
    typeof element === 'object' &&
    element !== null &&
    'spread' in element &&
    // and it is not a codec, which is decidable now that every codec carries a definition: a
    // marker is a position and has no `encode` to call
    !('def' in element)

/**
 * A list's repeating position: the element codec, marked for a position.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A> & { …marker }`, which
 * claimed a marker has an `encode` and a `decode` — true only because the marker was built by
 * spreading its element, so a bare one encoded as its element by accident. A spread is a
 * *position*, and a list is the only thing that has one. It unwraps the marker at construction.
 * Nothing else may be given one, and the type no longer offers a caller the two halves to call.
 */
export type SpreadCodec<T, A extends AttributeValue = AttributeValue> = {
    readonly [spreadMarker]: true
    readonly spread: AttributeCodec<T, A>
}

// ── narrowing ───────────────────────────────────────────────────────

/**
 * Narrows what a codec decodes to, checking it on the way in.
 *
 * Where a brand gets applied. `decimal` cannot stand in for a `Price` because `decode` returns a
 * bare `string` — and a row is data somebody else wrote, so running the brand's own predicate is
 * the right way to get one back, rather than asserting.
 *
 * @example
 * ```ts
 * const price = refine(decimal, isPrice, {
 *     // `decimal` generates negatives, which are not Prices; say what a valid one looks like
 *     arbitrary: (rng) => pick(rng, ['0', '1', '0.5']) as Price,
 * })
 * const petId = refine(string, isPetId)
 * ```
 *
 * **The obligation is `is`, and it is yours.** Like `held`'s pair and `custom`'s two functions,
 * `refine` is sound *iff* the predicate honestly decides `Narrow` — nothing here can check that,
 * because `Narrow` is a type and `is` is a claim about it. What follows from the claim is why the
 * two directions are checked differently:
 *
 * - **`decode` runs `is`.** A stored value was never type-checked — a row is data somebody else
 *   wrote — so the predicate is the only thing between the database and `Narrow`.
 * - **`encode` does not.** Its argument is already a `Narrow`, and TypeScript is what says so.
 *   Re-running `is` would assert nothing the call site had not already asserted.
 *
 * The asymmetry tracks how far the type system's guarantee reaches. Past that edge — `unsafeEncode`
 * still runs `encode`, but an `as` upstream of it is not checked by anything — `refine` will write
 * a value it would refuse to read. {@link literal} checks both directions for exactly that reason:
 * a union can widen a field's type, so the guarantee is not available, and its admissible set is
 * data this library owns, which gives the check an authority a caller's predicate cannot have.
 */
export type Refined<T, A extends AttributeValue> = AttributeCodec<T, A> &
    SetCapable<T, A>

/**
 * `.set()`, where the codec it sits on can be a set's element.
 *
 * The capability {@link setBaseOf} decides at runtime, stated at the type as far as the type can see
 * it — which is not all the way. A codec's *type* is not generic in its definition — every codec
 * carries a `Term`, and none of them carries *which* one at the type — so `refine(...)`'s type
 * knows the attribute and never the base it reduced through. So the gate here is the attribute — `S`, `N` or `B`, the three a stored set is built
 * from — and `refine(held(string, f, g), p).set()` type-checks and throws, because `held` writes
 * `S` and reduces to no base. That gap closes only by making the codec type generic in its
 * definition, which was measured at 481 of 968 signatures and rejected; the runtime refusal in
 * {@link set} is what stands in for it, and is tested at each of the six kinds that reach it.
 *
 * **One member at a time, and each test non-distributive.** Two shorter spellings were tried and
 * both admit `refine(union([string, number]), p).set()`, which is a set of an element writing two
 * members and cannot exist:
 *
 * - `[A] extends [Attribute<'S'> | Attribute<'N'> | Attribute<'B'>]` — a union of admissible
 *   attributes is assignable to a union of them, so it passes.
 * - the same without the tuples, distributing — each arm passes on its own, and the result is
 *   `{ set: () => SS } | { set: () => NS }`, a union whose members all have a `set`, so calling it
 *   is allowed.
 *
 * Asking each member separately, with `[A] extends [...]` so the question is about `A` whole, is
 * what refuses the union: it is not `Attribute<'S'>`, not `Attribute<'N'>` and not
 * `Attribute<'B'>`, so it falls through.
 *
 * `Record<never, never>` rather than `{}` in the last branch: an intersection with it is the codec
 * unchanged, and `{}` means "anything but null", which would make the intersection accept a `.set`
 * this type is declining to give.
 */
export type SetCapable<T, A extends AttributeValue> = [A] extends [
    Attribute<'S'>,
]
    ? { readonly set: () => AttributeCodec<ReadonlySet<T>, SS> }
    : [A] extends [Attribute<'N'>]
      ? { readonly set: () => AttributeCodec<ReadonlySet<T>, NS> }
      : [A] extends [Attribute<'B'>]
        ? { readonly set: () => AttributeCodec<ReadonlySet<T>, BS> }
        : Record<never, never>

/**
 * The `.set()` capability, attached to a codec that is not one of the four bases.
 *
 * The thunk closes over the codec **it returns**, not the one it was handed, and that is the whole
 * of the care needed here: `.set()` records its element in `def`, so a thunk closing over the
 * argument would make `amount.set().def` and `amount.set().def` two definitions that differ by a
 * `set` property nobody can see. Same reason {@link setCapability} reaches its base through a thunk
 * rather than naming the constant it is defining.
 */
const setCapable = <T, A extends AttributeValue>(
    self: AttributeCodec<T, A>,
): Refined<T, A> => {
    const capable = {
        ...self,
        set: () => set(capable as unknown as AnyCodec),
    }
    return capable as unknown as Refined<T, A>
}

export const refine = <Wide, Narrow extends Wide, A extends AttributeValue>(
    inner: AttributeCodec<Wide, A>,
    is: (value: Wide) => value is Narrow,
    options: {
        /**
         * Values satisfying `is`.
         *
         * Optional, but supply it when the inner codec's values rarely pass: generation falls back
         * to filtering, and a predicate that rejects most of what it sees wastes the search.
         */
        readonly arbitrary?: (rng: Rng, size: number) => Narrow
        /** Named in the error when a stored value fails the check. */
        readonly describe?: string
        /**
         * Told when filtering keeps less than half of what it generates, instead of `console.warn`.
         *
         * Only ever called from a generator, so only ever during a property run.
         */
        readonly onThinSearch?: (what: string, rate: number) => void
    } = {},
): Refined<Narrow, A> => {
    const what = options.describe ?? 'the expected form'

    /**
     * Generation falls back to filtering the inner codec's values, and reports when that thins the
     * search badly.
     *
     * `decimal` generates negatives, which are not prices, and fractions, which are not sequence numbers —
     * so a run of a hundred cases can quietly be a run of forty. The declaration is not the place to
     * fix that: a predicate is what a brand *is*, and demanding an example of one beside it would
     * tax every codec for something only a property run cares about. But a run that has been halved
     * without saying so is worth a word, and this can only be reached from a generator, so the word
     * only ever lands in a test.
     */
    // `member` reads through a refinement, which is what lets a set of a brand work; `constantOf`
    // does not, because the predicate may be exactly what rejects the constant.
    //
    // `setCapable` is what carries `.set()` across the refinement, and it is the whole of why the
    // brand survives: `amount.set()` decodes as `ReadonlySet<Price>` because the set is built from
    // `amount`, where the predicate that produces a `Price` already lives.
    return setCapable(
        codecOfTerm<Narrow, A>({
            kind: 'refine',
            inner: termOf(inner as unknown as AnyCodec),
            q: {
                kind: 'closure',
                q: {
                    is: is as (value: never) => boolean,
                    what,
                    arbitrary: options.arbitrary as
                        | ((rng: Rng, size: number) => unknown)
                        | undefined,
                    onThinSearch: options.onThinSearch,
                },
            },
        }),
    )
}

// ── reading what is already there ───────────────────────────────────

/**
 * A field that stands in a value where the attribute is absent.
 *
 * Not a codec, for the reason {@link OptionalCodec} records. The stand-in is the marker's payload at
 * the type level and `def.value` at run time, and the run-time side is the one {@link withLegacyRead}
 * checks against §3 `(withLegacyRead)`.
 */
type MissingCodec<
    T,
    A extends AttributeValue = AttributeValue,
    // the codec the mark is about, carried rather than erased to `AttributeCodec<T, A>`. A brand
    // sits on the codec — `constant` is the one that matters here — and erasing to the two type
    // arguments drops it before a derivation over the spec can ask
    C = AttributeCodec<T, A>,
> = {
    readonly [fallbackMarker]: T
    readonly codec: C
    readonly def: Extract<Field, { readonly mark: 'fallback' }>
}

/**
 * Reads a missing attribute as a value, and writes the attribute always.
 *
 * Not {@link optional}: the entity always has it, the *data* may not — a row written before the
 * attribute existed. Replaces `item.channel ?? 'IN_STORE'` at every read site.
 *
 * **The stand-in must be writable by the codec it stands in for**, and that is checked here, at the
 * declaration. §3 `(withLegacyRead)` carries it as a premise, `ObligationsField`'s `.req` row, and it
 * exists because the proof failed without it: a row missing the attribute reads back as the
 * stand-in, and if the inner codec cannot write that value the item cannot be written back —
 * **(C)** broken at the read, with the refusal surfacing on some later write rather than at the
 * declaration responsible for it. `withLegacyRead({ current: string('A'), whenMissing: 'B' })` is the whole of it.
 *
 * The stand-in is a **value and not a thunk**, which is what makes the check possible here rather
 * than on whichever read happens to need it first. It does not become shared state for that: the
 * declaration holds one value and each read that needs one gets a `structuredClone` of it, so a
 * mutable stand-in still cannot leak between entities. Primitives are handed over as they are,
 * being unable to leak anything.
 */
const withMissing = <const C extends AnyCodec>(
    // the *argument's own* type, not a re-declared `AttributeCodec<T, A>`: the guard has to see the
    // marker the caller passed, and a parameter written in terms of inferred `T` and `A` reconstructs
    // a plain codec that never carries one
    inner: C,
    // `NoInfer` so the codec is the only thing that says what it holds. Inferring from both sites
    // unified them, and a stand-in written `'A'` widens to `string`, which then refused the very
    // codec it stands in for — invisible while the entity was declared first and pinned it itself
    value: NoInfer<Decoded<C>>,
): MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> => {
    // §3 `(withLegacyRead)`: the stand-in must be *writable*, or a row missing the name decodes to a
    // value the item cannot be written back as — (C) broken at the read, with the refusal arriving
    // on the next write instead of at the declaration that caused it. Decidable here, from the
    // declaration alone, which is why the stand-in is a value and not a thunk.
    if (!accepts(inner as unknown as AnyCodec, value)) {
        throw new CodecError(
            `\`withLegacyRead\`'s stand-in must be a value the codec it stands in for can write, and ${describeShape(value)} is not one this \`${(inner as unknown as AnyCodec).def?.kind ?? 'codec'}\` writes. A row missing the attribute would read back as it and then refuse on the way out`,
        )
    }
    const attribute = inner as unknown as AttributeCodec<Decoded<C>>
    return {
        codec: attribute,
        def: { mark: 'fallback', t: termOf(inner), v: value },
    } as unknown as MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C>
}

/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart: an attribute is **stored** as `S`, `N`, `SS` — and it is
 * **held**, in your code, as a `string`, a `Date`, an array. Every other combinator changes the first
 * or narrows the second. This one changes only the second, by naming the two halves of the
 * conversion, and leaves what the table holds exactly as it was.
 *
 * Which makes it the answer to "my values arrive as an array and `.set()` wants a `Set`": nothing
 * about the *table* has to change for that, so nothing about the codec does either. It is also the
 * one to reach for where a caller holds a value the inner codec does not: the member, the
 * generation and the definition all keep coming from the codec underneath, where a codec written
 * by hand has to restate every one of them.
 *
 * @example
 * ```ts
 * // stored as SS, held as an array
 * const tags = held(string.set(), {
 *     encode: (tags: readonly string[]) => new Set(tags),
 *     decode: (tags) => [...tags],
 * })
 *
 * // stored as S, held as a Date
 * const when = held(string, {
 *     encode: (at: Date) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * **Both halves are total.** A conversion that can fail is two things at once, and they compose
 * better apart: narrow the inner codec first, so the failure is reported where the value is actually
 * wrong and with a message about it.
 *
 * ```ts
 * held(refine(string, isIsoDate, { describe: 'an ISO timestamp' }), {
 *     encode: (at: Date) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * The pair must round-trip — `decode(encode(x))` equal to `x`, and `encode(decode(y))` equal to `y` —
 * or the codec's own law does not hold either. `checkRoundTrip` over a spec holding one is what
 * establishes it, and generation reaches through: values are generated for the inner codec and
 * handed out through `decode`, so what is generated is always something the pair produced.
 *
 * **Nothing here checks it, and nothing here can.** The model carries it as `IsoCancels` — a
 * premise, in both directions: `g(f v) = v` wherever `f v` lands writable, and `f(g v) = v` on the
 * writable values themselves. It is a premise there for the same reason it is unchecked here. One
 * direction quantifies over the *held* type, which has no generator except `decode` itself, so
 * every value this library could make is already in the pair's image; and probing the other at
 * construction is worse than not probing it, because a legitimate adapter is an isomorphism on the
 * values its inner codec describes and *throws* off them — `held(string, dateAdapter)` would be
 * refused for `new Date('<anything>')`, which is exactly the narrowing the example above asks for
 * rather than a defect.
 *
 * So this is a written obligation, and `checkIso` is how a caller discharges it: it generates for
 * the inner codec and checks `encode(decode(y))`, which is the half a table depends on. The
 * failure mode it catches, unrefused today and pinned in `codec.laws.spec.ts`, is an adapter that
 * *normalises* — `{ encode: v => v.toUpperCase(), decode: v => v }` reads `'a'` back as `'A'`,
 * and every read-modify-write on that row rewrites the value.
 */
export const held = <T, const C extends AnyCodec>(
    inner: C,
    adapt: {
        /**
         * The value, as the inner codec holds it. Runs on the way to the table.
         *
         * Return a {@link CodecError} where the conversion has nothing to hand over — a value
         * outside the range the inner codec describes, or text that does not parse. That is a
         * refusal like any other and reaches the caller as one.
         */
        readonly encode: (value: T) => Result<NoInfer<Decoded<C>>>
        /** What the inner codec read, as you hold it. Runs on the way back. Refuses the same way. */
        readonly decode: (held: Decoded<C>) => Result<NoInfer<T>>
        /**
         * **How to generate one of these, where the pair is partial.**
         *
         * Omit both and the adapter derives them from the inner codec: a value is generated
         * there and handed out through `decode`, and a value is shrunk there and handed back.
         * That is right while the conversion accepts everything the inner codec produces.
         *
         * State them when it does not. A conversion that refuses part of the inner codec's range
         * makes the derived generator offer values the pair never makes, so a property run fails
         * on the generator instead of on the codec.
         */
        readonly arbitrary?: (rng: Rng, size: number) => T
        /** How to shrink one, where the pair is partial. Derived from the inner codec otherwise. */
        readonly shrink?: (value: T) => readonly T[]
    },
): AttributeCodec<T, AttributeOf<C>> => {
    /**
     * **A half that cannot convert returns a `CodecError`**, and the signature says so. A refusal
     * is a value here, as it is everywhere else on this surface, so nothing about declining a
     * conversion is special and no caller has to catch.
     *
     * The two halves are still the one place in a codec where code this library did not write
     * runs, so the throw stays contained as a backstop rather than as the contract. A conversion
     * is ordinary code and ordinary code throws — `new Set(4)` for an adapter typed to take an
     * array, a `.toISOString()` on something that is not a `Date`. A codec that let that escape
     * would make every caller defensive about it, and one already was: a union tries an option to
     * find out whether it is the right one, and had to catch, which meant it also swallowed
     * failures that were nothing to do with an adapter.
     */
    return codecOfTerm<T, AttributeOf<C>>({
        kind: 'held',
        inner: termOf(inner as unknown as AnyCodec),
        f: adapt.encode,
        g: adapt.decode,
        arbitrary: adapt.arbitrary,
        shrink: adapt.shrink as
            | ((value: never) => readonly unknown[])
            | undefined,
    })
}

/**
 * One direction, which is all an older encoding is ever asked for.
 *
 * `withLegacyRead` never writes through `older` — that is the whole of what makes it a migration rather than
 * a union — so asking for a whole codec there asked for a half nobody calls. It also *forced* one:
 * an older encoding whose held type differs from the current one has to be adapted, and {@link held}
 * requires both halves, so adapting a reader meant writing an encode path that is dead by
 * construction. Every `AttributeCodec<T>` is one of these, so nothing that worked stops working.
 *
 * @example
 * ```ts
 * // stored as N now; some rows still hold the digits as B, from a migration nobody finished
 * withLegacyRead({
 *     current: decimal,
 *     older: { decode: (at) => andThen(binary.decode(at), (b) => decoder.decode(b)) },
 * })
 * ```
 */
export type Reader<T> = {
    readonly decode: (attribute: AttributeValue) => Result<T>
}

/**
 * Reads any of several encodings, writes only `current`.
 *
 * A table holds every shape it has ever held. Reading tolerantly and writing canonically converges:
 * old rows stay readable and every write moves one closer. `decode ∘ encode = id` survives because
 * encode only ever produces `current`.
 *
 * Deliberately breaks {@link checkMembersStable} — changing what is stored *is* the migration — so
 * an index key cannot use it: DynamoDB rejects a write whose index key has the wrong type.
 *
 * @example
 * **One older encoding.** A table that has held three needs two of these, nested — and `withLegacyRead` is
 * itself a {@link Reader}, so it nests directly:
 *
 * ```ts
 * withLegacyRead({ current: decimal, older: withLegacyRead({ current: string, older: fromBytes }) })
 * ```
 *
 * Not a union: {@link union} requires its options to read back as *different* types so that a value
 * says which one it is, and every encoding of one attribute reads back as the same type by
 * definition. Which is the whole difference between the two — a union asks "which of these is it",
 * a migration asks "can any of these still read it".
 *
 * ```ts
 * // stored as N today, and as S in rows written before that; always written as N
 * rate: withLegacyRead({ current: decimal, older: string })
 * ```
 *
 * **Two things §3 asks of the older reader** (`ReadsCoherently`), and only one of them is
 * checkable.
 *
 * `ran(r) ⊆ dom(e)` — a migration lands on values the current encoding can *write*. This is
 * checked, per read, as soon as the older reader has answered, because that is the earliest
 * anything can know what it returns. Unchecked it read a row and refused on the way out, which is
 * **(C)** broken at the migrated row and reported at some later write.
 *
 * Coherence — where both readers read an attribute, they agree — is **not** checkable, and the
 * reason is sharper than that. The current encoding is tried first and the older one only on its
 * failure, here and in the model (`Codec.extendRead`), so on `dom(p_current)` the older reader is
 * never consulted and a disagreement has no observable consequence at all. What the premise buys
 * is that the *ordering does not matter*: with it, this presentation equals the order-free
 * `p ∪ r`. Without it the reading depends on declaration order, which is the one thing §5 says
 * resolution never does. So it is a written obligation, and the thing to check is that two
 * readers of one attribute agree — nothing in this library will tell you they do not.
 */
export type WithLegacyReadOptions<C extends AnyCodec> = {
    readonly current: C
} & (
    | {
          readonly older: Reader<Decoded<C>>
          readonly whenMissing?: NoInfer<Decoded<C>>
      }
    | {
          readonly older?: Reader<Decoded<C>>
          readonly whenMissing: NoInfer<Decoded<C>>
      }
)

/**
 * Reads an older attribute encoding or a missing object attribute.
 *
 * `older` extends an attribute codec's read side. `whenMissing` declares an object slot, because
 * absence belongs to an object map and no attribute codec can read an absent attribute.
 */
export function withLegacyRead<const C extends AnyCodec>(options: {
    readonly current: C
    readonly older: Reader<Decoded<C>>
    readonly whenMissing?: never
}): AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue>
export function withLegacyRead<const C extends AnyCodec>(options: {
    readonly current: C
    readonly older?: Reader<Decoded<C>>
    readonly whenMissing: NoInfer<Decoded<C>>
}): MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C>
export function withLegacyRead<const C extends AnyCodec>(
    options: WithLegacyReadOptions<C>,
):
    | AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue>
    | MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> {
    const { current, older } = options
    const currentCodec = current as unknown as AttributeCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue
    >
    const extended = older
        ? codecOfTerm<Decoded<C>, AttributeOf<C> & AttributeValue>({
              kind: 'legacy',
              inner: termOf(current),
              r: older.decode,
          })
        : currentCodec
    return (
        'whenMissing' in options
            ? withMissing(extended, options.whenMissing as Decoded<C>)
            : extended
    ) as
        | AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue>
        | MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C>
}

/**
 * A codec resolved on first use, so an entity can contain itself.
 *
 * `item()` evaluates its spec eagerly, so a category whose children are categories cannot name
 * itself — the constant is not initialised yet. A thunk defers that to the first encode, decode or
 * path walk, by which time it is.
 *
 * Resolved once and kept. Declares no {@link AttributeCodec.member}: reading one would force
 * resolution at construction, which is the cycle this exists to break, so a lazy codec cannot be a
 * set's element — no loss, since a set holds strings, numbers or binary and none of those recurse.
 *
 * @example
 * ```ts
 * type Category = { name: string; children?: readonly Category[] }
 *
 * const Category: AttributeCodec<Category, Attribute<'M'>> = lazy(() =>
 *     object({ name: string, children: optional(array(Category)) }),
 * )
 * ```
 */
export const lazy = <T, A extends AttributeValue = AttributeValue>(
    get: () => Nestable<T>,
): AttributeCodec<T, A> => {
    let resolved: AttributeCodec<T> | undefined
    const inner = (): AttributeCodec<T> => {
        resolved ??= get()
        return resolved
    }
    return codecOfTerm<T, A>({
        kind: 'lazy',
        get: () => termOf(inner()),
    })
}

// ── presence ────────────────────────────────────────────────────────

/**
 * An attribute that may be absent — which is not the same as null. `{ NULL: true }` is an attribute
 * DynamoDB *has*; use {@link nullable} for that.
 *
 * `undefined` is not injective in: `{ a: undefined }` and `{}` both encode without `a`.
 *
 * **A name is the only thing this can be said of**, so the result goes in an object's spec and
 * nowhere else. A list, a set, a tuple, an open block and a union option have no name at that position for
 * anything to be missing from, and each of those refuses this because a field is not a codec — the
 * member for a value that may be stored as `NULL` in one of them is {@link nullable}. Marking a
 * marked declaration is refused the same way: `withLegacyRead({ current: c, whenMissing: v })` is the attribute that may be absent
 * and has a stand-in, and it is what both nestings meant.
 */
export const optional = <const C extends AnyCodec>(
    inner: C,
): OptionalCodec<Decoded<C>, AttributeOf<C>, C> => {
    // the marked codec beside the definition, not a copy of the codec with a definition stamped on
    // it: a field has no pair of its own, and spreading one gave it the pair of the codec it marks.
    // `inner` itself, so the mark carries the codec the caller passed and not its erasure
    // one assertion, and it cannot come off. `optionalMarker` is a `declare const` symbol, so it
    // exists in the type and nowhere a literal can write it: removing the assertion reports
    // "Property '[optionalMarker]' is missing". It is `rest`'s spelling for `rest`'s reason
    return {
        codec: inner,
        def: { mark: 'optional', t: termOf(inner) },
    } as unknown as OptionalCodec<Decoded<C>, AttributeOf<C>, C>
}

/**
 * A key that is always present, holding `undefined` when the row carries no such attribute.
 *
 * The mark for a model that writes `k: T | undefined` rather than `k?: T`. Both describe the same
 * row, and they are different TypeScript types, which is the whole of the difference from
 * {@link optional}.
 *
 * ```ts
 * object({ tags: undefinable(string.set()) })   // { tags: ReadonlySet<string> | undefined }
 * object({ tags: optional(string.set()) })      // { tags?: ReadonlySet<string> }
 * ```
 *
 * **It stores nothing, and never `NULL`** — {@link nullable} is the codec for a value that *is*
 * null and writes an attribute; this writes none.
 *
 * It is the stricter of the pair: `optional` reads both `{}` and `{ k: undefined }` back as `{}`,
 * so **(R)** holds for it modulo that identification, while here the round trip is an equality. It
 * takes on no premise of its own — unlike {@link withLegacyRead}, which must check its stand-in is
 * writable because it writes one.
 */
export const undefinable = <const C extends AnyCodec>(
    inner: C,
): UndefinableCodec<Decoded<C>, AttributeOf<C>, C> =>
    ({
        codec: inner,
        def: { mark: 'undefinable', t: termOf(inner) },
    }) as unknown as UndefinableCodec<Decoded<C>, AttributeOf<C>, C>

/**
 * A value that may be null, stored as `NULL` when it is — **unless `inner` already owns the null
 * point**, in which case this is `inner`'s own pair, untouched.
 *
 * Without the guard the wrapper's `NULL` branch shadows the inner codec, and **(R)** fails on a
 * term the specification proves lawful: `nullable(held(nullable(string), adapter))`, where the
 * adapter maps `'SENTINEL'` to `null`, writes `{ NULL: true }` for `'SENTINEL'` and reads back
 * `null`. The value written is not the value read. No declaration in this repository builds that
 * term and `held` is unemittable, so no generated vector could ever have found it.
 *
 * Where the guard does *not* fire, null-honesty is a theorem rather than an assumption: an
 * `inner` that wrote `⟨NULL, ∗⟩` would read it straight back by **(R)** and so would own the
 * point, and one that read some attribute to `null` would write the point by **(C)** and own it
 * again. Both hypotheses are refuted by the guard rather than required of the caller.
 *
 * **The question is asked once, at first use rather than at construction.** `owns` is a property
 * of the pair and the probes are two calls, so asking repeatedly would be a walk with a known
 * answer. It is not asked *at* construction because {@link lazy} exists: a recursive declaration
 * forces its thunk when probed, and at module-evaluation time that is a reference to a binding
 * that does not exist yet. Deferring costs one boolean test per call and is the difference
 * between answering the question and catching an error from having asked it too early.
 */
export const nullable = <T, A extends AttributeValue>(
    inner: AttributeCodec<T, A>,
): AttributeCodec<T | null, A | Attribute<'NULL'>> => {
    const t = termOf(inner as unknown as AnyCodec)
    const owns = ownsNullOf(t)
    if (owns === undefined) {
        throw new CodecError(
            `nullable: ${t.kind} decides the null point by running a function this cannot read, ` +
                'so whether the union would be certified is unknown. ' +
                'Write the wrapper inside instead, as in held(nullable(inner), adapter).',
        )
    }
    if (owns) return inner as AttributeCodec<T | null, A | Attribute<'NULL'>>
    if (t.kind === 'never') {
        return nullValue as AttributeCodec<T | null, A | Attribute<'NULL'>>
    }
    return codecOfTerm<T | null, A | Attribute<'NULL'>>({
        kind: 'union',
        options: [t, { kind: 'null' }],
    })
}

// ── the escape hatch ────────────────────────────────────────────────

/**
 * `opaque`'s codec, with its **term's kind visible in the type**.
 *
 * The narrowing exists for one caller: {@link ValidateOptions} refuses a union holding an `opaque`
 * option, and to do that at compile time the type has to say which term this is. `AttributeCodec`
 * declares `def` as the whole of {@link Term}, so `opaque.def.kind` was the full twenty-one-member
 * union and no clause could match on it.
 *
 * **Matching on the kind and not on the decoded type**, deliberately: an adapter at an `unknown`
 * outer type also decodes to `unknown`, and it is not `opaque` — it admits exactly what its own
 * conversion admits, which may be one value. The rule is about a term that admits *everything*,
 * and the term is what says so.
 */
type OpaqueCodec<Def = { readonly kind: 'opaq' }> = AttributeCodec<unknown> & {
    readonly def: Def
}

/**
 * The term of a numeric policy: a `held` over the canonical `opaque`, named by `via`.
 *
 * {@link ValidateOptions} matches this shape as well as the bare `opaq`, because a policy admits
 * every value that holds no number, and so no other option can share a union with it.
 */
type OpaquePolicyDef = {
    readonly kind: 'held'
    readonly inner: { readonly kind: 'opaq' }
    readonly via: OpaqueSugar
}

// **One cast per codec, and it recovers what the construction site erases.** `codecOfTerm` takes
// a `Term` and returns a codec whose `def` is `Term`, so the kind of the term it was *given* is not
// in its result type. `opaqueTerms` holds exactly these shapes; nothing else can be. Making
// `codecOfTerm` generic in its term would push a type parameter through twenty-one constructors
// to narrow three.
const canonicalOpaque = codecOfTerm(opaqueTerms.canonical) as OpaqueCodec
const opaquePolicies: {
    readonly [Of in opaque.Numbers]: OpaqueCodec<OpaquePolicyDef>
} = {
    lossy: codecOfTerm(opaqueTerms.lossy) as OpaqueCodec<OpaquePolicyDef>,
    refuse: codecOfTerm(opaqueTerms.refuse) as OpaqueCodec<OpaquePolicyDef>,
}

function opaqueOf(): OpaqueCodec
function opaqueOf(numbers: opaque.Numbers): OpaqueCodec<OpaquePolicyDef>
function opaqueOf(
    numbers?: opaque.Numbers,
): OpaqueCodec | OpaqueCodec<OpaquePolicyDef> {
    return numbers === undefined ? canonicalOpaque : opaquePolicies[numbers]
}

/**
 * Any attribute, decoded to `unknown`, with a number held exactly as a {@link DynamoNumber}.
 *
 * The honest default, and **total**: every wire value has one value here. `N` reads as a
 * `DynamoNumber` and an `NS` as a `Set` of them, and both write back as they were read. A JS
 * `number` is refused, because a float is not the exact number that `N` stores.
 *
 * One entry point with its only parameter optional, the shape {@link native} takes: `opaque` *is*
 * the canonical codec, so `opaque.encode(value)` needs no call. A call names one of the two
 * numeric policies of {@link opaque.Numbers}. Each policy is a `held` over the canonical codec,
 * so the policies add no term to the language.
 *
 * ```ts
 * opaque.encode(value)             // `DynamoNumber` ⇄ `N`, exact
 * opaque('lossy').encode(value)    // `number` ⇄ `N`, digits only while a float holds them
 * opaque('refuse').encode(value)   // a number is refused, which guesses nothing
 * ```
 *
 * Callable *and* a codec, which is what lets `opaque.encode` and {@link opaque.Encode} keep the same
 * name.
 */
export const opaque: OpaqueCodec & typeof opaqueOf = Object.assign(
    opaqueOf,
    canonicalOpaque,
)

/**
 * The shapes, named as the runtime names them.
 *
 * A type-only namespace merged with the codec above, so `opaque.Encode<T>` sits beside
 * `opaque.encode(value)` and reads as the same pair. Non-instantiated — it declares no value — which
 * is what lets it share the name with a `const`, and `import type { opaque }` brings the types in
 * with no runtime import.
 *
 * `Decode` and `ItemDecode` are the two this does not have yet, and their absence is the point of
 * spelling the family out: `decodeUnknown` has behaviour worth describing — every native set comes
 * back as a `Set`, an `N` is a `DynamoNumber`, and an `N` under `'refuse'` is a refusal — and it is not a
 * mirror of {@link native.Decode}.
 */
export namespace opaque {
    /**
     * What a numeric policy of `opaque` does with a JS `number`, where the canonical codec holds a
     * `DynamoNumber`.
     *
     * `N` is a decimal string and no JS scalar carries it faithfully: decoding to `number` rounds
     * anything wider than a float, and decoding to `string` re-encodes as `S` — silently changing
     * the attribute's *stored type* on the next write. The canonical codec reads `N` as a
     * `DynamoNumber`, which is exact. A policy is for a caller who holds JS numbers, and each one
     * is a `held` over the canonical codec:
     *
     * - `'refuse'` — numbers are not written, and reading an `N` throws. Nothing is guessed.
     * - `'lossy'` — `number` ⇄ `N`. The member always survives a read-modify-write; the digits survive
     *   only while they fit in a float.
     */
    export type Numbers = 'refuse' | 'lossy'

    /**
     * What {@link opaque} writes for a value of type `T`, or why it refuses to.
     *
     * The counterpart of {@link native.Encode} for *this* package's marshaller, and they are not the
     * same function. The canonical `opaque` writes a `DynamoNumber` as `N` and refuses a JS number,
     * refuses a `bigint`, refuses a `Map`, and refuses a class instance — because each of those decodes
     * back as something else, and its whole domain is the values whose type survives a round trip. The
     * SDK's marshaller accepts all of them. `Of` names a numeric policy, which converts or refuses a JS
     * number and writes no `NS`. So a team whose in-house marshaller resembles `opaque` needs this
     * type to diff against, not that one.
     *
     * Every branch mirrors one in `encodeUnknown` or in a policy, refusals included: where the runtime returns a
     * {@link CodecError}, this resolves to an {@link ErrorMessage} carrying the same reason. A shape
     * containing a refused value therefore fails to *describe*, rather than describing a write that
     * throws.
     *
     * One place it is more permissive than the runtime, and deliberately: a class instance is refused at
     * runtime by checking the prototype, which no type can do. `Date` is named because it is the one the
     * runtime's own error message names, but a type cannot tell an arbitrary instance from a plain
     * object — so `Encode<SomeClass>` describes it as `M` where `encode` would refuse it.
     */
    export type Encode<T, Of extends Numbers | undefined = undefined> = [
        T,
    ] extends [never]
        ? never
        : [Of] extends [undefined]
          ? T extends DynamoNumber
              ? N
              : Encoded<T, Of>
          : Encoded<T, Of>

    /**
     * {@link Encode} after the one row that only the canonical codec has. Under a policy, a
     * `DynamoNumber` is a class instance, and it reaches the object row as today.
     */
    type Encoded<T, Of extends Numbers | undefined> = [T] extends [never]
        ? never
        : T extends null
          ? NULL
          : T extends undefined
            ? ErrorMessage<'[opaque] DynamoDB has no attribute holding undefined; omit the key, or use `optional(...)` on a declared attribute'>
            : T extends string
              ? S
              : T extends boolean
                ? BOOL
                : T extends Uint8Array
                  ? B
                  : T extends number
                    ? Of extends 'lossy'
                        ? N
                        : Of extends 'refuse'
                          ? ErrorMessage<"[opaque] a number is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`. Declare it with `number` or `decimal`, or opt in with `opaque('lossy')`">
                          : ErrorMessage<"[opaque] a JS number is a binary64 float, and `opaque` holds a number exactly, as a `DynamoNumber`. Build one with `DynamoNumber.from` or `DynamoNumber.fromNumber`, declare the attribute with `dynamoNumber` or `number`, or opt in with `opaque('lossy')`">
                    : T extends bigint
                      ? [Of] extends [undefined]
                          ? ErrorMessage<'[opaque] a bigint writes `N` and reads back as a `DynamoNumber`, so `1n` would not come back as `1n`. Pass `DynamoNumber.from(value.toString())`'>
                          : ErrorMessage<'[opaque] a bigint shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`'>
                      : T extends ReadonlySet<infer Member>
                        ? [Member] extends [string]
                            ? SS
                            : [Member] extends [Uint8Array]
                              ? BS
                              : [Of] extends [undefined]
                                ? [Member] extends [DynamoNumber]
                                    ? NS
                                    : ErrorMessage<'[opaque] a set writes `SS`, `BS` or `NS`, and each holds one kind: every member a string, every member binary, or every member a `DynamoNumber`'>
                                : ErrorMessage<'[opaque] `NS` decodes as strings, because its members are decimal strings. Use a set of strings, or `array(number)` if the order does not matter'>
                        : T extends ReadonlyMap<unknown, unknown>
                          ? ErrorMessage<'[opaque] DynamoDB has one map member, `M`, and it decodes as a plain object. Pass an object, or use `object([string, optional(...)])` to state the value type'>
                          : T extends Date
                            ? ErrorMessage<'[opaque] only plain objects survive: `M` carries the own enumerable properties and nothing that says how to rebuild the instance. A `Date` is faithful as an ISO string'>
                            : T extends readonly (infer Element)[]
                              ? Encode<Element, Of> extends infer Written
                                  ? [Written] extends [AttributeValue]
                                      ? L<Written>
                                      : Written
                                  : never
                              : T extends object
                                ? ItemEncode<T, Of> extends infer Item
                                    ? Refused<Item> extends infer Why
                                        ? [Why] extends [never]
                                            ? M<
                                                  Item &
                                                      Readonly<
                                                          Record<
                                                              string,
                                                              | AttributeValue
                                                              | undefined
                                                          >
                                                      >
                                              >
                                            : Why
                                        : never
                                    : never
                                : ErrorMessage<'[opaque] no DynamoDB member carries this'>

    /**
     * A refusal, carried out of the collection that contains it.
     *
     * A list of numbers under `'refuse'`, or an object with a `bigint` attribute, cannot be described —
     * so the refusal *is* the answer rather than something buried in an `L` or an `M`. Without this the
     * refusal fails `L`'s and `M`'s own constraints and the error lands on this file's definitions
     * instead of on the shape somebody wrote.
     */
    type Refused<T> = Extract<T[keyof T], ErrorMessage<string>>

    /**
     * An item {@link opaque} writes, attribute by attribute.
     *
     * Optional exactly where the property is. The runtime *refuses* a property that is present and
     * holding `undefined` — `{ a: undefined }` is an error, where `{}` is fine — and a type cannot tell
     * those apart, so an optional property is described as one that may be absent. The same reading
     * {@link native.ItemEncode} takes, for the same reason.
     */
    export type ItemEncode<
        T,
        Of extends Numbers | undefined = undefined,
    > = show<
        {
            [K in keyof T as undefined extends T[K] ? never : K]: Encode<
                T[K],
                Of
            >
        } & {
            [K in keyof T as undefined extends T[K] ? K : never]?: Encode<
                Exclude<T[K], undefined>,
                Of
            >
        }
    >

    /**
     * What {@link opaque} reads a stored attribute back as, or why it refuses to.
     *
     * The other direction from {@link opaque.Encode}, and *not* a mirror of {@link native.Decode} —
     * `decodeUnknown` is a different function from the SDK's in three places, and each is a reason
     * this type has to exist rather than the SDK's being reused:
     *
     * - `NS` is a `Set<DynamoNumber>`, where the SDK's answers `Set<number | bigint>`: exact, and it
     *   writes back as the `NS` it came from. Under a policy it is a **refusal**, because nothing
     *   without a schema can say which member a JS number holds faithfully, so a policy will not
     *   *write* a set of numbers, and a member it cannot write is one it cannot read. See
     *   `Calculus.Lawful.no_read_without_write`.
     * - `N` is a `DynamoNumber`, where the SDK's reads a JS number. Under `'refuse'` it is a
     *   *refusal*, and under `'lossy'` it is a `number`.
     * - `L` and `M` carry a refused member out with them, the way {@link opaque.Encode} does, so a
     *   list of `N` under `'refuse'` is the refusal itself rather than a list of nothing.
     *
     * A bare {@link AttributeValue} distributes, which is the useful answer: it resolves to every
     * value a stored attribute could be read as, the refusal for `N` among them.
     */
    export type Decode<A, Of extends Numbers | undefined = undefined> = [
        A,
    ] extends [never]
        ? never
        : A extends NULL
          ? null
          : A extends BOOL
            ? boolean
            : A extends N
              ? [Of] extends [undefined]
                  ? DynamoNumber
                  : Of extends 'lossy'
                    ? number
                    : ErrorMessage<"[opaque] a stored number is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`. Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`">
              : A extends S
                ? string
                : A extends B
                  ? Uint8Array
                  : A extends SS
                    ? Set<string>
                    : A extends NS
                      ? [Of] extends [undefined]
                          ? Set<DynamoNumber>
                          : // a member this codec cannot write is a member it cannot read: `NS`
                            // has no write path here, so reading one would re-encode as `SS` and
                            // change the attribute's stored type — (MP), which `μ = ⊤` leaves as
                            // the only law watching
                            ErrorMessage<'[opaque] a stored set of numbers has no counterpart this codec can write, so reading it would re-encode as `SS`. Declare the attribute with `number.set()` or `decimal.set()`'>
                      : A extends BS
                        ? Set<Uint8Array>
                        : A extends L<infer Element>
                          ? Decode<Element, Of> extends infer Read
                              ? [Read] extends [ErrorMessage<string>]
                                  ? Read
                                  : Read[]
                              : never
                          : A extends M<infer Item>
                            ? ItemDecode<Item, Of> extends infer Read
                                ? Refused<Read> extends infer Why
                                    ? [Why] extends [never]
                                        ? Read
                                        : Why
                                    : never
                                : never
                            : ErrorMessage<'[opaque] an AttributeValue carrying no member'>

    /**
     * An item {@link opaque} reads back, attribute by attribute.
     *
     * Homomorphic, so an attribute the stored shape marks optional stays optional — and its
     * `undefined` is excluded before decoding, since `undefined` is not a member and would otherwise
     * fall through to the refusal at the end.
     */
    export type ItemDecode<
        Item,
        Of extends Numbers | undefined = undefined,
    > = show<{
        [K in keyof Item]: Decode<Exclude<Item[K], undefined>, Of>
    }>
}

/**
 * An attribute path, which is a string and exists whether or not the attribute does.
 *
 * Optionality is stripped at every level, and that is the point: `deliveredAt?` describes whether
 * a *value* is there, and a path to it is well formed regardless — writing the path is how you ask
 * whether it exists. Typing the proxy as the entity leaks that value-level optionality into path
 * construction and forces a `!` at every optional hop, which is a non-null assertion about something
 * that was never a value.
 *
 * `at(i)` indexes a list. Bracket syntax works too, but under `noUncheckedIndexedAccess` a variable
 * index yields `| undefined` — again about a value, not a path — so `at` is the form that stays
 * clean. An entity with its own attribute named `at` should use brackets for that one hop.
 */
export type PathOf<T> = PathTerminal<T> & PathBody<NonNullable<T>>

type PathBody<T> = [T] extends [readonly unknown[]]
    ? PathList<T[number]>
    : [T] extends [object]
      ? {
            readonly [K in UnionKeys<T>]: PathOf<ValueAt<T, K>>
        } & PathRecord<T> &
            PathNarrowing<T>
      : Record<never, never>

/**
 * Every key any member of a union states, not only the shared ones.
 *
 * The reasoning that strips optionality: `priceIn` is a union whose CASH member has a `cardId` and
 * whose STORE_CREDIT member does not, but the path is well formed either way — writing it is how
 * you ask. The shared keys are never the interesting ones. Every key here belongs to some member,
 * so no path this admits is impossible for every variant.
 */
type UnionKeys<T> = T extends unknown ? keyof T : never

type ValueAt<T, K extends PropertyKey> = T extends unknown
    ? K extends keyof T
        ? T[K]
        : never
    : never

/**
 * Picking one member of a union before walking further.
 *
 * Merging every member's keys works while the members are objects, and stops working where they
 * disagree about *kind* — a key holding an object in one and a string in another merges to neither.
 *
 * `when` adds nothing to the path: narrowing is a statement about the type. Only present on a union.
 *
 * @example
 * ```ts
 * p.priceIn.when<Tender<'CASH'>>().cardId   // → 'priceIn.cardId'
 * ```
 */
type PathNarrowing<T> = IsUnion<T> extends true
    ? {
          /**
           * Narrows to the members matching `Filter`.
           *
           * A type rather than a discriminant and a value, because not every union has one. The
           * checked form of the cast otherwise written here: `when<Pet<'DOG'>>()` must match a
           * member or it does not compile.
           *
           * Narrows the *type* only. Where two members put different codecs at one attribute,
           * {@link ItemCodec.at} still cannot choose — types are gone by the time anything runs.
           * Reach for `tagged.variant(name)`, which is an item codec with its own `at`.
           */
          when<Filter extends Partial<T>>(): [Extract<T, Filter>] extends [
              never,
          ]
              ? ErrorMessage<'[when] no member of this union matches that filter'>
              : PathOf<Extract<T, Filter>>
      }
    : unknown

/**
 * A map whose keys are not known ahead of time, indexed by `at`.
 *
 * `requirements[someId]` is an index signature access, and under `noUncheckedIndexedAccess` that
 * yields `| undefined` — a statement about whether a *value* is there, which a path does not care
 * about. Only present when the type actually has a string index signature, so an object with known
 * keys is untouched and `.foo` stays the way to reach `foo`.
 */
type PathRecord<T> = string extends UnionKeys<T>
    ? { at(key: string): PathOf<ValueAt<T, string>> }
    : unknown

/**
 * A list, indexed by `at`.
 *
 * Deliberately not a mapped tuple. Preserving the tuple would let a literal index work in brackets,
 * but it also inherits `Array.prototype.at`, whose signature returns `| undefined` and shadows this
 * one — reintroducing at every index the assertion this type exists to remove.
 */
type PathList<Element> = {
    readonly [index: number]: PathOf<Element>
    at(index: number): PathOf<Element>
}

/**
 * The end of a path, carrying what lives there as a phantom.
 *
 * The phantom is what lets {@link ItemCodec.at} recover the type from a path expression: a selector
 * returns `PathTerminal<Adoption>`, and `Adoption` is inferred straight back out. Optional, so it costs
 * nothing at runtime and nothing to construct.
 */
export type PathTerminal<T> = {
    toString(): string
    readonly [pathValue]?: T
}

declare const pathValue: unique symbol

// ── items ───────────────────────────────────────────────────────────

/**
 * The entity a spec describes.
 *
 * An absent rest says the row holds nothing else, so the entity is closed. A rest codec says it
 * holds anything that codec can read, which is exactly an index signature — the mirror of
 * what {@link EncodedBy} does to the stored shape.
 */
type DerivedItem<Spec, Rest> = [Rest] extends [undefined]
    ? show<ObjectOf<Spec>>
    : show<ObjectOf<Spec>> & { readonly [name: string]: Decoded<Rest> }

/**
 * The keys a type states, without an index signature's.
 *
 * The value is `0` and not `T[K]`: only the keys are read back out, and naming the property type
 * instantiates one per key of every entity every spec is checked against, to be thrown away.
 */
type KnownKeys<T> = keyof {
    [K in keyof T as string extends K ? never : number extends K ? never : K]: 0
}

/**
 * The codecs an item needs: one per attribute, optional exactly where the entity is.
 *
 * Total coverage replaces the `key satisfies never` of a hand-written marshaller — a new field is a
 * compile error here, not a field that silently stops being written.
 */
export type ItemSpec<T> = T extends unknown
    ? {
          // distributed explicitly: `KnownKeys` is computed, so the mapped type is no longer
          // homomorphic and a union entity would otherwise collapse to the keys its members share
          [K in KnownKeys<T>]-?: undefined extends T[K]
              ? OptionalCodec<Exclude<T[K], undefined>>
              : Nestable<T[K]>
      }
    : never

/**
 * Reading and writing a whole item.
 *
 * The four item-shaped codecs — this, {@link Tagged}, {@link Untagged} and {@link TaggedCodec} —
 * each spell these members out rather than sharing one record. Factoring them out is the obvious
 * move and measurably the wrong one: as an intersection the result costs more to instantiate than
 * the flat object type, and stops being *comparable* to a hand-written shape, so the `as` a caller
 * writes to bypass a declaration-time check no longer compiles.
 */
export type ObjectCodec<
    Spec extends Record<string, ObjectSlot>,
    Rest extends AnyCodec | undefined = undefined,
> = {
    // spelled out rather than intersected with `AttributeCodec`, for the reason recorded on
    // {@link ItemCodec}: as an intersection the same type costs more to instantiate and stops being
    // *comparable* to a hand-written shape. Measured at +14k instantiations across this repo
    readonly encode: (
        value: DerivedItem<Spec, Rest>,
    ) => Result<M<EncodedBy<Spec, Rest>>>
    readonly decode: (
        attribute: AttributeValue,
    ) => Result<DerivedItem<Spec, Rest>>
    readonly unsafeEncode: (
        value: DerivedItem<Spec, Rest>,
    ) => M<EncodedBy<Spec, Rest>>
    readonly unsafeDecode: (
        attribute: AttributeValue,
    ) => DerivedItem<Spec, Rest>
    readonly def: Term
    /**
     * The same declaration, read as a whole item: the same two directions without the top-level map,
     * and the things only a top-level codec can offer — `encodePartial`, `field`, `at`, `path`.
     *
     * A DynamoDB item is a map that is never written as one; `PutItem` takes the attributes bare.
     * That is the *only* thing that separated an item codec from a nested one, and it is a fact about
     * where a codec is used rather than about what it declares — so it is a reading of one codec
     * rather than a second constructor. The marshaller draws the same line, under
     * `convertTopLevelContainer`.
     */
    readonly item: ItemCodec<DerivedItem<Spec, Rest>, Spec, Rest>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
}

/**
 * A union of objects, and the same union read as a whole item.
 *
 * Only a union of *objects* has an item reading: an item is a map, so a union that could also be an
 * `S` or an `L` is an attribute and nothing else. Which is why this is what the two union
 * constructors return, rather than what `union` is constrained to accept.
 */
export type DiscriminatedCodec<T, D extends string, Spec> = {
    readonly encode: (value: T) => Result<Attribute<'M'>>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (value: T) => Attribute<'M'>
    readonly unsafeDecode: (attribute: AttributeValue) => T
    readonly def: Term
    readonly item: Tagged<T, D, Spec>
    /**
     * **The members a clause keeps**, over the same keys — or `never` where it keeps none.
     *
     * `Spec` does not shrink with `T`. A member the clause dropped is still keyed in the table, and
     * asking for it gives an `ItemCodec<never>`: the entity type is what the slice narrows, and the
     * runtime is what refuses the assignment. Narrowing the table too would need the spec list
     * filtered in step with the entity union, and the two are matched by their decoded types rather
     * than positionally.
     */
    readonly extract: <const C extends ClauseOf<Spec[keyof Spec]>>(
        clause: C & ValidateClause<Spec[keyof Spec], C>,
    ) => DiscriminatedCodec<
        VariantsOf<KeptByTag<Spec, C>>,
        D,
        KeptByTag<Spec, C>
    >
    /** …and the members it rejects, the complement of the same clause. */
    readonly exclude: <const C extends ClauseOf<Spec[keyof Spec]>>(
        clause: C & ValidateClause<Spec[keyof Spec], C>,
    ) => DiscriminatedCodec<
        VariantsOf<KeptByTag<Spec, C, false>>,
        D,
        KeptByTag<Spec, C, false>
    >
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
}

/**
 * A dissection read as a whole item: the members, chosen by an assignment.
 *
 * {@link Tagged} at several discriminators. Two fields move, and both because there is no single
 * discriminator to name: `keys` holds the key set where `discriminator` held the one name, and
 * `variant` takes the assignment as an **object literal** rather than a bare tag. An object type is
 * unordered, so the selector carries no order and no rendered key — which is the whole of what the
 * multi-key term buys, said at the type level.
 *
 * `spec` is the members' specs as the caller declared them. There is no string to key them by: a
 * key would be a rendering of an assignment, and a rendering is an order.
 */
export type Dissected<
    T,
    Ks extends readonly string[],
    Specs extends readonly unknown[],
> = {
    /** Every attribute, or why one could not be written. */
    readonly encode: (item: T) => Result<AttributeMap>
    readonly unsafeEncode: (item: T) => AttributeMap
    /** The attributes a patch names. Every discriminator is required: they choose the codec. */
    readonly encodePartial: (
        patch: Partial<T> & Pick<T, Ks[number] & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        patch: Partial<T> & Pick<T, Ks[number] & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /** One member, by the assignment it carries. */
    readonly variant: <A extends AssignmentOf<Specs[number], Ks>>(
        assignment: A,
    ) => ItemCodec<Extract<T, A>, unknown>
    readonly keys: Ks
    readonly spec: Specs
    /** What this codec is — see {@link Term}. */
    readonly def: Term
}

/** {@link Dissected} with the top-level `M` back on, which is what a `dunion` codec is. */
export type DissectedCodec<
    T,
    Ks extends readonly string[],
    Specs extends readonly unknown[],
> = {
    readonly encode: (value: T) => Result<Attribute<'M'>>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (value: T) => Attribute<'M'>
    readonly unsafeDecode: (attribute: AttributeValue) => T
    readonly def: Term
    readonly item: Dissected<T, Ks, Specs>
    /** **The members a clause keeps**, over the same keys — or `never` where it keeps none. */
    readonly extract: <const C extends ClauseOf<Specs[number]>>(
        clause: C & ValidateClause<Specs[number], C>,
    ) => DissectedCodec<
        DerivedVariants<Extracted<Specs, C>>,
        Ks,
        Extracted<Specs, C>
    >
    /** …and the members it rejects, the complement of the same clause. */
    readonly exclude: <const C extends ClauseOf<Specs[number]>>(
        clause: C & ValidateClause<Specs[number], C>,
    ) => DissectedCodec<
        DerivedVariants<Excluded<Specs, C>>,
        Ks,
        Excluded<Specs, C>
    >
}

/**
 * What {@link mdunion} returns, read at the arity the caller wrote.
 *
 * **At one key it is today's type, exactly.** `discriminatedUnion` is `mdunion` at one
 * discriminator, so the two have to be the same type and not merely compatible ones — a caller
 * who swaps the call changes no annotation, and `variant`, `discriminator`, `spec` and the
 * `Writes` pin all read as they did.
 */
export type Dissection<
    Ks extends readonly string[],
    Options extends readonly unknown[],
> = Ks extends readonly [infer D extends string]
    ? DiscriminatedCodec<
          DerivedVariants<SpecsOf<Options>>,
          D,
          ByTag<SpecsOf<Options>, D>
      >
    : DissectedCodec<DerivedVariants<SpecsOf<Options>>, Ks, SpecsOf<Options>>

export type UnionCodec<T, Options extends readonly unknown[]> = {
    readonly encode: (value: T) => Result<WrittenBy<Options>>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (value: T) => WrittenBy<Options>
    readonly unsafeDecode: (attribute: AttributeValue) => T
    readonly def: Term
    /**
     * The same union read as a whole item — only where every option is an object.
     *
     * An item is a map, so a union that can also be an `S` has no top-level reading. Saying so with a
     * message rather than with an absent property is what makes reaching for it report *why* instead
     * of "property does not exist".
     */
    readonly item: AllObjects<Options> extends true
        ? Untagged<T, SpecsOf<Options>>
        : ErrorMessage<'[union] this union can hold an attribute that is not a map, so it has no whole-item reading — an item is always a map'>
    /**
     * **The options a clause keeps** — only where every option is an object, for the reason `item`
     * gives: a clause names attributes, and an option that writes no map declares none.
     *
     * The same operation the dissection has, and the same implementation, because a dissection is a
     * union of objects with a tag table over it. Every option survives or is dropped whole; no key
     * moves.
     */
    readonly extract: AllObjects<Options> extends true
        ? <const C extends ClauseOf<SpecsOf<Options>[number]>>(
              clause: C & ValidateClause<SpecsOf<Options>[number], C>,
          ) => UnionCodec<
              DerivedUnion<KeptOptions<Options, C>>,
              KeptOptions<Options, C>
          >
        : ErrorMessage<'[union] this union can hold an attribute that is not a map, so a clause has nothing to name — only a union of objects has a slice'>
    /** …and the options it rejects, the complement of the same clause. */
    readonly exclude: AllObjects<Options> extends true
        ? <const C extends ClauseOf<SpecsOf<Options>[number]>>(
              clause: C & ValidateClause<SpecsOf<Options>[number], C>,
          ) => UnionCodec<
              DerivedUnion<KeptOptions<Options, C, false>>,
              KeptOptions<Options, C, false>
          >
        : ErrorMessage<'[union] this union can hold an attribute that is not a map, so a clause has nothing to name — only a union of objects has a slice'>
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<SpecsOf<Options>>
}

export type ItemCodec<T, Spec = unknown, Rest = undefined> = {
    /** Every attribute, or why one could not be written. For `PutItem`. */
    readonly encode: (item: T) => Result<EncodedBy<Spec, Rest>>
    readonly unsafeEncode: (item: T) => EncodedBy<Spec, Rest>
    /**
     * The attributes a patch names, or why one could not be written. For `UpdateItem`, which
     * addresses attributes individually — the reason a whole-value codec does not fit DynamoDB and
     * this is a record of per-attribute ones.
     */
    readonly encodePartial: <const Patch extends Partial<T>>(
        patch: Patch,
    ) => Result<EncodedPatch<Spec, Patch>>
    readonly unsafeEncodePartial: <const Patch extends Partial<T>>(
        patch: Patch,
    ) => EncodedPatch<Spec, Patch>
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /** One attribute's codec, for building `ExpressionAttributeValues` by hand. */
    readonly field: <K extends keyof Spec>(name: K) => Marks<Spec[K]>
    /**
     * The codec at a path, together with the path.
     *
     * A nested update needs both halves and they must agree: the document path to write at, and the
     * codec declared for what lives there. Deriving them from one expression is what keeps them
     * agreeing — reaching for the generic marshaller at a nested path, which is the alternative,
     * drops out of the schema for that subtree and loses every guarantee it makes.
     *
     * @example
     * ```ts
     * const delivered = Adoption.at((p) => p.shipment.legs.at(i).deliveredAt)
     * delivered.path()            // 'shipment.legs[1].deliveredAt'
     * delivered.encode(stamp)     // through the codec declared for it
     * ```
     */
    readonly at: <X>(
        select: (path: PathOf<T>) => PathTerminal<X>,
    ) => LocatedCodec<X>
    /**
     * A builder for document paths into this item.
     *
     * One instance builds any number of independent paths: every hop returns a new builder carrying
     * its own segments, so nothing accumulates and nothing is consumed. Hoist it.
     */
    readonly path: () => PathOf<T>
    readonly spec: Spec
    /** The codec of an attribute the spec does not declare, or `undefined` for a closed object. */
    readonly rest: Rest
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
}

/** An {@link AttributeCodec} that also knows where it lives. */
export type LocatedCodec<T> = AttributeCodec<T> & {
    /** The document path, as DynamoDB expression syntax. */
    readonly path: () => string
    readonly segments: readonly (string | number)[]
}

/**
 * One declared attribute, with the questions about its declaration already answered.
 *
 * Whether an attribute may be absent and what stands in for it are facts about the spec, not about
 * the row being read, so they are settled once when the codec is built.
 */
export type Declared = {
    readonly name: string
    readonly codec: AnyCodec
    /** The attribute may be omitted — true for both `optional` and `undefinable`. */
    readonly optional: boolean
    /** On decode, an omitted attribute still gets its key, holding `undefined`. */
    readonly keyed: boolean
    readonly absent:
        | { readonly value: unknown; readonly copy: boolean }
        | undefined
}

/**
 * The marker taken off, once, at the declaration.
 *
 * A field names the codec it marks, so the two halves are that codec's and taking the mark off
 * changes nothing about what the member encodes or decodes. What it changes is that the mark is
 * *named* rather than left to be recovered from a definition kind, which is what {@link Field} is
 * for.
 */
const fieldOf = (declared: ObjectSlot): Field => {
    const def = declared.def
    return 'mark' in def ? def : { mark: 'req', t: def }
}

/**
 * Declares how an entity is stored, once, in both directions.
 *
 * The spec is the declaration, and the entity is derived from it. Nothing has to be named twice, and
 * there is no type argument to get wrong.
 *
 * Whatever else is worth checking is asked of the codec afterwards, and asked separately, because
 * they are separate questions:
 *
 * - `satisfies ItemCodec<Entity>` — the entity, exactly. `ItemCodec` is invariant in it, sitting in
 *   `encode`'s parameter and `decode`'s return, so a missing attribute, an extra one, and one that
 *   decodes to the wrong type are all caught. This is the totality the entity-first form used to
 *   check by construction.
 * - `satisfies Writes<Row>` — the stored shape. Covariant on its own, hence {@link Writes}.
 *
 * Which is the whole reason the entity is no longer a type parameter: it never needed to be one.
 *
 * @example
 * ```ts
 * const Pet = item({
 *     PK: string,
 *     SK: string,
 *     ownerId: string,
 *     price: decimal,               // money, never a float
 *     tags: string.set(),           // SS, not L
 *     adopted: boolean,
 *     soldAt: optional(string),
 * })
 *
 * // and the two questions worth asking of it, each on its own, chainable
 * const Checked = item(spec) satisfies ItemCodec<PetEntry> satisfies Writes<PetItem>
 * ```
 */
const objectFromMap = <
    const Spec extends Record<string, ObjectSlot>,
    const Rest extends AnyCodec | undefined = undefined,
>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
    rest: Rest,
): ObjectCodec<Spec, Rest> => {
    // the marker off each declared attribute, once — the term. What the two directions walk is
    // the *compiled* form of it, which `bodySem` builds and which carries one thing the term does
    // not: whether a stand-in has to be copied per read, a fact about this runtime and not about
    // the declaration.
    const fields: Record<string, Field> = {}
    const declaredSpec = spec as unknown as Record<string, ObjectSlot>
    for (const name in declaredSpec) {
        fields[name] = fieldOf(declaredSpec[name] as ObjectSlot)
    }

    /**
     * **A name the row always writes, declared at a term that holds no value.**
     *
     * The model types such an object and gives it an empty held set, which is correct as a model.
     * Here it is a second spelling for `never`, and the trap is that it looks like a schema: the
     * row would refuse every entity and say so one field at a time. `optional` is the mark that
     * makes the name a non-slot, and `never` itself is the term for "holds nothing".
     */
    for (const name in fields) {
        const field = fields[name] as Field
        if (alwaysWritten(field) && field.t.kind === 'never') {
            throw new CodecError(
                `'${name}' is declared at \`never\` and the row always writes it, so the object holds no value at all — mark it \`optional\`, or use \`never\` itself`,
            )
        }
    }
    const declaredBody: Body =
        rest === undefined ? { fields } : { fields, rest: termOf(rest) }
    const itemDef = { kind: 'object', body: declaredBody } as const
    // the term's item pair, not a second one built beside it — `denote`'s row asks `itemSem` for
    // the same object, so `.item` and the codec run one body rather than two that agree
    /**
     * **The view, and this is where it starts.**
     *
     * The owner's ruling: the top-level map belongs to the view, not to the codec. An `object`
     * codec writes an `M` like any other term, and `.item` is the one reading that writes no map —
     * the same pair, one level in.
     *
     * So the pair is not built here. `denote.ts` builds one item pair per term and this hands out
     * that one, which is what makes `item.encode === codec.encode`'s body the same function. They
     * were two objects before `579ed89`, and nothing said which of them a caller was running.
     */
    const body = itemSem(itemDef)

    type T = DerivedItem<Spec, Rest>
    const self: ItemCodec<T, Spec, Rest> = {
        encode: (item) =>
            body.encode(item as Record<string, unknown>) as Result<
                EncodedBy<Spec, Rest>
            >,

        encodePartial: (patch) => {
            const held = patch as Record<string, unknown>
            const out: Record<string, AttributeValue> = {}
            for (const name in held) {
                const value = held[name]
                if (value === undefined) continue
                const field = fields[name]
                if (!field) {
                    return new CodecError(`'${name}' is not an attribute`)
                }
                const written = codecOfTerm(field.t).encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
            }
            return out as never
        },

        decode: (item) =>
            body.decode(
                item as Readonly<Record<string, AttributeValue>>,
            ) as Result<T>,

        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        unsafeEncodePartial: (patch) => orThrow(self.encodePartial(patch)),

        path: () => pathBuilder<T>(),
        at: <X>(select: (path: PathOf<T>) => PathTerminal<X>) => {
            const segments = segmentsOf(select(pathBuilder<T>()))
            const path = asPath(segments)

            /**
             * The walk carries a *set* of codecs, not one.
             *
             * A path may pass through a segment the variants declare differently and still arrive
             * where they agree — `legs` is a one-tuple in `SINGLE_LEG` and a two-tuple in
             * `MULTI_LEG`, but indexing either reaches the same leg codec. So the disagreement is
             * carried along and reported only if it survives to the end, where using it would mean
             * encoding with a codec nobody declared.
             */
            let frontier: readonly AnyCodec[] = [self as unknown as AnyCodec]
            for (const segment of segments) {
                const next = [
                    ...new Set(frontier.flatMap((c) => childrenOf(c, segment))),
                ]
                if (next.length === 0) {
                    throw new CodecError(
                        `no attribute is declared at '${path}'`,
                    )
                }
                frontier = next
            }
            const [first, ...ambiguous] = frontier as [AnyCodec, ...AnyCodec[]]
            const here =
                ambiguous.length === 0 ? first : unresolvedAt(String(path))

            return {
                ...(here as AttributeCodec<X>),
                path: () => path,
                segments,
            }
        },
        // the codec the member declares, never the field that marks it: a field has no pair, and a
        // caller that asked for the attribute at a name asked for the thing that reads and writes it
        field: <K extends keyof Spec>(name: K) => {
            const declared = fields[name as string]
            return (declared && codecOfTerm(declared.t)) as Marks<Spec[K]>
        },
        spec: spec as Spec,
        rest,
        def: itemDef,
    }

    // the `M` is what this codec writes; `.item` is the same two directions with the wrapper taken
    // off. Named member by member rather than spread so the cast keeps the *shape* the map carries —
    // `Attribute<'M'>` would flatten it to "some map" — and so that a call to `object` stays a plain
    // object literal, which is what lets a bundler drop an unused one
    const nested = codecOfTerm(itemDef) as unknown as AttributeCodec<
        DerivedItem<Spec, Rest>,
        M<EncodedBy<Spec, Rest>>
    >
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        item: self as ItemCodec<DerivedItem<Spec, Rest>, Spec, Rest>,
    }
}

export type ObjectEntry<
    Key extends string = string,
    Value extends ObjectSlot = ObjectSlot,
> = readonly [AttributeCodec<Key, Attribute<'S'>>, Value]

type AnyObjectEntry = readonly [AnyCodec, ObjectSlot]

type OptionalObjectSlot = {
    readonly def: Extract<Field, { readonly mark: 'optional' | 'undefinable' }>
}

type EntryAdmission<Entry> = Entry extends readonly [
    AttributeCodec<infer Key, Attribute<'S'>>,
    infer Value extends ObjectSlot,
]
    ? Key extends string
        ? string extends Key
            ? Value extends OptionalObjectSlot
                ? unknown
                : ErrorMessage<'[object] an open key entry must be optional, because a required wildcard means at least one matching key'>
            : unknown
        : ErrorMessage<'[object] an entry key must be a string codec'>
    : ErrorMessage<'[object] an entry must contain a string codec and an object slot'>

type EntriesAdmission<Entries extends readonly AnyObjectEntry[]> =
    UnionToIntersection<EntryAdmission<Entries[number]>>

type UnionToIntersection<Value> = (
    Value extends unknown
        ? (value: Value) => void
        : never
) extends (value: infer Intersection) => void
    ? Intersection
    : never

type EntrySpec<Entry> = Entry extends readonly [
    AttributeCodec<infer Key extends string, Attribute<'S'>>,
    infer Value extends ObjectSlot,
]
    ? string extends Key
        ? Record<never, never>
        : { readonly [K in Key]: Value }
    : never

type EntrySpecs<Entries extends readonly AnyObjectEntry[]> = show<
    UnionToIntersection<EntrySpec<Entries[number]>>
>

type SlotCodec<Slot> = Slot extends { readonly codec: infer Codec }
    ? Codec
    : Slot

type WildcardEntry<Entries extends readonly AnyObjectEntry[]> =
    Entries[number] extends infer Entry
        ? Entry extends readonly [
              AttributeCodec<infer Key, Attribute<'S'>>,
              infer Value extends ObjectSlot,
          ]
            ? string extends Key
                ? SlotCodec<Value>
                : never
            : never
        : never

type EntryRest<Entries extends readonly AnyObjectEntry[]> = [
    WildcardEntry<Entries>,
] extends [never]
    ? undefined
    : Extract<WildcardEntry<Entries>, AnyCodec>

const entryNames = (key: AnyCodec): string[] => {
    const term = termOf(key)
    if (term.kind === 'literal' && term.base === 'string') return [term.v]
    if (
        term.kind === 'union' &&
        term.options.every(
            (option) => option.kind === 'literal' && option.base === 'string',
        )
    ) {
        return term.options.map((option) => (option as { v: string }).v)
    }
    if (term.kind === 'string') return []
    throw new CodecError(
        'an object entry key must be `string` or a string literal key set',
    )
}

const entryCodec = (slot: ObjectSlot): AnyCodec =>
    ('codec' in slot ? slot.codec : slot) as AnyCodec

export function object<const Spec extends Record<string, ObjectSlot>>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
): ObjectCodec<show<Spec>>
export function object<const Entries extends readonly AnyObjectEntry[]>(
    ...entries: Entries & EntriesAdmission<Entries>
): ObjectCodec<EntrySpecs<Entries>, EntryRest<Entries>>
export function object<
    const Spec extends Record<string, ObjectSlot>,
    const FirstEntry extends AnyObjectEntry,
    const Entries extends readonly AnyObjectEntry[],
>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
    firstEntry: FirstEntry & EntriesAdmission<[FirstEntry, ...Entries]>,
    ...entries: Entries
): ObjectCodec<
    show<Spec & EntrySpecs<[FirstEntry, ...Entries]>>,
    EntryRest<[FirstEntry, ...Entries]>
>
export function object(
    first?: Record<string, ObjectSlot> | AnyObjectEntry,
    ...tail: AnyObjectEntry[]
): ObjectCodec<Record<string, ObjectSlot>, AnyCodec | undefined> {
    const isEntry = Array.isArray(first)
    const spec: Record<string, ObjectSlot> =
        !isEntry && first !== undefined
            ? (first as Record<string, ObjectSlot>)
            : {}
    const entries = (isEntry ? [first, ...tail] : tail) as AnyObjectEntry[]
    const fields: Record<string, ObjectSlot> = { ...spec }
    let rest: AnyCodec | undefined
    for (const [key, slot] of entries) {
        const names = entryNames(key)
        if (names.length === 0) {
            const field = fieldOf(slot)
            if (field.mark !== 'optional' && field.mark !== 'undefinable') {
                throw new CodecError(
                    'an open key entry must be optional, because a required wildcard means at least one matching key',
                )
            }
            if (rest !== undefined) {
                throw new CodecError('an object has at most one open key entry')
            }
            rest = entryCodec(slot)
            continue
        }
        for (const name of names) {
            if (name in fields) {
                throw new CodecError(`'${name}' is declared more than once`)
            }
            fields[name] = slot
        }
    }
    return objectFromMap(fields, rest) as ObjectCodec<
        Record<string, ObjectSlot>,
        AnyCodec | undefined
    >
}

/** The options a factor offers, at the type level: a union's, or the factor itself. */
type FactorOptions<F> = F extends UnionCodec<infer _T, infer Os>
    ? Os
    : readonly [F]

/** Every name a factor can declare, across all of its options. */
type DeclaredNames<F> = FactorOptions<F>[number] extends infer O
    ? O extends ObjectCodec<infer S, infer _R>
        ? keyof S & string
        : never
    : never

/** Whether any option of a factor is left open by a rest codec. */
type AnyOpen<F> = FactorOptions<F>[number] extends infer O
    ? O extends ObjectCodec<infer _S, infer R>
        ? [R] extends [undefined]
            ? never
            : true
        : true
    : never

/**
 * One merge: `Body.merge` at the type level. The merge is closed, because a name neither factor
 * declares is one the product refuses.
 */
type MergeTwo<X, Y> = X extends ObjectCodec<infer A, infer _RA>
    ? Y extends ObjectCodec<infer B, infer _RB>
        ? ObjectCodec<show<A & B>>
        : never
    : never

type DistributeOne<X, Ys extends readonly unknown[]> = {
    [I in keyof Ys]: MergeTwo<X, Ys[I]>
}

/** The `flatMap` order the model's distribution law states: outer first, inner second. */
type Distribute<
    Xs extends readonly unknown[],
    Ys extends readonly unknown[],
> = Xs extends readonly [infer H, ...infer T extends readonly unknown[]]
    ? [...DistributeOne<H, Ys>, ...Distribute<T, Ys>]
    : []

/** One merge needs no union around it; several are one flat union. */
type ProductOfTwo<X, Y> = Distribute<
    FactorOptions<X>,
    FactorOptions<Y>
> extends infer Ms extends readonly unknown[]
    ? Ms extends readonly [infer One]
        ? One
        : UnionCodec<DerivedUnion<Ms>, Ms>
    : never

/** More than two factors fold left, which `merge_assoc` is why the other nesting agrees. */
type FoldProduct<Fs extends readonly unknown[]> = Fs extends readonly [
    infer A,
    infer B,
    ...infer R extends readonly unknown[],
]
    ? FoldProduct<[ProductOfTwo<A, B>, ...R]>
    : Fs extends readonly [infer A]
      ? A
      : never

/** A name two factors both declare, which is the one thing a product cannot have. */
type SharedAcross<Fs extends readonly unknown[]> = Fs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? (DeclaredNames<H> & DeclaredNames<T[number]>) | SharedAcross<T>
    : never

/** Whether any factor is `never`, matched on the term's kind as {@link HasOpaque} is. */
type HasNeverFactor<Fs extends readonly unknown[]> = Fs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? // `[H] extends [never]` is true only where `H` *is* `never`, which is how a spec casts a
      // factor past the type. Without this guard that cast matches every shape below it
      [H] extends [never]
        ? HasNeverFactor<T>
        : [H] extends [{ readonly def: { readonly kind: 'never' } }]
          ? true
          : HasNeverFactor<T>
    : false

/**
 * Nothing, or why these factors have no product.
 *
 * **Three rules, in the order that gives the advice a caller can act on.** A `never` factor comes
 * first: §5's (D) fails at a product against a factor that holds nothing, because every merge
 * holds nothing and two empty held sets are comparable in both directions. Without this clause the
 * open-factor one fired on it and told the caller to close a rest policy `never` does not have,
 * which is the same misdirection {@link ValidateOptions} orders its `opaque` clause to avoid.
 *
 * The shared name is next, because its message names the name. The open factor is last: a `rest`
 * codec holds an undeclared name through a codec of its own, and the product would have to hold it
 * through both. The model says the same by making `Rest.merge` answer `none` there.
 *
 * `never` is the only term a factor can be that holds no value: `tuple` and `object` refuse a slot
 * declared at it, so no other declaration reaches here empty.
 */
export type ValidateProduct<Fs extends readonly unknown[]> =
    HasNeverFactor<Fs> extends true
        ? ErrorMessage<'[product] one factor is `never`, which holds no value — so every product with it holds none either and no value could select between the results. Remove the factor'>
        : [SharedAcross<Fs>] extends [never]
          ? [AnyOpen<Fs[number]>] extends [never]
              ? unknown
              : ErrorMessage<'[product] a factor holds undeclared names through a `rest` codec, and a product declares no meet of two of them. Close every factor: give it no open key entry'>
          : ErrorMessage<`[product] two factors both declare '${SharedAcross<Fs>}', and a product needs disjoint names. Rename it, or drop it from one factor`>

/** One option of a factor: what the merge reads off it. */
type Factor = {
    readonly spec: Record<string, ObjectSlot>
    readonly rest: AnyCodec | undefined
    readonly def: Term
}

/**
 * The options a factor offers: a union's, or the factor itself.
 *
 * **A tagged builder is a union here, and that is why it is no longer refused.** It used to be a
 * term of its own, chosen by a tag where a union is chosen by names, so one product would have
 * needed two selection rules and the refusal named the ruling that was missing. The ruling was to
 * delete the second sum: a dissection is a certified union, so a product of two of them is the
 * distribution over one selection rule, and the merges are what comes out.
 */
const optionsOfFactor = (factor: unknown): readonly Factor[] => {
    const codec = factor as
        | {
              readonly def?: Term
              readonly item?: {
                  readonly spec?: Record<string, ObjectSlot>
                  readonly rest?: AnyCodec
                  readonly variant?: (index: number) => Factor
              }
          }
        | undefined
    const def = codec?.def
    // §5's (D) fails at a product against a factor that holds nothing: every merge would hold
    // nothing too, and two empty held sets are comparable both ways, so no value tells the options
    // apart. `not_subset_prodOn` is the theorem, and this is the hypothesis it carries. `never` is
    // the only way in, because every other term that holds nothing is refused at its constructor
    if (def?.kind === 'never') {
        throw new CodecError(
            '`never` holds no value, so every product with it holds none either and no value could select between the results — remove the factor',
        )
    }
    if (def?.kind === 'union') {
        const variant = codec?.item?.variant
        if (!variant) {
            throw new CodecError(
                'a union factor must read as a whole item, and this one cannot — every option of it has to be an object for the product to merge names',
            )
        }
        // **A dissection is a union now and its members are not reached positionally.** Its
        // `variant` is keyed by the assignment its members carry, where a plain union's is keyed by
        // position, so the loop below would ask for member `0` and be handed nothing. The term-level
        // refusal this replaces named a ruling the owner had not made; that ruling has been made
        // and what is left is the wiring, which is its own pass.
        if ((codec?.item as { readonly keys?: unknown })?.keys !== undefined) {
            throw new CodecError(
                'a `discriminatedUnion` is a union of objects and a product distributes over it, but its members are reached by the assignment they carry rather than by position, and this loop reads a union positionally — take the product inside each member, or use an untagged `union` of objects',
            )
        }
        return def.options.map((_, index) => variant(index))
    }
    if (def?.kind === 'object' && codec?.item?.spec) {
        return [codec.item as Factor]
    }
    throw new CodecError(
        'a factor of a product is an object codec or a `union` of object codecs, and this is neither — a product merges declared names, and only an object declares any',
    )
}

/** The binary product, over the options each factor offers. */
const productOfTwo = (first: unknown, second: unknown): unknown => {
    const lefts = optionsOfFactor(first)
    const rights = optionsOfFactor(second)
    for (const option of [...lefts, ...rights]) {
        if (!option?.spec) {
            throw new CodecError(
                'an option of a union factor is not an object codec — a product merges declared names, and only an object declares any',
            )
        }
        if (option.rest !== undefined) {
            throw new CodecError(
                'a factor holds undeclared names through a `rest` codec, and a product declares no meet of two of them. Close every factor: give it no open key entry',
            )
        }
    }
    const merges = lefts.flatMap((left) =>
        rights.map((right) => {
            for (const name in right.spec) {
                if (Object.hasOwn(left.spec, name)) {
                    throw new CodecError(
                        `both factors declare '${name}', and a product needs disjoint names — rename it, or drop it from one factor`,
                    )
                }
            }
            return objectFromMap({ ...left.spec, ...right.spec }, undefined)
        }),
    )
    // one merge is an object and needs no union around it; several are one flat union, built
    // through `union` itself so `Collides` and `separable` run over the products
    return merges.length === 1
        ? merges[0]
        : union(merges as unknown as readonly AnyCodec[])
}

/**
 * **The product of two objects, or of unions of objects: the object of their merged spec.**
 *
 * The founding operation of the Cartesian product over codecs. `Body.merge` is the model's, and
 * `typed_merge` is the corollary that makes the result derivable from the two factors' own
 * judgements.
 *
 * **A union factor distributes.** The result is one flat `union` of the `n·m` merges, outer over
 * the first factor's options and inner over the second — the `flatMap` order the model's
 * distribution law states. It is built through {@link union}, so `Collides` and `separable` run
 * over the products and a pair of merges no value can tell apart is refused there rather than here.
 *
 * **More than two factors fold left.** `product(a, b, c)` is `product(product(a, b), c)`, and the
 * model's `merge_assoc` on `fields` and `rest` is why the other nesting gives the same term.
 *
 * @example
 * ```ts
 * product(object({ petId: string }), object({ price: decimal }))
 * product(union([object({ a: string }), object({ b: string })]), object({ n: boolean }))
 * ```
 */
export const product = <const Fs extends readonly unknown[]>(
    ...factors: Fs & ValidateProduct<Fs>
): FoldProduct<Fs> => {
    const [head, ...rest] = factors as readonly unknown[]
    if (head === undefined || rest.length === 0) {
        throw new CodecError(
            'a product is taken of two or more factors, and fewer were given',
        )
    }
    return rest.reduce(
        (carried, next) => productOfTwo(carried, next),
        head,
    ) as FoldProduct<Fs>
}

/**
 * A builder for document paths into `T`.
 *
 * The one implementation behind both `item(...).path()` and `tableEntry(...).path()`. They must
 * agree about what a path means — `at` resolves a codec by walking the same segments this records —
 * and the surest way for two implementations to agree is for there to be one.
 */
export const pathBuilder = <T>(): PathOf<T> => recordPath([]) as PathOf<T>

/** A segment addressing a list position, as opposed to an attribute named in digits. */
const asIndex = /^\d+$/

/** What each recorder recorded — read back by {@link segmentsOf}. */
const recorded = new WeakMap<object, readonly (string | number)[]>()

/** Nothing, shared: every `get` is trapped, so the target is only an identity to hang one on. */
const nothing = {}

/**
 * Records what a path expression walks through.
 *
 * Every hop returns a *new* recorder carrying its own segments, rather than pushing into a shared
 * array. Accumulating in place would be shorter and wrong: a selector that names an intermediate
 * node and reads more than one attribute off it — `const step = p.route.at(0); step.id; return
 * step.status` — would record both reads as one path. It also makes a recorder reusable, which is
 * what `path()` has always been.
 */
const recordPath = (segments: readonly (string | number)[]): unknown => {
    const recorder = new Proxy(nothing, {
        get: (_target, prop) => {
            if (typeof prop !== 'string') return undefined
            if (prop === 'toString') return () => asPath(segments)
            if (prop === 'at') {
                return (index: number) => recordPath([...segments, index])
            }
            // narrowing is a statement about the type; the document path is unchanged
            if (prop === 'when') return () => recordPath(segments)
            // digits all the way through, or it is an attribute name: `parseInt` accepted a
            // leading number and dropped the rest, so `'1abc'` recorded `[NaN]`
            return recordPath([
                ...segments,
                asIndex.test(prop) ? Number(prop) : prop,
            ])
        },
    })
    recorded.set(recorder, segments)
    return recorder
}

/**
 * The path a selector built.
 *
 * Read from a side table keyed on the recorder, because the two alternatives are both worse. A
 * property would have to be a key the `get` trap carves out of the entity's own namespace, which is
 * what a private symbol was for. A callable target — recovering the path by calling it — carves
 * nothing out, but it makes `typeof path` be `'function'`, and a recorder answers `.then` with
 * another recorder: a path whose target is callable *is a thenable*, so `await path` and
 * `Promise.resolve(path)` hang forever, silently. The target stays inert and the segments live
 * beside it.
 */
const segmentsOf = (path: unknown): readonly (string | number)[] => {
    // no `typeof` guard: `WeakMap.prototype.get` answers `undefined` for a key that cannot be held
    // weakly, so a selector that returned a string or a number falls into the same branch
    const segments = recorded.get(path as object)
    if (!segments) {
        throw new CodecError(
            'a path selector must return a path — an attribute, `at(...)` or `when()`',
        )
    }
    return segments
}

/**
 * Type-level only, and a function *pair* rather than a value, for one reason: invariance.
 *
 * A property whose type is `Written` is covariant, so a codec writing a subset of the pinned shape
 * would be accepted — which is the whole thing the pin exists to refuse. Naming `Written` in both a
 * parameter and a return position makes the comparison mutual, and mutual is what "the same shape"
 * means. `in out` is not an alternative: it constrains instantiations of one generic against each
 * other, and a `satisfies` compares two different types.
 */
declare const writesMarker: unique symbol

/**
 * The shape a codec puts in the table, asked of the codec itself.
 *
 * ```ts
 * const Pet = item(spec) satisfies Writes<PetItem>
 * ```
 *
 * Kept off {@link ItemCodec} and intersected onto what a constructor returns instead. On `ItemCodec`
 * the phantom would be invariant there too, and `satisfies ItemCodec<Pet>` — which leaves `Spec` at
 * its default — would then refuse every real codec. The two questions are separate and ask
 * separately: `satisfies ItemCodec<Pet>` is the entity, `satisfies Writes<PetItem>` is the row, and
 * they chain.
 */
export type Writes<Written> = {
    readonly [writesMarker]?: (written: Written) => Written
}

/**
 * The pin as {@link ItemCodec} carries it: inert until something asks.
 *
 * `unknown` is what the phantom is when no shape is named, and every function is assignable to
 * `unknown` — so `satisfies ItemCodec<Pet>`, which leaves `Spec` at its default, is untouched by
 * this and stays a question about the entity alone.
 *
 * Carried on the codec rather than intersected onto what `item` returns, which is where this
 * started: `tableEntry` infers `CodecSpec` and `CodecRest` from the codec it is handed, and an
 * intersection is a source those inferences do not survive — `Rest` fell back to its default, and a
 * row that really does carry an open policy's attributes typed as though it did not.
 */
type WritesPin<Spec, Rest> = unknown extends Spec
    ? unknown
    : (written: EncodedBy<Spec, Rest>) => EncodedBy<Spec, Rest>

/**
 * The same pin for a union, whose row is one variant's attributes or another's.
 *
 * A union has no single encoded shape to name — `encode` returns "some attribute map", because which
 * attributes are written depends on which variant the value is. So the phantom is the only place the
 * shape appears at all, which makes it the only thing a pin can be asked of.
 */
type WritesVariantsPin<Spec> = unknown extends Spec
    ? unknown
    : (written: EncodedVariants<Spec>) => EncodedVariants<Spec>

/**
 * What a union of variants writes: one variant's attributes, or another's.
 *
 * A row of a tagged or untagged entity is exactly one variant, so the shape is the union rather than
 * the merge — which is what lets a pin catch a variant that has drifted while the others have not.
 * Handles a record of variants (`tagged`) and a list of them (`untagged`); the two differ only in
 * how they are keyed.
 */
export type EncodedVariants<Variants> = Variants extends readonly unknown[]
    ? { [V in keyof Variants]: Encoded<Variants[V]> }[number]
    : { [V in keyof Variants]: Encoded<Variants[V]> }[keyof Variants]

/**
 * Which set an element reaches, from what the element writes.
 *
 * The runtime asks `term.ts`'s `member`; this is the same question of the type, so a spec can pin `SS`
 * and be told when the element stops being a string. `L` and `SS` are the distinction a marshaller
 * that guesses gets wrong, so a shape that could not tell them apart would pin very little.
 */
export type SetOf<C> = AttributeOf<C> extends Attribute<'S'>
    ? SS
    : AttributeOf<C> extends Attribute<'N'>
      ? NS
      : AttributeOf<C> extends Attribute<'B'>
        ? BS
        : never

/**
 * The attribute a codec writes, as a type.
 *
 * The mirror of {@link Decoded}: that side says what the entity holds, this side says what the
 * *table* holds. A codec has carried both since the beginning — `AttributeCodec<T, A>` — so this
 * reads the half nobody was reading.
 */
export type AttributeOf<C> = C extends {
    readonly attribute: AttributeCodec<infer _Nested, infer Nesting>
}
    ? Nesting
    : // the same for a field: the attribute is the one the codec it marks writes
      C extends { readonly codec: AttributeCodec<infer _Marked, infer Marks> }
      ? Marks
      : C extends AttributeCodec<infer _Held, infer Written>
        ? Written
        : never

/**
 * The attributes a patch writes, read off the patch rather than off the whole spec.
 *
 * `Partial<Encoded<Spec>>` is the weaker answer and it loses the thing a patch knows: which
 * attributes are being written. Naming them means an `UpdateItem` built from this is checked
 * against the attributes it actually sets, not against every attribute the entity could have.
 *
 * Optional exactly where the patch's own value admits `undefined`, because that is the value the
 * implementation skips — a key present with no value writes no attribute.
 *
 * Based on {@link Encoded} and *not* {@link EncodedBy}: a patch never reaches a rest policy. The
 * implementation looks each name up among the declared attributes and refuses one it does not
 * find, so a type carrying the rest policy's index signature would promise a write that is an
 * error at runtime.
 */
export type EncodedPatch<Spec, Patch> = Encoded<Spec> extends infer Full
    ? show<
          {
              [K in keyof Patch as K extends keyof Full
                  ? undefined extends Patch[K]
                      ? never
                      : K
                  : never]: Written<Full, K>
          } & {
              [K in keyof Patch as K extends keyof Full
                  ? undefined extends Patch[K]
                      ? K
                      : never
                  : never]?: Written<Full, K>
          }
      >
    : never

/**
 * The attribute at `K`, without the `undefined` that optionality adds.
 *
 * Indexing an optional key of {@link Encoded} yields `Attribute<'S'> | undefined`, which is a fact
 * about whether the attribute is *there* rather than about what it carries — and a patch that names
 * it has settled that question. Carrying the `undefined` through would put it back, so every read
 * of a patched attribute would need a `?.` for a value the patch just supplied.
 */
type Written<Full, K> = Exclude<Full[K & keyof Full], undefined>

/**
 * What an item writes: the attributes the spec declares, plus whatever a rest policy adds.
 *
 * {@link Encoded} alone is a *lower bound* rather than the answer. With no rest nothing else
 * is written and the two agree; a rest codec emits attributes the spec never named, so
 * claiming `Encoded<Spec>` exactly would be a promise the compiler then enforces against the
 * caller — refusing to read an attribute the codec really did write.
 *
 * The closed state is matched rather than the codec: an {@link AttributeCodec} is
 * invariant in its value, so `Rest extends AttributeCodec<unknown, infer A>` fails for every codec
 * of a narrower value and quietly takes the wrong branch. {@link AttributeOf} infers both
 * parameters, so the open block's attribute is exact. The index also admits each declared
 * attribute, because an index signature intersects with every declared key.
 */
type EncodedBy<Spec, Rest> = [Rest] extends [undefined]
    ? Encoded<Spec>
    : Encoded<Spec> & {
          readonly [name: string]:
              | AttributeOf<Rest>
              | Encoded<Spec>[keyof Encoded<Spec>]
      }

/**
 * The item a spec writes, as a shape you could have written by hand.
 *
 * The fixed point. `Encoded<typeof Pet>` is what the codec puts in the table; a `PetItem` written
 * out by hand is what the table is believed to hold; pinning one against the other is what makes a
 * migration checkable rather than hoped for. Optional attributes are optional keys, because an
 * attribute a codec may omit is one the item may not have.
 */
export type Encoded<Spec> = show<
    {
        [K in keyof Spec as Spec[K] extends {
            readonly [optionalMarker]: true
        }
            ? never
            : K]: AttributeOf<Spec[K]>
    } & {
        // an optional name at `never` writes no attribute, so the item has no such key
        [K in keyof Spec as Spec[K] extends {
            readonly [optionalMarker]: true
        }
            ? [AttributeOf<Spec[K]>] extends [never]
                ? never
                : K
            : never]?: AttributeOf<Spec[K]>
    }
>

export type ObjectOf<Spec> = {
    // required key, and the attribute is always there
    [K in keyof Spec as Spec[K] extends { readonly [undefinableMarker]: true }
        ? never
        : Spec[K] extends { readonly [optionalMarker]: true }
          ? never
          : K]: Decoded<Spec[K]>
} & {
    // required key, and the attribute may not be there — so `undefined` joins the value
    [K in keyof Spec as Spec[K] extends { readonly [undefinableMarker]: true }
        ? K
        : never]: Decoded<Spec[K]> | undefined
} & {
    // the key itself may not be there
    [K in keyof Spec as Spec[K] extends { readonly [undefinableMarker]: true }
        ? never
        : Spec[K] extends { readonly [optionalMarker]: true }
          ? K
          : never]?: Decoded<Spec[K]>
}

// ── unions ─────────────────────────────────────────────────────────

export type IsUnion<T, U = T> = T extends unknown
    ? [U] extends [T]
        ? false
        : true
    : never

/**
 * The member a tag selects.
 *
 * `Extract<T, { [D]: V }>` is not enough: a variant may span several tags — a `Vendor` member
 * typed `vendorId: 'ACME' | 'GLOBEX'` does not extend `{ vendorId: 'ACME' }`. Asking whether the
 * tag is *among* the member's tags does reach it.
 */
export type VariantOf<T, D extends keyof T, V> = T extends unknown
    ? V extends T[D]
        ? T
        : never
    : never

/**
 * A tagged codec, structural so a signature can ask for one without naming its discriminator —
 * `Tagged` carries `D` contravariantly, so naming it would accept only the one guessed.
 */
export type TaggedCodec<T, Spec = unknown> = {
    readonly encode: (item: T) => Result<AttributeMap>
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeEncode: (item: T) => AttributeMap
    readonly unsafeDecode: (item: StoredItem) => T
    readonly discriminator: keyof T & string
    readonly spec: Spec
    readonly variant: (name: keyof Spec) => unknown
}

/**
 * The codecs a discriminated entity needs: every variant, and every attribute of each.
 *
 * Coverage is total on two axes. Missing a variant is a compile error, and so is missing an
 * attribute of one — a variant that gains a field cannot silently stop being written.
 */
export type TaggedSpec<T, D extends keyof T> = {
    [V in T[D] & (string | number)]: ItemSpec<VariantOf<T, D, V>>
}

export type Tagged<T, D extends string = keyof T & string, Spec = unknown> = {
    /** Every attribute, or why one could not be written. */
    readonly encode: (item: T) => Result<AttributeMap>
    readonly unsafeEncode: (item: T) => AttributeMap
    /**
     * The attributes a patch names, or why one could not be written.
     *
     * The discriminator is required in a patch, because it is what chooses the codec. This is a type
     * error, not a runtime one: `Partial<T> & Pick<T, D>`.
     */
    readonly encodePartial: (
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /** One variant's codec, with everything {@link item} gives. */
    readonly variant: <V extends keyof Spec>(
        name: V,
    ) => ItemCodec<VariantOf<T, D & keyof T, V>, Spec[V]>
    readonly discriminator: D
    readonly spec: Spec
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
}

/**
 * How an entity that is a union of objects is stored.
 *
 * **Discriminated, not a bare `oneOf`.** Trying each member until one parses is ambiguous, order-
 * dependent, and can return a different variant than the one encoded — breaking
 * `decode ∘ encode = id`. A discriminator makes decode a lookup.
 *
 * Mirrors `tableEntry`'s discriminated key schema, so a union spells its discriminator the same way
 * for keys and for attributes.
 *
 * @example
 * ```ts
 * const Visit = tagged<Visit>()('type', {
 *     CHECKUP: { type: string('CHECKUP'), petId: string, vetId: string },
 *     VACCINATION: { type: string('VACCINATION'), petId: string, vaccine: string },
 * })
 * ```
 */
const dissect = <T extends Record<string, unknown>>(
    ks: readonly string[],
    options: readonly AnyObjectCodec[],
): DiscriminatedCodec<T, string, Record<string, unknown>> => {
    // **the empty key set, refused where the type cannot refuse it.** Over no discriminator every
    // value carries the empty assignment, so the first member answers for all of them and the
    // union is a union of one. The model carries no key set at all, so it never asks this; here
    // the key set is a `readonly string[]`, which cannot say it, and this is the gate
    if (ks.length === 0) {
        throw new CodecError(
            `a discriminated union needs at least one discriminator, and this one has none — every value carries the empty assignment, so the first variant would answer for all of them`,
        )
    }
    // **An empty option list is a mistake, not the bottom.** `never` is the bottom and says so as
    // a term; a `dunion` over no variants is what a typo or a `map` over an empty array produces,
    // and it admits nothing while no rule reads it as admitting nothing. The type refuses this
    // too — what reaches here is a cast, plain JavaScript, or an erased path
    if (options.length === 0) {
        throw new CodecError(
            `a discriminated union needs at least one option, and this one has none — no tag reaches a variant, so nothing can be written or read. If a codec that admits no value is what you meant, that is \`never\``,
        )
    }
    for (const option of options) {
        if (!option?.item?.spec) {
            throw new CodecError(
                `every option must be an object codec, and one of them is not — a bare spec has no variant to select, so pass \`object(...)\` around it`,
            )
        }
    }
    /**
     * **The term is a `union`, and the tag table is this builder's index over it.**
     *
     * A dissection is a certified union: its members are objects that differ at a required literal
     * key with disjoint alternatives, which is exactly what structural admission resolves and what
     * `Calculus.OrthS` certifies. So there is one sum in the term language, and the key set below
     * is a lookup this builder keeps for `variant`, `encodePartial` and the item path — a host
     * index, carried by no term.
     */
    const memberTerms = options.map((option) =>
        termOf(option.item as unknown as AnyCodec),
    )
    const unionDef = { kind: 'union', options: memberTerms } as const

    // **every member's assignment, read off the member's own body, and no two alike.** Both rules
    // are the index's, not the union's: the one-key refusals `discriminatedUnion` used to spell
    // inline are these two at one key. The union's own gate does not replace them, because a
    // duplicated index key is a different fact from a non-empty structural meet, and the index is
    // what needs it.
    const members = membersOf(
        ks,
        memberTerms.map((term, at) => {
            if (term.kind !== 'object') {
                throw new CodecError(
                    `every option must be an object codec, and option ${at} is a \`${term.kind}\` — a bare spec has no variant to select, so pass \`object(...)\` around it`,
                )
            }
            return [
                term.body,
                options[at]?.item as unknown as ItemCodec<T, unknown>,
            ] as const
        }),
    )
    if (failed(members)) throw members

    const { pick, tagOf } = byTagSem(ks, members) as unknown as {
        pick: (
            assignment: Readonly<Record<string, string>>,
        ) => Result<ItemCodec<T, unknown>>
        tagOf: (item: Partial<T>) => Result<Readonly<Record<string, string>>>
    }

    // **the published one-key surface carries `discriminator`, and this is that name.** Where the
    // key set has one element, that element *is* the discriminator: it is the whole set, not the
    // head of a list. Where it has several there is no such name, and the codec carries `keys`
    // instead — so the field is absent rather than holding one of several
    const [only, ...rest] = ks
    const oneKey = rest.length === 0 ? (only as string) : undefined

    const self = {
        encode: (item: T) =>
            andThen(andThen(tagOf(item), pick), (variant) =>
                variant.encode(item as never),
            ),
        encodePartial: (patch: Partial<T>) =>
            andThen(andThen(tagOf(patch), pick), (variant) =>
                variant.encodePartial(patch as never),
            ),
        decode: (item: StoredItem) =>
            andThen(andThen(readTags(item, ks), pick), (variant) =>
                variant.decode(item),
            ) as Result<T>,
        unsafeEncode: (item: T) => orThrow(self.encode(item)),
        unsafeEncodePartial: (patch: Partial<T>) =>
            orThrow(self.encodePartial(patch)),
        unsafeDecode: (item: StoredItem) => orThrow(self.decode(item)),
        /**
         * One variant, selected by its assignment.
         *
         * An **object literal**, matched key by key with {@link sameAssignment}, so the selector is
         * the same unordered thing the term's key is. A bare tag is the one-key spelling and means
         * that tag at the one key there is; at several keys it names no member, which is what a
         * caller who wrote one meant to be told.
         */
        variant: (selector: unknown) => {
            const assignment =
                typeof selector === 'object' && selector !== null
                    ? Object.fromEntries(
                          Object.entries(selector).map(([name, tag]) => [
                              name,
                              String(tag),
                          ]),
                      )
                    : Object.fromEntries(
                          ks.map((name) => [name, String(selector)]),
                      )
            return members.find(([one]) =>
                sameAssignment(ks, one, assignment),
            )?.[1] as never
        },
        keys: ks,
        ...(oneKey === undefined ? {} : { discriminator: oneKey }),
        // at one key the spec is keyed by the tag, which is what a caller walking the variants
        // reads today; at several there is no one string to key it by, so it is the members' specs
        // in the order the caller declared them
        spec:
            oneKey === undefined
                ? members.map(([, variant]) => variant.spec)
                : Object.fromEntries(
                      members.map(([assignment, variant]) => [
                          assignment[oneKey],
                          variant.spec,
                      ]),
                  ),
        def: unionDef,
    }

    const nested = codecOfTerm<T, Attribute<'M'>>(unionDef)
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        item: self as unknown as Tagged<T, string, Record<string, unknown>>,
        // **The slice keeps every key**, at one member as at several. A key the clause pins to one
        // tag is a constant key on the result, and no normalisation drops a constant key: the
        // codec writes the tag out of the member's own field, so every item carries it whatever
        // the key set says. So a one-member result is a one-member dissection that still reads its
        // key, and `dissect` is handed the same `ks` it was built with.
        extract: (clause: Readonly<Record<string, unknown>>) =>
            slicedDissection(ks, options, clause, true),
        exclude: (clause: Readonly<Record<string, unknown>>) =>
            slicedDissection(ks, options, clause, false),
    } as DiscriminatedCodec<T, string, Record<string, unknown>>
}

/**
 * A dissection's slice: the same keys, the members the clause keeps, and `never` where it keeps
 * none.
 *
 * `never` and not an empty dissection, which `dissect` refuses: an empty option list is what a typo
 * produces, so a rule reading it as the bottom reads that accident as intent. An extraction that
 * keeps nothing is the bottom on purpose, and there is one name for the bottom.
 */
const slicedDissection = (
    ks: readonly string[],
    options: readonly AnyObjectCodec[],
    clause: Readonly<Record<string, unknown>>,
    keep: boolean,
): unknown => {
    const kept = sliced(options, clause, keep)
    return kept.length === 0 ? never : dissect(ks, kept)
}

// ── unions with no discriminator ────────────────────────────────────

/**
 * Whether two variants can ever hold the same set of attribute names.
 *
 * A variant admits every name set between its required keys and its declared keys. Two such
 * intervals intersect exactly when each variant's required keys are all declared by the other —
 * which makes collision decidable at declaration, before any item exists.
 *
 * Prior art: degenerate's `VariantOverlapAnalyzer` runs the same check while generating Dart from
 * an OpenAPI spec and warns "consider adding a discriminator". It has to be conservative — it works
 * from a spec it did not write and can only report what it can *prove* — and it cannot refuse,
 * because real specs violate `oneOf` constantly. A hand-written codec is not so constrained: the
 * rule below is exact rather than one-sided, and a collision is an error rather than a warning.
 */
type Collides<A, B> = [Exclude<RequiredKeysOf<A>, keyof B>] extends [never]
    ? [Exclude<RequiredKeysOf<B>, keyof A>] extends [never]
        ? true
        : false
    : false

type RequiredKeysOf<Spec> = {
    [K in keyof Spec]-?: Spec[K] extends { readonly [optionalMarker]: true }
        ? never
        : K
}[keyof Spec]

/**
 * **A type that is a literal rather than a base.**
 *
 * The type level's reading of "this name is pinned to a literal", and it has to be a reading:
 * nothing in a codec's *type* says which constructor built it, so the question is put to the type
 * the codec decodes to. `'a'` and `'a' | 'b'` answer `true`; `string`, `number` and `boolean`
 * answer `false`, each excluded by its own row, because a base is assignable *from* its literals
 * and `extends` alone cannot tell the two apart.
 *
 * **Where this and the runtime disagree, and it is one case.** `literalsOf` reads the *term* and
 * accepts a `literal`, a `refine` over one included. A `held` or `custom` whose adapter happens to
 * decode to a literal type is read as pinned here and is not read as pinned there, so such a pair
 * would declare and then be ambiguous on the first item. An adapter that narrows to a literal type
 * is the only way to write it.
 */
type PinsALiteral<V> = [V] extends [never]
    ? false
    : string extends V
      ? false
      : number extends V
        ? false
        : boolean extends V
          ? false
          : [V] extends [string | number | boolean]
            ? true
            : false

/** What a spec declares at one name, as the type that name decodes to. */
type PinnedAt<Spec, K extends PropertyKey> = K extends keyof Spec
    ? Spec[K] extends AttributeCodec<infer V, AttributeValue>
        ? V
        : never
    : never

/**
 * **Two specs pin one shared required name to alternatives with nothing in common.**
 *
 * `Calculus.OrthS` written in the type, and `required` on both sides is a rule rather than a
 * precaution: two objects sharing an *optional* literal name with disjoint alternatives both admit
 * the map that omits the name, so a mark-blind test would certify a pair no value can resolve.
 *
 * At some shared name, not at the first, and the mapped type over the intersection of the two
 * required key sets is what makes the answer independent of the order they were written in.
 */
type SharedRequired<A, B> = Extract<
    RequiredKeysOf<A> & RequiredKeysOf<B>,
    PropertyKey
>

type LiteralsApart<A, B> = true extends {
    [K in SharedRequired<A, B>]: PinsALiteral<PinnedAt<A, K>> extends true
        ? PinsALiteral<PinnedAt<B, K>> extends true
            ? [PinnedAt<A, K> & PinnedAt<B, K>] extends [never]
                ? true
                : false
            : false
        : false
}[SharedRequired<A, B>]
    ? true
    : false

/**
 * **The structural meet of two object options**: some value satisfies both structures.
 *
 * The whole of what structural admission decides, in the type. `denote.ts` reads a value's names
 * and then every literal field it carries; this asks the same two questions of the declarations.
 * The name intervals must meet — {@link Collides} — *and* no shared required literal name may tell
 * the two apart. Either alone is not the rule: names alone refuse
 * `union([object({ kind: string('a'), x: string }), object({ kind: string('b'), x: number })])`,
 * which resolves; literals alone accept two options with no name in common at all, which do not
 * collide in the first place.
 */
type StructuralMeet<A, B> = Collides<A, B> extends true
    ? LiteralsApart<A, B> extends true
        ? false
        : true
    : false

type PairwiseConflictsFrom<
    Head,
    Rest extends readonly unknown[],
    Label extends string,
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (StructuralMeet<Head, Next> extends true
                ? `${Label} ${At} and ${Cursor['length']}`
                : never)
          | PairwiseConflictsFrom<Head, Tail, Label, At, [...Cursor, unknown]>
    : never

/**
 * **Which pairs of options meet**, as `${Label} i and j`, over every pair once.
 *
 * `Label` is a string and not a second predicate, because TypeScript has no way to pass one: a
 * higher-kinded parameter would be what the walk actually wants, and the walk is the part worth
 * having once.
 */
type PairwiseConflicts<
    Specs extends readonly unknown[],
    Label extends string,
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | PairwiseConflictsFrom<
                Head,
                Rest,
                Label,
                Cursor['length'],
                [...Cursor, unknown]
            >
          | PairwiseConflicts<Rest, Label, [...Cursor, unknown]>
    : never

/**
 * Rejects a declaration whose variants cannot be told apart, at the declaration rather than on the
 * first item that collides in production.
 */
export type ValidateVariants<Specs extends readonly unknown[]> = [
    PairwiseConflicts<Specs, 'variants'>,
] extends [never]
    ? unknown
    : ErrorMessage<`[untagged] ${PairwiseConflicts<Specs, 'variants'>} can hold the same attributes and cannot be told apart; give them a discriminator, or a literal field that tells them apart`>

/**
 * Whether two options read back as types a value could not choose between.
 *
 * One direction is enough to be ambiguous: if everything of A's type is also a valid B, a value of
 * that type matches both. `string` and `decimal` both read back as `string`, so *every* value is
 * ambiguous — which is also why the union is ill-formed rather than merely risky: its entity type is
 * `string`, so nothing about a value says which option produced it and `decode ∘ encode = id` cannot
 * hold. `string('A')` and `string('B')` read back as `'A'` and `'B'`, which no value satisfies
 * both of.
 */
type Overlaps<A, B> = [Decoded<A>] extends [Decoded<B>]
    ? true
    : [Decoded<B>] extends [Decoded<A>]
      ? true
      : false

/**
 * Object options are exempt, because a different rule already covers them.
 *
 * Two object options are told apart by their structure, which is neither stricter nor looser than
 * their types but a different question: `{ a, b }` is assignable to `{ a }`, and yet an item
 * carrying both attributes is admitted by only one of them, while two options whose types differ at
 * a field no literal pins are not told apart at all. Judging those by type would refuse
 * declarations that work and accept declarations that do not, so they are judged by
 * {@link StructuralMeet} instead.
 */
type BothObjects<A, B> = A extends AnyObjectCodec
    ? B extends AnyObjectCodec
        ? true
        : false
    : false

/**
 * **One option's decoded type is a strict subtype of another's**, so every value it admits, the
 * other admits too.
 *
 * `Overlaps` above answers assignability *either* way round and reports ambiguity. This is the
 * half of it where the containment is one-directional, and it is a different failure with
 * different advice: §5's `select` acts only where exactly one option admits, so the narrower
 * option is never selected and no discriminator reaches it.
 *
 * Mutual assignability answers `false` here and falls through to `Overlaps`, which is the right
 * split: two options that read back as the *same* type are ambiguous, and one inside the other is
 * dead. `union([string('A'), string('B')])` answers `false` on both counts, neither literal being
 * assignable to the other, and declares.
 */
type Restricts<A, B> = [Decoded<A>] extends [Decoded<B>]
    ? [Decoded<B>] extends [Decoded<A>]
        ? false
        : true
    : false

type RestrictsFrom<
    Head,
    Rest extends readonly unknown[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (BothObjects<Head, Next> extends true
                ? never
                : Restricts<Head, Next> extends true
                  ? `option ${At} inside option ${Cursor['length']}`
                  : Restricts<Next, Head> extends true
                    ? `option ${Cursor['length']} inside option ${At}`
                    : never)
          | RestrictsFrom<Head, Tail, At, [...Cursor, unknown]>
    : never

type Restricting<
    Options extends readonly unknown[],
    Cursor extends readonly unknown[] = [],
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | RestrictsFrom<Head, Rest, Cursor['length'], [...Cursor, unknown]>
          | Restricting<Rest, [...Cursor, unknown]>
    : never

type OverlapsFrom<
    Head,
    Rest extends readonly unknown[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (BothObjects<Head, Next> extends true
                ? never
                : Overlaps<Head, Next> extends true
                  ? `options ${At} and ${Cursor['length']}`
                  : never)
          | OverlapsFrom<Head, Tail, At, [...Cursor, unknown]>
    : never

type Overlapping<
    Options extends readonly unknown[],
    Cursor extends readonly unknown[] = [],
> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | OverlapsFrom<Head, Rest, Cursor['length'], [...Cursor, unknown]>
          | Overlapping<Rest, [...Cursor, unknown]>
    : never

/**
 * Whether any option is an `opaque` — the one option that cannot share a union.
 *
 * Matched on the **term's kind**, which is why {@link opaque} narrows its `def`. Not on the decoded
 * type: an adapter at an `unknown` outer type also reads back as `unknown` and is not `opaque`,
 * because it admits exactly what its own conversion admits and that may be a single value. What
 * this rule is about is a term that admits *everything*, and only the term says so.
 */
type HasOpaque<Options extends readonly unknown[]> = Options extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ? Head extends
          | { readonly def: { readonly kind: 'opaq' } }
          | { readonly def: OpaquePolicyDef }
        ? true
        : HasOpaque<Rest>
    : false

/**
 * Four rules, in the order that gives the more specific message.
 *
 * **The two containment rules are reported first, because their advice differs.** The other two
 * failures are ambiguity, and the answer to ambiguity is a discriminator. Containment is not
 * ambiguity: where one option admits every value another admits, §5's `select` acts nowhere on the
 * narrower one, so it is a declared option no value reaches. No discriminator fixes it and no
 * ranking resolves it — the option has to go, and the message has to say so.
 *
 * **`opaque` is the containment rule at its widest**, and it is matched on the term's kind rather
 * than on the decoded type, because it reads back as `unknown`. {@link Restricting} is the same
 * rule where the decoded types say it: a literal inside its base, a set of a literal inside the
 * plain set. Both would otherwise fall to the overlap clause and be offered the discriminator
 * advice, which is why the order is load-bearing rather than cosmetic.
 *
 * The runtime carries the same two rules in the same order — `term.ts`'s `restricts` ahead of the
 * occupancy rows — so a cast that reaches past this gets the same sentence rather than a different
 * one.
 *
 * An overlap is the deeper of the remaining two — the union cannot round-trip at all — so it is
 * reported before a name collision, which {@link ValidateVariants} reports.
 */
export type ValidateOptions<Options extends readonly unknown[]> =
    HasOpaque<Options> extends true
        ? ErrorMessage<`[union] one option is \`opaque\`, which admits every value the others admit — so no value can select between them and the others can never be chosen. Remove the \`opaque\` option; a discriminator does not fix this`>
        : [Restricting<Options>] extends [never]
          ? [Overlapping<Options>] extends [never]
              ? ValidateVariants<ObjectSpecsOf<Options>>
              : ErrorMessage<`[union] ${Overlapping<Options>} read back as the same type, so nothing about a value says which one it came from — give them a discriminator and use discriminatedUnion`>
          : ErrorMessage<`[union] ${Restricting<Options>}: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this`>

/**
 * An object codec with its spec forgotten — the constraint form, as {@link AnyCodec} is for codecs.
 *
 * Structural, and deliberately: it asks for the one member that says "I am an object codec and this
 * is what I declare". A bare spec record does not have it, so passing one where an option is expected
 * is refused rather than silently read as a codec.
 */
export type AnyObjectCodec = {
    readonly item: {
        // `never` in and `unknown` out, the same erasure {@link AnyCodec} uses, so every object codec
        // fits and none of them has to be named
        readonly encode: (item: never) => unknown
        readonly decode: (item: StoredItem) => unknown
        readonly spec: Record<string, ObjectSlot>
    }
}

/**
 * Whether every option is an object codec, which decides whether the union has an item reading.
 */
export type AllObjects<Options extends readonly unknown[]> =
    Options extends readonly [
        infer Head,
        ...infer Rest extends readonly unknown[],
    ]
        ? Head extends AnyObjectCodec | AnyTaggedCodec
            ? AllObjects<Rest>
            : false
        : true

/**
 * A tagged codec with its variants forgotten — {@link AnyObjectCodec} for a `discriminatedUnion`.
 *
 * A tagged option reads a whole item as readily as an object one: its `Tagged` carries the same
 * `encode` and `decode` over an item, and the union's item path delegates to it unchanged. What it
 * does not carry is a record of attributes at `spec` — that position holds the tag map — so
 * `AnyObjectCodec` does not match it and a union holding one was told it had no whole-item
 * reading. `discriminator` is the member that says which of the two this is.
 */
type AnyTaggedCodec = {
    readonly item: {
        readonly encode: (item: never) => unknown
        readonly decode: (item: StoredItem) => unknown
        readonly discriminator: string
    }
}

/**
 * The specs of the object options, with the others dropped.
 *
 * Only object options can collide on attribute names, so only they are checked. Positions in the
 * message {@link ValidateVariants} produces therefore count object options — the same thing for the
 * all-object union that is the common case.
 *
 * **A tagged option is one of the others, and its `spec` is the trap that says why.** A
 * {@link Tagged} carries its variants keyed by tag, so `item.spec` there is the *tag map* —
 * `{ placed: …, delivered: … }` — and not a record of attributes. Read as one, two tagged options
 * both "require" `placed` and `delivered`, {@link Collides} answers true, and a union of two
 * tagged options was refused whatever names its variants carried. That refusal was wrong in both halves: the specs
 * compared are not attribute specs, and the question is not asked of a tagged option at all.
 *
 * {@link identifies} is why it is not asked. A tag lookup fails for a value carrying no tag it
 * knows, so a tagged option identifies its own values and {@link separable} certifies it against
 * anything — the runtime selects it by attempting, never by names. Dropping it here is what makes
 * the two halves agree.
 *
 * Nothing is lost. Ambiguity between tagged options is still refused by the two clauses ahead of
 * this one: {@link Restricting} where one option's entity is a subtype of another's, and
 * {@link Overlapping} where they read back as the same type.
 *
 * This is what lets the two axes of a product nest — the outer {@link union} picking a group, an
 * inner {@link discriminatedUnion} picking the variant by tag — where neither combinator spans
 * both axes alone.
 */
export type ObjectSpecsOf<Options extends readonly unknown[]> =
    Options extends readonly [
        infer Head,
        ...infer Rest extends readonly unknown[],
    ]
        ? Head extends { readonly item: { readonly discriminator: string } }
            ? ObjectSpecsOf<Rest>
            : Head extends { readonly item: { readonly spec: infer S } }
              ? [S, ...ObjectSpecsOf<Rest>]
              : ObjectSpecsOf<Rest>
        : []

/** The entity a list of options describes: whatever any one of them reads back. */
export type DerivedUnion<Options extends readonly unknown[]> = {
    [I in keyof Options]: Decoded<Options[I]>
}[number]

/** What a union writes: whatever the option it chose writes. */
export type WrittenBy<Options extends readonly unknown[]> = Extract<
    { [I in keyof Options]: AttributeOf<Options[I]> }[number],
    AttributeValue
>

/** What each option declares, read off the options. */
export type SpecsOf<Options extends readonly unknown[]> = {
    [I in keyof Options]: Options[I] extends {
        readonly item: { readonly spec: infer S }
    }
        ? S
        : never
}

/** The variants of an untagged union. There is no tag, so there is nothing to key them by. */
export type UntaggedSpec<T> = readonly ItemSpec<T>[]

/**
 * The entity a list of variant specs describes: one variant, or another.
 *
 * The union and not the merge, which is the same distinction {@link EncodedVariants} makes about the
 * stored side — a row is exactly one variant, so an attribute only one of them declares is not an
 * attribute the entity always has.
 */
export type DerivedVariants<Specs extends readonly unknown[]> = {
    [I in keyof Specs]: show<ObjectOf<Specs[I]>>
}[number]

export type Untagged<T, Specs extends readonly unknown[] = UntaggedSpec<T>> = {
    /** Every attribute, or why one could not be written. */
    readonly encode: (item: T) => Result<AttributeMap>
    readonly unsafeEncode: (item: T) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (item: StoredItem) => Result<T>
    readonly unsafeDecode: (item: StoredItem) => T
    /**
     * One variant by position.
     *
     * Indexing a list with a `number` yields `| undefined` under `noUncheckedIndexedAccess`, which is
     * a statement about a position that may not exist — and it landed on the *codec*, so reaching a
     * variant written as a literal one line below its declaration needed a `!`. Getting the index
     * right is the caller's job, as with any list; what comes back is a codec.
     */
    readonly variant: <I extends number>(
        index: I,
    ) => ItemCodec<show<ObjectOf<NonNullable<Specs[I]>>>, NonNullable<Specs[I]>>
    readonly spec: Specs
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Specs>
}

/**
 * One option of a union, reduced to what matching it actually asks.
 *
 * **Every option is admitted by attempt**, an object option included, as the model's `admitOptV`
 * and `admitOptA` admit. The kind of the value is a cheap filter in front of the attempt, and the
 * names present select nothing. The declaration guard makes the attempt decide: two options that
 * both admit one value are refused where the union is declared, so at most one attempt succeeds.
 */
export type Option = {
    readonly codec: AnyCodec
    /** The member it writes, where the kind alone decides — a cheap filter on decode. */
    readonly member: AttributeName | undefined
    /** The kinds of value it takes, where the kind alone decides — the same filter on encode. */
    readonly carries: readonly Shape[] | undefined
    /** The whole-item reading, for object options only. */
    readonly item: ItemCodec<Record<string, unknown>, unknown> | undefined
    /** The names it declares, for object options only. */
    readonly declares: ReadonlySet<string> | undefined
    /** How it is named in a message — written the way it was declared. */
    readonly describe: string
}

const optionOf = (codec: AnyCodec): Option => {
    /**
     * Read from the definition, not from the presence of `.item`.
     *
     * A nested union has an `.item` too, and its `spec` is the *list* of its options rather than a
     * record of attributes — so testing for the member classified a union as an object and then walked
     * that list as though `0` and `1` were attribute names. `attributes` is the definition of an
     * object codec and of nothing else.
     */
    const base = optionOfTerm(termOf(codec))
    // a tagged builder carries a whole-item reading of its own — its `Tagged` — over a term that
    // is now an ordinary union, so the test is the presence of that reading and not the kind
    const asObject =
        codec.def?.kind === 'object' ||
        (codec.def?.kind === 'union' &&
            !!(codec as unknown as Partial<AnyObjectCodec>).item)
            ? (codec as unknown as Partial<AnyObjectCodec>).item
            : undefined
    return asObject
        ? {
              ...base,
              item: asObject as unknown as ItemCodec<
                  Record<string, unknown>,
                  unknown
              >,
          }
        : base
}

/**
 * The tag values a variant answers to — its discriminator's whole admissible set, not one value.
 *
 * A variant may span several tags, and this codebase relies on it: a carrier declared
 * `carrierId: string('ACME', 'GLOBEX')` is *one* variant covering two stored values, which is why
 * {@link VariantOf} asks whether a tag is *among* a member's tags rather than equal to it.
 */
type TagsOf<Spec, D extends PropertyKey> = Spec extends unknown
    ? // distributed over the *variants*: the conditional below is on `Spec[D]`, so a union of specs
      // handed in whole would ask about a union of codecs and answer nothing
      D extends keyof Spec
        ? Spec[D] extends AttributeCodec<infer Tag, AttributeValue>
            ? // a tag is stored as `S` or as `N`, so a numeric enum indexes variants as readily as
              // a string one — `readTag` reads either member and keys on the text it carries
              Tag extends string | number
                ? Tag
                : never
            : never
        : never
    : never

/**
 * The options keyed by their own tag, which is what a lookup needs.
 *
 * Derived rather than declared. A record keyed by tag value repeats what the option's own `literal`
 * already says, so `{ SHOT: { type: string('CHECKUP') } }` is expressible and the two can disagree.
 * Reading the tag off the option makes that unrepresentable — and it is how `zod` does it.
 */
type ByTag<Specs extends readonly unknown[], D extends PropertyKey> = {
    [Spec in Specs[number] as TagsOf<Spec, D>]: Spec
}

/**
 * Whether a tag set has more than one member.
 *
 * The intersection of a union of distinct literals is `never`, and of a single literal is itself —
 * so this is the one distinction a conditional cannot make directly, because `extends` on a naked
 * type parameter distributes and every branch then sees one member.
 */
type TagIntersection<Tags> = (
    Tags extends unknown
        ? (x: Tags) => void
        : never
) extends (x: infer One) => void
    ? One
    : never

/**
 * The options whose discriminator literal admits more than one value.
 *
 * Indexed by position like {@link SharedAssignments}, and one option at a time rather than a
 * pair: this is
 * a defect in a single option, so naming its neighbour would say nothing.
 */
type MultiTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | ([TagsOf<Head, D>] extends [TagIntersection<TagsOf<Head, D>>]
                ? never
                : `option ${Cursor['length']}`)
          | MultiTagged<Rest, D, [...Cursor, unknown]>
    : never

/**
 * The assignment a variant's spec names: its tag at each key.
 *
 * An **object type**, so the type level carries what the term carries and no more. An object type
 * has no order on its keys, which is the property `Calculus.Assignment` has by being a function on
 * a `Finset`; a tuple would put the order back and make two types for one dissection.
 */
export type AssignmentOf<Spec, Ks extends readonly PropertyKey[]> = {
    readonly [K in Ks[number]]: TagsOf<Spec, K>
}

/**
 * A key that **some** option names with no tag: that option cannot be found at it.
 *
 * Asked of each option in turn, and not of `Specs[number]`. Asking the union of the specs answers a
 * question about the collection — "does anybody name this key" — and an option that names none of
 * them passes, because its neighbours answered for it. Every other rule here is already distributed
 * over the options one at a time ({@link MultiTagged}) or over their pairs
 * ({@link SharedAssignments}, {@link Overlapping}); this is the same shape, and it was the one
 * clause that was not.
 */
type UntaggedKey<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | {
                [K in Ks[number]]: [TagsOf<Head, K>] extends [never] ? K : never
            }[Ks[number]]
          | UntaggedKey<Rest, Ks>
    : never

/** An option whose literal at some key admits more than one value, at any key. */
type MultiTaggedAnywhere<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = { [K in Ks[number]]: MultiTagged<Specs, K> }[Ks[number]]

/**
 * Whether two options differ at some key.
 *
 * **At some key, not at the first.** Two members of a dissection are distinct when their
 * assignments differ anywhere, and asking that of every key at once is what makes the answer
 * independent of how the keys were written.
 */
type DiffersSomewhere<A, B, Ks extends readonly PropertyKey[]> = true extends {
    [K in Ks[number]]: [TagsOf<A, K> & TagsOf<B, K>] extends [never]
        ? true
        : false
}[Ks[number]]
    ? true
    : false

type SharedAssignmentsFrom<
    Head,
    Rest extends readonly unknown[],
    Ks extends readonly PropertyKey[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (DiffersSomewhere<Head, Next, Ks> extends true
                ? never
                : `options ${At} and ${Cursor['length']}`)
          | SharedAssignmentsFrom<Head, Tail, Ks, At, [...Cursor, unknown]>
    : never

/**
 * Which pairs of options carry one assignment, as `options i and j`.
 *
 * A discriminated union is a *lookup*, so two options claiming one assignment is not an ambiguity
 * to be resolved when a value turns up — it is a table with one key written twice, and the second
 * write wins in silence. Decidable from the declaration, so it is refused there, the way
 * {@link Overlapping} refuses an untagged union's.
 */
type SharedAssignments<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
    Cursor extends readonly unknown[] = [],
> = Specs extends readonly [
    infer Head,
    ...infer Rest extends readonly unknown[],
]
    ?
          | SharedAssignmentsFrom<
                Head,
                Rest,
                Ks,
                Cursor['length'],
                [...Cursor, unknown]
            >
          | SharedAssignments<Rest, Ks, [...Cursor, unknown]>
    : never

/**
 * Nothing, or the fact that the options cannot be looked up — at a key set.
 *
 * The same three failures in the same order, asked of every key instead of one. An option that
 * does not name a key with a `literal` cannot be found at all; an option whose literal admits
 * several values is arity one's refusal; two options carrying one assignment can each be found and
 * only one ever is.
 *
 * The arity check comes before the sharing check because it is a defect in one option rather than
 * in a pair, and because an option with two tags has to lose one before the sharing question is
 * even well posed.
 */
type MembersTagged<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = Specs extends readonly []
    ? ErrorMessage<'[discriminatedUnion] a discriminated union needs at least one option, and this one has none — no tag reaches a variant, so nothing can be written or read. If a codec that admits no value is what you meant, that is `never`'>
    : [UntaggedKey<Specs, Ks>] extends [never]
      ? [MultiTaggedAnywhere<Specs, Ks>] extends [never]
          ? [SharedAssignments<Specs, Ks>] extends [never]
              ? unknown
              : ErrorMessage<`[discriminatedUnion] ${SharedAssignments<Specs, Ks>} answer to the same discriminator value, and a lookup reaches only one of them — give them distinct values`>
          : ErrorMessage<`[discriminatedUnion] ${MultiTaggedAnywhere<Specs, Ks>} names the discriminator with a literal admitting several values, and a variant answers to exactly one tag — split it into one option per value`>
      : ErrorMessage<'[discriminatedUnion] every option must name the discriminator with a literal at `string`, `number` or `decimal`, or a lookup cannot find it'>

/**
 * The one-key gate, as the instance of {@link MembersTagged} at a one-element key set.
 *
 * One rule and not two: the messages are the same strings at one key, so the surface a caller
 * reads did not move, and a change to the rule cannot reach one arity and miss the other.
 */
type EveryOptionTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
> = MembersTagged<Specs, readonly [D]>

/* ── the slice of a union ─────────────────────────────────────────────────────────────── */

/**
 * **A clause**: a partial assignment pinning each key it names to a **literal codec**.
 *
 * `Calculus.AltClause` at the host, whose value at each key is `Alts` — a base with a non-empty set
 * of that base's carriers. A codec and not a tag, because a tag is text and text does not say which
 * base it was written at: `string('1')` and `decimal('1')` carry the same character and are read
 * from different members, and `number(1)` is a third thing again. A clause spelled as text cannot
 * tell the three apart, and one spelled as a codec cannot fail to.
 *
 * A set of tags is a literal with several alternatives — `string('dog', 'cat')` — so there is one
 * spelling and not two. An object literal and not a list of pairs, so the keys carry no order and
 * no repeat, which is the reason the model's clause is a `Finset` and a function on it.
 *
 * **Over the member specs, not over the entity type.** A union is a pair — the type it carries and
 * the structure it is — and the slice acts on the structure. `S` is the union of the members'
 * specs, and {@link ClauseKeys} distributes over it explicitly: a mapped type whose constraint is
 * `keyof S` would be homomorphic and distribute on its own, giving one clause type per member.
 */
export type ClauseOf<S> = {
    readonly [K in ClauseKeys<S>]?: AnyLiteralCodec
}

/** Every name some member requires, which is every name a clause may speak about. */
type ClauseKeys<S> = S extends unknown
    ? Extract<RequiredKeysOf<S>, PropertyKey>
    : never

/**
 * The shape of a clause value: something with a term and a read.
 *
 * Read-only and structural, not `AttributeCodec<…>` at the members' tags. A codec is invariant in
 * the value it carries — `encode` takes it — so a slot typed at the members' whole tag set would
 * refuse `string('CHECKUP')` against members carrying `'CHECKUP' | 'SHOT'`, which is every clause
 * that selects anything. The slot admits any codec and {@link ValidateClause} is what asks whether
 * it fits, which also lets the refusal name the key.
 */
type AnyLiteralCodec = {
    readonly def: Term
    readonly decode: (attribute: AttributeValue) => Result<unknown>
}

/** The codec a spec declares at one name, or nothing where it declares none. */
type FieldAt<Spec, K> = K extends keyof Spec ? Spec[K] : never

/**
 * **Whether one member's spec answers a clause** — `clauseKeeps` at the type, reading the same two
 * facts off the same declaration.
 *
 * At every clause key the member must **require** the name, write it at the clause's **attribute**,
 * and admit **only** values the clause admits. The attribute is what carries the base: `string`
 * writes `S`, `decimal` and `number` write `N`, and those two are told apart by the values, `'1'`
 * against `1`. So the pair (attribute, values) is a base and its alternatives, and the two levels
 * cannot disagree about which member a clause keeps.
 */
type SpecKeeps<Spec, C> = {
    [K in keyof C]-?: K extends RequiredKeysOf<Spec>
        ? [AttributeOf<FieldAt<Spec, K>>] extends [AttributeOf<C[K]>]
            ? [Decoded<FieldAt<Spec, K>>] extends [Decoded<C[K]>]
                ? never
                : K
            : K
        : K
}[keyof C] extends never
    ? true
    : false

/**
 * **The member specs a clause keeps**, in the order they were declared.
 *
 * `Keep` is `true` for the extraction and `false` for the exclusion, so the two are one walk and
 * the complement cannot drift from the selection.
 */
export type Extracted<
    Specs extends readonly unknown[],
    C,
    Keep extends boolean = true,
> = Specs extends readonly [
    infer Head,
    ...infer Tail extends readonly unknown[],
]
    ? [
          ...(SpecKeeps<Head, C> extends Keep ? [Head] : []),
          ...Extracted<Tail, C, Keep>,
      ]
    : []

/** …and the ones it rejects, the same walk at the complement. */
export type Excluded<Specs extends readonly unknown[], C> = Extracted<
    Specs,
    C,
    false
>

/** The option codecs a clause keeps, read through each option's own spec. */
export type KeptOptions<
    Options extends readonly unknown[],
    C,
    Keep extends boolean = true,
> = Options extends readonly [
    infer Head,
    ...infer Tail extends readonly unknown[],
]
    ? [
          ...(SpecKeeps<SpecOf<Head>, C> extends Keep ? [Head] : []),
          ...KeptOptions<Tail, C, Keep>,
      ]
    : []

type SpecOf<Option> = Option extends {
    readonly item: { readonly spec: infer S }
}
    ? S
    : never

/** The members of a tag table a clause keeps, keyed as they were. */
export type KeptByTag<Spec, C, Keep extends boolean = true> = {
    [K in keyof Spec as SpecKeeps<Spec[K], C> extends Keep ? K : never]: Spec[K]
}

/** The entity a tag table describes, which is what its members describe. */
export type VariantsOf<Spec> = {
    [K in keyof Spec]: show<ObjectOf<Spec[K]>>
}[keyof Spec]

/**
 * The tags the members carry at one key, at one attribute — and only where the member pins a
 * literal there.
 *
 * The last clause is what stops a clause selecting on a plain field: `toy: string` writes an `S`
 * and admits every string, so a clause naming `'t'` would fit it and select nothing meaningful.
 */
type TagsAtSpecs<S, K, A> = S extends unknown
    ? K extends RequiredKeysOf<S>
        ? [AttributeOf<FieldAt<S, K>>] extends [A]
            ? PinsALiteral<Decoded<FieldAt<S, K>>> extends true
                ? Decoded<FieldAt<S, K>>
                : never
            : never
        : never
    : never

/** A clause key no member could ever answer, whatever the values turn out to be. */
type BadClauseKey<S, C> = {
    [K in keyof C]: PinsALiteral<Decoded<C[K]>> extends true
        ? [TagsAtSpecs<S, K, AttributeOf<C[K]>>] extends [never]
            ? K
            : [Decoded<C[K]>] extends [TagsAtSpecs<S, K, AttributeOf<C[K]>>]
              ? never
              : K
        : K
}[keyof C]

/**
 * Rejects a clause a member could never answer, at the call rather than on the result.
 *
 * Three failures with one message, because they are one mistake in three spellings: a value that is
 * no literal at all, a literal at a base no member pins that key at, and a literal whose
 * alternatives no member carries. Each is decidable from the declaration, which is the line the
 * runtime's refusals draw too.
 */
export type ValidateClause<S, C> = [BadClauseKey<S, C>] extends [never]
    ? unknown
    : ErrorMessage<`[extract] the clause at '${BadClauseKey<S, C> & string}' is not a literal the members pin that key to — a clause pins each key it names to a literal codec at the base the members declare, written as \`string('a')\`, \`decimal('1')\` or \`number(1)\`, because a bare tag does not say which base it was written at`>

/**
 * The alternatives a clause pins one key to, or a refusal naming the key.
 *
 * A clause value is a codec and the question is asked of its term, which is where a base lives. The
 * type refuses a non-literal codec by its decoded type; this is the same refusal for a caller who
 * reached here through a cast or through plain JavaScript.
 *
 * A set of tags is `string('a', 'b')`, which is a union of literals, so the reader is
 * {@link literalAlternatives} and not a test for one constructor.
 */
const clauseLiteral = (name: string, value: unknown): NameForm => {
    const def = (value as { readonly def?: Term } | undefined)?.def
    const pinned = def && clauseForm(def)
    if (!pinned) {
        throw new CodecError(
            `the clause at '${name}' is not a literal codec — a clause pins each key it names to a literal, written as \`string('a')\`, \`decimal('1')\`, \`number(1)\`, \`boolean(true)\` or \`binary(...)\`, because a bare tag does not say which base it was written at`,
        )
    }
    return { required: true, ...pinned }
}

/**
 * **Whether a clause describes one member**: the member declares every clause key as a *required*
 * literal **at the clause's base**, and that literal's alternatives all lie inside the clause's.
 *
 * `required` is read for `Calculus.litSubAt`'s reason: an optional literal name admits the map that
 * omits the name, so the member holds values outside every fibre the clause describes.
 *
 * The base is compared before the alternatives, and a mismatch keeps the member out. That is
 * `Calculus.altsSub`, whose four rows are four bases and whose fall-through row is every pair that
 * does not share one.
 */
const clauseKeeps = (
    clause: ReadonlyMap<string, NameForm>,
    term: Term,
): boolean => {
    const literals = clauseLiteralsOf(term)
    if (!literals) return false
    for (const [name, pinned] of clause) {
        const mine = literals[name]
        if (!mine?.required || mine.form !== pinned.form) return false
        const inside = (mine.alts.ls as readonly LiteralValue[]).every((one) =>
            (pinned.alts.ls as readonly LiteralValue[]).some((tag) =>
                sameLiteral(one, tag),
            ),
        )
        if (!inside) return false
    }
    return true
}

/**
 * The members kept, with two refusals taken before anything is filtered.
 *
 * **A clause key no member pins to a literal**, and **a clause at a base no member carries at that
 * key**. Both keep nothing, and both keep nothing *whatever the values are*: they are facts about
 * the declaration, decidable before any item exists, and a clause that cannot describe a member is
 * a typo rather than an answer. An empty result stays a legitimate answer where the bases agree and
 * the alternatives simply do not meet, because that is a fact about values. That line is where the
 * foreign-key refusal already sits, and the base refusal sits beside it for the same reason.
 *
 * The model cannot have either failure — its clause keys are a subset of the dissection's by the
 * type, and `Alts` carries the base at the key — so both refusals are the host's own.
 */
const sliced = <O>(
    options: readonly O[],
    clause: Readonly<Record<string, unknown>>,
    keep: boolean,
): readonly O[] => {
    const terms = options.map((option) => termOf(option as unknown as AnyCodec))
    const pinned = new Map<string, Set<LiteralForm>>()
    for (const term of terms) {
        for (const [name, one] of Object.entries(
            clauseLiteralsOf(term) ?? {},
        )) {
            const bases = pinned.get(name) ?? new Set<LiteralForm>()
            bases.add(one.form)
            pinned.set(name, bases)
        }
    }
    const read = new Map<string, NameForm>()
    for (const [name, value] of Object.entries(clause)) {
        const bases = pinned.get(name)
        if (!bases) {
            throw new CodecError(
                `'${name}' is not a key any member pins to a literal, so a clause naming it selects nothing; the keys available are ${[...pinned.keys()].map((one) => `'${one}'`).join(', ') || '(none)'}`,
            )
        }
        const literal = clauseLiteral(name, value)
        if (!bases.has(literal.form)) {
            throw new CodecError(
                `the clause at '${name}' is a \`${literal.form}\` literal and no member pins '${name}' at that base, so it describes no member whatever its alternatives; the bases declared at '${name}' are ${[...bases].map((one) => `\`${one}\``).join(', ')}`,
            )
        }
        read.set(name, literal)
    }
    return options.filter(
        (_option, at) => clauseKeeps(read, terms[at] as Term) === keep,
    )
}

/**
 * A union of objects told apart by one attribute — `zod`'s `discriminatedUnion`, over an item.
 *
 * The stored value of the discriminator chooses the option, and each option says which value it is by
 * naming that attribute with a literal — `string('CHECKUP')`, `number(1)`, `decimal('1')`. A
 * lookup rather than a search: it cannot be ambiguous,
 * and it is the only union that can encode a *patch*, because a subset of the attributes does not say
 * which option it belongs to.
 *
 * The options are *codecs*, not bare specs, so an option that already has a name can be handed over
 * by it and a nested union reads the same as a nested anything else. What the union needs of an
 * option — its attributes, and what its discriminator admits — an object codec already carries.
 *
 * @example
 * ```ts
 * discriminatedUnion('type', [
 *     object({ type: string('CHECKUP'), petId: string, vetId: string }),
 *     object({ type: string('SHOT'), petId: string, vaccine: string }),
 * ])
 * ```
 */
export const mdunion = <
    const Ks extends readonly [string, ...string[]],
    const Options extends readonly AnyObjectCodec[],
>(
    ks: Ks,
    options: Options & MembersTagged<SpecsOf<Options>, Ks>,
): Dissection<Ks, Options> =>
    // one cast, at the one place where a runtime table meets a type computed from the specs: the
    // builder is written once over `readonly string[]`, and {@link Dissection} is what that builder
    // produces read at the arity the caller wrote
    dissect(ks, options as readonly AnyObjectCodec[]) as never

/**
 * A union of objects told apart by one attribute — `zod`'s `discriminatedUnion`, over an item.
 *
 * The stored value of the discriminator chooses the option, and each option says which value it is by
 * naming that attribute with a literal — `string('CHECKUP')`, `number(1)`, `decimal('1')`. A
 * lookup rather than a search: it cannot be ambiguous,
 * and it is the only union that can encode a *patch*, because a subset of the attributes does not say
 * which option it belongs to.
 *
 * The options are *codecs*, not bare specs, so an option that already has a name can be handed over
 * by it and a nested union reads the same as a nested anything else. What the union needs of an
 * option — its attributes, and what its discriminator admits — an object codec already carries.
 *
 * **{@link mdunion} at one discriminator**, and nothing else: the two spellings build the same term,
 * the same table and the same codec, so a caller can replace one with the other and change no other
 * line. This name is the one-key case because one discriminator is what almost every entity needs.
 *
 * @example
 * ```ts
 * discriminatedUnion('type', [
 *     object({ type: string('CHECKUP'), petId: string, vetId: string }),
 *     object({ type: string('SHOT'), petId: string, vaccine: string }),
 * ])
 * ```
 */
export const discriminatedUnion = <
    const D extends string,
    const Options extends readonly AnyObjectCodec[],
>(
    discriminator: D,
    options: Options & EveryOptionTagged<SpecsOf<Options>, D>,
): DiscriminatedCodec<
    DerivedVariants<SpecsOf<Options>>,
    D,
    ByTag<SpecsOf<Options>, D>
> =>
    // **the type arguments are given, not inferred, and that is what makes the alias cast-free.**
    // Inferring them from `options` would take `Options` to be the *intersection* the parameter
    // declares — `Options & MembersTagged<…>` — and the return type computed from that intersection
    // is not the one this signature promises. Pinned, `Dissection<readonly [D], Options>` reduces to
    // exactly the `DiscriminatedCodec` below, and `EveryOptionTagged<SpecsOf<Options>, D>` is
    // `MembersTagged<SpecsOf<Options>, readonly [D]>` by definition, so the argument needs nothing.
    mdunion<readonly [D], Options>([discriminator], options)

/**
 * **The term that admits no value**, and the unit the product and the slice need.
 *
 * `Term.never` on both sides. The model types it — `Typed.never` gives it the held set `HNever`,
 * which is `False` — and denotes it as `Codec.empty`, whose laws hold vacuously because both
 * domains are empty.
 *
 * **A constructor rather than a `discriminatedUnion` over no options.** The derived form works and
 * costs a structural test: an empty option list is a term a caller can build by accident, so every
 * rule reading it as the bottom reads that accident as intent, and the term carries a discriminator
 * no value will ever name. `discriminatedUnion` stays refused on an empty list — that list is a
 * typo or a `map` over an empty array — and this is the one name that reaches the bottom.
 *
 * The model makes it an option of any `union`: `False` is a subset of every held set, and §5's
 * (D) admits an option disjoint from its partner, which the bottom is from every held set, so
 * `union([X, never])` is `Typed`
 * (`dincomp_never_left`, `dincomp_never_right`). `union` here refuses it all the same, and on a
 * different ground: an option admitting nothing can never be chosen, which `restricts` answers
 * and which is a lint rather than a soundness rule. Well formed and useful are different claims,
 * and `.separations.lean` carries the divergence as a theorem.
 */
export const never: AttributeCodec<never, never> & {
    readonly def: { readonly kind: 'never' }
} = codecOfTerm({ kind: 'never' }) as AttributeCodec<never, never> & {
    readonly def: { readonly kind: 'never' }
}

/**
 * A union told apart by what each option holds, with no tag to switch on — `zod`'s `union`.
 *
 * Options are codecs of any kind, and the rule is the same for all of them: **exactly one** option
 * must match, or it is an error. What "match" means is the only thing that differs, and it differs
 * because the options do — see {@link Option}. Each option is attempted, and the option that
 * alone admits the value is chosen. An object option is no exception: the names present select
 * nothing.
 *
 * Ambiguity is reported rather than resolved by declaration order. Two options that can admit one
 * value are refused at the declaration where the guard can see it. Where the guard cannot, two
 * options that both admit one value are reported when that value turns up.
 *
 * **Refused rather than scored**, and that is what keeps `decode ∘ encode = id` where first-match
 * wins does not: the one option that admits a value is the one option that reads what it wrote, so
 * both directions reach the same variant. A tie-break would commit in silence to an owner of the
 * overlap that nobody named.
 *
 * @example
 * ```ts
 * union([object({ petId: string, price: decimal }), object({ petIds: array(string) })])
 * union([string, number])                    // an attribute that is either
 * union([object({ at: string }), string])     // a map or a bare string
 * ```
 */
export const union = <const Options extends readonly AnyCodec[]>(
    options: Options & ValidateOptions<Options>,
): UnionCodec<DerivedUnion<Options>, Options> => {
    const all: readonly Option[] = (options as readonly AnyCodec[]).map(
        optionOf,
    )

    /**
     * Two options that no *value* can choose between, refused where the declaration is.
     *
     * {@link separable} is the rule and states its own four exemptions; this is why the question is
     * asked *here*. `ValidateOptions` refuses the pairs no stored attribute can choose between at
     * compile time, by asking whether they read back as the same type. This is the other direction,
     * and the types cannot see it: `array(string)` and `array(number)` read back as different types
     * and are handed the same array. Asking once at the declaration reports it once, where asking
     * per encode would report it once per write forever.
     *
     * **Which containers separate turns on whether the container has an empty inhabitant**, and the
     * pairs that share a value share only that one:
     *
     *     array(string) / array(number)     `[]`
     *     open object of string / of number `{}`
     *     set(string) / set(number)         nothing
     *
     * So `array` and an open object stay refused and `set` does not, because **DynamoDB has no empty
     * set**. That is the asymmetry the term's own rows record — `[]` is admitted and an empty `Set`
     * is not — deciding a question about declarations. `codec.laws.spec.ts` pins both halves.
     *
     * **A sufficient condition, deliberately.** "No value can choose between these two" is not
     * decidable from two terms in general, so this refuses wherever it cannot show separation.
     * Widening it means adding a container that provably has no empty inhabitant, not weakening
     * what is here.
     */
    // **Every option has a term.** A `set` over a restricted element is spelled as a restriction
    // of the set, and a `set` whose element reduces to no base is refused by `.set()` at
    // construction — so the conversion is total here. This carried a `Term | undefined` and a row
    // for the absent case until the suite was run with the catch removed and stayed green
    const pairs = all.map((option) => ({
        option,
        term: option.codec.def,
    }))

    for (const [at, { option: first, term: x }] of pairs.entries()) {
        for (const { option: second, term: y } of pairs.slice(at + 1)) {
            if (separable(x, y)) continue
            // **The restriction refusal comes first, because its advice differs.** The two below
            // are ambiguity and the answer to ambiguity is a discriminator. This one is not:
            // every value the narrower option admits, the wider one admits too, so `select` acts
            // nowhere on the narrower and it can never be chosen. The option has to go. The
            // `opaque` refusal is the same sentence and `ValidateOptions` orders its clauses the
            // same way, for the same reason.
            const narrow = restricts(x, y)
                ? ([first, second] as const)
                : restricts(y, x)
                  ? ([second, first] as const)
                  : undefined
            if (narrow) {
                throw new CodecError(
                    `${narrow[0].describe} admits only values that ${narrow[1].describe} also admits, so no value can ever select it and the option can never be chosen. Remove it; a discriminator does not fix this`,
                )
            }
            // **The values, before the slots.** Where both options pin a set of values, the
            // values are what refused them and the slot they share is incidental — two `string`
            // literals always share `S`, and that says nothing about whether they are resolvable.
            // So this names what actually meets.
            const shared = sharedLiterals(x, y)
            if (shared?.length) {
                throw new CodecError(
                    `${first.describe} and ${second.describe} both carry ${shared.map(namedLiteral).join(', ')}, so no value and no stored attribute can choose between them; give the entity a discriminator and use discriminatedUnion`,
                )
            }
            // the label the refusal names, asked again on the path that is about to throw:
            // `separable` answers the `Bool` the model's `Orth` answers, so the meeting is
            // recomputed here rather than carried back through it
            const bothWrite = meet(occV(x), occV(y))
            if (bothWrite) {
                throw new CodecError(
                    `${first.describe} and ${second.describe} both take the same kind of value — ${bothWrite} — and neither checks what it is given, so no value can choose between them; give the entity a discriminator and use discriminatedUnion`,
                )
            }
            const bothRead = meet(occA(x), occA(y))
            if (bothRead) {
                throw new CodecError(
                    `${first.describe} and ${second.describe} both store '${bothRead}', and neither checks what it reads, so no stored attribute can choose between them; give the entity a discriminator and use discriminatedUnion`,
                )
            }
        }
    }

    type T = DerivedUnion<Options>

    const {
        pair: { encode: write, decode: read },
        only,
        onlyAdmitting,
        naming,
    } = altSem(all)

    const optionTerms = all.map((option) => termOf(option.codec))

    /**
     * The item reading's own matcher: the value is always a record, so the shape filter has nothing
     * to do, and each option is attempted. The names present select nothing, as the model's
     * `admitOptA` reads no name.
     */
    const readItem = (item: StoredItem): Result<T> => {
        const names = namesOf(item)
        return only(
            () => true,
            naming('this item', names),
            (option) =>
                (
                    option.item as ItemCodec<Record<string, unknown>, unknown>
                ).decode(item) as Result<T>,
        )
    }

    const writeItem = (item: T): Result<AttributeMap> => {
        const names = namesOf(item as Record<string, unknown>)
        return onlyAdmitting(
            () => true,
            naming('this entity', names),
            item,
            (option) =>
                (
                    option.item as ItemCodec<Record<string, unknown>, unknown>
                ).encode(item as Record<string, unknown>),
        )
    }

    /**
     * The same union read as a whole item, which only an all-object union has.
     *
     * An item is a map, so an option that writes anything else has nothing to contribute at the top
     * level. The type says so — {@link UnionCodec} replaces this with a message where it does not
     * apply — and the runtime is built either way rather than branching, because an option that could
     * not be reached here also cannot be selected here: `declares` is what selects, and only an
     * object option has it.
     */
    const self: Untagged<T, SpecsOf<Options>> = {
        encode: writeItem,
        decode: readItem,
        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        variant: (index) => (all[index] as Option).item as never,
        spec: (options as readonly AnyCodec[]).map(
            (option) =>
                (option as unknown as Partial<AnyObjectCodec>).item?.spec,
        ) as never,
        def: {
            kind: 'union',
            options: optionTerms,
        },
    }

    // the option chosen writes what it writes; `WrittenBy` is the union of those, which no single
    // call can be narrowed to from inside
    // the resolution is erased — a sum's rule is about options, not about the type they carry —
    // so the two halves get their types back here, once, the way `codecOfTerm` does for a term
    const encode = write as (value: T) => Result<WrittenBy<Options>>
    const decode = read as (attribute: AttributeValue) => Result<T>
    return {
        encode,
        decode,
        unsafeEncode: (value) => orThrow(encode(value)),
        unsafeDecode: (attribute) => orThrow(decode(attribute)),
        def: {
            kind: 'union',
            options: optionTerms,
        },
        item: self as never,
        // built either way rather than branched, exactly as `item` is: an option that writes no map
        // declares no name, so it survives no clause, and the type is what says the capability does
        // not apply to such a union
        extract: ((clause: Readonly<Record<string, unknown>>) =>
            slicedUnion(options as readonly AnyCodec[], clause, true)) as never,
        exclude: ((clause: Readonly<Record<string, unknown>>) =>
            slicedUnion(
                options as readonly AnyCodec[],
                clause,
                false,
            )) as never,
    }
}

/**
 * A union's slice: the options the clause keeps, and `never` where it keeps none.
 *
 * Rebuilt through {@link union} and not assembled here, so the declaration guard runs over the
 * result. It has to: a sub-selection of a certified union is certified, and a sub-selection of one
 * that was never certified is not — which is the premise `Calculus.uAtAct_extract` takes and the
 * reason it takes one.
 */
const slicedUnion = (
    options: readonly AnyCodec[],
    clause: Readonly<Record<string, unknown>>,
    keep: boolean,
): unknown => {
    const kept = sliced(options, clause, keep)
    return kept.length === 0 ? never : union(kept as never)
}

/**
 * How a union of objects is declared: with a tag, or by the attributes each variant has.
 *
 * One parameter and one signature. Overloads would read the same at the call and cost the
 * diagnostic — `No overload matches this call` at the call site instead of a message on the
 * argument, which is what two signatures on `tableEntry` were measured to do. A union in one
 * inference slot would cost worse: a string and an array sharing a slot is how `tableEntry` came to
 * infer a codec from a separator.
 */
