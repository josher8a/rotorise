import type { ErrorMessage } from '../utils'
import type {
    Attribute,
    AttributeMap,
    AttributeValue,
    StoredItem,
} from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    AttributeOf,
    Closed,
    Free,
    FreeOf,
    freeMarker,
    ObjectSlot,
    WritesVariantsPin,
} from './build'
import { codecOfTerm } from './capabilities'
import type { Option } from './denote'
import { altSem, membersTooDeeply, optionOfTerm, termOf } from './denote'
import type {
    AnyObjectCodec,
    DecodedTags,
    DerivedUnion,
    DerivedVariants,
    ItemOf,
    RestsOf,
    SpecsOf,
    TagIntersection,
} from './derivedItem'
import { keySets } from './derivedItem'
import type { DecodeTerm, OwnsNull } from './pathModel'
import { nullValue } from './prisms'
import type { Result } from './result'
import { CodecError, failed, orThrow } from './result'
import type {
    ItemCodec,
    ObjectCodec,
    ObjectFree,
    Reading,
    UnionCodec,
} from './scope'
import { dissectionOf, itemMark, objectItem, objectNamed } from './scope'
import type {
    BaseT,
    FreeTerm,
    Itemable,
    itemMarker,
    OptionsMark,
    ReadingOf,
    restsMarker,
    Term,
    TermMark,
    TermOf,
    TermsOf,
    termMarker,
    writesMarker,
} from './term'
import {
    holdsNoValue,
    openRefusal,
    ownsNullOf,
    resolvedTerm,
    unboundRefs,
} from './term'
import { itemRefusal, namesOf } from './value'

/**
 * The refusal in the type of {@link nullable} over a term whose null point no term decides. The run
 * time refuses at construction, unless a free name leaves the question open for the scope.
 */
export type NullPointOver<Tm, F extends string> = [F] extends [never]
    ? [OwnsNull<Tm>] extends ['unknown']
        ? ErrorMessage<'[nullable] this term decides the null point by running a function, so whether the union would be certified is unknown. Write the wrapper inside instead, as in held(nullable(inner), outer, adapter)'>
        : unknown
    : unknown

/**
 * A value that may be null, stored as `NULL` when it is — **unless `inner` already owns the null
 * point**, in which case this is `inner`'s own pair, untouched.
 *
 * Without the guard the wrapper's `NULL` branch shadows the inner codec, and **(R)** fails on a
 * term the specification proves lawful: `nullable(held(nullable(string), string, adapter))`, where the
 * adapter maps `'SENTINEL'` to `null`, writes `{ NULL: true }` for `'SENTINEL'` and reads back
 * `null`. The value written is not the value read. No declaration in this repository builds that
 * term and `held` is unemittable, so no generated vector could ever have found it.
 *
 * Where the guard does *not* fire, null-honesty is a theorem rather than an assumption: an
 * `inner` that wrote `⟨NULL, ∗⟩` would read it straight back by **(R)** and so would own the
 * point, and one that read some attribute to `null` would write the point by **(C)** and own it
 * again. Both hypotheses are refuted by the guard rather than required of the caller.
 *
 * **The question is asked once, at construction.** The term answers the question, and an answer
 * that the term does not determine is a refusal. **A {@link ref} that no scope binds yet leaves the
 * question open**: the codec is then the {@link union} with `NULL`, and the {@link scope} that binds
 * the name runs the check of the union. A `ref` to an entry that owns the null point fails the
 * check there, because two options then write `NULL`.
 */
export const nullable = <
    T,
    A extends AttributeValue,
    Tm = FreeTerm,
    F extends string = never,
>(
    inner: AttributeCodec<T, A> & TermMark<Tm> & Free<F> & NullPointOver<Tm, F>,
): AttributeCodec<T | null, A | Attribute<'NULL'>> &
    TermMark<['union', [Tm, BaseT<'null'>]]> &
    Free<F> => {
    const t = termOf(inner as unknown as AnyCodec)
    const owns = ownsNullOf(t)
    // **An unbound `ref` leaves the answer open**: the codec is the union with `NULL`, an open
    // fragment, and the scope that binds the names checks the union on its closed copy. A `ref`
    // whose entry owns the null point fails that check, as a second option that writes `NULL`
    if (owns === undefined && unboundRefs([t]).size > 0)
        return codecOfTerm<T | null, A | Attribute<'NULL'>>(
            union([inner, nullValue]).def,
        )
    if (owns === undefined) {
        throw new CodecError(
            `nullable: ${t.kind} decides the null point by running a function this cannot read, ` +
                'so whether the union would be certified is unknown. ' +
                'Write the wrapper inside instead, as in held(nullable(inner), outer, adapter).',
        )
    }
    if (owns) return inner as AttributeCodec<T | null, A | Attribute<'NULL'>>
    // a term that holds no value adds no option to the null point, so the union is `NULL` itself,
    // read at the node that the term names
    if (holdsNoValue(t)) {
        return nullValue as AttributeCodec<T | null, A | Attribute<'NULL'>>
    }
    return codecOfTerm<T | null, A | Attribute<'NULL'>>({
        kind: 'union',
        options: [t, { kind: 'null' }],
    })
}

/**
 * A union of objects, and the same union read as a whole item.
 *
 * Only a union of *objects* has an item reading: an item is a map, so a union that could also be an
 * `S` or an `L` is an attribute and nothing else. Which is why this is what the two union
 * constructors return, rather than what `union` is constrained to accept.
 */
export type DiscriminatedCodec<
    T,
    D extends string,
    Spec,
    F extends string = never,
> = {
    readonly encode: (this: Closed, value: T) => Result<Attribute<'M'>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => Attribute<'M'>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    /** The reading of this union as a whole item, which {@link item} returns. Type-level only. */
    readonly [itemMarker]: [Tagged<T, D, Spec> & Free<F>]
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Spec>
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [F]
}

/**
 * A dissection read as a whole item: the members, chosen by an assignment.
 *
 * {@link Tagged} at several discriminators. One field moves, because there is no single
 * discriminator to name: `keys` holds the key set where `discriminator` held the one name.
 *
 * `spec` is the members' specs as the caller declared them. There is no string to key them by: a
 * key would be a rendering of an assignment, and a rendering is an order.
 */
export type Dissected<
    T,
    Ks extends readonly string[],
    Specs extends readonly unknown[],
> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
    /** Every attribute, or why one could not be written. */
    readonly encode: (this: Closed, item: T) => Result<AttributeMap>
    readonly unsafeEncode: (this: Closed, item: T) => AttributeMap
    /** The attributes a patch names. Every discriminator is required: they choose the codec. */
    readonly encodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, Ks[number] & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, Ks[number] & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
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
    F extends string = never,
    Rests extends readonly unknown[] = [],
> = {
    readonly encode: (this: Closed, value: T) => Result<Attribute<'M'>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => Attribute<'M'>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    /** The reading of this dissection as a whole item, which {@link item} returns. Type-level only. */
    readonly [itemMarker]: [Dissected<T, Ks, Specs> & Free<F>]
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [F]
    /** The rest of each member, which a slice keeps with the member. Type-level only. */
    readonly [restsMarker]?: [Rests]
}

/**
 * What {@link mdunion} returns, read at the arity the caller wrote.
 *
 * **At one key it is today's type, exactly.** `discriminatedUnion` is `mdunion` at one
 * discriminator, so the two have to be the same type and not merely compatible ones — a caller
 * who swaps the call changes no annotation, and `discriminator`, `spec` and the
 * `Writes` pin all read as they did.
 */
export type Dissection<
    Ks extends readonly string[],
    Options extends readonly unknown[],
> = Ks extends readonly [infer D extends string]
    ? DiscriminatedCodec<
          DerivedVariants<SpecsOf<Options>, RestsOf<Options>>,
          D,
          ByTag<SpecsOf<Options>, D>,
          FreeOf<Options[number]>
      >
    : DissectedCodec<
          DerivedVariants<SpecsOf<Options>, RestsOf<Options>>,
          Ks,
          SpecsOf<Options>,
          FreeOf<Options[number]>,
          RestsOf<Options>
      >

/**
 * **The options of a codec that no union former built**: one option for each literal where the term
 * is a union of literals, as `string('A', 'B')` builds, because the run time slices that term by its
 * options. Any other codec is one option.
 */
export type LiteralOptions<C> = TermOf<C> extends [
    'union',
    infer Ts extends readonly ['prim', ['literal', string, unknown]][],
]
    ? {
          -readonly [I in keyof Ts]: AttributeCodec<
              DecodeTerm<Ts[I]>,
              AttributeOf<C> & AttributeValue
          > &
              TermMark<Ts[I]>
      }
    : [C]

/** The whole-item reading of the node that a term names: an object, a dissection, or a union. */
export const readingOf = (t: Term): Reading | undefined => {
    const node = resolvedTerm(t)
    if (node?.kind === 'object') return objectItem(node)
    if (node?.kind !== 'union') return undefined
    const ks = keySets.get(node)
    return ks ? dissectionOf(node, ks).self : unionOf(node)
}

/**
 * The same declaration, read as a whole item: the same two directions without the top-level map,
 * and the things only a top-level codec can offer: `encodePartial` and `unsafeEncodePartial`.
 *
 * A DynamoDB item is a map that is never written as one; `PutItem` takes the attributes bare.
 * That is the *only* thing that separated an item codec from a nested one, and it is a fact about
 * where a codec is used rather than about what it declares, so it is a reading of one codec
 * rather than a second constructor. The marshaller draws the same line, under
 * `convertTopLevelContainer`.
 *
 * A free function and not a member: a member is typed on each codec type that carries the member,
 * and a function is typed only at a call. The reading is a function of the term, built once per
 * term. An object codec carries no type for the reading. A union carries the type of the reading
 * in one tuple.
 *
 * The union overload reads a union by the reading that its type carries: the reading of a union
 * of objects, of a tagged union, or of a dissection. A union that can hold an attribute that is not
 * a map has no reading, and the type is a message that says so.
 */
export function item<
    Spec extends Record<string, ObjectSlot>,
    Rest extends AnyCodec | undefined,
    T,
    Tm,
>(
    codec: ObjectCodec<Spec, Rest, T, Tm>,
): ItemCodec<ItemOf<T, Spec, Rest>, Spec, Rest, Tm> &
    Free<ObjectFree<Spec, Rest, Tm>>
export function item<C extends Itemable<unknown>>(codec: C): ReadingOf<C>
export function item(codec: object): unknown {
    const reading = readingOf(termOf(codec as AnyCodec))
    if (reading === undefined) {
        throw new CodecError(
            'this codec has no whole-item reading: `item` takes an object or a union',
        )
    }
    return reading
}

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
    /** A use needs a closed codec, so a signature that asks for one admits no free name. */
    readonly [freeMarker]?: [never]
}

export type Tagged<T, D extends string = keyof T & string, Spec = unknown> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
    /** Every attribute, or why one could not be written. */
    readonly encode: (this: Closed, item: T) => Result<AttributeMap>
    readonly unsafeEncode: (this: Closed, item: T) => AttributeMap
    /**
     * The attributes a patch names, or why one could not be written.
     *
     * The discriminator is required in a patch, because it is what chooses the codec. This is a type
     * error, not a runtime one: `Partial<T> & Pick<T, D>`.
     */
    readonly encodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => Result<AttributeMap>
    readonly unsafeEncodePartial: (
        this: Closed,
        patch: Partial<T> & Pick<T, D & keyof T>,
    ) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
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
 */
export const dissect = <T extends Record<string, unknown>>(
    ks: readonly string[],
    options: readonly (AnyObjectCodec | AnyCodec)[],
): DiscriminatedCodec<T, string, Record<string, unknown>> => {
    // **the empty key set, refused where the type cannot refuse it.** Over no discriminator every
    // value carries the empty assignment, so the first member answers for all of them and the
    // union is a union of one. The model carries no key set at all, so it never asks this; here
    // the key set is a `readonly string[]`, which cannot say it, and this is the gate
    if (ks.length === 0) {
        throw new CodecError(
            'a discriminated union needs at least one discriminator, and this one has none — every value carries the empty assignment, so the first variant would answer for all of them',
        )
    }
    // **An empty option list is a mistake, not the bottom.** `never` is the bottom and says so as
    // a term; a `dunion` over no variants is what a typo or a `map` over an empty array produces,
    // and it admits nothing while no rule reads it as admitting nothing. The type refuses this
    // too — what reaches here is a cast, plain JavaScript, or an erased path
    if (options.length === 0) {
        throw new CodecError(
            'a discriminated union needs at least one option, and this one has none — no tag reaches a variant, so nothing can be written or read. If a codec that admits no value is what you meant, that is \`never\`',
        )
    }
    // **Each option names an object node, read through its `ref`s.** An option that names a `ref`
    // that no scope binds is read by the scope, where the index reads the node of the closed copy
    for (const option of options) {
        const node = resolvedTerm(termOf(option as unknown as AnyCodec))
        if (node?.kind !== 'ref' && !(node && objectNamed(node))) {
            throw new CodecError(
                'every option must be an object codec, and one of them is not',
            )
        }
    }
    /**
     * **The term is a `union`, and the tag table is this builder's index over it.**
     *
     * A dissection is a certified union: its members are objects that differ at a required literal
     * key with disjoint alternatives, which is exactly what structural admission resolves and what
     * `Calculus.Closed.viewsDisjoint` certifies. So there is one sum in the term language, and the key set below
     * is a lookup this builder keeps for `encodePartial` and the item path — a host
     * index, carried by no term.
     */
    const memberTerms = options.map((option) =>
        termOf(option as unknown as AnyCodec),
    )
    const unionDef = { kind: 'union', options: memberTerms } as const

    keySets.set(unionDef, ks)
    // **A tag that a member reads through an unbound `ref` is indexed by the scope**, on the closed
    // copy, because the index reads the literal of each tag through the `ref`
    if (unboundRefs(memberTerms).size === 0)
        dissectionOf(unionDef, ks).resolution()
    const nested = codecOfTerm<T, Attribute<'M'>>(unionDef)
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
    } as unknown as DiscriminatedCodec<T, string, Record<string, unknown>>
}

export const optionOf = (
    t: Term,
): Option<ItemCodec<Record<string, unknown>, unknown>> => {
    /**
     * Read from the definition, not from the presence of a reading.
     *
     * A nested union has a reading too, and its `spec` is the *list* of its options rather than a
     * record of attributes — so testing for the reading classified a union as an object and then walked
     * that list as though `0` and `1` were attribute names. `attributes` is the definition of an
     * object codec and of nothing else.
     */
    const base = optionOfTerm(t)
    const asObject = readingOf(t)
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

/** The stored literals that a term names: a literal, or the options of a union of literals. */
export type StoredLiterals<T> = T extends ['prim', ['literal', string, infer V]]
    ? V extends string
        ? V
        : never
    : T extends ['union', infer Os extends readonly unknown[]]
      ? StoredLiterals<Os[number]>
      : never

/**
 * The stored literals of a field under the adapter of a caller, which the inner term names, or
 * `never`. A library adapter is lawful by its own term: `number` reads its text as its value.
 */
export type HeldStored<Field> = Field extends {
    readonly [termMarker]?: infer M
}
    ? Unrefined<M> extends [
          'held',
          false,
          infer Inner,
          unknown,
          [['caller'], false],
          ...unknown[],
      ]
        ? StoredLiterals<Inner>
        : never
    : never

/** The term under each `refine` and each presence mark, as `pinOfG` reads it. */
export type Unrefined<M> = M extends ['refine', infer I, ...unknown[]]
    ? Unrefined<I>
    : M extends ['optional' | 'undefinable' | 'fill', infer J]
      ? Unrefined<J>
      : M

/** Whether a field is under the adapter of a caller, through each `refine` and each presence mark. */
export type CallerHeld<Field> = Field extends {
    readonly [termMarker]?: infer M
}
    ? Unrefined<M> extends [
          'held',
          false,
          unknown,
          unknown,
          [['caller'], false],
          ...unknown[],
      ]
        ? true
        : false
    : false

/**
 * The text that a field of an entity prints in a key, where the entity holds `Value`. A field under
 * the adapter of a caller prints the stored text, which the caller's value does not give: the
 * literal of the inner term where the inner term pins one, and `string` where it pins none. Any
 * other field prints its value.
 *
 * An absent value stays absent: where `Value` holds `undefined` or `null`, so does the text.
 *
 * A key of one attribute reads this type too. That key holds the stored payload of an attribute
 * under the adapter of a caller, as the row does, because an entry that holds a value such as a
 * `Date` cannot be stored. A field with no adapter of a caller holds its value.
 */
export type KeyText<Value, Field> = [Field] extends [never]
    ? Value
    : true extends CallerHeld<Field>
      ?
            | ([HeldStored<Field>] extends [never] ? string : HeldStored<Field>)
            | Extract<Value, null | undefined>
      : Value

/**
 * The tag values a variant answers to — its discriminator's whole admissible set, not one value.
 * A tag is the stored literal on both sides, so a field under `held` answers to the literal of its
 * inner term, and the caller's value is written through the field to reach it.
 *
 * A variant may span several tags, and this codebase relies on it: a carrier declared
 * `carrierId: string('ACME', 'GLOBEX')` is *one* variant covering two stored values, which is why
 * {@link VariantOf} asks whether a tag is *among* a member's tags rather than equal to it.
 */
export type TagsOf<Spec, D extends PropertyKey> = Spec extends unknown
    ? // distributed over the *variants*: the conditional below is on `Spec[D]`, so a union of specs
      // handed in whole would ask about a union of codecs and answer nothing
      D extends keyof Spec
        ? [HeldStored<Spec[D]>] extends [never]
            ? true extends CallerHeld<Spec[D]>
                ? // an adapter of a caller whose inner term pins no literal names no tag, and the run
                  // time refuses the codec at construction
                  never
                : Spec[D] extends AttributeCodec<infer Tag, AttributeValue>
                  ? // a tag is stored as `S` or as `N`, so a numeric enum indexes variants as readily as
                    // a string one — `readTag` reads either member and keys on the text it carries
                    Tag extends string | number
                      ? Tag
                      : never
                  : never
            : HeldStored<Spec[D]>
        : never
    : never

/**
 * The options keyed by their own tag, which is what a lookup needs.
 *
 * Derived rather than declared. A record keyed by tag value repeats what the option's own `literal`
 * already says, so `{ SHOT: { type: string('CHECKUP') } }` is expressible and the two can disagree.
 * Reading the tag off the option makes that unrepresentable — and it is how `zod` does it.
 */
export type ByTag<Specs extends readonly unknown[], D extends PropertyKey> = {
    [Spec in Specs[number] as TagsOf<Spec, D>]: Spec
}

/**
 * The options whose discriminator literal admits more than one value.
 *
 * Indexed by position like {@link SharedAssignments}, and one option at a time rather than a
 * pair: this is
 * a defect in a single option, so naming its neighbour would say nothing.
 */
export type MultiTagged<
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
 * A key that **some** option names with no tag: that option cannot be found at it.
 *
 * Asked of each option in turn, and not of `Specs[number]`. Asking the union of the specs answers a
 * question about the collection — "does anybody name this key" — and an option that names none of
 * them passes, because its neighbours answered for it. Every other rule here is already distributed
 * over the options one at a time ({@link MultiTagged}) or over their pairs
 * ({@link SharedAssignments}); this is the same shape, and it was the one
 * clause that was not.
 */
export type UntaggedKey<
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
export type MultiTaggedAnywhere<
    Specs extends readonly unknown[],
    Ks extends readonly PropertyKey[],
> = { [K in Ks[number]]: MultiTagged<Specs, K> }[Ks[number]]

/**
 * Whether two options differ at some key.
 *
 * **At some key, not at the first.** Two members of a dissection are distinct when their
 * assignments differ anywhere, and asking that of every key at once is what makes the answer
 * independent of how the keys were written.
 *
 * **A tag is its text**, as the lookup keys it: `string('1')`, `number(1)` and `decimal('1')` each
 * answer to '1'. The type spells a number as a template does, so a number with an exponent form
 * differs from its stored text here.
 */
export type DiffersSomewhere<
    A,
    B,
    Ks extends readonly PropertyKey[],
> = true extends {
    [K in Ks[number]]: [`${TagsOf<A, K>}` & `${TagsOf<B, K>}`] extends [never]
        ? true
        : false
}[Ks[number]]
    ? true
    : false

/**
 * Whether two options decode one value at a key where they store two texts. The run time refuses
 * such a pair, because the write of the value reaches only one of the two stored texts. **The
 * narrowing:** the type states the overlap of the decoded tags, and it compares the values by
 * their types, so `1` and `'1'` are two values. The type does not state the lookup law of the
 * run time: that the write of each decoded value gives the text of its own option. A caller
 * adapter that does not write its own literal stays a refusal at construction. The narrowing has a
 * second direction: the type refuses a pair that the run time admits. The overlap reads the
 * decoded type of the adapter, so an adapter whose decoded type is wider than the values that its
 * schema admits overlaps every tag of that type, and the pair is refused.
 */
export type DecodesTogether<
    A,
    B,
    Ks extends readonly PropertyKey[],
> = true extends {
    [K in Ks[number]]: [DecodedTags<A, K> & DecodedTags<B, K>] extends [never]
        ? false
        : [`${TagsOf<A, K>}` & `${TagsOf<B, K>}`] extends [never]
          ? true
          : false
}[Ks[number]]
    ? true
    : false

export type SharedAssignmentsFrom<
    Head,
    Rest extends readonly unknown[],
    Ks extends readonly PropertyKey[],
    At extends number,
    Cursor extends readonly unknown[],
> = Rest extends readonly [infer Next, ...infer Tail extends readonly unknown[]]
    ?
          | (DiffersSomewhere<Head, Next, Ks> extends true
                ? DecodesTogether<Head, Next, Ks> extends true
                    ? `options ${At} and ${Cursor['length']}`
                    : never
                : `options ${At} and ${Cursor['length']}`)
          | SharedAssignmentsFrom<Head, Tail, Ks, At, [...Cursor, unknown]>
    : never

/**
 * Which pairs of options carry one assignment, as `options i and j`.
 *
 * A discriminated union is a *lookup*, so two options claiming one assignment is not an ambiguity
 * to be resolved when a value turns up — it is a table with one key written twice, and the second
 * write wins in silence. Decidable from the declaration, so it is refused there.
 */
export type SharedAssignments<
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
export type MembersTagged<
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
export type EveryOptionTagged<
    Specs extends readonly unknown[],
    D extends PropertyKey,
> = MembersTagged<Specs, readonly [D]>

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
): Dissection<Ks, Options> &
    TermMark<['union', TermsOf<Options>]> &
    OptionsMark<Options> =>
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
    DerivedVariants<SpecsOf<Options>, RestsOf<Options>>,
    D,
    ByTag<SpecsOf<Options>, D>,
    FreeOf<Options[number]>
> &
    TermMark<['union', TermsOf<Options>]> &
    OptionsMark<Options> =>
    // **the type arguments are given, not inferred, and that is what makes the alias cast-free.**
    // Inferring them from `options` would take `Options` to be the *intersection* the parameter
    // declares — `Options & MembersTagged<…>` — and the return type computed from that intersection
    // is not the one this signature promises. Pinned, `Dissection<readonly [D], Options>` reduces to
    // exactly the `DiscriminatedCodec` below, and `EveryOptionTagged<SpecsOf<Options>, D>` is
    // `MembersTagged<SpecsOf<Options>, readonly [D]>` by definition, so the argument needs nothing.
    mdunion<readonly [D], Options>([discriminator], options)

/**
 * A union told apart by what each option holds, with no tag to switch on — `zod`'s `union`.
 *
 * **The union is the join of its options.** Options are codecs of any kind. The first option that
 * admits a value writes the value, and the first option that reads an attribute reads it. An
 * object option is no exception: the names present select nothing.
 *
 * **The declaration refuses a pair that it cannot show compatible**, and nothing else. Two
 * compatible options that both admit a value write it to one attribute, and two that both read an
 * attribute read it to one value, so no value and no attribute can observe the option order.
 * Options that overlap, nest, or repeat are therefore well formed: `union([string('A'), string])`
 * is `string`. A pair that the declaration cannot show compatible is refused, because there the
 * order would choose an owner of the overlap that nobody named.
 *
 * @example
 * ```ts
 * union([object({ petId: string, price: decimal }), object({ petIds: array(string) })])
 * union([string, number])                    // an attribute that is either
 * union([object({ at: string }), string])     // a map or a bare string
 * union([string('A', 'B'), string('B', 'C')]) // two restrictions of one base
 * ```
 */
export const union = <const Options extends readonly AnyCodec[]>(
    options: Options,
): UnionCodec<DerivedUnion<Options>, Options> => {
    const declared = { kind: 'union', options: options.map(termOf) } as const
    // the judgment of the node runs here, and the item reading is a function of the term
    return codecOfTerm(declared) as unknown as UnionCodec<
        DerivedUnion<Options>,
        Options
    >
}

/** The whole-item reading of a union, a function of the term. The memo is a cache only. */
export const unions = new WeakMap<Term, Reading>()

export const unionOf = (
    declared: Extract<Term, { kind: 'union' }>,
): Reading => {
    const built = unions.get(declared)
    if (built) return built
    // **The judgment decides the union's obligation**: each two options compatible, at the
    // declaration, or at the first scope that binds a name of an option. The resolution reads each
    // option through its `ref`s, so it runs at the first use, where every name is bound
    const settle = () => {
        const all: readonly Option<
            ItemCodec<Record<string, unknown>, unknown>
        >[] = declared.options.map(optionOf)
        return { all, ...altSem(all) }
    }
    let settled: ReturnType<typeof settle> | undefined
    const resolution = (): ReturnType<typeof settle> => {
        settled ??= settle()
        return settled
    }
    type T = Record<string, unknown>

    /**
     * The item reading's own matcher: the value is always a record, so the shape filter has nothing
     * to do, and each option is attempted. The names present select nothing, as the model's
     * `Closed.AdmA` reads no name.
     */
    const readItem = (item: StoredItem): Result<T> => {
        const open = openRefusal(declared)
        if (open) return open
        const refused = itemRefusal(item)
        if (refused) return refused
        const deep = membersTooDeeply(item, 0)
        if (deep) return deep
        const names = namesOf(item)
        const { only, naming, named } = resolution()
        // The item reading asks the same lookup as the attribute reading, so the outer union of a table
        // dispatches. The cast drops the `undefined` that `StoredItem` admits: a lookup reads it as missing.
        const hit = named({ M: item } as AttributeValue)
        if (hit?.item) {
            const direct = (
                hit.item as ItemCodec<Record<string, unknown>, unknown>
            ).decode(item) as Result<T>
            if (!failed(direct)) return direct
        }
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
        const open = openRefusal(declared)
        if (open) return open
        const names = namesOf(item as Record<string, unknown>)
        const { onlyAdmitting, naming } = resolution()
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
     * not be reached here also cannot be selected here: `item` is what an all-object union reads,
     * and only an object option has it.
     */
    const self = {
        [itemMark]: true as const,
        encode: writeItem,
        decode: readItem,
        unsafeEncode: (item: T) => orThrow(self.encode(item)),
        unsafeDecode: (item: StoredItem) => orThrow(self.decode(item)),
        // an object option declares its spec, and a tagged option declares its tag map
        spec: declared.options.map((option) => readingOf(option)?.spec),
        def: declared,
    }

    unions.set(declared, self)
    return self
}
