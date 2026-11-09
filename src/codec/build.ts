/**
 * The one place a codec is constructed.
 *
 * Its own module for one reason: it must be reachable from `native.ts`, which builds the SDK's
 * marshaller, and it must *not* be reachable from the package's public surface, which re-exports
 * `./codec` wholesale. A separate module is the only thing that gives both — an explicit export list
 * on the barrel would give it too, at the cost of naming all eighty-odd exports twice and silently
 * dropping whichever one is forgotten next.
 *
 * The types of a codec are here too: {@link AttributeCodec}, {@link AnyCodec} and {@link ObjectSlot}.
 * Each file that reads one imports it from this file, and `./codec` names the published ones again.
 * No file of a lower layer imports a type from `./codec`: `formal/scripts/layer_order.py` checks it.
 */

import type { show } from '../utils'
import type { Attribute, AttributeValue } from './attribute'
import type { HoldsNoValue } from './pathModel'
import type { Result } from './result'
import { orThrow } from './result'
import type {
    Field,
    optionalMarker,
    setMember,
    spreadMarker,
    Term,
    TermOf,
    TermsOf,
    undefinableMarker,
    writesMarker,
} from './term'

/*
 * **The free names of a codec, in its type**: the names that its term reads through a `ref` and
 * that no scope binds. Optional, so no value carries it. Wrapped in a tuple, because a reader
 * infers an optional `never` as `string`. A field carries the names of the codec that it marks.
 */
export declare const freeMarker: unique symbol

/**
 * The `this` of each use: **a use needs a closed codec**, with no free name. `encode` is a
 * member of each codec, and keeps the type from being weak, so a codec with no mark is closed.
 */
export type Closed = {
    readonly encode: unknown
    readonly [freeMarker]?: [never]
}

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
    readonly encode: (this: Closed, value: In) => Result<A>
    /** The value this attribute holds, or why it cannot be read. */
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<Out>
    /**
     * The same, throwing.
     *
     * What every codec calls to compose with another: a nested decode that returned a union would
     * have to be unwrapped at each of the fifty-odd places one codec reaches into the next, and the
     * unwrapping is the part that gets forgotten. So composition throws and the boundary converts,
     * which is why these are the ones the composites are built from.
     */
    readonly unsafeEncode: (this: Closed, value: In) => A
    /** The same, throwing. */
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => Out
    /**
     * What this codec is — see {@link Term}.
     *
     * A term and not a declaration: the two field kinds denote a field, a field is not a codec,
     * and so no codec's definition is one. It is what makes each reader total over the kinds it can
     * be handed rather than over the kinds that exist.
     */
    readonly def: Term
}

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

/** Any codec, both directions erased — `never` in and `unknown` out, so every codec fits. */
export type AnyCodec = CodecShape<never, unknown, AttributeValue>

/**
 * Anything an object member can be declared as: a codec, or a field that marks one.
 *
 * `optional` and `fill` state that the attribute at a *name* may be absent, and the name belongs
 * to the object rather than to the thing declared at it. So a field is not a codec, and the pair a
 * member is read and written through is the one the field marks.
 *
 * Written as the definition alone, because the definition is the whole of what both cases carry that
 * an object reads: `fieldOf` takes the mark off `def.mark` and the child term out of the same record.
 */
export type ObjectSlot = AnyCodec | { readonly def: Field }

/**
 * What has to be said to build a codec; the rest of {@link CodecShape} follows from it.
 *
 * Spelled out rather than `Pick`ed from {@link AttributeCodec}. It is the argument type of the one
 * construction site, so it is instantiated once per codec *written*, and a `Pick & Partial<Pick>`
 * instantiates the record it selects from twice over to answer the same five fields.
 */
export type Codec<T, A extends AttributeValue> = {
    readonly encode: (value: T) => Result<A>
    readonly decode: (attribute: AttributeValue) => Result<T>
    readonly def: Term
}

/**
 * A codec from the two directions that can fail, with the throwing pair derived.
 *
 * The one construction site. Every codec in this file is this shape, so the {@link orThrow} pairing
 * is written once and no constructor can end up with `unsafeEncode` disagreeing with `encode` —
 * which is a divergence nothing else would catch, since both round-trip perfectly on their own.
 */
export const codec = <T, A extends AttributeValue>({
    encode,
    decode,
    def,
}: Codec<T, A>): AttributeCodec<T, A> => ({
    encode,
    decode,
    unsafeEncode: (value) => orThrow(encode(value)),
    unsafeDecode: (attribute) => orThrow(decode(attribute)),
    def,
})

export type Free<F extends string> = { readonly [freeMarker]?: [F] }
export type FreeOf<C> = C extends {
    readonly [freeMarker]?: [infer F extends string]
}
    ? F
    : C extends { readonly codec: infer Marked }
      ? FreeOf<Marked>
      : never
export type ListTermOf<
    Items,
    Pre extends unknown[] = [],
> = Items extends readonly [infer H, ...infer R]
    ? H extends AnySpread
        ? ['list', Pre, ['some', TermOf<H>], TermsOf<R>]
        : ListTermOf<R, [...Pre, TermOf<H>]>
    : ['list', Pre, ['none'], []]

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
 * A declaration that fills a **slot** with a term holding no value.
 *
 * A slot is a position a value must fill: a declared element of a list, and a `req` or `fill`
 * field. `optional` and `undefinable` are not slots, because the key may be absent. A list's
 * spread is not one either, because a value of the declared length omits it.
 */
export type IsNeverSlot<D> = [D] extends [{ readonly [optionalMarker]: true }]
    ? false
    : // `never`, the node that a `ref` names, and each other form that holds no value
      HoldsNoValue<
            TermOf<D extends { readonly codec: infer C } ? C : D>
        > extends true
      ? true
      : false

/**
 * Anything that can sit where an attribute codec is expected — which is every codec.
 *
 * There used to be a second thing: an item, tagged or untagged codec, which *was* one `M` attribute
 * but exposed it as `.attribute`, so specs had to accept both shapes and every combinator had to
 * convert. The distinction was never about attributes. It was about the top-level map, and the top
 * level is the one place a map is not written — so it belongs to the *view*, not to the codec.
 * {@link object} writes its `M` like anything else, and offers {@link item} for the one place that does
 * not: the top level.
 */
export type Nestable<T> = AttributeCodec<T>

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

/** A map of attribute name to codec — what `item`, `map` and each `tagged` variant hold. */
export type Attributes = Readonly<Record<string, AnyCodec>>

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
export type WritesPin<Spec, Rest> = unknown extends Spec
    ? unknown
    : (written: EncodedBy<Spec, Rest>) => EncodedBy<Spec, Rest>

/**
 * The same pin for a union, whose row is one variant's attributes or another's.
 *
 * A union has no single encoded shape to name — `encode` returns "some attribute map", because which
 * attributes are written depends on which variant the value is. So the phantom is the only place the
 * shape appears at all, which makes it the only thing a pin can be asked of.
 */
export type WritesVariantsPin<Spec> = unknown extends Spec
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
export type SetOf<C> = SetAttribute<AttributeOf<C>>

/** The set that holds an element of the attribute `A`, or `never`. `A` is asked whole, not by member. */
export type SetAttribute<A> = {
    [M in keyof typeof setMember]: [A] extends [Attribute<M>]
        ? Attribute<(typeof setMember)[M]>
        : never
}[keyof typeof setMember]

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
 * Based on {@link Encoded} and *not* {@link EncodedBy}, so the type is a lower bound. The
 * implementation writes a name that the spec does not declare through the open entry, as `encode`
 * writes it, and refuses the name where the codec has no open entry. The type keeps the declared
 * names only, so a name of the open entry has no type in the result.
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
export type Written<Full, K> = Exclude<Full[K & keyof Full], undefined>

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
 * attribute, because an index signature intersects with every declared key. The index takes no
 * `undefined` from an optional key: an absent field writes no entry, so no entry holds `undefined`,
 * and the map stays an attribute that nests in another codec.
 */
export type EncodedBy<Spec, Rest> = [Rest] extends [undefined]
    ? Encoded<Spec>
    : Encoded<Spec> & {
          readonly [name: string]:
              | AttributeOf<Rest>
              | Written<Encoded<Spec>, keyof Encoded<Spec>>
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
