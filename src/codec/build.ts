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
import type { AttributeValue } from './attribute'
import type { HoldsNoValue } from './pathModel'
import type { Result } from './result'
import { orThrow } from './result'
import type {
    Field,
    optionalMarker,
    spreadMarker,
    Term,
    TermOf,
    TermsOf,
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
