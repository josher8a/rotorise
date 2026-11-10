import type { show } from '../utils'
import type { Attribute, AttributeValue } from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    Decoded,
    ObjectOf,
    ObjectSlot,
} from './build'
import { defOf } from './denote'
import type { Norm } from './pathModel'
import type { Field, Itemable, OfParts, Term } from './term'

// ── items ───────────────────────────────────────────────────────────

/** The decoded type `T` of an object codec, or the entity that its spec describes. */
export type ItemOf<T, Spec, Rest> = [T] extends [OfParts]
    ? DerivedItem<Spec, Rest>
    : T

/**
 * The entity a spec describes.
 *
 * An absent rest says the row holds nothing else, so the entity is closed. A rest codec says it
 * holds anything that codec can read, which is exactly an index signature — the mirror of
 * what {@link EncodedBy} does to the stored shape.
 */
export type DerivedItem<Spec, Rest> = [Rest] extends [undefined]
    ? show<ObjectOf<Spec>>
    : show<ObjectOf<Spec>> & {
          // TypeScript checks each declared key against the index of an intersection, so the index
          // admits the declared fields too. An optional field adds `undefined`, as the key may hold it
          readonly [name: string]:
              | Decoded<Rest>
              | ObjectOf<Spec>[keyof ObjectOf<Spec>]
      }

/**
 * The keys a type states, without an index signature's.
 *
 * The value is `0` and not `T[K]`: only the keys are read back out, and naming the property type
 * instantiates one per key of every entity every spec is checked against, to be thrown away.
 */
export type KnownKeys<T> = keyof {
    [K in keyof T as string extends K ? never : number extends K ? never : K]: 0
}

/**
 * The marker taken off, once, at the declaration.
 *
 * A field names the codec it marks, so the two halves are that codec's and taking the mark off
 * changes nothing about what the member encodes or decodes. What it changes is that the mark is
 * *named* rather than left to be recovered from a definition kind, which is what {@link Field} is
 * for.
 */
export const fieldOf = (declared: ObjectSlot): Field => {
    const def = defOf(declared)
    return 'mark' in def ? def : { mark: 'req', t: def }
}

/**
 * **The key set of each dissection**, keyed by the term. The term of a dissection is a `union`
 * term, and only the builder holds the key set: the one fact of a reading that the term lacks.
 */
export const keySets = new WeakMap<Term, readonly string[]>()

export type ObjectEntry<
    Key extends string = string,
    Value extends ObjectSlot = ObjectSlot,
> = readonly [AttributeCodec<Key, Attribute<'S'>>, Value]

export type AnyObjectEntry = readonly [AnyCodec, ObjectSlot]

export type UnionToIntersection<Value> = (
    Value extends unknown
        ? (value: Value) => void
        : never
) extends (value: infer Intersection) => void
    ? Intersection
    : never

export type EntrySpec<Entry> = Entry extends readonly [
    AttributeCodec<infer Key extends string, Attribute<'S'>>,
    infer Value extends ObjectSlot,
]
    ? string extends Key
        ? Record<never, never>
        : { readonly [K in Key]: Value }
    : never

export type EntrySpecs<Entries extends readonly AnyObjectEntry[]> = show<
    UnionToIntersection<EntrySpec<Entries[number]>>
>

export const entryCodec = (slot: ObjectSlot): AnyCodec =>
    ('codec' in slot ? slot.codec : slot) as AnyCodec

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
export type OptionInexact<O, E> = Norm<O, E>[0] extends [
    'prim',
    ['literal', unknown, infer V],
]
    ? InexactValue<V>
    : 'other'
export type InexactAll<X> = 'other' extends X
    ? false
    : true extends X
      ? true
      : false
export type InexactValue<V> = IsUnion<V> extends true
    ? true
    : [V] extends [PropertyKey]
      ? Record<never, never> extends Record<V, 1>
          ? true
          : false
      : false

/**
 * An object codec with its spec forgotten — the constraint form, as {@link AnyCodec} is for codecs.
 *
 * Structural, and deliberately: it asks for the members that say "I am an object codec and this is
 * what I declare": a spec beside a decode of one attribute. A bare spec record has no decode, so
 * passing one where an option is expected is refused rather than silently read as a codec. An item
 * reading decodes a whole item and not an attribute, so an item reading is refused too.
 */
export type AnyObjectCodec = {
    // `never` in and `unknown` out, the same erasure {@link AnyCodec} uses, so every object codec
    // fits and none of them has to be named
    readonly encode: (value: never) => unknown
    readonly decode: (attribute: AttributeValue) => unknown
    readonly spec: Record<string, ObjectSlot>
}

/** The entity a list of options describes: whatever any one of them reads back. */
export type DerivedUnion<Options extends readonly unknown[]> = {
    [I in keyof Options]: Decoded<Options[I]>
}[number]

/** What each option declares, read off the options. */
export type SpecsOf<Options extends readonly unknown[]> = {
    [I in keyof Options]: Options[I] extends Declares<infer S> ? S : never
}

/**
 * A codec that declares a spec: an object declares its own, and a union declares the spec of its
 * reading, which is a tag map or a list of the specs of its options.
 */
export type Declares<Spec> =
    | { readonly spec: Spec }
    | Itemable<{ readonly spec: Spec }>

/**
 * The entity a list of variant specs describes: one variant, or another.
 *
 * The union and not the merge, which is the same distinction {@link EncodedVariants} makes about the
 * stored side — a row is exactly one variant, so an attribute only one of them declares is not an
 * attribute the entity always has.
 */
export type DerivedVariants<
    Specs extends readonly unknown[],
    Rests extends readonly unknown[] = [],
> = {
    [I in keyof Specs]: DerivedItem<
        Specs[I],
        I extends keyof Rests ? Rests[I] : undefined
    >
}[number]

/** The rest of each option: the codec of the attributes that its spec does not declare. */
export type RestsOf<Options extends readonly unknown[]> = {
    [I in keyof Options]: Options[I] extends { readonly rest: infer R }
        ? R
        : undefined
}

/**
 * The values that a variant decodes its tag to. The table is keyed by the stored literal, and the
 * entity holds the decoded value, so a member of the entity is found by the second and not by the
 * first. The two are one value except under the adapter of a caller.
 */
export type DecodedTags<Spec, D> = D extends keyof Spec
    ? Spec[D] extends AttributeCodec<infer Tag, AttributeValue>
        ? Tag
        : never
    : never

/**
 * Whether a tag set has more than one member.
 *
 * The intersection of a union of distinct literals is `never`, and of a single literal is itself —
 * so this is the one distinction a conditional cannot make directly, because `extends` on a naked
 * type parameter distributes and every branch then sees one member.
 */
export type TagIntersection<Tags> = (
    Tags extends unknown
        ? (x: Tags) => void
        : never
) extends (x: infer One) => void
    ? One
    : never
