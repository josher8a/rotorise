import type { ErrorMessage, show } from '../utils'
import type { Attribute, M } from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    AttributeOf,
    Decoded,
    EncodedBy,
    Marks,
    ObjectSlot,
} from './build'
import { codecOfTerm } from './capabilities'
import { defOf, termOf } from './denote'
import type {
    AnyObjectEntry,
    DerivedItem,
    EntrySpecs,
    InexactAll,
    InexactValue,
    OptionInexact,
    UnionToIntersection,
} from './derivedItem'
import { entryCodec, fieldOf } from './derivedItem'
import type { Norm } from './pathModel'
import type { LibraryInner } from './prisms'
import type { NoNeverField, NoSpreadMember } from './products'
import { CodecError, setOwn } from './result'
import type {
    ObjectCodec,
    OptionalCodec,
    UndefinableCodec,
    UnionCodec,
} from './scope'
import type { Body, Field, optionsMarker, TermMark, TermOf } from './term'
import { pinnedValue, resolvedTerm, storedPin } from './term'

/* ── the readers ──────────────────────────────────────────────────────────────────────── */

/*
 * A reader here answers from the **term** and nothing else, which is what makes the term determine
 * the codec rather than describe it. `constantOf` is the one left in this file; `member` and
 * `occV` are `term.ts`'s, `agrees` is `scoped.ts`'s, and
 * `accepts` and `readsBack` ask the pair in `denote.ts`.
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
 * What one declared attribute decides, read where the field is held.
 *
 * The two presence marks answer differently and neither is the codec's answer. A name that may be absent
 * decides nothing about a key, because a key built from it would have no value to build from in the
 * rows that omit it. A fill value is written always, so what it fills still decides.
 *
 * A reader of the term alone does not answer this. A term is what a codec has, a field is not a
 * codec, and the body is what holds a field — so this reads the mark first and the term second.
 */
export const constantOf = (declared: ObjectSlot): unknown => {
    const def = defOf(declared)
    if (
        'mark' in def &&
        (def.mark === 'optional' || def.mark === 'undefinable')
    )
        return undefined
    const t = 'mark' in def ? def.t : def
    // **A single-valued literal decides; two admissible values narrow without deciding.** The term
    // answers the row, deliberately *not* through the wrappers `member` descends: a constant is a claim about
    // the value, and `refine` can reject it, `legacy` can decode an older encoding into something
    // else, and `optional` admits absence, which is not the value. `fill` is the one that keeps
    // it, always writing the attribute at a value typed to the same alternative.
    //
    // **An adapter is the second that keeps it**, and it has to be: `number` and `decimal` are
    // adapters over the one numeric base, so a numeric discriminator is a literal under a
    // `held` and reading only the bare row would lose every one of them. The value is the
    // caller's rather than the carrier's, so it is the inner literal's put back through the
    // adapter — well defined because `held` owes that the pair cancels.
    //
    // The walk is `storedPin`, the one reader of a term through its wrappers, and a `ref` is read as
    // its target. A throw of the adapter of a caller is not caught here: the caller of this
    // function names the attribute in the refusal.
    const at = resolvedTerm(t)
    if (at === undefined || at.kind === 'refine') return undefined
    return pinnedValue(storedPin(at))
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
 * marked declaration is refused the same way: `fill(c, v)` is the attribute that may be absent
 * and has a fill value, and it is what both nestings meant.
 */
export const optional = <const C extends AnyCodec>(
    inner: C,
): OptionalCodec<Decoded<C>, AttributeOf<C>, C> &
    TermMark<['optional', TermOf<C>]> => {
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
 * takes on no premise of its own — unlike {@link fill}, which must check its fill value is
 * writable because it writes one.
 */
export const undefinable = <const C extends AnyCodec>(
    inner: C,
): UndefinableCodec<Decoded<C>, AttributeOf<C>, C> &
    TermMark<['undefinable', TermOf<C>]> =>
    ({
        codec: inner,
        def: { mark: 'undefinable', t: termOf(inner) },
    }) as unknown as UndefinableCodec<Decoded<C>, AttributeOf<C>, C>

/**
 * Declares how an entity is stored, once, in both directions.
 *
 * The spec is the declaration, and the entity is derived from it. Nothing has to be named twice, and
 * there is no type argument to get wrong.
 *
 * Whatever else is worth checking is asked of the codec afterwards, and asked separately, because
 * they are separate questions:
 *
 * - `satisfies ItemCodec<Entity>` — the entity, up to assignability both ways. `ItemCodec` is
 *   invariant in it, sitting in `encode`'s parameter and `decode`'s return, so a required attribute
 *   that is missing or extra, and one that decodes to the wrong type, are caught. An optional key
 *   that is added or dropped is not caught: an object without `k?` is assignable to an object with
 *   it, and back. {@link pin} compares the key paths with their optional marks, and refuses it.
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
export const objectFromMap = <
    const Spec extends Record<string, ObjectSlot>,
    const Rest extends AnyCodec | undefined = undefined,
>(
    spec: Spec & NoSpreadMember<Spec> & NoNeverField<Spec>,
    rest: Rest,
): ObjectCodec<Spec, Rest> => {
    // the marker off each declared attribute, once — the term. What the two directions walk is
    // the *compiled* form of it, which `bodySem` builds and which carries one thing the term does
    // not: whether a fill value has to be copied per read, a fact about this runtime and not about
    // the declaration.
    const fields: Record<string, Field> = {}
    const declaredSpec = spec as unknown as Record<string, ObjectSlot>
    for (const name in declaredSpec) {
        setOwn(fields, name, fieldOf(declaredSpec[name] as ObjectSlot))
    }

    const declaredBody: Body =
        rest === undefined ? { fields } : { fields, rest: termOf(rest) }
    const itemDef = { kind: 'object', body: declaredBody } as const
    // the judgment of the node runs before the item pair is built
    const nested = codecOfTerm(itemDef) as unknown as AttributeCodec<
        DerivedItem<Spec, Rest>,
        M<EncodedBy<Spec, Rest>>
    >
    // the `M` is what this codec writes; `item` is the same two directions with the wrapper taken
    // off. Named member by member rather than spread so the cast keeps the *shape* the map carries —
    // `Attribute<'M'>` would flatten it to "some map" — and so that a call to `object` stays a plain
    // object literal, which is what lets a bundler drop an unused one
    return {
        encode: nested.encode,
        decode: nested.decode,
        unsafeEncode: nested.unsafeEncode,
        unsafeDecode: nested.unsafeDecode,
        def: nested.def,
        spec,
        rest,
    }
}

export type OptionalObjectSlot = {
    readonly def: Extract<Field, { readonly mark: 'optional' | 'undefinable' }>
}

export type EntryAdmission<Entry> = Entry extends readonly [
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

export type EntriesAdmission<Entries extends readonly AnyObjectEntry[]> =
    UnionToIntersection<EntryAdmission<Entries[number]>>

export type WildcardEntry<Entries extends readonly AnyObjectEntry[]> =
    Entries[number] extends infer Entry
        ? Entry extends readonly [
              AttributeCodec<infer Key, Attribute<'S'>>,
              infer Value extends ObjectSlot,
          ]
            ? string extends Key
                ? Marks<Value>
                : never
            : never
        : never

export type EntryRest<Entries extends readonly AnyObjectEntry[]> = [
    WildcardEntry<Entries>,
] extends [never]
    ? undefined
    : Extract<WildcardEntry<Entries>, AnyCodec>

/**
 * The names an entry key declares, read from the node that the key names, through its `ref`s. The
 * names fix the body at the declaration, so a key that names a `ref` that no scope binds is
 * refused at the declaration.
 */
export const entryNames = (key: AnyCodec): string[] => {
    const term = resolvedTerm(termOf(key))
    if (term?.kind === 'literal' && term.base === 'string') return [term.v]
    if (term?.kind === 'union') {
        const names = term.options.flatMap((option) => {
            const one = resolvedTerm(option)
            return one?.kind === 'literal' && one.base === 'string'
                ? [one.v]
                : []
        })
        if (names.length === term.options.length) {
            // a union with no option names no key, and an empty list of names is the wildcard
            if (names.length > 0) return names
            throw new CodecError(
                'an object entry key is a union with no option, which names no key',
            )
        }
    }
    if (term?.kind === 'string') return []
    throw new CodecError(
        'an object entry key must be `string` or a string literal key set',
    )
}

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
): unknown {
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
            if (Object.hasOwn(fields, name)) {
                throw new CodecError(`'${name}' is declared more than once`)
            }
            setOwn(fields, name, slot)
        }
    }
    return objectFromMap(fields, rest) as ObjectCodec<
        Record<string, ObjectSlot>,
        AnyCodec | undefined
    >
}

/** The options a factor offers, at the type level: a union's, or the factor itself. */
// the term is matched too: an entry of a scope is a union at the term of the entry, and a match at
// the default term reads such an entry as one option
export type FactorOptions<F> = F extends UnionCodec<
    infer _T,
    infer Os,
    infer _Tm
>
    ? Os
    : F extends {
            readonly [optionsMarker]?: infer Os extends readonly unknown[]
        }
      ? Os
      : readonly [F]

/** Whether any option of a factor is left open by a rest codec. */
export type AnyOpen<F> = FactorOptions<F>[number] extends infer O
    ? O extends ObjectCodec<infer _S, infer R, infer _T, infer _Tm>
        ? [R] extends [undefined]
            ? never
            : true
        : never
    : never

/**
 * The members that the attribute of a codec carries: the required keys of `Attribute`, because an
 * `Attribute` types each other member as an optional `never`.
 */
export type StoredMembers<C> = AttributeOf<C> extends infer W
    ? W extends unknown
        ? {
              [K in keyof W]-?: object extends Pick<W, K> ? never : K
          }[keyof W]
        : never
    : never

// ── unions with no discriminator ────────────────────────────────────

/**
 * **Whether a term holds a literal that the type does not name exactly**: the value type is a
 * union, a template literal, a whole base, or a list that is no tuple, as `string(u)` gives for
 * `u: 'a' | 'b'`. A `binary` and a `dynamoNumber` with free text are the same case, because the
 * type of their value is the whole base. The constructor keeps such an argument. The value at run
 * time is one value, or the values of the list, and the type names a set that holds it. So the type
 * cannot say which alternative the term pins ({@link FitsCodec}). A union with an option that is no
 * literal is no literal term.
 */
export type Inexact<T, Env = []> = Norm<T, Env> extends [infer N, infer E]
    ? N extends ['prim', ['literal', unknown, infer V]]
        ? InexactValue<V>
        : N extends ['union', infer Os extends unknown[]]
          ? InexactAll<{ [I in keyof Os]: OptionInexact<Os[I], E> }[number]>
          : N extends ['refine', infer I, ...unknown[]]
            ? Inexact<I, E>
            : [LibraryInner<N>] extends [never]
              ? false
              : Inexact<LibraryInner<N>, E>
    : false
