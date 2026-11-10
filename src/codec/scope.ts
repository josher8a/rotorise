import type { ErrorMessage } from '../utils'
import type { MissingCodec } from './adapters'
import type { AttributeMap, AttributeValue, M, StoredItem } from './attribute'
import type {
    AnyCodec,
    AnySpread,
    AttributeCodec,
    AttributeOf,
    Closed,
    Decoded,
    EncodedBy,
    EncodedPatch,
    Free,
    FreeOf,
    freeMarker,
    Nestable,
    ObjectSlot,
    WritesPin,
    WritesVariantsPin,
} from './build'
import { codecOfTerm, setOf, slotsOf } from './capabilities'
import type { ItemTerm } from './denote'
import {
    byTagSem,
    guard,
    itemSem,
    judged,
    membersOf,
    membersTooDeeply,
    termOf,
} from './denote'
import type { AnyObjectCodec, ItemOf, KnownKeys, SpecsOf } from './derivedItem'
import { keySets } from './derivedItem'
import type { DecodeTerm, ScopeWallCycle } from './pathModel'
import { checkFill } from './prisms'
import type { ArrayOver, ListCodec, SetCapable, SpreadOver } from './products'
import type { Result } from './result'
import { andThen, CodecError, failed, orThrow, setOwn } from './result'
import type {
    DefOf,
    ElementMark,
    ElementsMark,
    Field,
    fillMarker,
    Itemable,
    itemMarker,
    itemTermMarker,
    ObjectTermOf,
    OfParts,
    OptionsMark,
    optionalMarker,
    ScopeTerms,
    Term,
    TermMark,
    TermOf,
    TermsOf,
    termMarker,
    undefinableMarker,
    writesMarker,
} from './term'
import {
    closedCopy,
    isCallerPin,
    openRefusal,
    resolvedTerm,
    storedPin,
    unboundRefs,
} from './term'
import { itemRefusal, own, readTags } from './value'

/** The free names of an object: the names of its spec and its rest. An entry of a scope has none. */
export type ObjectFree<Spec, Rest, Tm> = [Tm] extends [OfParts]
    ? FreeOf<Spec[keyof Spec]> | FreeOf<Rest>
    : never

/**
 * An attribute that may be absent from the item entirely.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A>` intersected with the
 * marker, so it claimed a field has an `encode` and a `decode` — true only because {@link optional}
 * built its answer by spreading the codec it marks. The field stratum refuses it: a field is a statement about a
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

/*
 * **A cycle is a name in one declaration.** `ref(name)` is the reference, and its term is the
 * name. `scope(defs)` binds each name of `defs`. The term of an entry is `['scope', D, K]`: the
 * record `D` of the terms of the definitions, and the name `K`. A `ref` resolves by one lookup
 * in `D`, so the type substitutes nothing and copies nothing. The decoded type of an entry is a
 * function of that term, so no caller states the decoded type of a cycle.
 *
 * At run time, a `ref` is a node that carries a slot, and `scope` fills the slot. Each former that
 * runs before `scope` reads the `ref` as unbound. So a cycle of the term graph passes through a `ref`.
 */
export type Ref<N extends string> = AttributeCodec<unknown> &
    TermMark<['ref', N]> &
    Free<N>
export type ScopeTerm<Defs, K> = ['scope', ScopeTerms<Defs>, K]
export type ScopeOf<Defs> = {
    readonly [K in keyof Defs]: EntryOf<
        DefOf<Defs, Defs[K]>,
        ScopeTerm<Defs, K>,
        Defs
    >
}
/**
 * **A `ref` read in a scope**: the codec of the `ref` with the term of the entry that the name
 * binds. The decoded type reads the term, and the attribute reads the definition. The codec holds
 * no structure of the entry, so a cycle of entries is no cycle of types, and a reader of the term
 * resolves the name where the run time resolves it.
 */
export type ClosedRef<Defs, N extends keyof Defs> = AttributeCodec<
    DecodeTerm<ScopeTerm<Defs, N>>,
    AttributeOf<DefOf<Defs, Defs[N]>> & AttributeValue
> &
    TermMark<ScopeTerm<Defs, N>> &
    SpecOfEntry<Defs, DefOf<Defs, Defs[N]>>
/** The spec of the object that an entry names, so a fit reads the object through the `ref`. */
export type SpecOfEntry<Defs, C> = C extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    AnyCodec | undefined
>
    ? { readonly spec: SpecInScope<Spec, Defs> }
    : C extends UnionCodec<infer _T, infer Os extends readonly unknown[]>
      ? { readonly spec: OptionSpecs<Defs, Os> }
      : unknown
/**
 * The specs of the options of a union entry, one for each object, or `false` where an option is no
 * object. An option that names a union entry reads as the options of that entry.
 */
export type OptionSpecs<
    Defs,
    Os extends readonly unknown[],
> = Os extends readonly [infer H, ...infer R extends readonly unknown[]]
    ? OptionSpec<Defs, DefOf<Defs, H>> extends infer S extends
          readonly unknown[]
        ? OptionSpecs<Defs, R> extends infer T extends readonly unknown[]
            ? [...S, ...T]
            : false
        : false
    : []
export type OptionSpec<Defs, D> = D extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    AnyCodec | undefined,
    infer _T,
    infer _Tm
>
    ? [SpecInScope<Spec, Defs>]
    : D extends UnionCodec<infer _T, infer Os extends readonly unknown[]>
      ? OptionSpecs<Defs, Os>
      : false
/**
 * A slot of an object, with each `ref` closed in the scope `Defs` that the slot reads: a bare `ref`,
 * the codec that an `optional` or an `undefinable` marks, each option of a union, and each slot of
 * an object, at any depth of those nodes. A fill closes only a bare `ref`. Any other slot is the slot.
 */
export type SlotInScope<S, Defs> = [FreeOf<S>] extends [never]
    ? S
    : S extends { readonly codec: infer C }
      ? TermOf<C> extends ['ref', infer N extends keyof Defs]
          ? S extends { readonly [fillMarker]: infer T }
              ? MissingCodec<
                    T,
                    AttributeOf<ClosedRef<Defs, N>> & AttributeValue,
                    ClosedRef<Defs, N>
                > &
                    TermMark<['fill', ScopeTerm<Defs, N>]>
              : MarkLike<S, ClosedRef<Defs, N>>
          : S extends { readonly [fillMarker]: unknown }
            ? S
            : Deep<C, Defs> extends infer D extends AnyCodec
              ? MarkLike<S, D>
              : S
      : Deep<S, Defs>
/** A codec with each `ref` of its union options and object slots closed in the scope `Defs`. */
export type Deep<C, Defs> = TermOf<C> extends [
    'ref',
    infer N extends keyof Defs,
]
    ? ClosedRef<Defs, N>
    : C extends UnionCodec<infer _T, infer Os extends readonly unknown[]>
      ? UnionInScope<{ [I in keyof Os]: SlotInScope<Os[I], Defs> }>
      : C extends ObjectCodec<
              infer Spec extends Record<string, ObjectSlot>,
              infer Rest extends AnyCodec | undefined
          >
        ? ObjectCodec<SpecInScope<Spec, Defs>, Rest>
        : C extends ElementsMark<infer Cs extends readonly unknown[]>
          ? [readonly unknown[]] extends [Cs]
              ? C
              : ListCodec<{
                    [I in keyof Cs]: Cs[I] extends AnySpread
                        ? SpreadInScope<Cs[I], Defs>
                        : SlotInScope<Cs[I], Defs>
                }>
          : C extends ElementMark<infer E>
            ? Deep<E, Defs> extends infer D extends AnyCodec
                ? ArrayOver<D>
                : C
            : C
/** A spread with each `ref` of its element closed in the scope `Defs`. */
export type SpreadInScope<S, Defs> = S extends ElementMark<infer E>
    ? Deep<E, Defs> extends infer D extends AnyCodec
        ? SpreadOver<D>
        : S
    : S
export type UnionInScope<Os extends readonly unknown[]> = UnionCodec<
    DecodeTerm<['union', TermsOf<Os>]>,
    Os
>
/** The spec of an object, with each bare `ref` of a slot closed in the scope `Defs`. */
export type SpecInScope<Spec extends Record<string, ObjectSlot>, Defs> = {
    [K in keyof Spec]: SlotInScope<Spec[K], Defs>
} extends infer S extends Record<string, ObjectSlot>
    ? S
    : never
/** An option of an entry: an object reads its slots in the scope `Defs`, and any other option is the option. */
export type OptionInScope<O, Defs> = O extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    infer Rest extends AnyCodec | undefined
>
    ? ObjectCodec<SpecInScope<Spec, Defs>, Rest>
    : O
/**
 * An entry: the codec of the definition that the entry names, read at the term `Tm` of the entry.
 * An object keeps its item, and a union keeps its item and its slices, each typed from the term.
 * Each option of a union is the definition that the option names, so a slice reads a `ref` option
 * as the definition. Each slot of an object, and of an option that is an object, reads a bare `ref`
 * as the entry that the `ref` names ({@link ClosedRef}). Any other entry keeps the `.set()` of an
 * element that writes `S`, `N` or `B`, and a dissection keeps its options in declared order, each
 * the definition that the option names.
 */
export type EntryOf<C, Tm, Defs> = C extends ObjectCodec<
    infer Spec extends Record<string, ObjectSlot>,
    infer Rest extends AnyCodec | undefined,
    infer _T,
    infer _Tm
>
    ? ObjectCodec<SpecInScope<Spec, Defs>, Rest, DecodeTerm<Tm>, Tm>
    : C extends UnionCodec<infer _T, infer Options extends readonly unknown[]>
      ? UnionCodec<
            DecodeTerm<Tm>,
            {
                [I in keyof Options]: OptionInScope<
                    DefOf<Defs, Options[I]>,
                    Defs
                >
            },
            Tm
        >
      : AttributeCodec<DecodeTerm<Tm>, AttributeOf<C> & AttributeValue> &
            TermMark<Tm> &
            SetCapable<DecodeTerm<Tm>, AttributeOf<C> & AttributeValue, Tm> &
            (C extends OptionsMark<infer Os extends readonly unknown[]>
                ? OptionsMark<{
                      [I in keyof Os]: OptionInScope<DefOf<Defs, Os[I]>, Defs>
                  }>
                : unknown)
/** A refusal on each definition that reads a name the scope does not declare. */
export type ScopeNamed<Defs> = {
    readonly [K in keyof Defs]: [Exclude<FreeOf<Defs[K]>, keyof Defs>] extends [
        never,
    ]
        ? unknown
        : ErrorMessage<`[scope] a ref names '${Exclude<FreeOf<Defs[K]>, keyof Defs> & string}', which this scope does not declare`>
}

/** A refusal on each definition that holds a wall over an entry on a cycle of this scope. */
export type ScopeWalls<Defs> = {
    readonly [K in keyof Defs]: [
        ScopeWallCycle<ScopeTerms<Defs>, TermOf<Defs[K]>>,
    ] extends [never]
        ? unknown
        : ErrorMessage<`[scope] a wall in '${K & string}' reads '${ScopeWallCycle<ScopeTerms<Defs>, TermOf<Defs[K]>> & string}', an entry on a cycle. A wall reaches no cycle`>
}

/**
 * A reference of a {@link scope}. The `ref` names an entry of the scope that holds it, and reads as
 * the codec of that entry.
 */
export function ref<const N extends string>(name: N): Ref<N>
export function ref(name: string): unknown {
    return codecOfTerm({ kind: 'ref', slot: { name } })
}

/**
 * **Codecs that name each other**, each one an entry. A {@link ref} in a definition names an entry,
 * and the decoded type of each entry follows from the definitions, with no annotation. A single
 * cycle is a scope of one entry.
 *
 * Each former ran before the names were bound, so the guard runs here: a recursion with no
 * container on its path, or with an adapter on its path, is refused. A `ref` to a name that `defs`
 * does not declare is refused. Then each check that reads through a `ref` runs on the closed copy:
 * the check of a `union` with a `ref` option, which a `nullable` over a `ref` builds, the index of
 * a dissection whose tag reads a `ref`, and the fill value of a `fill` that writes through
 * a `ref`.
 *
 * **A scope closes a copy, by lexical scope.** Each entry is the codec of its closed term. A `ref`
 * binds in the record of its own scope, and a cycle is a recursive binding of that record
 * (`letrec`), not a slot written in place. Each entry has no free name, in the type and at run
 * time, so each entry is a codec to use. A fragment stays an open term, so the fragment refuses
 * each use, and the result of a scope depends on its own arguments only.
 *
 * @example
 * ```ts
 * const { Folder } = scope({
 *     Folder: object({ name: string, children: array(ref('Node')) }),
 *     Node: union([object({ file: string }), ref('Folder')]),
 * })
 * ```
 */
export function scope<const Defs extends Readonly<Record<string, AnyCodec>>>(
    defs: Defs & ScopeNamed<Defs> & ScopeWalls<Defs>,
): ScopeOf<Defs>
export function scope(defs: Readonly<Record<string, AnyCodec>>): unknown {
    const terms = Object.fromEntries(
        Object.entries(defs).map(([name, def]) => [name, termOf(def)]),
    )
    for (const slot of unboundRefs(Object.values(terms)))
        if (!Object.hasOwn(defs, slot.name))
            throw new CodecError(
                `[scope] a ref names '${slot.name}', which this scope does not declare`,
            )
    // **A scope closes a copy.** Each `ref` of the copy is bound in `record`, and no slot that a
    // caller holds changes. So a scope reads its own arguments only, and a fragment stays open.
    // The key set of a dissection is the one fact that the term does not carry, so the copy of a
    // dissection takes the key set of the node that it replaces
    const record: Record<string, Term> = {}
    const [close, copies] = closedCopy(record)
    for (const [name, t] of Object.entries(terms))
        setOwn(record, name, close(t))
    for (const [was, copy] of copies) {
        const ks = keySets.get(was)
        if (ks !== undefined) keySets.set(copy, ks)
    }
    // The refusal of the guard carries the term of the entry, so a checker states the model's
    // guard on that term. Then each copy is judged one time, with each name bound
    for (const [name, t] of Object.entries(record)) {
        const refused = guard(t, name)
        if (refused) throw refused
    }
    for (const copy of copies.values()) {
        judged(copy, false)
        if (copy.kind === 'object')
            for (const f of Object.values(copy.body.fields))
                if (f.mark === 'fill') checkFill(codecOfTerm(f.t), f.v)
        const ks = keySets.get(copy)
        if (ks !== undefined && copy.kind === 'union')
            dissectionOf(copy, ks).resolution()
    }
    // **An entry is the codec of its closed term.** An entry that reaches no free name is the
    // codec that the caller declared. An object entry reads its spec and its open block from the
    // term. An entry carries the `.set()` of the node that its chain of `ref`s names, as its type
    // does. A `ref` and a literal carry no `.set()` of their own, so such an entry builds the set
    // of itself, and the judgment of the set refuses an element that writes no `S`, `N` or `B`. An
    // object and a union write `M` or no single member, so their entries carry no `.set()`
    return Object.fromEntries(
        Object.entries(defs).map(([name, def]) => {
            const t = record[name]
            if (t === undefined || t === terms[name])
                return [name, entryOf(def, t?.kind)]
            const codec: AnyCodec = codecOfTerm(t)
            if (t.kind !== 'object') return [name, entryOf(codec, t.kind)]
            const { spec, rest } = objectItem(t)
            return [name, { ...codec, spec, rest }]
        }),
    )
}

/** The entry of a scope over its codec: a codec with no `.set()` builds the set of itself. */
export const entryOf = (
    codec: AnyCodec,
    kind: Term['kind'] | undefined,
): object =>
    'set' in codec || kind === 'object' || kind === 'union'
        ? codec
        : { ...codec, set: setOf(() => codec) }

/**
 * **The marker of a whole-item reading.** Each reading that {@link item} returns carries the
 * marker, and no other codec carries it: an object codec has a `spec` too, so `spec` does not tell
 * a reading from a codec. Test a root with `itemMark in root`. The reading types state the same
 * fact as `readonly [itemMark]: true`, and the type of a root reads it from there.
 */
export const itemMark = Symbol('item reading')

/**
 * The codecs an item needs: one per attribute, optional exactly where the entity is.
 *
 * Each attribute that the entity states has a field, and the spec names no other attribute. A field
 * is an {@link OptionalCodec} where the entity admits `undefined` at the attribute. Elsewhere the
 * field is a {@link Nestable} codec of the type of the attribute. A plain codec at an optional
 * attribute is a type error of this type, and `tableEntry` accepts that record.
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
    // the decoded type and the term: an entry of a `scope` reads both from the term of the entry
    T = OfParts,
    Tm = OfParts,
> = {
    // spelled out rather than intersected with `AttributeCodec`, for the reason recorded on
    // {@link ItemCodec}: as an intersection the same type costs more to instantiate and stops being
    // *comparable* to a hand-written shape. Measured at +14k instantiations across this repo
    readonly encode: (
        this: Closed,
        value: ItemOf<T, Spec, Rest>,
    ) => Result<M<EncodedBy<Spec, Rest>>>
    readonly decode: (
        this: Closed,
        attribute: AttributeValue,
    ) => Result<ItemOf<T, Spec, Rest>>
    readonly unsafeEncode: (
        this: Closed,
        value: ItemOf<T, Spec, Rest>,
    ) => M<EncodedBy<Spec, Rest>>
    readonly unsafeDecode: (
        this: Closed,
        attribute: AttributeValue,
    ) => ItemOf<T, Spec, Rest>
    readonly def: Term
    /** What this object declares. {@link item} reads the same declaration as a whole item. */
    readonly spec: Spec
    /** The codec of an attribute the spec does not declare, or `undefined` for a closed object. */
    readonly rest: Rest
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
    /** The model's term of this codec. Type-level only. */
    readonly [termMarker]?: [Tm] extends [OfParts]
        ? ObjectTermOf<Spec, Rest>
        : Tm
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [ObjectFree<Spec, Rest, Tm>]
}

export type UnionCodec<
    T,
    Options extends readonly unknown[],
    // the term: an entry of a `scope` reads it, and its slices, from the term of the entry
    Tm = OfParts,
> = {
    readonly encode: (this: Closed, value: T) => Result<WrittenBy<Options>>
    readonly decode: (this: Closed, attribute: AttributeValue) => Result<T>
    readonly unsafeEncode: (this: Closed, value: T) => WrittenBy<Options>
    readonly unsafeDecode: (this: Closed, attribute: AttributeValue) => T
    readonly def: Term
    /**
     * The same union read as a whole item — only where every option is an object.
     *
     * An item is a map, so a union that can also be an `S` has no top-level reading. Saying so with a
     * message rather than with an absent property is what makes reaching for it report *why* instead
     * of "property does not exist".
     */
    readonly [itemMarker]: [
        AllObjects<Options> extends true
            ? Untagged<T, SpecsOf<Options>> & Free<UnionFree<Options, Tm>>
            : ErrorMessage<'[union] this union can hold an attribute that is not a map, so it has no whole-item reading — an item is always a map'>,
    ]
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<SpecsOf<Options>>
    /** The model's term of this codec. Type-level only. */
    readonly [termMarker]?: [Tm] extends [OfParts]
        ? ['union', TermsOf<Options>]
        : Tm
    /** The free names of this codec. Type-level only. */
    readonly [freeMarker]?: [UnionFree<Options, Tm>]
}

/** The free names of a union: the names of its options. An entry of a scope has none. */
export type UnionFree<Options extends readonly unknown[], Tm> = [Tm] extends [
    OfParts,
]
    ? FreeOf<Options[number]>
    : never

export type ItemCodec<T, Spec = unknown, Rest = undefined, Tm = OfParts> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
    /** Every attribute, or why one could not be written. For `PutItem`. */
    readonly encode: (this: Closed, item: T) => Result<EncodedBy<Spec, Rest>>
    readonly unsafeEncode: (this: Closed, item: T) => EncodedBy<Spec, Rest>
    /**
     * The attributes a patch names, or why one could not be written. For `UpdateItem`, which
     * addresses attributes individually — the reason a whole-value codec does not fit DynamoDB and
     * this is a record of per-attribute ones.
     */
    readonly encodePartial: <const Patch extends Partial<T>>(
        this: Closed,
        patch: Patch,
    ) => Result<EncodedPatch<Spec, Patch>>
    readonly unsafeEncodePartial: <const Patch extends Partial<T>>(
        this: Closed,
        patch: Patch,
    ) => EncodedPatch<Spec, Patch>
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    readonly spec: Spec
    /** The codec of an attribute the spec does not declare, or `undefined` for a closed object. */
    readonly rest: Rest
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesPin<Spec, Rest>
    /** The term that {@link at} walks. Type-level only. */
    readonly [itemTermMarker]?: [Tm]
}

/**
 * **The whole-item reading of an object node, a function of the node.** The spec holds the codec
 * of each field term, and `rest` holds the codec of the open term. The memo is a cache only.
 */
export const objectReadings = new WeakMap<ItemTerm, ObjectItem>()

export const objectItem = (itemDef: ItemTerm): ObjectItem => {
    const built = objectReadings.get(itemDef)
    if (built) return built
    /**
     * **The view, and this is where it starts.**
     *
     * The owner's ruling: the top-level map belongs to the view, not to the codec. An `object`
     * codec writes an `M` like any other term, and {@link item} is the one reading that writes no map —
     * the same pair, one level in.
     *
     * So the pair is not built here. `denote.ts` builds one item pair per term and this hands out
     * that one, which is what makes `item.encode === codec.encode`'s body the same function. They
     * were two objects before `579ed89`, and nothing said which of them a caller was running.
     */
    const body = itemSem(itemDef)
    const { spec, rest } = slotsOf(itemDef.body)
    // a term that reads a name that no scope binds refuses each use
    const self: ObjectItem = {
        [itemMark]: true,
        encode: (item) =>
            openRefusal(itemDef) ??
            itemRefusal(item) ??
            (body.encode(item) as never),

        encodePartial: (patch) =>
            openRefusal(itemDef) ??
            itemRefusal(patch) ??
            (body.encode(patch as Record<string, unknown>, 0, true) as never),

        decode: (item) =>
            openRefusal(itemDef) ??
            itemRefusal(item) ??
            membersTooDeeply(item, 0) ??
            (body.decode(
                item as Readonly<Record<string, AttributeValue>>,
            ) as never),

        unsafeEncode: (item) => orThrow(self.encode(item)),
        unsafeDecode: (item) => orThrow(self.decode(item)),
        unsafeEncodePartial: (patch) => orThrow(self.encodePartial(patch)),

        spec,
        rest,
        def: itemDef,
    }
    objectReadings.set(itemDef, self)
    return self
}

export type Marked = { readonly [itemMark]: true }

/** A whole-item reading, as the run time holds it. */
export type Reading = Marked & { readonly spec: unknown }

/** The whole-item reading of an object node: the declared spec, the open block, and the pair. */
export type ObjectItem = ItemCodec<
    Record<string, unknown>,
    Record<string, ObjectSlot>,
    AnyCodec | undefined
>

/** The whole-item reading of the node that a term names, or nothing where the node is no object. */
export const objectNamed = (t: Term): ObjectItem | undefined => {
    const node = resolvedTerm(t)
    return node?.kind === 'object' ? objectItem(node) : undefined
}

/** The whole-item reading of a dissection, a function of the term and the key set. */
export type Dissecting = {
    readonly self: Reading
    readonly resolution: () => unknown
}
export const dissections = new WeakMap<Term, Dissecting>()

export const dissectionOf = (
    unionDef: Extract<Term, { kind: 'union' }>,
    ks: readonly string[],
): Dissecting => {
    const built = dissections.get(unionDef)
    if (built) return built
    type T = Record<string, unknown>
    const memberTerms = unionDef.options
    // **every member's assignment, read off the member's own body, and no two alike.** Both rules
    // are the index's, not the union's: the one-key refusals `discriminatedUnion` used to spell
    // inline are these two at one key. The union's own gate does not replace them, because a
    // duplicated index key is a different fact from two members that are not disjoint, and the index is
    // what needs it.
    //
    // **A tag that a member reads through an unbound `ref` is indexed by the scope**, on the closed
    // copy, because the index reads the literal of each tag through the `ref`
    const index = () => {
        // a tag is written through its field only where a caller's adapter holds one: a plain
        // literal is its own stored text
        const callerMembers = new Map<unknown, Set<string>>()
        const written = (
            variant: ItemCodec<T, unknown>,
            patch: Readonly<Record<string, unknown>>,
            scope: 'member' | 'adapter',
        ) => {
            // the write of a tag reads `adapter`: it runs for a name that holds a caller's adapter in
            // this member, and for no other name, because a plain key of the member is its own
            // literal and no adapter refused it. The check of a member against its own value reads
            // `member`, the whole write of a member that holds an adapter at some key.
            const names = callerMembers.get(variant)
            return names &&
                (scope === 'member' ||
                    Object.keys(patch).every((name) => names.has(name)))
                ? variant.encodePartial(patch as never)
                : undefined
        }
        const members = membersOf(
            ks,
            memberTerms.map((term, at) => {
                const node = resolvedTerm(term)
                const item = node && objectNamed(node)
                if (node?.kind !== 'object' || !item) {
                    throw new CodecError(
                        `every option must be an object codec, and option ${at} is a \`${node?.kind}\``,
                    )
                }
                for (const name of ks) {
                    const field = own(node.body.fields, name)
                    if (field && isCallerPin(storedPin(field.t))) {
                        const names = callerMembers.get(item) ?? new Set()
                        callerMembers.set(item, names.add(name))
                    }
                }
                return [
                    node.body,
                    item as unknown as ItemCodec<T, unknown>,
                ] as const
            }),
            callerMembers.size > 0 ? written : undefined,
        )
        if (failed(members)) throw members
        const { pick, tagOf } = byTagSem(
            ks,
            members,
            callerMembers.size > 0 ? written : undefined,
        ) as unknown as {
            pick: (
                assignment: Readonly<Record<string, string>>,
            ) => Result<ItemCodec<T, unknown>>
            tagOf: (
                item: Partial<T>,
            ) => Result<Readonly<Record<string, string>>>
        }
        return { members, pick, tagOf }
    }
    let indexed: ReturnType<typeof index> | undefined
    const resolution = (): ReturnType<typeof index> => {
        indexed ??= index()
        return indexed
    }
    const pick = (assignment: Readonly<Record<string, string>>) =>
        resolution().pick(assignment)
    const tagOf = (item: Partial<T>) => resolution().tagOf(item)

    // **the published one-key surface carries `discriminator`, and this is that name.** Where the
    // key set has one element, that element *is* the discriminator: it is the whole set, not the
    // head of a list. Where it has several there is no such name, and the codec carries `keys`
    // instead — so the field is absent rather than holding one of several
    const [only, ...rest] = ks
    const oneKey = rest.length === 0 ? (only as string) : undefined

    // a term that reads a name that no scope binds refuses each use
    const self = {
        [itemMark]: true as const,
        encode: (item: T) =>
            openRefusal(unionDef) ??
            itemRefusal(item) ??
            andThen(andThen(tagOf(item), pick), (variant) =>
                variant.encode(item as never),
            ),
        encodePartial: (patch: Partial<T>) =>
            openRefusal(unionDef) ??
            itemRefusal(patch) ??
            andThen(andThen(tagOf(patch), pick), (variant) =>
                variant.encodePartial(patch as never),
            ),
        decode: (item: StoredItem) =>
            openRefusal(unionDef) ??
            itemRefusal(item) ??
            (andThen(andThen(readTags(item, ks), pick), (variant) =>
                variant.decode(item),
            ) as Result<T>),
        // the variant that the tags of an item select, read as `encode` reads them. The key layer
        // reads each variant through this one reader, so a tag under an adapter of a caller selects
        // the variant by the stored literal
        variantOf: (item: Partial<T>) =>
            openRefusal(unionDef) ?? andThen(tagOf(item), pick),
        // each variant, in the order of the options, for a key that no item names the variant of
        variants: () => resolution().members.map(([, variant]) => variant),
        unsafeEncode: (item: T) => orThrow(self.encode(item)),
        unsafeEncodePartial: (patch: Partial<T>) =>
            orThrow(self.encodePartial(patch)),
        unsafeDecode: (item: StoredItem) => orThrow(self.decode(item)),
        keys: ks,
        ...(oneKey === undefined ? {} : { discriminator: oneKey }),
        // at one key the spec is keyed by the tag, which is what a caller walking the variants
        // reads today; at several there is no one string to key it by, so it is the members' specs
        // in the order the caller declared them
        get spec() {
            const { members } = resolution()
            return oneKey === undefined
                ? members.map(([, variant]) => variant.spec)
                : Object.fromEntries(
                      members.map(([assignment, variant]) => [
                          assignment[oneKey],
                          variant.spec,
                      ]),
                  )
        },
        def: unionDef,
    }
    const made = { self, resolution }
    dissections.set(unionDef, made)
    return made
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
export type AnyTaggedCodec = Itemable<{
    readonly encode: (item: never) => unknown
    readonly decode: (item: StoredItem) => unknown
    readonly discriminator: string
}>

/** What a union writes: whatever the option it chose writes. */
export type WrittenBy<Options extends readonly unknown[]> = Extract<
    { [I in keyof Options]: AttributeOf<Options[I]> }[number],
    AttributeValue
>

/** The variants of an untagged union. There is no tag, so there is nothing to key them by. */
export type UntaggedSpec<T> = readonly ItemSpec<T>[]

export type Untagged<T, Specs extends readonly unknown[] = UntaggedSpec<T>> = {
    /** The marker of a whole-item reading. Type-level here, run-time in {@link itemMark}. */
    readonly [itemMark]: true
    /** Every attribute, or why one could not be written. */
    readonly encode: (this: Closed, item: T) => Result<AttributeMap>
    readonly unsafeEncode: (this: Closed, item: T) => AttributeMap
    /** The entity, or why the item could not be read. */
    readonly decode: (this: Closed, item: StoredItem) => Result<T>
    readonly unsafeDecode: (this: Closed, item: StoredItem) => T
    readonly spec: Specs
    /** What this codec is — see {@link Term}. */
    readonly def: Term
    /** The row this codec writes, pinnable with {@link Writes}. Type-level only. */
    readonly [writesMarker]?: WritesVariantsPin<Specs>
}
/** The codec `C` under the presence mark of the declared field `Opt`. */
export type MarkLike<Opt, C extends AnyCodec> = Opt extends {
    readonly [undefinableMarker]: true
}
    ? UndefinableCodec<Decoded<C>, AttributeOf<C>, C> &
          TermMark<['undefinable', TermOf<C>]>
    : OptionalCodec<Decoded<C>, AttributeOf<C>, C> &
          TermMark<['optional', TermOf<C>]>
