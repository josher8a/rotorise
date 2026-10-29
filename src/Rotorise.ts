import type {
    Attribute,
    AttributeMap,
    AttributeValue,
    StoredItem,
} from './codec/attribute'
import { carrying } from './codec/attribute'
import type {
    AnyCodec,
    Closed,
    Encoded,
    IsUnion,
    ItemCodec,
    ItemSpec,
    ObjectSlot,
    PathOf,
    Result,
    TaggedCodec,
} from './codec/codec'
import {
    andThen,
    CodecError,
    constantOf,
    failed,
    item as itemOf,
    object,
    orThrow,
    pathBuilder,
} from './codec/codec'
import type { Field } from './codec/term'
import type {
    DistributiveOmit,
    DistributivePick,
    ErrorMessage,
    Exact,
    MergeIntersectionObject,
    NonEmptyArray,
    Replace,
    SliceFromStart,
    show,
    ValueOf,
} from './utils'

// When a spec item has a transform function, use the transform's parameter type
// instead of the entity's property type. This allows callers to pass only the
// fields the transform actually needs (e.g. Pick<Obj, 'id'> instead of Obj).
type TransformOverride<
    Spec extends InputSpecShape,
    K,
    Fallback,
    Matched = Extract<Spec[number], [K, (...args: any[]) => any, ...any[]]>,
> = [Matched] extends [never]
    ? Fallback
    : // Contravariant inference: when the same key appears multiple times with
      // different transforms (e.g. Pick<Obj,'id'> and Pick<Obj,'name'>),
      // this intersects the parameter types rather than unioning them.
      (
            Matched extends [any, (x: infer P) => any, ...any[]] // biome-ignore lint/suspicious/noExplicitAny: inference
                ? (x: P) => void
                : never
        ) extends (x: infer I) => void
      ? I
      : Fallback

/** The names of a spec that no attribute of the entity has: the paths that the entity holds. */
type PathHeads<Entity, Heads> = Heads extends string
    ? Heads extends keyof Entity
        ? never
        : [ValueAt<Entity, Heads>] extends [never]
          ? never
          : Heads
    : never

/** The deep pick of paths: each path as the objects above one value, joined into one type. */
type DeepPick<
    Entity,
    Spec extends InputSpecShape,
    Paths,
    Optional extends boolean,
> = (
    Paths extends string
        ? (
              x: AtPath<
                  Paths,
                  TransformOverride<Spec, Paths, ValueAt<Entity, Paths>>,
                  Optional
              >,
          ) => void
        : never
) extends (x: infer Joined) => void
    ? Joined
    : never

type PlainKeyParams<
    Entity,
    InputSpec extends InputSpecShape,
    skip extends number = 1,
> = Entity extends unknown
    ? show<
          {
              [K in extractHeadOrPass<
                  SliceFromStart<
                      InputSpec,
                      number extends skip ? 1 : skip
                  >[number]
              > &
                  keyof Entity]: TransformOverride<InputSpec, K, Entity[K]>
          } & {
              [K in extractHeadOrPass<InputSpec[number]> &
                  keyof Entity]?: TransformOverride<InputSpec, K, Entity[K]>
          }
      >
    : never

type PathKeyParams<
    Entity,
    InputSpec extends InputSpecShape,
    skip extends number = 1,
    Required_ = extractHeadOrPass<
        SliceFromStart<InputSpec, number extends skip ? 1 : skip>[number]
    >,
    All = extractHeadOrPass<InputSpec[number]>,
> = Entity extends unknown
    ? show<
          {
              [K in Required_ & keyof Entity]: TransformOverride<
                  InputSpec,
                  K,
                  Entity[K]
              >
          } & {
              [K in All & keyof Entity]?: TransformOverride<
                  InputSpec,
                  K,
                  Entity[K]
              >
          } & ([PathHeads<Entity, All>] extends [never]
                  ? unknown
                  : DeepPick<
                        Entity,
                        InputSpec,
                        PathHeads<Entity, Required_>,
                        false
                    > &
                        DeepPick<
                            Entity,
                            InputSpec,
                            PathHeads<Entity, All>,
                            true
                        >)
      >
    : never

export type CompositeKeyParamsImpl<
    Entity,
    InputSpec extends InputSpecShape,
    skip extends number = 1,
> = HoldsPath<InputSpec> extends true
    ? PathKeyParams<Entity, InputSpec, skip>
    : PlainKeyParams<Entity, InputSpec, skip>

export type CompositeKeyParams<
    Entity extends Record<string, unknown>,
    FullSpec extends InputSpec<MergeIntersectionObject<Entity>>[],
    skip extends number = 1,
> = CompositeKeyParamsImpl<Entity, FullSpec, skip>

type CompositeKeyBuilderImpl<
    Entity,
    Spec,
    Separator extends string = '#',
    Deep extends number = number,
    isPartial extends boolean = false,
    Boundary extends boolean = false,
> = Entity extends unknown
    ? HoldsPath<Spec> extends true
        ? CompositeKeyStringBuilderPath<
              Entity,
              [Deep] extends [never]
                  ? Spec
                  : number extends Deep
                    ? Spec
                    : SliceFromStart<Spec, Deep>,
              Separator,
              boolean extends isPartial ? false : isPartial,
              '',
              never,
              Boundary,
              Boundary extends true ? StopsBeforeLast<Spec, Deep> : false
          >
        : CompositeKeyStringBuilder<
              Entity,
              [Deep] extends [never]
                  ? Spec
                  : number extends Deep
                    ? Spec
                    : SliceFromStart<Spec, Deep>,
              Separator,
              boolean extends isPartial ? false : isPartial,
              '',
              never,
              Boundary,
              Boundary extends true ? StopsBeforeLast<Spec, Deep> : false
          >
    : never

/**
 * Whether the depth keeps fewer components than the spec holds.
 *
 * The type half of the count in the run-time builder: the boundary follows a print that stops
 * before the last component. A depth that is no literal keeps the whole spec here, as the print does.
 */
type StopsBeforeLast<Spec, Deep extends number> = [Deep] extends [never]
    ? false
    : number extends Deep
      ? false
      : SliceFromStart<Spec, Deep> extends infer Kept extends readonly unknown[]
        ? Spec extends readonly unknown[]
            ? Kept['length'] extends Spec['length']
                ? false
                : true
            : false
        : false

export type CompositeKeyBuilder<
    Entity extends Record<string, unknown>,
    Spec extends InputSpec<MergeIntersectionObject<Entity>>[],
    Separator extends string = '#',
    Deep extends number = number,
    isPartial extends boolean = false,
> = CompositeKeyBuilderImpl<Entity, Spec, Separator, Deep, isPartial>

type joinable = string | number | bigint | boolean | null | undefined

type ExtractHelper<Key, Value> = Value extends object
    ? Value extends {
          tag: infer Tag extends string
          value: infer Value extends joinable
      }
        ? [Tag, Value]
        : Value extends {
                value: infer Value extends joinable
            }
          ? [never, Value]
          : never
    : [Key, Value]

type ExtractPair<Entity, Spec> = Spec extends [
    infer Key extends string,
    // biome-ignore lint/suspicious/noExplicitAny: required for generic transform inference
    (...key: any[]) => infer Value,
    ...unknown[],
]
    ? ExtractHelper<Uppercase<Key>, Value>
    : Spec extends keyof Entity & string
      ? [Uppercase<Spec>, Entity[Spec] & joinable]
      : never

type CompositeKeyStringBuilder<
    Entity,
    Spec,
    Separator extends string,
    KeepIntermediate extends boolean,
    Acc extends string = '',
    AllAcc extends string = never,
    Boundary extends boolean = false,
    Stops extends boolean = false,
> = Spec extends [infer Head, ...infer Tail]
    ? ExtractPair<Entity, Head> extends [
          infer Key extends joinable,
          infer Value extends joinable,
      ]
        ? CompositeKeyStringBuilder<
              Entity,
              Tail,
              Separator,
              KeepIntermediate,
              Acc extends ''
                  ? [Key] extends [never]
                      ? `${Value}`
                      : `${Key}${Separator}${Value}`
                  : [Key] extends [never]
                    ? `${Acc}${Separator}${Value}`
                    : `${Acc}${Separator}${Key}${Separator}${Value}`,
              KeepIntermediate extends true
                  ?
                        | AllAcc
                        | (Acc extends ''
                              ? never
                              : Boundary extends true
                                ? `${Acc}${Separator}`
                                : Acc)
                  : never,
              Boundary,
              Stops
          >
        : never
    :
          | AllAcc
          | (Boundary extends true
                ? Stops extends true
                    ? `${Acc}${Separator}`
                    : Acc
                : Acc)

/**
 * The pair of a component that reads a path: a name that the item holds as an attribute prints
 * whole, and a path prints its last name. A tag in an options object prints in place of the name.
 */
type ExtractPathPair<Entity, Spec> = Spec extends [
    infer Key extends string,
    // biome-ignore lint/suspicious/noExplicitAny: required for generic transform inference
    (...key: any[]) => infer Value,
    ...unknown[],
]
    ? ExtractHelper<NameOf<Entity, Key>, Value>
    : Spec extends [
            infer Key extends string,
            { readonly tag: infer Tag extends string },
        ]
      ? [Tag, ValueOfKey<Entity, Key> & joinable]
      : Spec extends string
        ? [NameOf<Entity, Spec>, ValueOfKey<Entity, Spec> & joinable]
        : never

/** Whether a spec holds a component that reads a path. */
type HoldsPath<Spec> = [
    Extract<
        extractHeadOrPass<
            Spec extends readonly unknown[] ? Spec[number] : never
        >,
        `${string}.${string}`
    >,
] extends [never]
    ? false
    : true

type CompositeKeyStringBuilderPath<
    Entity,
    Spec,
    Separator extends string,
    KeepIntermediate extends boolean,
    Acc extends string = '',
    AllAcc extends string = never,
    Boundary extends boolean = false,
    Stops extends boolean = false,
> = Spec extends [infer Head, ...infer Tail]
    ? ExtractPathPair<Entity, Head> extends [
          infer Key extends joinable,
          infer Value extends joinable,
      ]
        ? CompositeKeyStringBuilderPath<
              Entity,
              Tail,
              Separator,
              KeepIntermediate,
              Acc extends ''
                  ? [Key] extends [never]
                      ? `${Value}`
                      : `${Key}${Separator}${Value}`
                  : [Key] extends [never]
                    ? `${Acc}${Separator}${Value}`
                    : `${Acc}${Separator}${Key}${Separator}${Value}`,
              KeepIntermediate extends true
                  ?
                        | AllAcc
                        | (Acc extends ''
                              ? never
                              : Boundary extends true
                                ? `${Acc}${Separator}`
                                : Acc)
                  : never,
              Boundary,
              Stops
          >
        : never
    :
          | AllAcc
          | (Boundary extends true
                ? Stops extends true
                    ? `${Acc}${Separator}`
                    : Acc
                : Acc)

type DiscriminatedSchemaShape = {
    discriminator: PropertyKey
    spec: {
        [k in PropertyKey]: unknown
    }
}

type InputSpecShape =
    // biome-ignore lint/suspicious/noExplicitAny: key type is erased at runtime, any is needed for structural matching
    (
        | [PropertyKey, ((key: any) => unknown) | TagOptions, ...unknown[]]
        | PropertyKey
    )[]

export type TransformShape =
    | {
          tag?: string
          value: joinable
      }
    | joinable

type ComputeTableKeyType<
    Entity,
    Spec,
    Separator extends string,
    NullAs extends never | undefined = never,
> = Spec extends InputSpecShape
    ? CompositeKeyBuilderImpl<Entity, Spec, Separator, number, false>
    : Spec extends keyof Entity
      ? Replace<Entity[Spec], null, undefined>
      : Spec extends null
        ? NullAs
        : Spec extends DiscriminatedSchemaShape
          ? ComputeTableKeyType<
                Entity,
                ValueOf<
                    Spec['spec'],
                    ValueOfKey<Entity, Spec['discriminator']>
                >,
                Separator,
                NullAs
            >
          : never

type TableEntryImpl<
    Entity,
    Schema,
    Separator extends string = '#',
> = Entity extends unknown
    ? show<
          {
              readonly [Key in keyof Schema]: Schema[Key] extends DiscriminatedSchemaShape
                  ? ComputeTableKeyType<
                        Entity,
                        ValueOf<
                            Schema[Key]['spec'],
                            ValueOfKey<Entity, Schema[Key]['discriminator']>
                        >,
                        Separator
                    >
                  : Schema[Key] extends keyof Entity | InputSpecShape | null
                    ? ComputeTableKeyType<Entity, Schema[Key], Separator>
                    : ErrorMessage<'Invalid schema definition'>
          } & Entity
      >
    : never

/**
 * Represents a complete DynamoDB table entry, combining the original entity
 * with its computed internal and global keys.
 *
 * @template Entity The base entity type.
 * @template Schema The schema defining the table keys.
 * @template Separator The string used to join composite key components (default: '#').
 */
export type TableEntry<
    Entity extends Record<string, unknown>,
    Schema extends Record<string, FullKeySpec<Entity>>,
    Separator extends string = '#',
> = TableEntryImpl<Entity, Schema, Separator>

// Partial<T> for objects so narrowed transform defaults pass the InputSpec constraint.
type DefaultOf<T> = T extends Record<string, unknown> ? Partial<T> : T

/** The tag of a component, which prints in place of the name. */
type TagOptions = { readonly tag: string }

/**
 * The value at a path, through objects and unions of objects. An option that lacks a name adds
 * nothing. An optional name above the value adds `undefined`.
 */
type ValueAt<E, P extends string> = E extends unknown
    ? P extends keyof E
        ? E[P]
        : P extends `${infer Head}.${infer Tail}`
          ? Head extends keyof E
              ?
                    | ValueAt<NonNullable<E[Head]>, Tail>
                    | (null extends E[Head]
                          ? undefined
                          : undefined extends E[Head]
                            ? undefined
                            : never)
              : never
          : never
    : never

/** The value of a name that the item holds as an attribute, or at a path. */
type ValueOfKey<E, P> = [ValueOf<E, P>] extends [never]
    ? P extends string
        ? ValueAt<E, P>
        : never
    : ValueOf<E, P>

/** The last name of a path. */
type LastName<P extends string> = P extends `${string}.${infer Tail}`
    ? LastName<Tail>
    : P

/** The name that a component prints: the whole name of an attribute, or the last name of a path. */
type NameOf<E, P extends string> = P extends `${string}.${string}`
    ? [P] extends [keyof E]
        ? Uppercase<P>
        : Uppercase<LastName<P>>
    : Uppercase<P>

/** The object that holds one value at a path. */
type AtPath<
    P extends string,
    V,
    Optional extends boolean = false,
> = P extends `${infer Head}.${infer Tail}`
    ? Optional extends true
        ? { [K in Head]?: AtPath<Tail, V, true> }
        : { [K in Head]: AtPath<Tail, V> }
    : Optional extends true
      ? { [K in P]?: V }
      : { [K in P]: V }

/**
 * Any path: names joined by `.`.
 *
 * The constraint of a key spec is shallow on purpose. It admits a path and reads no path of the
 * entity, because a walk of the paths on every `tableEntry` costs far more than a spec that reads a
 * path costs: the walk measured +355% on the instantiation pin of the largest test, and a filter of
 * the names that can hold an object still measured +20% to +37%. {@link ValidatePaths} reads the
 * paths that a spec holds against the entity, and only a spec that holds one.
 */
type AnyPath = `${string}.${string}`

/**
 * A component that reads a path: the path, the path with a tag, or the path with a transform.
 *
 * The limit: the parameter of the transform has no contextual type. The constraint types it as
 * `any`, and the transforms of the other components give the parameter more than one type, so a
 * parameter without an annotation is an implicit `any` and the checker refuses it. Annotate the
 * parameter. {@link ValidatePaths} refuses an annotation that the value at the path does not fit.
 */
type PathComponent =
    | AnyPath
    | [AnyPath, TagOptions]
    // biome-ignore lint/suspicious/noExplicitAny: the value at a path is read by ValidatePaths, not by the constraint
    | [AnyPath, (key: any) => TransformShape, unknown?]

type InputSpec<E> =
    | {
          [key in keyof E]:
              | (undefined extends E[key]
                    ? [
                          key,
                          (key: Exclude<E[key], undefined>) => TransformShape,
                          DefaultOf<Exclude<E[key], undefined>>,
                      ]
                    : [key, (key: E[key]) => TransformShape])
              | (undefined extends E[key]
                    ? never
                    : null extends E[key]
                      ? never
                      : key)
      }[keyof E]
    | PathComponent

// --- 3-tuple default validation ---
// InputSpec uses DefaultOf so narrowed defaults pass the constraint.
// ValidateSchema mirrors the schema replacing each 3-tuple default slot with
// the transform's param type. The `Schema & ValidateSchema<Schema>` intersection
// then rejects defaults that don't match the transform param (e.g. `{}`).

// biome-ignore lint/suspicious/noExplicitAny: structural matching
type ValidateInputSpec<T> = {
    [I in keyof T]: T[I] extends readonly [
        unknown,
        (arg: infer P) => any,
        unknown,
    ]
        ? [T[I][0], T[I][1], P]
        : T[I]
}

type Tuple3 = { length: 3 }

// The arms of a match are validated one by one, and an arm that is a match validates its arms.
type ValidateMatch<M> = M extends {
    discriminator: unknown
    spec: infer Spec
}
    ? {
          discriminator: M['discriminator']
          spec: {
              [SV in keyof Spec]: Spec[SV] extends { discriminator: unknown }
                  ? ValidateMatch<Spec[SV]>
                  : ValidateInputSpec<Spec[SV]>
          }
      }
    : never

// True if any spec entry in V is a 3-tuple. Recurses into discriminated specs.
type NeedsValidation<V> = V extends readonly unknown[]
    ? Extract<V[number], Tuple3>
    : V extends { spec: infer S }
      ? NeedsValidation<S[keyof S]>
      : never

// Short-circuits to `unknown` when schema has no 3-tuples (zero overhead).
type ValidateSchema<Schema> = [NeedsValidation<Schema[keyof Schema]>] extends [
    never,
]
    ? unknown
    : {
          [K in keyof Schema]: Schema[K] extends {
              discriminator: unknown
              spec: unknown
          }
              ? ValidateMatch<Schema[K]>
              : ValidateInputSpec<Schema[K]>
      }

/**
 * What a spec holds that only the exact check reads: a path, in a component, a discriminator or an
 * attribute-name arm, and the marker `'cases'` for a match that groups literals. The marker holds no
 * `.`, so no path equals it. The walk stops at four matches, so a loose arm that names itself ends it.
 */
type NeedsExactCheck<S, Depth extends unknown[] = []> = S extends string
    ? S extends `${infer Head}.${string}`
        ? string extends Head // the pattern of the constraint, which names no path
            ? never
            : S
        : never
    : S extends readonly unknown[]
      ? NeedsExactCheck<S[number], Depth>
      : S extends { discriminator: infer D; spec: infer Arms }
        ? Depth['length'] extends 4
            ? never
            :
                  | NeedsExactCheck<D, Depth>
                  | NeedsExactCheck<Arms[keyof Arms], [...Depth, 0]>
        : S extends { discriminator: infer D; cases: infer C }
          ? Depth['length'] extends 4
              ? never
              :
                    | 'cases'
                    | NeedsExactCheck<D, Depth>
                    | NeedsExactCheck<ArmOfCases<C>, [...Depth, 0]>
          : never

type DefaultSlot<V> = [DefaultOf<Exclude<V, undefined>>]

/** What a name can be where the value is `V`: an optional value needs a transform with a default. */
type NameOfValue<N, V> = [V] extends [never]
    ? ErrorMessage<`'${N & string}' is no name or path of the entity`>
    : undefined extends V
      ? ErrorMessage<`'${N & string}' can be absent: give a transform with a default`>
      : null extends V
        ? ErrorMessage<`'${N & string}' can be null: give a transform with a default`>
        : N

/** One component of a spec, against the options of the entity that its arm reads. */
type ValidateComponent<E, C> = C extends string
    ? NameOfValue<C, ValueOfKey<E, C>>
    : C extends readonly [infer P extends string, infer Second, ...infer Rest]
      ? [ValueOfKey<E, P>] extends [never]
          ? ErrorMessage<`'${P}' is no name or path of the entity`>
          : Second extends (...args: never[]) => unknown
            ? [
                  P,
                  (key: Exclude<ValueOfKey<E, P>, undefined>) => TransformShape,
                  ...(Rest extends [unknown]
                      ? DefaultSlot<ValueOfKey<E, P>>
                      : []),
              ]
            : [P, Second]
      : C

/** A spec against the options of the entity that it reads. */
type ValidateSpec<E, S> = S extends string
    ? NameOfValue<S, ValueOfKey<E, S>>
    : S extends readonly unknown[]
      ? { [I in keyof S]: ValidateComponent<E, S[I]> }
      : S extends { discriminator: infer D extends string; spec: infer Arms }
        ? ValidateMatchPaths<E, D, Arms>
        : S extends { discriminator: infer D extends string; cases: infer C }
          ? ValidateCasesMatch<E, D, C>
          : S

/**
 * A match: the arms name the literals of the value at the discriminator and no other, and each arm
 * is a spec of the options that its literal selects.
 */
type ValidateMatchPaths<E, D extends string, Arms> = {
    discriminator: D
    spec: {
        [Literal in ValueOfKey<E, D> & PropertyKey]: Literal extends keyof Arms
            ? ValidateSpec<Extract<E, Tagged<D, Literal>>, Arms[Literal]>
            : ErrorMessage<`'${D}' has the literal '${Literal & string}', and this match has no arm for it`>
    }
} & {
    spec: {
        [Literal in Exclude<
            keyof Arms,
            ValueOfKey<E, D>
        >]: ErrorMessage<`'${D}' never holds '${Literal & string}'`>
    }
}

/** The arms of a list of cases. */
type ArmOfCases<C> = C extends readonly (readonly [unknown, infer Arm])[]
    ? Arm
    : never

/** The literals that a list of cases names. */
type LiteralOfCases<C> = C extends readonly (readonly [
    infer Literals extends readonly unknown[],
    unknown,
])[]
    ? Literals[number] & PropertyKey
    : never

/** The arm of the case that names a literal. */
type ArmOfLiteral<C, L> = C extends readonly unknown[]
    ? C[number] extends infer Case
        ? Case extends readonly [
              infer Literals extends readonly unknown[],
              infer Arm,
          ]
            ? L extends Literals[number]
                ? Arm
                : never
            : never
        : never
    : never

/**
 * A match that groups literals, as the match of one arm for each literal. Each case names its
 * literals once, so the two forms are one function from a literal to an arm.
 * The constraint is shallow, so an arm below the first match is inferred as a readonly tuple. The
 * list of components that the types of a key read is mutable, so the arm is made mutable here.
 */
type ExpandSpec<S> = S extends readonly unknown[]
    ? DeepMutable<S>
    : S extends { discriminator: infer D; cases: infer C }
      ? {
            discriminator: D
            spec: { [L in LiteralOfCases<C>]: ExpandSpec<ArmOfLiteral<C, L>> }
        }
      : S extends { discriminator: infer D; spec: infer Arms }
        ? { discriminator: D; spec: { [L in keyof Arms]: ExpandSpec<Arms[L]> } }
        : S

/** The schema with each grouped match written as a match of one arm for each literal. A schema with no group is unchanged. */
type ExpandCases<Schema> = string extends keyof Schema
    ? Schema
    : 'cases' extends NeedsExactCheck<Schema[keyof Schema]>
      ? {
            [K in keyof Schema]: ExpandSpec<Schema[K]> &
                (Schema[K] extends { readonly [tableKeyMark]: true }
                    ? { readonly [tableKeyMark]: true }
                    : unknown)
        }
      : Schema

/** Whether each option holds the name or the path. */
type HeldByEach<E, P extends string> = false extends (
    E extends unknown
        ? [ValueOfKey<E, P>] extends [never]
            ? false
            : true
        : never
)
    ? false
    : true

/**
 * The arm of a case, against the options that the literals of the case select. Where the case
 * selects more than one option, each option holds each name that the arm reads: an arm is one spec
 * for all of them.
 */
type ValidateGroupArm<E, Arm> = IsUnion<E> extends false
    ? ValidateSpec<E, Arm>
    : Arm extends string
      ? HeldByEach<E, Arm> extends true
          ? ValidateSpec<E, Arm>
          : ErrorMessage<`'${Arm}' is not held by each option of this case`>
      : Arm extends readonly unknown[]
        ? {
              [I in keyof Arm]: NameOfComponent<Arm[I]> extends infer N extends
                  string
                  ? [N] extends [never]
                      ? ValidateComponent<E, Arm[I]>
                      : HeldByEach<E, N> extends true
                        ? ValidateComponent<E, Arm[I]>
                        : ErrorMessage<`'${N}' is not held by each option of this case`>
                  : never
          }
        : ValidateSpec<E, Arm>

/** The name or the path that a component reads. */
type NameOfComponent<C> = C extends string
    ? C
    : C extends readonly [infer P extends string, ...unknown[]]
      ? P
      : never

/** One case of a match, against the options that the match reads: the literals it names, then its arm. */
type ValidateCases<E, D extends string, C, Seen = never> = C extends readonly [
    readonly [infer Literals extends readonly unknown[], infer Arm],
    ...infer Rest,
]
    ? [
          [
              {
                  [I in keyof Literals]: Literals[I] extends Seen
                      ? ErrorMessage<`'${D}' has the literal '${Literals[I] & (string | number)}' in two cases`>
                      : Literals[I] extends ValueOfKey<E, D>
                        ? Literals[I]
                        : ErrorMessage<`'${D}' never holds '${Literals[I] & (string | number)}'`>
              },
              ValidateGroupArm<
                  Extract<E, Tagged<D, Literals[number] & PropertyKey>>,
                  Arm
              >,
          ],
          ...ValidateCases<E, D, Rest, Seen | Literals[number]>,
      ]
    : C

/**
 * A match that groups literals: the literals of each case are literals of the value at the
 * discriminator, no case repeats a literal, the cases cover each literal, and each arm is a spec of
 * the options that its literals select.
 */
type ValidateCasesMatch<E, D extends string, C> = {
    discriminator: [
        Exclude<ValueOfKey<E, D> & PropertyKey, LiteralOfCases<C>>,
    ] extends [never]
        ? D
        : ErrorMessage<`'${D}' has the literal '${Exclude<ValueOfKey<E, D> & PropertyKey, LiteralOfCases<C>> & (string | number)}', and no case names it`>
    cases: ValidateCases<E, D, C>
}

/**
 * Reads each path that a schema holds against the entity. A wrong path, a path that no option
 * holds, a transform whose parameter does not fit the value, a path whose value can be absent, and a
 * match that lacks a literal are each refused on the element that is wrong. Short-circuits to
 * `unknown` when the schema holds no path, so a schema with no path pays nothing.
 */
type ValidatePaths<Schema, E> = string extends keyof Schema // the constraint, before a schema is inferred
    ? unknown
    : [NeedsExactCheck<Schema[keyof Schema]>] extends [never]
      ? unknown
      : { [K in keyof Schema]: ValidateSpec<E, Schema[K]> }

type extractHeadOrPass<T> = T extends readonly unknown[] ? T[0] : T

/**
 * A key spec that is not discriminated: a list of components, one attribute name, or nothing.
 *
 * Checked against the attributes the entity *states*. An entity carrying a string index signature
 * states none that can be found: `keyof ({ id: string } & { [key: string]: unknown })` is
 * `string | number`, because a literal unioned with `string` is `string` — so `'id'` is gone before
 * any filtering can see it, in `keyof` and in a homomorphic mapped type alike. Nothing can be
 * recovered from such an entity, which is why the way through is to name the closed part: see the
 * second type argument to {@link tableEntry}.
 */
type FullKeySpecSimple<Entity> =
    | NonEmptyArray<InputSpec<MergeIntersectionObject<Entity>>>
    | (keyof Entity & string)
    | null

type FullKeySpecSimpleShape = InputSpecShape | string | null

/**
 * The attributes that a match can read. Below a match, an attribute that the variant holds as one
 * literal has nothing to select, and an attribute that selected an arm above is used.
 */
type OpenKeys<E, Used extends PropertyKey> = {
    [K in Exclude<keyof E, Used>]: [Used] extends [never]
        ? K
        : IsUnion<E[K]> extends true
          ? K
          : never
}[Exclude<keyof E, Used>]

/**
 * A match: a discriminator and one arm for each literal of the attribute. An arm reads only the
 * variant that its literal selects, and is a key spec of that variant, so an arm can be a match
 * on an attribute that only that variant has. `Used` holds the discriminators above the match: an
 * attribute that already selected an arm selects nothing again.
 */
type DiscriminatedSchema<Entity, E, Used extends PropertyKey = never> = {
    [key in OpenKeys<E, Used>]: E[key] extends PropertyKey
        ? {
              discriminator: key
              cases?: never
              spec: {
                  [val in E[key]]: NestedKeySpec<
                      Extract<
                          Entity,
                          {
                              [k in key]: val
                          }
                      >,
                      Used | key
                  >
              }
          }
        : never
}[OpenKeys<E, Used>]

/**
 * A match on a path: the discriminator is a path below the top level. The constraint is shallow,
 * for the reason at {@link ObjectKeys}: each arm is a loose spec, and {@link ValidatePaths} reads
 * the literals of the value at the path, the arms against the options that each literal selects, and
 * the names that each arm reads.
 */
type PathMatch = {
    discriminator: AnyPath
    spec: { [literal: string]: LooseArm }
    cases?: never
}

/**
 * A match that groups literals: each case is a list of literals and the arm that they share. The
 * constraint is shallow for the same reason: {@link ValidatePaths} reads the cases.
 */
type CasesMatch = {
    discriminator: string
    spec?: ErrorMessage<'a match holds spec or cases, not both'>
    cases: [[string | number, ...(string | number)[]], LooseArm][]
}

type LooseArm =
    | (string | unknown[])[]
    | string
    | null
    | { discriminator: string; spec: { [literal: string]: unknown } }
    | { discriminator: string; cases: unknown[] }

type NestedKeySpec<Entity, Used extends PropertyKey> =
    | FullKeySpecSimple<Entity>
    | DiscriminatedSchema<Entity, MergeIntersectionObject<Entity>, Used>
    | PathMatch
    | CasesMatch

type FullKeySpec<Entity> =
    | FullKeySpecSimple<Entity>
    | DiscriminatedSchema<Entity, MergeIntersectionObject<Entity>>
    | PathMatch
    | CasesMatch

type FullKeySpecShape = FullKeySpecSimpleShape | DiscriminatedSchemaShape

export class RotoriseError extends Error {
    constructor(message: string) {
        super(message)
        this.name = 'RotoriseError'
    }
}

// Runtime implementation uses `as never` casts because the generic types are
// too complex for TS to verify at the value level. Type correctness is enforced
// by the type-level types (CompositeKeyStringBuilder, TableEntryImpl, etc.) and
// validated by the attest-based test suite.

/**
 * Answers every property with itself, so `infer` can be walked at the type level.
 *
 * Read through `typeof` and never at runtime — which is also why it answers `then` like anything
 * else. A callable target with a callable `then` is a *thenable*, so awaiting this hangs; carving
 * `then` out would fix that and cost an attribute name mid-walk, which is the worse trade for a
 * value nothing reads at runtime in the first place. Do not await it.
 */
const chainableNoOpProxy: unknown = new Proxy(() => chainableNoOpProxy, {
    get: () => chainableNoOpProxy,
})

/**
 * The segments of a key path: names joined by `.`, which read into objects only. A position in
 * brackets and an empty name are refused, because a key does not read into a list.
 */
const pathSegments = (path: string): string[] => {
    const segments = path.split('.')
    if (segments.some((segment) => segment === '' || /[[\]]/.test(segment))) {
        throw new RotoriseError(
            `'${path}' is no key path: a key path joins names with '.', and holds no empty name and no position`,
        )
    }
    return segments
}

/**
 * The value of an attribute name or of a path. A name that holds no `.` is an attribute of the
 * item, as it was before paths. An item that holds the whole name as an attribute gives that
 * attribute. Otherwise the path reads into objects, one own property for each segment, and a
 * missing segment gives `undefined`.
 */
const valueAt = (attributes: object, path: string): unknown => {
    const record = attributes as Record<string, unknown>
    if (!path.includes('.') || Object.hasOwn(record, path)) return record[path]
    let current: unknown = attributes
    for (const segment of pathSegments(path)) {
        if (
            typeof current !== 'object' ||
            current === null ||
            !Object.hasOwn(current, segment)
        ) {
            return undefined
        }
        current = (current as Record<string, unknown>)[segment]
    }
    return current
}

/** The name that a component prints: the whole name of an attribute, or the last name of a path. */
const printedName = (attributes: object, path: string): string =>
    (Object.hasOwn(attributes, path) ? path : (path.split('.').pop() ?? path))
        .toString()
        .toUpperCase()

/**
 * Two key paths are related when one is the other, or one is a prefix of the other at a name. A
 * write to a path changes each key that reads a related path.
 */
const related = (a: string, b: string): boolean =>
    a === b || a.startsWith(`${b}.`) || b.startsWith(`${a}.`)

/** Whether an item that holds these names holds the path: it holds the path, or a path above it. */
const holdsPath = (path: string, names: Iterable<string>): boolean => {
    for (const name of names) {
        if (path === name || path.startsWith(`${name}.`)) return true
    }
    return false
}

/** Whether a path is related to any of the names. */
const relatedToAny = (path: string, names: Iterable<string>): boolean => {
    for (const name of names) if (related(path, name)) return true
    return false
}

/** Refuses each name or path of a schema that is no key path, once, where the schema is read. */
const checkPaths = (schema: Record<string, unknown>): void => {
    const visit = (spec: unknown): void => {
        if (typeof spec === 'string') {
            pathSegments(spec)
        } else if (Array.isArray(spec)) {
            for (const entry of spec) {
                visit(Array.isArray(entry) ? entry[0] : entry)
            }
        } else if (isMatch(spec)) {
            pathSegments(String(spec.discriminator))
            for (const arm of Object.values(spec.spec)) visit(arm)
        }
    }
    for (const spec of Object.values(schema)) visit(spec)
}

/** A match that groups literals: a discriminator and a list of cases. */
const holdsCases = (
    value: unknown,
): value is { discriminator: PropertyKey; cases?: unknown; spec?: unknown } =>
    typeof value === 'object' &&
    value !== null &&
    !Array.isArray(value) &&
    'discriminator' in value &&
    'cases' in value

/**
 * Writes each grouped match of a key spec as a match of one arm for each literal, at each level.
 * A spec that holds no group stays the same object. The refusals name the discriminator and the
 * literal, which are part of the spec and not values of an item.
 */
const expandCases = (spec: unknown): unknown => {
    if (!holdsCases(spec)) {
        if (!isMatch(spec)) return spec
        const arms = Object.entries(spec.spec)
        const expanded = arms.map(
            ([literal, arm]) => [literal, expandCases(arm)] as const,
        )
        return expanded.every(([, arm], i) => arm === arms[i]?.[1])
            ? spec
            : { ...spec, spec: Object.fromEntries(expanded) }
    }
    const name = String(spec.discriminator)
    if ('spec' in spec) {
        throw new RotoriseError(
            `Match on ${name} holds both spec and cases: write one`,
        )
    }
    if (!Array.isArray(spec.cases)) {
        throw new RotoriseError(`Match on ${name}: cases is no list of cases`)
    }
    const arms = new Map<string, unknown>()
    for (const entry of spec.cases as unknown[]) {
        const [literals, arm] = Array.isArray(entry) ? entry : []
        if (!Array.isArray(literals) || literals.length === 0) {
            throw new RotoriseError(
                `Match on ${name}: a case names no literal, or is no pair of literals and an arm`,
            )
        }
        for (const literal of literals) {
            if (typeof literal !== 'string' && typeof literal !== 'number') {
                throw new RotoriseError(
                    `Match on ${name}: a literal is a string or a number`,
                )
            }
            if (arms.has(String(literal))) {
                throw new RotoriseError(
                    `Match on ${name}: the literal ${String(literal)} is in two cases`,
                )
            }
            arms.set(String(literal), expandCases(arm))
        }
    }
    // `fromEntries` defines each property, so a literal such as `__proto__` is a key like any other
    return { discriminator: spec.discriminator, spec: Object.fromEntries(arms) }
}

/** A key spec that matches: a discriminator and one arm for each literal. */
const isMatch = (
    value: unknown,
): value is { discriminator: PropertyKey; spec: Record<string, unknown> } =>
    typeof value === 'object' &&
    value !== null &&
    !Array.isArray(value) &&
    'discriminator' in value &&
    'spec' in value

/** The match that the run-time builders accept: the type level checks each arm against its variant. */
type ErasedMatch<Entity> = {
    discriminator: string
    spec: {
        [val in string]:
            | InputSpec<MergeIntersectionObject<Entity>>[]
            | string
            | ErasedMatch<Entity>
    }
}

const key =
    <const Entity>() =>
    <
        const Schema extends Record<
            string,
            | InputSpec<MergeIntersectionObject<Entity>>[]
            | keyof Entity
            | ErasedMatch<Entity>
        >,
        Separator extends string = '#',
    >(
        schema: Schema,
        separator: Separator = '#' as Separator,
    ) => {
        checkPaths(schema)
        return <
            const Key extends keyof Schema,
            const Config extends {
                depth?: number
                allowPartial?: boolean
                enforceBoundary?: boolean
            },
            const Attributes extends Partial<Entity>,
        >(
            key: Key,
            attributes: Attributes,
            config?: Config,
        ): string | undefined => {
            const case_ = schema[key]

            if (case_ === undefined) {
                throw new RotoriseError(
                    `Key ${key.toString()} not found in schema`,
                )
            }
            let structure: InputSpec<MergeIntersectionObject<Entity>>[]

            if (Array.isArray(case_)) {
                structure = case_
            } else if (typeof case_ === 'object') {
                // a match selects an arm by the value of its discriminator, and the arm can be a match.
                // The arm is read as an own property, so a literal that names a property of the
                // prototype names no arm. An error names the discriminator and holds no value.
                let arm: unknown = case_
                while (isMatch(arm)) {
                    const discriminatorName = arm.discriminator
                    const discriminator = valueAt(
                        attributes,
                        String(discriminatorName),
                    )
                    if (discriminator === undefined) {
                        throw new RotoriseError(
                            `Discriminator ${String(discriminatorName)} not found in the attributes`,
                        )
                    }
                    const literal = String(discriminator)
                    arm = Object.hasOwn(arm.spec, literal)
                        ? arm.spec[literal]
                        : undefined
                    if (arm === undefined) {
                        throw new RotoriseError(
                            `Discriminator value of ${String(discriminatorName)} not found in the spec`,
                        )
                    }
                }
                if (arm === null) {
                    return undefined
                }

                if (!Array.isArray(arm)) {
                    return valueAt(attributes, String(arm)) as never
                }

                structure = arm as typeof structure
            } else {
                const value = valueAt(attributes, String(case_))
                if (value == null) return undefined as never

                return value as never
            }

            const fullLength = structure.length

            if (config?.depth !== undefined) {
                structure = structure.slice(0, config.depth) as typeof structure
            }
            const composite: joinable[] = []
            let printed = 0

            // A segment that holds the separator reads back as two. The refusal names the component,
            // and never the value that it printed.
            const push = (component: string, segment: joinable) => {
                if (
                    segment !== undefined &&
                    segment !== null &&
                    String(segment).includes(separator)
                ) {
                    throw new RotoriseError(
                        `buildCompositeKey: the print of ${component} holds the separator, so the key cannot be read back. Remove the separator from the value, or choose another separator.`,
                    )
                }
                composite.push(segment)
            }

            for (const keySpec of structure) {
                const [key, transform, Default] = Array.isArray(keySpec)
                    ? keySpec
                    : [keySpec]
                const path = String(key)
                // a second slot that is an object gives the tag, and shapes no value
                const tag =
                    typeof transform === 'object' && transform !== null
                        ? (transform as { tag: string }).tag
                        : undefined
                const shape =
                    typeof transform === 'function' ? transform : undefined
                const name = printedName(attributes, path)

                const value = valueAt(attributes, path) ?? Default

                if (shape && value !== undefined) {
                    const transformed = shape(value as never)
                    if (
                        typeof transformed === 'object' &&
                        transformed !== null
                    ) {
                        if (transformed.tag !== undefined)
                            push(`the tag of ${path}`, transformed.tag)
                        push(path, transformed.value)
                    } else {
                        push(`the name ${path}`, name)
                        push(path, transformed)
                    }
                } else if (
                    value !== undefined &&
                    value !== null &&
                    value !== ''
                ) {
                    push(
                        tag === undefined
                            ? `the name ${path}`
                            : `the tag of ${path}`,
                        tag ?? name,
                    )
                    push(path, value as joinable)
                } else if (config?.allowPartial) {
                    break
                } else {
                    throw new RotoriseError(
                        `buildCompositeKey: Attribute ${path} not found`,
                    )
                }
                printed++
            }

            // A component prints one or two segments: a transform that gives a value with no tag prints
            // one. So the components are counted, and not the segments. If the print stops before the
            // last component (a partial key), append a trailing separator.
            if (config?.enforceBoundary && printed < fullLength) {
                composite.push('')
            }

            return composite.join(separator) as never
        }
    }

const toEntry =
    <const Entity extends Record<string, unknown>>() =>
    <
        const Schema extends Record<
            string,
            | InputSpec<MergeIntersectionObject<Entity>>[]
            | keyof Entity
            | ErasedMatch<Entity>
        >,
        Separator extends string = '#',
    >(
        schema: Schema,
        separator: Separator = '#' as Separator,
    ) =>
    <const ExactEntity extends Entity>(
        item: ExactEntity,
    ): ExactEntity extends infer E extends Entity
        ? TableEntryImpl<E, Schema, Separator>
        : never => {
        const entry = { ...item }
        const buildKey = key<Entity>()(schema, separator)

        for (const key_ in schema) {
            const val = buildKey(key_, item)
            if (val !== undefined) {
                entry[key_] = val satisfies string as never
            }
        }
        return entry as never
    }

/**
 * The key that the attributes build, or `undefined` where they build none: a component is absent,
 * a discriminator names no arm, or the arm is `null`. The stored key is then no key of these
 * attributes.
 */
const rebuilt = (
    build: (name: never, attributes: never) => unknown,
    name: string,
    attributes: object,
): unknown => {
    try {
        return build(name as never, attributes as never)
    } catch (thrown) {
        if (thrown instanceof RotoriseError) return undefined
        throw thrown
    }
}

/** The error of a stored key that the attributes do not build. It names the key, and not the value. */
const keyDisagrees = (name: string): CodecError =>
    new CodecError(
        'the stored key differs from the key that the attributes build',
    ).under(name)

const fromEntry =
    <const Entity extends Record<string, unknown>>() =>
    <
        const Schema extends Record<string, FullKeySpecShape>,
        Separator extends string = '#',
    >(
        schema: Schema,
        separator: Separator,
    ) => {
        const build = key<Entity>()(schema as never, separator) as (
            name: never,
            attributes: never,
        ) => unknown
        return <const Entry extends TableEntryImpl<Entity, Schema, Separator>>(
            entry: Entry,
        ): Result<DistributiveOmit<Entry, keyof Schema>> => {
            const item = { ...entry }

            for (const key_ in schema) {
                delete item[key_]
            }
            // a key that the entry lacks is a row outside that index. A key that it holds must be
            // the key that the attributes build
            for (const key_ in schema) {
                const stored = (entry as Record<string, unknown>)[key_]
                if (stored === undefined) continue
                const built = rebuilt(build, key_, item)
                if (built === undefined || String(built) !== String(stored)) {
                    return keyDisagrees(key_)
                }
            }
            return item as never
        }
    }

type ProcessSpecType<
    Entity,
    Spec,
    Config extends SpecConfigShape,
> = Spec extends string
    ? DistributivePick<Entity, Spec>
    : Spec extends InputSpecShape
      ? CompositeKeyParamsImpl<
            Entity,
            Spec,
            Config['allowPartial'] extends true
                ? 1
                : Extract<Config['depth'], number>
        >
      : Spec extends null | undefined
        ? unknown
        : Spec extends DiscriminatedSchemaShape
          ? OptimizedAttributes<Entity, Spec, Config>
          : ErrorMessage<'Invalid Spec: Expected string, InputSpecShape, null, undefined or a match'>

// Cache commonly used conditional types
type SpecConfig<Spec> = Spec extends string ? never : SpecConfigShape

type SpecConfigShape = {
    depth?: number
    allowPartial?: boolean
    enforceBoundary?: boolean
}

/** The object that holds the literal of a discriminator, which is an attribute or a path. */
type Tagged<K extends PropertyKey, V extends PropertyKey> = K extends string
    ? AtPath<K, V>
    : { [k in K]: V }

/** A variant of a match on a path: the options that hold the literal at the path. */
type ProcessPathVariant<
    Entity,
    K extends string,
    V extends PropertyKey,
    Spec extends DiscriminatedSchemaShape,
    Config extends SpecConfigShape,
    VariantSpec = Spec['spec'][V & keyof Spec['spec']],
> = [
    VariantSpec extends null | undefined
        ? unknown
        : ProcessSpecType<
              [Entity] extends [never] ? never : Extract<Entity, AtPath<K, V>>,
              VariantSpec,
              Config
          >,
] extends [infer Processed]
    ? [Processed] extends [never]
        ? AtPath<K, V>
        : Processed & AtPath<K, V>
    : never

// Pre-compute discriminated variant types
type ExtractVariant<Entity, K extends PropertyKey, V extends PropertyKey> = [
    Entity,
] extends [never]
    ? never
    : Extract<Entity, { [k in K]: V }>

type TagVariant<Entity, K extends PropertyKey, V extends PropertyKey> = [
    Entity,
] extends [never]
    ? { [k in K]: V }
    : Entity & { [k in K]: V }

// Flatten nested type computation
type ProcessVariant<
    Entity,
    K extends PropertyKey,
    V extends PropertyKey,
    Spec extends DiscriminatedSchemaShape,
    Config extends SpecConfigShape,
    VariantSpec = Spec['spec'][V & keyof Spec['spec']],
> = TagVariant<
    VariantSpec extends null | undefined
        ? unknown
        : ProcessSpecType<ExtractVariant<Entity, K, V>, VariantSpec, Config>,
    K,
    V
>

// Optimized attribute processing
type OptimizedAttributes<Entity, Spec, Config extends SpecConfigShape> = show<
    Spec extends DiscriminatedSchemaShape
        ? Spec['discriminator'] extends `${string}.${string}`
            ? {
                  [K in Spec['discriminator']]: {
                      [V in keyof Spec['spec']]: ProcessPathVariant<
                          Entity,
                          K,
                          V,
                          Spec,
                          Config
                      >
                  }[keyof Spec['spec']]
              }[Spec['discriminator']]
            : {
                  [K in Spec['discriminator']]: {
                      [V in keyof Spec['spec']]: ProcessVariant<
                          Entity,
                          K,
                          V,
                          Spec,
                          Config
                      >
                  }[keyof Spec['spec']]
              }[Spec['discriminator']]
        : ProcessSpecType<Entity, Spec, Config>
>

type ProcessKey<
    Entity,
    Spec,
    Separator extends string,
    NullAs extends never | undefined = never,
    Config extends SpecConfigShape = SpecConfigShape,
    Attributes = Pick<Entity, Spec & keyof Entity>,
> = [Entity] extends [never]
    ? never
    : Spec extends keyof Entity
      ? Replace<ValueOf<Attributes>, null, undefined>
      : Spec extends InputSpecShape
        ? CompositeKeyBuilderImpl<
              Entity,
              Spec,
              Separator,
              Exclude<Config['depth'], undefined>,
              Exclude<Config['allowPartial'], undefined>,
              [Config['enforceBoundary']] extends [true] ? true : false
          >
        : Spec extends null | undefined
          ? NullAs
          : Spec extends DiscriminatedSchemaShape
            ? ProcessKey<
                  Entity,
                  ValueOf<
                      Spec['spec'],
                      ValueOfKey<Entity, Spec['discriminator']>
                  >,
                  Separator,
                  NullAs,
                  Config,
                  Attributes
              >
            : ErrorMessage<'Invalid Spec'>

type OptimizedBuiltKey<
    Entity,
    Spec,
    Separator extends string,
    Config extends SpecConfigShape,
    Attributes,
> = Entity extends unknown
    ? show<
          Spec extends DiscriminatedSchemaShape
              ? ProcessKey<
                    Entity,
                    ValueOf<
                        Spec['spec'],
                        ValueOfKey<Entity, Spec['discriminator']>
                    >,
                    Separator,
                    undefined,
                    Config,
                    Attributes
                >
              : ProcessKey<
                    Entity,
                    Spec,
                    Separator,
                    undefined,
                    Config,
                    Attributes
                >
      >
    : never

type TableEntryDefinition<
    Entity,
    Schema,
    Separator extends string,
    CodecSpec = undefined,
    CodecRest = undefined,
> = {
    /**
     * Converts a raw entity into a complete table entry with all keys computed.
     * Use this when preparing items for insertion into DynamoDB.
     */
    toEntry: <const ExactEntity>(
        item: Exact<Entity, ExactEntity>,
    ) => TableEntryImpl<ExactEntity, Schema, Separator>

    /**
     * Extracts the raw entity from a table entry by removing all computed keys, or says which key
     * disagrees with the attributes.
     *
     * A key that the entry holds must be the key that the attributes build, with the same separator.
     * A key that the entry lacks is accepted: the row is not in that index. A key that the attributes
     * cannot build, because a component is absent, is a disagreement too. The error names the key
     * and never its value.
     * Use this when processing items retrieved from DynamoDB.
     */
    fromEntry: <const Entry extends TableEntryImpl<Entity, Schema, Separator>>(
        entry: Entry,
    ) => Result<DistributiveOmit<Entry, keyof Schema>>

    /**
     * Generates a specific key for the given entity attributes.
     * Supports partial keys and depth limiting for query operations.
     * Throws a `RotoriseError` that names the component where a segment of its print holds the
     * separator, because the key would read back as another list of segments.
     *
     * @param key The name of the key to generate (e.g., 'PK', 'GSIPK').
     * @param attributes the object containing the values needed to build the key.
     * @param config Optional configuration for partial keys or depth limiting.
     */
    key: <
        const Key extends keyof Schema,
        const Config extends SpecConfig<Spec>,
        const Attributes extends OptimizedAttributes<Entity, Spec, Config_>,
        Spec = Schema[Key],
        Config_ extends SpecConfigShape = [SpecConfigShape] extends [Config]
            ? {
                  depth?: undefined
                  allowPartial?: undefined
                  enforceBoundary?: boolean
              }
            : Config,
    >(
        key: Key,
        attributes: Attributes,
        config?: Config,
    ) => OptimizedBuiltKey<Attributes, Spec, Separator, Config_, Attributes>

    /**
     * The keys a change to these attributes invalidates, rebuilt.
     *
     * Changing an attribute without rewriting the keys built from it leaves an index pointing at a
     * value the item no longer has — the write succeeds and nothing fails until something reads it.
     * Only this layer can see it: the schema knows what a key is built from, the caller knows what
     * is changing, neither knows alone.
     *
     * A change carries every component of each key it touches. The keys share attributes, so the
     * change is a union of blocks: the attributes that the keys tie together, however far the tie
     * runs. The refusal names the whole block. A block that holds a component of a table key is
     * frozen, because rewriting it moves the item, and the refusal says so.
     *
     * Components a single-valued `literal` already decides join no key and are never written —
     * see {@link ConstantAttributes}. A discriminated key reads the components of the variant that
     * the change selects. A change that carries no discriminator reads every variant, so it has to
     * carry the discriminator.
     */
    keyUpdates: <const Changed extends Partial<Entity>>(
        changed: Changed &
            KeyUpdateRefusal<Schema, Changed, DecidedValues<CodecSpec>>,
    ) => AttributeMap

    /**
     * The named keys, encoded.
     *
     * `key` gives one key's value, because that is what a query condition holds. `keys` gives an
     * item, because that is what a request's `Key` holds — the plural is not only about how many.
     */
    keys(
        names: readonly (keyof Schema)[],
        attributes: Partial<Entity> & Record<string, unknown>,
    ): AttributeMap

    /**
     * A zero-runtime inference helper. Use this with `typeof` to get the
     * total type of a table entry.
     */
    infer: TableEntryImpl<Entity, Schema, Separator>

    /**
     * Creates a proxy to generate property paths as strings.
     * Useful for building UpdateExpressions or ProjectionExpressions.
     *
     * @example
     * table.path().data.nested.property.toString() // returns "data.nested.property"
     */
    path: () => PathOf<TableEntryImpl<Entity, Schema, Separator>>
} & ([CodecSpec] extends [undefined]
    ? Record<never, never>
    : EntryCodecMethods<Entity, Schema, CodecSpec, CodecRest, Separator>) &
    ([TableKeys<Schema>] extends [never]
        ? Record<never, never>
        : {
              /**
               * The table's keys, encoded — together they are the `Key` of a request.
               *
               * The no-names form of {@link TableEntryDefinition.keys}. Absent unless the schema
               * marks a key with {@link table}, because until it does the schema does not know
               * which keys address the table.
               */
              keys(
                  attributes: Partial<Entity> & Record<string, unknown>,
              ): AttributeMap
          })

/**
 * Present only when a codec spec was given.
 *
 * Reading and writing an item is `tableEntry` and a codec doing half a job each, so they are
 * declared together: the keys the schema computes are encoded as `S` without being declared, and
 * `fromItem` never reads them at all — which is why it needs no cast where `fromEntry` needed one.
 */
type EntryCodecMethods<
    Entity,
    Schema,
    CodecSpec,
    CodecRest,
    Separator extends string,
> = {
    /**
     * Entity to a complete item, or why it could not be written: keys computed by the schema,
     * attributes encoded by the codec.
     *
     * Typed attribute by attribute, which is what makes this the shape to diff in review: the
     * declared attributes come from the codec and the computed keys from the schema.
     */
    toItem: (
        item: Entity,
    ) => Result<EncodedItem<Entity, Schema, CodecSpec, CodecRest, Separator>>
    /** The same, throwing. */
    unsafeToItem: (
        item: Entity,
    ) => EncodedItem<Entity, Schema, CodecSpec, CodecRest, Separator>
    /** Item back to the entity. Key attributes are not decoded, because they are not the entity. */
    fromItem: (item: StoredItem) => Result<Entity>
    /** The same, throwing. */
    unsafeFromItem: (item: StoredItem) => Entity
    /**
     * The underlying attribute codecs — a discriminated one where the entity is a union, since that is
     * what had to be passed for one.
     */
    codec: IsVariantSpec<CodecSpec> extends true
        ? TaggedCodec<Entity, CodecSpec>
        : ItemCodec<Entity, CodecSpec>
}

/**
 * Nothing, or why this entry does not write the row it was pinned to.
 *
 * Intersected with the *options* argument rather than the schema, because that is where the codec
 * arrives and so where `CodecSpec` is inferred from — a check on the schema would run before the
 * codec was known. `unknown` is the identity of intersection, so an entry that agrees is left
 * exactly as it was.
 */
type WritesRow<
    Pinned,
    Entity,
    Schema,
    CodecSpec,
    CodecRest,
    Separator extends string,
> = [Pinned] extends [never]
    ? unknown
    : EncodedItem<
            Entity,
            Schema,
            CodecSpec,
            CodecRest,
            Separator
        > extends infer Row
      ? [Row] extends [Pinned]
          ? [Pinned] extends [Row]
              ? unknown
              : ErrorMessage<'[tableEntry] this entry does not write the row it is pinned to — compare the row against the shape and fix whichever is wrong'>
          : ErrorMessage<'[tableEntry] this entry does not write the row it is pinned to — compare the row against the shape and fix whichever is wrong'>
      : never

/**
 * A whole row: the attributes the codec writes, and the keys the schema computes.
 *
 * A composite key is a joined string, so every one of them is carried as `S` — the reason they are
 * derived here rather than declared beside the attributes they are built from.
 *
 * Present exactly where the entry says the key is: a discriminated key spec can name `null` for a
 * variant, which computes no key at all, and the implementation omits what came back `undefined`.
 * {@link TableEntryImpl} already works that out, so this reads the answer rather than repeating it.
 */
type EncodedItem<
    Entity,
    Schema,
    CodecSpec,
    CodecRest,
    Separator extends string,
> = [Schema] extends [never]
    ? // a schema that is not statically known cannot say which keys it computes, and an
      // intersection with `never` is `never` — which would describe a row nobody can read
      AttributeMap
    : TableEntryImpl<Entity, Schema, Separator> extends infer Entry
      ? show<
            EncodedAttributes<CodecSpec, CodecRest> & {
                [K in keyof Schema as NamedKey<
                    Schema,
                    Entry,
                    K,
                    false
                >]: Attribute<'S'>
            } & {
                [K in keyof Schema as NamedKey<
                    Schema,
                    Entry,
                    K,
                    true
                >]?: Attribute<'S'>
            }
        >
      : never

/**
 * A key the schema names, kept when whether it may be absent matches `Absent`.
 *
 * The `string extends K` guard is what keeps the result an {@link AttributeMap}. A schema whose keys
 * are not statically known maps to an index signature, and the optional half of one is
 * `Attribute<'S'> | undefined` — which no request will accept. Only named keys are ever computed,
 * so only named keys are described.
 */
type NamedKey<
    Schema,
    Entry,
    K extends keyof Schema,
    Absent extends boolean,
> = string extends K
    ? never
    : (undefined extends Entry[K & keyof Entry] ? true : false) extends Absent
      ? K
      : never

/**
 * What the codec half writes.
 *
 * A tagged spec is a map of variants rather than of attributes, so the shape is the union of what
 * each variant writes — which is what a row of that entity may hold.
 */
type EncodedAttributes<CodecSpec, CodecRest> =
    IsVariantSpec<CodecSpec> extends true
        ? { [V in keyof CodecSpec]: Encoded<CodecSpec[V]> }[keyof CodecSpec]
        : CodecRest extends AnyCodec
          ? Encoded<CodecSpec> & { readonly [name: string]: AttributeValue }
          : Encoded<CodecSpec>

/**
 * Marks a table key.
 *
 * Type-level only. Which keys address the table is held in a {@link tableKeys} set at runtime, so
 * nothing is added to the spec at all — where a marked property had to be defined non-enumerably
 * and then *hoped* not to surface in the walks that read the spec to build a key from it. The
 * declaration stays because the type needs a brand: {@link TableKeys} and {@link MovesTheItem} read
 * it to decide what {@link TableEntryDefinition.keyUpdates} may rebuild.
 */
declare const tableKeyMark: unique symbol

/**
 * The specs {@link table} marked.
 *
 * Keyed on the spec object rather than written into it, which is what leaves the spec exactly the
 * data the caller wrote. Weak, so a schema declared and dropped is collectable.
 */
const tableKeys = new WeakSet<object>()

/** A key spec marked as belonging to the table itself rather than to an index. */
export type TableKeySpec<Spec> = Spec & { readonly [tableKeyMark]: true }

/**
 * Marks a key as the table's own, rather than an index's.
 *
 * DynamoDB will not update a key attribute — it is the item's address. An index key is an ordinary
 * attribute, so {@link TableEntryDefinition.keyUpdates} rebuilds those and must never emit these.
 * The schema is the only place that difference is visible: `['petId']` looks the same either way.
 *
 * @example
 * ```ts
 * tableEntry<Pet>()({
 *     PK: table(['petId']),
 *     SK: table(['petId']),
 *     GSI1PK: ['ownerId'],
 * })
 * ```
 */
export const table = <const Spec extends object>(
    spec: Spec,
): TableKeySpec<Mutable<Spec>> => {
    // a copy, so that marking what is returned does not also mark a spec the caller holds and may
    // reuse for an index key
    const marked: object = Array.isArray(spec) ? [...spec] : { ...spec }
    tableKeys.add(marked)
    return marked as TableKeySpec<Mutable<Spec>>
}

/** `const` infers a readonly tuple; the schema wants the mutable one. */
type Mutable<T> = {
    -readonly [K in keyof T]: K extends 'cases' ? DeepMutable<T[K]> : T[K]
}

/** The cases of a grouped match hold lists in lists, and `const` infers each as a readonly tuple. */
type DeepMutable<T> = T extends (...args: never[]) => unknown
    ? T
    : T extends object
      ? { -readonly [K in keyof T]: DeepMutable<T[K]> }
      : T

/** The keys marked with {@link table}. */
export type TableKeys<Schema> = {
    [K in keyof Schema]: Schema[K] extends { readonly [tableKeyMark]: true }
        ? K
        : never
}[keyof Schema]

/**
 * The components that a write to one of the names changes: a component is related to a name when
 * the two are one path, or one is a prefix of the other at a name.
 */
type TouchedBy<Components, Names> = Components extends string
    ? Names extends string
        ? Components extends Names | `${Names}.${string}`
            ? Components
            : Names extends `${Components}.${string}`
              ? Components
              : never
        : never
    : never

/** The components that an item with these names holds: a name, or a name above the path. */
type HeldBy<Components, Names> = Components extends string
    ? Names extends string
        ? Components extends Names | `${Names}.${string}`
            ? Components
            : never
        : never
    : never

/**
 * The table keys a change would move the item out of.
 *
 * Not something to rebuild — something to refuse. Rewriting the address is a delete and a create,
 * and an `UpdateItem` carrying a key attribute is rejected by the service anyway; catching it here
 * says why, which the service's error does not.
 */
export type MovesTheItem<Schema, Changed> = {
    [K in TableKeys<Schema>]: [
        TouchedBy<KeyComponents<Schema[K]>, keyof Changed>,
    ] extends [never]
        ? never
        : K
}[TableKeys<Schema>]

/**
 * The attributes a key is built from, at the type level.
 *
 * The mirror of {@link keyComponents}, and the reason this is worth doing twice: a runtime check
 * tells you what is missing after you have written the call and run it. This one asks for it while
 * you are writing the call, which is the only place it stops being your problem.
 */
export type KeyComponents<Spec, Given = unknown> = Spec extends string
    ? Spec
    : Spec extends null | undefined
      ? never
      : Spec extends readonly unknown[]
        ? {
              [I in keyof Spec]: Spec[I] extends string
                  ? Spec[I]
                  : Spec[I] extends readonly [
                          infer Named extends string,
                          ...unknown[],
                      ]
                    ? Named
                    : never
          }[number]
        : Spec extends {
                discriminator: infer Discriminator extends string
                spec: infer Variants
            }
          ? // the discriminator chooses which list applies, so it is a component of the key
            Discriminator | VariantComponents<Variants, Discriminator, Given>
          : never

/**
 * The components of the variants that the given discriminant selects, or of every variant.
 *
 * The type half of the narrowing in {@link componentsOf}. A discriminant that is not a literal
 * of a variant selects nothing, so every variant is read.
 */
type VariantComponents<
    Variants,
    Discriminator extends string,
    Given,
> = Discriminator extends keyof Given
    ? Given[Discriminator] extends infer Chosen extends keyof Variants
        ? KeyComponents<Variants[Chosen], Given>
        : KeyComponents<Variants[keyof Variants], Given>
    : KeyComponents<Variants[keyof Variants], Given>

/**
 * The components a change touches but does not carry, across every key it touches.
 *
 * `never` when the change is self-sufficient, which is what makes the refusal disappear from the
 * signature. A table key is read as any other key: a change that touches one is refused by
 * {@link MovesTheItem} whatever this holds.
 *
 * `KeyComponents` is bound once for each key. Asking twice for the same answer, once to decide
 * whether a key is touched and once to say what the key lacks, is what made this the most
 * expensive type in the signature.
 */
export type MissingComponents<
    Schema,
    Changed,
    Known = never,
    Given = Changed,
> = {
    [K in keyof Schema]: KeyComponents<Schema[K], Given> extends infer Of
        ? [TouchedBy<Of, Exclude<keyof Changed, Known>>] extends [never]
            ? never
            : Exclude<Of, HeldBy<Of, keyof Changed | Known>>
        : never
}[keyof Schema]

/**
 * The attributes that the keys tie to a set of attributes, the set included.
 *
 * Two attributes are tied when a key holds both, so the tie is transitive and the result is the
 * block of the set. A component that the codec decides joins no key: it is read from the codec and
 * never written. The recursion ends because each step only grows a finite union. The refusal reads
 * it on the failing path only, so a complete change never pays for it.
 */
type BlockOf<Schema, Given, Known, Block> = {
    [K in keyof Schema]: KeyComponents<Schema[K], Given> extends infer Of
        ? [TouchedBy<Of, Block>] extends [never]
            ? never
            : Exclude<Of, Known>
        : never
}[keyof Schema] extends infer Joined
    ? [Joined] extends [Block]
        ? Block
        : BlockOf<Schema, Given, Known, Block | Joined>
    : never

/**
 * The table keys that hold a component of the block, which freezes the block.
 *
 * `never` when the block moves no item.
 */
type FrozenBy<Schema, Given, Block> = {
    [K in TableKeys<Schema>]: [
        TouchedBy<KeyComponents<Schema[K], Given>, Block>,
    ] extends [never]
        ? never
        : K
}[TableKeys<Schema>]

/**
 * Nothing, or why a change is not a union of blocks.
 *
 * The refusal lands on the parameter. A change that lacks a component of a touched key, or that
 * touches a table key, gets a message that names the whole block. Where the block holds a component
 * of a table key, the message names the table key and says that the block is frozen. The block is
 * bound once with `infer`: naming it twice evaluates it twice.
 */
type KeyUpdateRefusal<Schema, Changed, Decided> = KeyRefusal<
    Schema,
    Changed,
    keyof Decided,
    Changed & Decided
>

type KeyRefusal<Schema, Changed, Known, Given> = [
    | MissingComponents<Schema, Changed, Known, Given>
    | MovesTheItem<Schema, Omit<Changed, Known & string>>,
] extends [never]
    ? unknown
    : BlockOf<
            Schema,
            Given,
            Known,
            Exclude<keyof Changed, Known>
        > extends infer Block
      ? [FrozenBy<Schema, Given, Block>] extends [never]
          ? ErrorMessage<`[keyUpdates] this change touches a key and lacks '${Exclude<Block, HeldBy<Block, keyof Changed | Known>> & string}', which the keys tie to what it writes. Write the whole block`>
          : ErrorMessage<`[keyUpdates] '${FrozenBy<Schema, Given, Block> & string}' is a table key that holds '${TouchedBy<KeyComponents<Schema[FrozenBy<Schema, Given, Block> & keyof Schema], Given>, Block> & string}', and the block of this change is frozen: a rewrite would move the item. DynamoDB cannot update a key attribute`>
      : never

/**
 * The value of each attribute that the codec decides, as the codec states it.
 *
 * The type twin of `decided` at run time, and read from the codec as {@link ConstantAttributes}
 * reads the names. The entity can type a decided attribute wider than the codec does, so the
 * entity is not read. A variant spec reads the value that every variant agrees on.
 */
type DecidedValues<Spec> = {
    [K in ConstantAttributes<Spec>]: IsVariantSpec<Spec> extends true
        ? AcrossVariants<Spec, K>
        : ConstantValue<Spec[K & keyof Spec]>
}

/**
 * The attributes whose codec admits exactly one value.
 *
 * Gated on the codec, not the entity type: `TAG: 'PET'` is a type and types are gone by the time a
 * key is built, whereas a {@link ConstantCodec} is still there at runtime. So the signature stops
 * asking for exactly what the implementation can supply. `never` without a codec.
 */
export type ConstantAttributes<Spec> = [Spec] extends [undefined]
    ? never
    : IsVariantSpec<Spec> extends true
      ? AgreedAttributes<Spec>
      : {
            // the constant's *value* and not merely its presence, so that a codec admitting two of
            // them decides neither — which is what `constantOf` answers at runtime. Asking only whether
            // a `constant` was declared had the type promise a component nobody needed to pass,
            // while the implementation went on to demand it
            [K in keyof Spec]: ConstantValue<Spec[K]> extends infer Only extends
                string
                ? IsUnion<Only> extends true
                    ? never
                    : K
                : never
        }[keyof Spec]

/**
 * A spec of variants, as opposed to a spec of attributes.
 *
 * Structural, because the codec is inferred through its `spec` and is itself gone
 * by the time this is asked. Every attribute codec reads and writes; a variant's map of them
 * does not.
 */
type IsVariantSpec<Spec> = [Spec[keyof Spec]] extends [
    // a member declares one attribute either way, and the two say so differently: a codec by its
    // pair, a field by its definition. A variant is a spec rather than a declaration and has neither
    | { readonly unsafeEncode: unknown; readonly unsafeDecode: unknown }
    | { readonly def: Field },
]
    ? false
    : true

/**
 * A constant, or the fact that there is none.
 *
 * `unknown` rather than `never` because these are unioned across variants: `never` vanishes and
 * would let a variant that decides nothing be outvoted, where `unknown` absorbs. One silent variant
 * is enough.
 */
type ConstantOrAny<C> = ConstantValue<C> extends infer V extends string
    ? V
    : unknown

/**
 * What one declared attribute decides, at the type level, with the two presence marks of a field read.
 *
 * The type half of {@link constantOf}, and it must give the same answer: a name that may be absent
 * decides nothing, a stand-in is written always so what it stands in for still decides, and the
 * constants spec is what holds the two together.
 */
type ConstantValue<C> = C extends {
    readonly def: { readonly mark: 'optional' }
}
    ? unknown
    : C extends {
            readonly def: { readonly mark: 'fallback' }
            readonly codec: infer Marked
        }
      ? ConstantValue<Marked>
      : C extends { readonly constant: infer V extends string }
        ? V
        : unknown

/** What the variants say about one attribute, collapsed. */
type AcrossVariants<Variants, K> = {
    [V in keyof Variants]: K extends keyof Variants[V]
        ? ConstantOrAny<Variants[V][K]>
        : unknown
}[keyof Variants]

/**
 * The attributes every variant decides, and decides the same way.
 *
 * The rule a union needs, and the same rule one map needs — "exactly one value" — asked of the
 * variants together rather than of a single codec. `TAG: string('PAYMENT')` in every variant is
 * decided; a discriminator is not, because deciding it is the variants' whole disagreement.
 *
 * `keyof Variants[keyof Variants]` is the attributes *shared* by every variant, because `keyof` of
 * a union is the intersection of its keys — an attribute one variant lacks is not one they agree on.
 */
type AgreedAttributes<Variants> = {
    [K in keyof Variants[keyof Variants]]: AcrossVariants<
        Variants,
        K
    > extends infer Said
        ? // bound once: what the variants say is asked for twice — is it a string at all, and is it
          // one string — and answering it walks every variant
          [Said] extends [string]
            ? IsUnion<Said> extends true
                ? never
                : K
            : never
        : never
}[keyof Variants[keyof Variants]]

/**
 * A built key, as the attribute that carries it.
 *
 * A composite key is a joined string, so `S` is the only member it can take — which is why it is
 * derived here rather than declared in the codec spec beside the attributes it is built from.
 */
const asKey = (value: unknown): Attribute<'S'> => carrying('S', String(value))

const isTableKey = (spec: unknown): spec is TableKeySpec<unknown> =>
    typeof spec === 'object' && spec !== null && tableKeys.has(spec)

/**
 * The named members are present and callable.
 *
 * One object check instead of three, but the point is the `keys` parameter: it is
 * `(keyof T & string)[]`, so the names a probe looks for are checked against the type that declares
 * them. These predicates decide which branch a codec argument takes. A probe that looks for
 * `'field'` as a bare string keeps compiling after a rename of `field` on {@link ItemCodec}, and
 * then matches nothing, which sends every codec down the "this is a spec" branch.
 */
const callable = <T>(
    value: unknown,
    keys: readonly (keyof T & string)[],
): value is T =>
    typeof value === 'object' &&
    value !== null &&
    keys.every(
        (key) => typeof (value as Record<string, unknown>)[key] === 'function',
    )

/** An erased item codec — what {@link isItemCodec} narrows to, and all this layer uses. */
type ItemCodecRuntime = ItemCodec<
    Record<string, unknown>,
    Record<string, ObjectSlot>
>

/**
 * An item codec, as opposed to any other codec that could be passed here.
 *
 * `rest` is what separates one: a union of maps has `unsafeEncode`, `unsafeDecode` and even `unsafeEncodePartial`,
 * but no single set of attributes, and so no open entry for an attribute that the set lacks. Checking the member this actually uses is what
 * keeps a wrong argument a reported error rather than a `TypeError` two lines later.
 */
const isItemCodec = (value: unknown): value is ItemCodecRuntime =>
    callable<ItemCodecRuntime>(value, ['unsafeEncodePartial']) &&
    'rest' in (value as object)

/** Anything that reads and writes an attribute — the shape a spec is *not*. */
const isCodecLike = (value: unknown): value is AnyCodec =>
    callable<AnyCodec>(value, ['unsafeEncode', 'unsafeDecode'])

/** An erased tagged codec: the spec of each variant, keyed by the tag of the variant. */
type TaggedRuntime = TaggedCodec<
    Record<string, unknown>,
    Record<string, Record<string, ObjectSlot>>
>

/** A codec that decides its variant from the item, rather than having one set of attributes. */
const isTagged = (value: unknown): value is TaggedRuntime =>
    callable<TaggedRuntime>(value, ['unsafeEncode', 'unsafeDecode']) &&
    typeof (value as TaggedRuntime).discriminator === 'string'

/**
 * The value every variant writes at this attribute, when they all write the same one.
 *
 * The rule for a union is the rule for one codec, asked of each variant: one value, or none. A
 * variant that decides nothing, one that lacks the attribute, and two that disagree all answer the
 * same way — nothing is decided, so the caller is asked, as it was before any of this.
 */
const agreedConstant = (codec: TaggedRuntime, component: string): unknown => {
    let agreed: unknown
    for (const name of Object.keys(codec.spec)) {
        const found = codec.spec[name]?.[component]
        const value = found && constantOf(found)
        if (value === undefined) return undefined
        if (agreed === undefined) agreed = value
        else if (agreed !== value) return undefined
    }
    return agreed
}

/**
 * The attributes a key is built from, at runtime.
 *
 * The mirror of {@link KeyComponents}, and the two must agree: the type decides what `keyUpdates`
 * *asks* for, this decides what it actually *needs*. Exported so that agreement can be asserted
 * rather than assumed — a spec shape one walk learns and the other does not is a key that is either
 * demanded without being used, or used without being demanded.
 *
 * `given` narrows a discriminated spec: when the discriminant's value is known, only that variant's
 * components are needed, because the others describe an item this is not.
 */
export const keyComponents = (
    spec: unknown,
    given: Record<string, unknown> = {},
): ReadonlySet<string> => componentsOf(spec, given).components

/**
 * The one walk, which also says whether a discriminant chose anything along the way.
 *
 * Walks the shapes a schema entry can take: a bare attribute name, a list of them, a list carrying
 * transform tuples, and a discriminated spec, whose discriminator is itself a component because it
 * chooses which list applies.
 *
 * `narrows` is what lets a key be walked once at declaration instead of once per update: without a
 * discriminator the answer cannot depend on the item, so there is nothing to recompute. With one, it
 * can, and it is.
 */
const componentsOf = (
    spec: unknown,
    given: Record<string, unknown>,
): { components: ReadonlySet<string>; narrows: boolean } => {
    const components = new Set<string>()
    let narrows = false

    const walk = (value: unknown): void => {
        if (value === null || value === undefined) return
        if (typeof value === 'string') {
            components.add(value)
            return
        }
        if (Array.isArray(value)) {
            for (const entry of value) {
                // a transform tuple names its attribute first: ['a', (x) => x, default]
                walk(Array.isArray(entry) ? entry[0] : entry)
            }
            return
        }
        if (typeof value !== 'object') return

        const { discriminator, spec: variants } = value as {
            discriminator?: unknown
            spec?: Record<string, unknown>
        }
        if (typeof discriminator !== 'string') return
        components.add(discriminator)
        narrows = true

        // the discriminant chooses which list applies, so when its value is known only that
        // variant's components are needed — the others describe an item this is not
        const chosen = valueAt(given, discriminator)
        if (chosen === undefined) {
            for (const variant of Object.values(variants ?? {})) walk(variant)
            return
        }
        // an own property, so a value that names a property of the prototype names no variant
        if (variants !== undefined && Object.hasOwn(variants, String(chosen)))
            walk(variants[String(chosen)])
    }

    walk(spec)
    return { components, narrows }
}

/**
 * Entry point for defining a DynamoDB table schema with Rotorise.
 *
 * @template Entity The base entity type that this table represents.
 * @returns A builder function that accepts the schema and an optional separator.
 *
 * Note: the double-call `<Entity>()(schema)` is required for partial type parameter inference.
 *
 * @example
 * const userTable = tableEntry<User>()({
 *   PK: ["orgId", "id"],
 *   SK: "role"
 * })
 */
export const tableEntry =
    <
        const Entity extends Record<string, unknown>,
        /**
         * The row this entry must write, to be told when it stops writing it.
         *
         * The second slot for the same reason it is `item`'s: the pin is the thing most often
         * reached for, and one place for it across the API is worth more than saving a `never` at
         * the rare call that needs {@link KeyedBy} too.
         *
         * Pinned against the whole *row* — the attributes the codec writes and the keys the schema
         * computes — because that is what a table holds and what a team diffs in review. A shape
         * that is only the attributes would not notice a key changing name.
         */
        Pinned = never,
        /**
         * The attributes a key may be built from, when that is not the whole entity.
         *
         * Only useful for an entity carrying a string index signature, and necessary there. Such an
         * entity states no findable attribute names — `keyof` collapses them into `string` — so a
         * schema checked against it is checked against nothing: `['nonsense']` is as valid as
         * `['id']`, and a key built from an attribute that does not exist is a wrong index entry
         * rather than an error. Naming the closed part restores the check, and costs nothing,
         * because it is the type the entity was built from:
         *
         * ```ts
         * type MetaKeys = { TAG: 'META'; id: string }
         * type Meta = MetaKeys & { [key: string]: unknown }
         *
         * tableEntry<Meta, MetaKeys>()({ PK: ['id'], SK: ['TAG'] }, { codec })
         * ```
         */
        const KeyedBy extends Record<string, unknown> = Entity,
    >() =>
    <
        const Schema extends Record<string, FullKeySpec<KeyedBy>>,
        const CodecSpec extends
            | ItemSpec<Entity>
            | Record<string, unknown>
            | undefined = undefined,
        const CodecRest = undefined,
        Separator extends string = '#',
    >(
        schema: Schema &
            ValidateSchema<Schema> &
            ValidatePaths<Schema, KeyedBy>,
        ...[options]: [Separator] extends ['']
            ? [ErrorMessage<'Separator must not be an empty string'>]
            : [
                  /**
                   * The separator on its own, or everything else this entry needs.
                   *
                   * A bare string is the separator, which is the only shape this argument has ever
                   * had and still means what it meant.
                   *
                   * The codec is a *named* slot rather than a second positional, and it has to be:
                   * a parameter typed `Separator | CodecSpec` gives the two one inference site, and
                   * `tableEntry(schema, '-')` then infers a `CodecSpec` from the separator — so the
                   * type hands back `toItem` and `codec` that the implementation never built, and
                   * calling one is a `TypeError` that compiled. Two properties are two sites.
                   */
                  options?:
                      | Separator
                      | ({
                            /**
                             * The attributes, as a spec or as a codec already built from one.
                             *
                             * A spec is the short form and takes the defaults. Pass a built codec
                             * where a default is not what you want — `item` is where a rest policy
                             * is chosen, and anything else it grows is reached the same way,
                             * without this signature needing to learn about it.
                             *
                             * Where the entity is a union this must be a codec `union` built with
                             * a discriminator, for the reason `item` refuses one: a single map of
                             * attributes names one variant's, and the type would let the others
                             * through it. That is worse here than it is there, because a
                             * discriminant is usually a key component, so the mis-description lands
                             * in an index rather than in a field.
                             */
                            readonly codec?: IsUnion<Entity> extends true
                                ? TaggedCodec<Entity, CodecSpec>
                                :
                                      | CodecSpec
                                      | (ItemCodec<
                                            Entity,
                                            CodecSpec,
                                            CodecRest
                                        > &
                                            Closed)
                            readonly separator?: Separator
                        } & WritesRow<
                            Pinned,
                            Entity,
                            ExpandCases<Schema>,
                            CodecSpec,
                            CodecRest,
                            Separator
                        >),
              ]
    ): TableEntryDefinition<
        Entity,
        ExpandCases<Schema>,
        Separator,
        CodecSpec,
        CodecRest
    > => {
        // a bare string is the separator; anything else carries it alongside the codec
        const { codec: codecSpec, separator } =
            typeof options === 'string'
                ? { codec: undefined, separator: options }
                : ((options ?? {}) as {
                      codec?: unknown
                      separator?: Separator
                  })

        const sep = separator ?? ('#' as Separator)
        if (sep === '' || typeof sep !== 'string') {
            throw new RotoriseError('Separator must not be an empty string')
        }

        const expanded = Object.fromEntries(
            Object.entries(schema).map(([name, spec]) => {
                const grouped = expandCases(spec)
                // the mark of `table(...)` is on the object that the caller built, so a copy carries it
                if (grouped !== spec && isTableKey(spec)) {
                    tableKeys.add(grouped as object)
                }
                return [name, grouped]
            }),
        )

        const buildEntry = toEntry()(expanded as never, sep) as (
            item: never,
        ) => Record<string, unknown>
        const buildKey = key()(expanded as never, sep) as (
            name: never,
            attributes: never,
        ) => unknown

        /**
         * A built codec carries its own options; a spec takes the defaults.
         *
         * Asked once each, in the order the three answers actually rank: a codec this layer can
         * use, a codec it cannot, or a spec. The probes used to run twice — once to reject and once
         * to choose — which is two chances for the two lists to disagree about what a codec is.
         */
        const attributes: ItemCodecRuntime | TaggedRuntime | undefined =
            (() => {
                if (codecSpec === undefined) return undefined
                if (isItemCodec(codecSpec) || isTagged(codecSpec)) {
                    return codecSpec
                }
                if (isCodecLike(codecSpec)) {
                    throw new RotoriseError(
                        'the codec passed here is neither an item codec nor a tagged one. A union of maps only knows which attributes an item has once it knows which variant the item is, so it has to be able to say — which is what `tagged` adds and a bare union codec does not.',
                    )
                }
                return itemOf(
                    object(codecSpec as never),
                ) as unknown as ItemCodecRuntime
            })()

        /**
         * The value a component is already decided to have, or `undefined` if it is not.
         *
         * How a constant is read depends on the *codec*, which does not change between components,
         * so the choice is made once rather than at each one.
         */
        const constantAt =
            attributes === undefined
                ? undefined
                : isTagged(attributes)
                  ? (component: string) => agreedConstant(attributes, component)
                  : (component: string) => {
                        // the spec and not `field`, which hands back the codec a member marks:
                        // the two marks are the answer here, so the declaration is what is read
                        const found = attributes.spec[component]
                        return found && constantOf(found)
                    }

        /**
         * What the codec decides, so nobody has to pass it.
         *
         * Read from the components the schema actually builds keys from — a constant on an attribute
         * no key mentions is not a fact about any key.
         */
        const decided: Record<string, unknown> = {}

        /**
         * One key, with everything knowable about it before any item exists.
         *
         * The schema is walked once here rather than once per key per update, and `decided` is
         * filled from the same walk. A key whose components a discriminant chooses is the one that
         * must still be walked per update, and says so — see {@link componentsOf}.
         */
        const keys = Object.keys(expanded).map((name) => {
            const spec = expanded[name]
            const { components, narrows } = componentsOf(spec, {})
            if (constantAt) {
                for (const component of components) {
                    const value = constantAt(component)
                    if (value !== undefined) decided[component] = value
                }
            }
            return {
                name,
                spec,
                ofTable: isTableKey(spec),
                fixed: narrows ? undefined : components,
            }
        })

        const quoted = (names: Iterable<string>) =>
            [...names].map((x) => `'${x}'`).join(', ')

        /** The components of a key that this change carries, which is what rewrites it. */
        const touchedIn = (
            components: Iterable<string>,
            changed: Record<string, unknown>,
        ) =>
            [...components].filter(
                (component) =>
                    relatedToAny(component, Object.keys(changed)) &&
                    !(component in decided),
            )

        /**
         * The attributes that the keys tie to the change, the change included.
         *
         * The runtime half of {@link BlockOf}. Two attributes are tied when a key holds both, so the
         * walk repeats until no key adds an attribute. A component that the codec decides joins no key.
         */
        const blockOf = (
            changed: Record<string, unknown>,
            given: Record<string, unknown>,
        ): Set<string> => {
            const block = new Set(
                Object.keys(changed).filter((name) => !(name in decided)),
            )
            for (let grew = true; grew; ) {
                grew = false
                for (const key of keys) {
                    const components =
                        key.fixed ?? componentsOf(key.spec, given).components
                    if (![...components].some((c) => relatedToAny(c, block)))
                        continue
                    for (const component of components) {
                        if (component in decided || block.has(component))
                            continue
                        block.add(component)
                        grew = true
                    }
                }
            }
            return block
        }

        /** The error for a change that is not a union of blocks, once a touched key shows it. */
        const refusal = (
            changed: Record<string, unknown>,
            given: Record<string, unknown>,
            touched: { name: string; components: ReadonlySet<string> },
        ): RotoriseError => {
            const block = blockOf(changed, given)
            for (const key of keys) {
                if (!key.ofTable) continue
                const components =
                    key.fixed ?? componentsOf(key.spec, given).components
                const held = [...components].filter((c) =>
                    relatedToAny(c, block),
                )
                if (held.length === 0) continue
                return new RotoriseError(
                    `'${key.name}' is the table's own key and is built from ${quoted(components)}. This change writes ${quoted(Object.keys(changed))}. The keys tie it to ${quoted(block)}, and the block holds ${quoted(held)} of '${key.name}'. A table key freezes its block, because rewriting the block would move the item and DynamoDB cannot update a key attribute. Write the new item and delete the old one.`,
                )
            }
            const givenNames = Object.keys(given)
            const missing = [...touched.components].filter(
                (c) => !holdsPath(c, givenNames),
            )
            const needed = [...block].filter((c) => !holdsPath(c, givenNames))
            return new RotoriseError(
                `'${touched.name}' is built from ${quoted(touched.components)} and this change touches ${quoted(touchedIn(touched.components, changed))}, so it has to be rebuilt, but ${quoted(missing)} ${missing.length === 1 ? 'is' : 'are'} not given. The keys tie ${quoted(block)} together. Write ${quoted(needed)} in the change.`,
            )
        }

        /**
         * Whether a written value is the constant the codec decides.
         *
         * A primitive constant is compared as it is. A constant that an adapter puts back, such as a
         * decimal, is an object, so two of them are the same when they print the same: the key is built
         * from that print.
         */
        const sameConstant = (written: unknown, constant: unknown): boolean =>
            Object.is(written, constant) ||
            (typeof written === 'object' &&
                written !== null &&
                typeof constant === 'object' &&
                constant !== null &&
                String(written) === String(constant))

        const keyUpdates = (changed: Record<string, unknown>): AttributeMap => {
            const out: Record<string, AttributeValue> = {}
            const given = { ...decided, ...changed }
            const changedNames = Object.keys(changed)
            const givenNames = Object.keys(given)

            // the codec admits one value for a decided attribute, so any other value is not a write
            // of that attribute. The message names the constant and never the written value
            for (const name of Object.keys(decided)) {
                if (
                    name in changed &&
                    !sameConstant(changed[name], decided[name])
                ) {
                    throw new RotoriseError(
                        `'${name}' is decided by the codec as '${String(decided[name])}', and this change writes another value. The codec admits one value, so write '${String(decided[name])}' or leave '${name}' out.`,
                    )
                }
            }

            for (const key of keys) {
                const components =
                    key.fixed ?? componentsOf(key.spec, given).components

                /**
                 * Two questions of the components, as two flags.
                 *
                 * Most keys a change reaches nothing of, so the answer is usually "no" and the
                 * lists that name the components are only ever read to build a message. They are
                 * gathered on the paths that throw instead of on every key of every update.
                 *
                 * `else if` is exact rather than a shortcut: `given` contains `changed`, so a
                 * component the change carries is never one that is missing.
                 */
                let touches = false
                let lacks = false
                for (const component of components) {
                    if (
                        relatedToAny(component, changedNames) &&
                        !(component in decided)
                    )
                        touches = true
                    else if (!holdsPath(component, givenNames)) lacks = true
                }
                if (!touches) continue

                if (key.ofTable || lacks) {
                    throw refusal(changed, given, {
                        name: key.name,
                        components,
                    })
                }

                out[key.name] = asKey(
                    buildKey(key.name as never, given as never),
                )
            }

            return out
        }

        const tableKeyNames = keys
            .filter((key) => key.ofTable)
            .map((key) => key.name)

        /** The names the schema computes, as opposed to the attributes the codec declares. */
        const keyNames = keys.map((key) => key.name)

        const definition = {
            keyUpdates,
            keys: (
                first: readonly string[] | Record<string, unknown>,
                second?: Record<string, unknown>,
            ): AttributeMap => {
                const [names, attributes] = Array.isArray(first)
                    ? [first, second as Record<string, unknown>]
                    : [tableKeyNames, first as Record<string, unknown>]

                if (names.length === 0) {
                    throw new RotoriseError(
                        'no key is marked with `table(...)`, so the schema does not say which keys address the table',
                    )
                }

                const out: Record<string, AttributeValue> = {}
                for (const name of names) {
                    out[name] = asKey(
                        buildKey(name as never, attributes as never),
                    )
                }
                return out
            },
            toEntry: buildEntry as never,
            fromEntry: fromEntry()(expanded as never, sep) as never,
            key: buildKey as never,
            infer: chainableNoOpProxy as never,
            path: () => pathBuilder() as never,
        }

        if (attributes === undefined) return definition as never

        const toItem = (item: Record<string, unknown>): Result<AttributeMap> =>
            andThen(
                attributes.encode(item as never),
                (written: AttributeMap) => {
                    const entry = buildEntry(item as never)
                    // the keys are gathered into their own small object and merged in one spread.
                    // Adding them to a copy of the attributes one at a time is the same result and
                    // a hidden-class transition per key, on an object that already has thirty
                    const built: Record<string, AttributeValue> = {}
                    for (const name of keyNames) {
                        const value = entry[name]
                        if (value !== undefined) built[name] = asKey(value)
                    }
                    return { ...written, ...built }
                },
            )
        /**
         * The keys are removed before decoding, not merely left undeclared.
         *
         * A codec that drops what it does not declare would ignore them anyway. One that keeps
         * them — a rest policy of `'lossy'`, say, which is how an open entity is declared —
         * would sweep the computed keys into the entity, and `PK` is not an attribute of
         * anything. Removing them here is what makes `fromItem` mean the same thing under every
         * policy.
         */
        const fromItem = (item: AttributeMap) => {
            // copied and stripped rather than rebuilt by omission: the copy is one intrinsic and
            // the keys are few, where testing every attribute for membership is a lookup per
            // attribute of every item read. `keyNames` is walked instead of `Object.keys(schema)`,
            // which allocated the same list on every read
            const withoutKeys: Record<string, AttributeValue> = { ...item }
            for (const name of keyNames) delete withoutKeys[name]
            const entity = attributes.decode(withoutKeys) as Result<unknown>
            if (failed(entity)) return entity
            // a key that the item lacks is a row outside that index. A key that it holds must be the
            // key that `toItem` writes from the entity
            for (const name of keyNames) {
                const stored = item[name]
                if (stored === undefined) continue
                const built = rebuilt(
                    buildKey as (name: never, attributes: never) => unknown,
                    name,
                    entity as object,
                )
                if (built === undefined || stored.S !== String(built)) {
                    return keyDisagrees(name)
                }
            }
            return entity
        }

        return {
            ...definition,
            codec: attributes as never,
            toItem,
            fromItem,
            unsafeToItem: (item: Record<string, unknown>) =>
                orThrow(toItem(item)),
            unsafeFromItem: (item: AttributeMap) => orThrow(fromItem(item)),
        } as never
    }

export * from './codec/attribute'

/**
 * The codec surface, **enumerated rather than starred**, because not everything `codec.ts` exports
 * is API.
 *
 * `carries`, `member`, `occV`, `occA`, `specOf`, `tagsOf`, `agrees` and `constantOf`
 * read a **term**, and `accepts` and `readsBack` ask the **pair**. Both kinds exist
 * so this library's own resolver, declaration guard and emitter can ask what a codec is; a caller
 * has the codec's behaviour instead, which is the thing they are derived from. Every one of them
 * reached the published surface once, because this was `export * from './codec/codec'`, and `46cb950`
 * shipped the reader then called `admits` that way without the export being a decision anyone took.
 * `Rotorise.spec.ts` holds the list, and holds it at the live names for the reason written there.
 *
 * Six of the listed values reach here *through* `codec.ts` from `result.ts`, which is where the
 * pair's error and its combinators live — `CodecError`, `andThen`, `every`, `everyEntry`,
 * `failed`, `orThrow`. They were starred before and are listed now like the rest.
 *
 * So the values are listed and the types are starred. **Adding a codec means adding a line here**,
 * which is the cost of the list and the point of it: an export becomes a decision rather than a
 * consequence of where a function happens to live. `Rotorise.spec.ts` pins both halves, the names
 * that are API and the names that are not, so a name cannot rejoin the surface by accident either
 * — and the counts live there, in the lists the test actually walks, rather than here where
 * nothing would keep them true.
 */
export type {
    AllObjects,
    AnyCodec,
    AnyObjectCodec,
    AnySpread,
    AttributeCodec,
    AttributeOf,
    Attributes,
    BinaryCodec,
    BooleanCodec,
    ConstantCodec,
    Decoded,
    DerivedUnion,
    DerivedVariants,
    DiscriminatedCodec,
    Dissected,
    DissectedCodec,
    Dissection,
    Encoded,
    EncodedPatch,
    EncodedVariants,
    IsUnion,
    ItemCodec,
    ItemSpec,
    ListOf,
    ListWrites,
    LiteralAttribute,
    LiteralBase,
    LiteralValue,
    LocatedCodec,
    Marks,
    Nestable,
    ObjectCodec,
    ObjectEntry,
    ObjectOf,
    ObjectSlot,
    OptionalCodec,
    PathOf,
    PathTerminal,
    Precondition,
    Reader,
    Refined,
    Refinement,
    Result,
    Rng,
    Segment,
    SetBase,
    SetCapable,
    SetOf,
    SetSlot,
    Shape,
    SpecsOf,
    SpreadCodec,
    SpreadOnce,
    StringCodec,
    Tagged,
    TaggedCodec,
    TaggedSpec,
    UndefinableCodec,
    UnionCodec,
    Untagged,
    UntaggedSpec,
    VariantOf,
    WithLegacyReadOptions,
    Writes,
    WrittenBy,
} from './codec/codec'
export {
    andThen,
    array,
    at,
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    every,
    everyEntry,
    exclude,
    extract,
    failed,
    held,
    item,
    list,
    mdunion,
    meet,
    narrow,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    orThrow,
    path,
    pathBuilder,
    preconditions,
    ref,
    refine,
    scope,
    spread,
    string,
    undefinable,
    union,
    withLegacyRead,
} from './codec/codec'
export { pin } from './codec/pin'
export type { Field, Term } from './codec/term'
// `shapeOf` classifies a *value* and reaches no term, so it moved to `value.ts` with the twelve
// others `denote.ts` needs. The name on the surface is unchanged; only the module that declares
// it moved, which is why this is a second `export` rather than an entry in the list above.
export { shapeOf } from './codec/value'
