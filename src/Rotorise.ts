import type {
    Attribute,
    AttributeMap,
    AttributeValue,
    StoredItem,
} from './codec/attribute'
import { carrying } from './codec/attribute'
import type {
    AnyCodec,
    AnyDeclaration,
    Encoded,
    EncodedBy,
    IsUnion,
    ItemCodec,
    ItemSpec,
    PathOf,
    Result,
    TaggedCodec,
} from './codec/codec'
import {
    andThen,
    constantOf,
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

export type CompositeKeyParamsImpl<
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
> = Entity extends unknown
    ? CompositeKeyStringBuilder<
          Entity,
          [Deep] extends [never]
              ? Spec
              : number extends Deep
                ? Spec
                : SliceFromStart<Spec, Deep>,
          Separator,
          boolean extends isPartial ? false : isPartial
      >
    : never

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
                  ? AllAcc | (Acc extends '' ? never : Acc)
                  : never
          >
        : never
    : AllAcc | Acc

type DiscriminatedSchemaShape = {
    discriminator: PropertyKey
    spec: {
        [k in PropertyKey]: unknown
    }
}

type InputSpecShape =
    // biome-ignore lint/suspicious/noExplicitAny: key type is erased at runtime, any is needed for structural matching
    ([PropertyKey, (key: any) => unknown, ...unknown[]] | PropertyKey)[]

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
                            ValueOf<Entity, Schema[Key]['discriminator']>
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

type InputSpec<E> = {
    [key in keyof E]:
        | (undefined extends E[key]
              ? [
                    key,
                    (key: Exclude<E[key], undefined>) => TransformShape,
                    DefaultOf<Exclude<E[key], undefined>>,
                ]
              : [key, (key: E[key]) => TransformShape])
        | (undefined extends E[key] ? never : null extends E[key] ? never : key)
}[keyof E]

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
              spec: infer Spec
          }
              ? {
                    discriminator: Schema[K]['discriminator']
                    spec: {
                        [SV in keyof Spec]: ValidateInputSpec<Spec[SV]>
                    }
                }
              : ValidateInputSpec<Schema[K]>
      }

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

type DiscriminatedSchema<Entity, E> = {
    [key in keyof E]: E[key] extends PropertyKey
        ? {
              discriminator: key
              spec: {
                  [val in E[key]]: FullKeySpecSimple<
                      Extract<
                          Entity,
                          {
                              [k in key]: val
                          }
                      >
                  >
              }
          }
        : never
}[keyof E]

type FullKeySpec<Entity> =
    | FullKeySpecSimple<Entity>
    | DiscriminatedSchema<Entity, MergeIntersectionObject<Entity>>

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

const key =
    <const Entity>() =>
    <
        const Schema extends Record<
            string,
            | InputSpec<MergeIntersectionObject<Entity>>[]
            | keyof Entity
            | {
                  discriminator: keyof Entity
                  spec: {
                      [val in string]:
                          | InputSpec<MergeIntersectionObject<Entity>>[]
                          | keyof Entity
                  }
              }
        >,
        Separator extends string = '#',
    >(
        schema: Schema,
        separator: Separator = '#' as Separator,
    ) =>
    <
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
            throw new RotoriseError(`Key ${key.toString()} not found in schema`)
        }
        let structure: InputSpec<MergeIntersectionObject<Entity>>[]

        if (Array.isArray(case_)) {
            structure = case_
        } else if (typeof case_ === 'object') {
            const discriminator =
                attributes[case_.discriminator as keyof Attributes]
            if (discriminator === undefined) {
                throw new RotoriseError(
                    `Discriminator ${case_.discriminator.toString()} not found in ${JSON.stringify(attributes)}`,
                )
            }
            const val = case_.spec[discriminator as keyof typeof case_.spec]
            if (val === undefined) {
                throw new RotoriseError(
                    `Discriminator value ${discriminator?.toString()} not found in ${JSON.stringify(attributes)}`,
                )
            }
            if (val === null) {
                return undefined
            }

            if (!Array.isArray(val)) {
                return attributes[val as keyof Attributes] as never
            }

            structure = val
        } else {
            const value = attributes[case_ as keyof Attributes]
            if (value == null) return undefined as never

            return value as never
        }

        const fullLength = structure.length

        if (config?.depth !== undefined) {
            structure = structure.slice(0, config.depth) as typeof structure
        }
        const composite: joinable[] = []

        for (const keySpec of structure) {
            const [key, transform, Default] = Array.isArray(keySpec)
                ? keySpec
                : [keySpec]

            const value = attributes[key as keyof Attributes] ?? Default

            if (transform && value !== undefined) {
                const transformed = transform(value as never)
                if (typeof transformed === 'object' && transformed !== null) {
                    if (transformed.tag !== undefined)
                        composite.push(transformed.tag)
                    composite.push(transformed.value)
                } else {
                    composite.push(key.toString().toUpperCase())
                    composite.push(transformed)
                }
            } else if (value !== undefined && value !== null && value !== '') {
                composite.push(key.toString().toUpperCase())
                composite.push(value as joinable)
            } else if (config?.allowPartial) {
                break
            } else {
                throw new RotoriseError(
                    `buildCompositeKey: Attribute ${key.toString()} not found in ${JSON.stringify(attributes)}`,
                )
            }
        }

        // Each spec element produces 2 segments (KEY, value). If fewer segments
        // were emitted than expected (partial key), append a trailing separator.
        if (config?.enforceBoundary && fullLength * 2 > composite.length) {
            composite.push('')
        }

        return composite.join(separator) as never
    }

const toEntry =
    <const Entity extends Record<string, unknown>>() =>
    <
        const Schema extends Record<
            string,
            | InputSpec<MergeIntersectionObject<Entity>>[]
            | keyof Entity
            | {
                  discriminator: keyof Entity
                  spec: {
                      [val in string]:
                          | InputSpec<MergeIntersectionObject<Entity>>[]
                          | keyof Entity
                  }
              }
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

const fromEntry =
    <const Entity extends Record<string, unknown>>() =>
    <
        const Schema extends Record<string, FullKeySpecShape>,
        Separator extends string = '#',
    >(
        schema: Schema,
    ) =>
    <const Entry extends TableEntryImpl<Entity, Schema, Separator>>(
        entry: Entry,
    ): DistributiveOmit<Entry, keyof Schema> => {
        const item = { ...entry }

        for (const key_ in schema) {
            delete item[key_]
        }
        return item as never
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
        : ErrorMessage<'Invalid Spec: Expected string, InputSpecShape, null or undefined'>

// Cache commonly used conditional types
type SpecConfig<Spec> = Spec extends string ? never : SpecConfigShape

type SpecConfigShape = {
    depth?: number
    allowPartial?: boolean
    enforceBoundary?: boolean
}

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
        ? {
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
              Exclude<Config['allowPartial'], undefined>
          >
        : Spec extends null | undefined
          ? NullAs
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
                        ValueOf<Entity, Spec['discriminator']>
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
    CodecRest = 'drop',
> = {
    /**
     * Converts a raw entity into a complete table entry with all keys computed.
     * Use this when preparing items for insertion into DynamoDB.
     */
    toEntry: <const ExactEntity>(
        item: Exact<Entity, ExactEntity>,
    ) => TableEntryImpl<ExactEntity, Schema, Separator>

    /**
     * Extracts the raw entity from a table entry by removing all computed keys.
     * Use this when processing items retrieved from DynamoDB.
     */
    fromEntry: <const Entry extends TableEntryImpl<Entity, Schema, Separator>>(
        entry: Entry,
    ) => DistributiveOmit<Entry, keyof Schema>

    /**
     * Generates a specific key for the given entity attributes.
     * Supports partial keys and depth limiting for query operations.
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
     * A key that cannot be rebuilt is reported rather than left stale; pass its other components as
     * `context`. Components a single-valued `literal` already decides are neither asked for nor
     * accepted — see {@link ConstantAttributes}.
     */
    keyUpdates: <const Changed extends Partial<Entity>>(
        changed: Changed &
            ([MovesTheItem<Schema, Changed>] extends [never]
                ? unknown
                : ErrorMessage<'[keyUpdates] this changes an attribute the table key is built from, which would move the item; DynamoDB cannot update a key attribute'>),
        ...context: ContextFor<
            Entity,
            Schema,
            Changed,
            ConstantAttributes<CodecSpec>
        >
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
        : EncodedBy<CodecSpec, CodecRest>

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
type Mutable<T> = { -readonly [K in keyof T]: T[K] }

/** The keys marked with {@link table}. */
export type TableKeys<Schema> = {
    [K in keyof Schema]: Schema[K] extends { readonly [tableKeyMark]: true }
        ? K
        : never
}[keyof Schema]

/**
 * The table keys a change would move the item out of.
 *
 * Not something to rebuild — something to refuse. Rewriting the address is a delete and a create,
 * and an `UpdateItem` carrying a key attribute is rejected by the service anyway; catching it here
 * says why, which the service's error does not.
 */
export type MovesTheItem<Schema, Changed> = {
    [K in TableKeys<Schema>]: [
        Extract<KeyComponents<Schema[K]>, keyof Changed>,
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
export type KeyComponents<Spec> = Spec extends string
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
            Discriminator | KeyComponents<Variants[keyof Variants]>
          : never

/**
 * The components a change touches but does not carry, across every key it invalidates.
 *
 * `never` when the change is self-sufficient, which is what makes `context` disappear from the
 * signature rather than sit there as an optional nobody reads.
 *
 * `TableKeys` and `KeyComponents` are each bound once. Both are a walk over the schema, and asking
 * either twice for the same answer — once to decide whether a key is touched, once to say what
 * rebuilding it is missing — is what made this the most expensive type in the signature.
 */
export type MissingComponents<
    Schema,
    Changed,
    Known = never,
> = TableKeys<Schema> extends infer Table
    ? {
          [K in keyof Schema]: K extends Table
              ? never
              : KeyComponents<Schema[K]> extends infer Of
                ? [Extract<Of, keyof Changed>] extends [never]
                    ? never
                    : Exclude<Of, keyof Changed | Known>
                : never
      }[keyof Schema]
    : never

/**
 * The trailing `context` parameter, or nothing at all.
 *
 * `infer` binds the missing set once — naming it twice evaluates it twice. The brackets stop the
 * conditional distributing: the components are a union, and "is each one alone `never`" is not the
 * question.
 */
type ContextFor<Entity, Schema, Changed, Known> = [
    MissingComponents<Schema, Changed, Known>,
] extends [infer Missing]
    ? [Missing] extends [never]
        ? []
        : [context: Pick<Entity, Missing & keyof Entity>]
    : never

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
 * What one declared attribute decides, at the type level, with §4's two marks read.
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
 * them. These predicates decide which branch a codec argument takes, and they used to look for
 * `'field'` and `'variant'` as bare strings — renaming either on {@link ItemCodec} or
 * {@link TaggedCodec} would have left the probe compiling and quietly matching nothing, sending
 * every codec down the "this is a spec" branch.
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
    Record<string, AnyDeclaration>
>

/**
 * An item codec, as opposed to any other codec that could be passed here.
 *
 * `field` is what separates one: a union of maps has `unsafeEncode`, `unsafeDecode` and even `unsafeEncodePartial`,
 * but no single set of attributes to name one of. Checking the member this actually uses is what
 * keeps a wrong argument a reported error rather than a `TypeError` two lines later.
 */
const isItemCodec = (value: unknown): value is ItemCodecRuntime =>
    callable<ItemCodecRuntime>(value, ['unsafeEncodePartial', 'field'])

/** Anything that reads and writes an attribute — the shape a spec is *not*. */
const isCodecLike = (value: unknown): value is AnyCodec =>
    callable<AnyCodec>(value, ['unsafeEncode', 'unsafeDecode'])

/**
 * An erased tagged codec.
 *
 * `variant` is replaced rather than intersected: an intersection of two function types is an
 * overload set, and the first signature wins, so `& { variant }` would have kept the `unknown`
 * return {@link TaggedCodec} declares and hidden the item codec underneath it.
 */
type TaggedRuntime = Omit<
    TaggedCodec<Record<string, unknown>, Record<string, unknown>>,
    'variant'
> & {
    readonly variant: (name: string) => ItemCodecRuntime | undefined
}

/** A codec that decides its variant from the item, rather than having one set of attributes. */
const isTagged = (value: unknown): value is TaggedRuntime =>
    callable<TaggedRuntime>(value, ['variant']) &&
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
        const found = codec.variant(name)?.spec[component]
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
        const chosen = given[discriminator]
        if (chosen === undefined) {
            for (const variant of Object.values(variants ?? {})) walk(variant)
            return
        }
        walk(variants?.[String(chosen)])
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
        const CodecRest = 'drop',
        Separator extends string = '#',
    >(
        schema: Schema & ValidateSchema<Schema>,
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
                                      | ItemCodec<Entity, CodecSpec, CodecRest>
                            readonly separator?: Separator
                        } & WritesRow<
                            Pinned,
                            Entity,
                            Schema,
                            CodecSpec,
                            CodecRest,
                            Separator
                        >),
              ]
    ): TableEntryDefinition<
        Entity,
        Schema,
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

        const buildEntry = toEntry()(schema as never, sep) as (
            item: never,
        ) => Record<string, unknown>
        const buildKey = key()(schema as never, sep) as (
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
                return object(codecSpec as never)
                    .item as unknown as ItemCodecRuntime
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
        const keys = Object.keys(schema).map((name) => {
            const spec = (schema as Record<string, unknown>)[name]
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
        ) => [...components].filter((component) => component in changed)

        const keyUpdates = (
            changed: Record<string, unknown>,
            context: Record<string, unknown> = {},
        ): AttributeMap => {
            const out: Record<string, AttributeValue> = {}
            const given = { ...decided, ...context, ...changed }

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
                    if (component in changed) touches = true
                    else if (!(component in given)) lacks = true
                }
                if (!touches) continue

                if (key.ofTable) {
                    throw new RotoriseError(
                        `'${key.name}' is the table's own key and is built from ${quoted(touchedIn(components, changed))}, which this change rewrites. That would move the item, and DynamoDB cannot update a key attribute — write the new item and delete the old one.`,
                    )
                }

                if (lacks) {
                    const missing = [...components].filter(
                        (component) => !(component in given),
                    )
                    throw new RotoriseError(
                        `'${key.name}' is built from ${quoted(components)} and this change touches ${quoted(touchedIn(components, changed))}, so it has to be rebuilt — but ${quoted(missing)} ${missing.length === 1 ? 'is' : 'are'} not given. Pass ${missing.length === 1 ? 'it' : 'them'} as \`context\`, or the index will disagree with the item.`,
                    )
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
            fromEntry: fromEntry()(schema as never) as never,
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
            return attributes.decode(withoutKeys) as Result<unknown>
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
 * `carries`, `member`, `occV`, `occA`, `specOf`, `tagsOf`, `separable`, `identifies`, `setBaseOf`
 * and `constantOf` read a **term**, and `accepts` and `readsBack` ask the **pair**. Both kinds exist
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
    AnyDeclaration,
    AnyObjectCodec,
    AnySpread,
    AttributeCodec,
    AttributeOf,
    Attributes,
    BinaryCodec,
    BooleanCodec,
    ConstantCodec,
    DecimalCodec,
    Decoded,
    DerivedItem,
    DerivedUnion,
    DerivedVariants,
    DiscriminatedCodec,
    Dissected,
    DissectedCodec,
    Dissection,
    Encoded,
    EncodedBy,
    EncodedPatch,
    EncodedVariants,
    FallbackCodec,
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
    NumberCodec,
    ObjectCodec,
    ObjectOf,
    ObjectSpecsOf,
    OptionalCodec,
    PathOf,
    PathTerminal,
    Reader,
    Refined,
    Refinement,
    RestDeclaration,
    RestPolicy,
    Result,
    Rng,
    SetBase,
    SetCapable,
    SetOf,
    Shape,
    Slot,
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
    ValidateOptions,
    ValidateVariants,
    VariantOf,
    Writes,
    WrittenBy,
} from './codec/codec'
export {
    andThen,
    array,
    binary,
    boolean,
    CodecError,
    custom,
    decimal,
    discriminatedUnion,
    every,
    everyEntry,
    failed,
    fallback,
    held,
    lazy,
    legacy,
    list,
    mdunion,
    never,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    orThrow,
    pathBuilder,
    product,
    record,
    refine,
    spread,
    string,
    undefinable,
    union,
} from './codec/codec'
export type { Field, Term } from './codec/term'
// `shapeOf` classifies a *value* and reaches no term, so it moved to `value.ts` with the twelve
// others `denote.ts` needs. The name on the surface is unchanged; only the module that declares
// it moved, which is why this is a second `export` rather than an entry in the list above.
export { shapeOf } from './codec/value'
