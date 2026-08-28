/**
 * What DynamoDB carries, written as the members a value may take.
 *
 * **An AttributeValue is a coproduct whose tag is the key.** `{ S: 'abc' }` is a tagged value where
 * `S` is the tag, so this file writes it that way: a keyed map of the cases, indexed to a union.
 *
 * The shape is structurally identical to the AWS SDK's `AttributeValue` and to Brushless's, so
 * values pass between them without adapters and Rotorise keeps its zero dependencies. It is
 * deliberately *stricter* than the SDK's: see `ExactlyOne`.
 */

/**
 * Exactly one of the members, and the others shut out.
 *
 * The `never` on every other key is what makes this exact. A mapped type over one key says nothing
 * about the rest and an object type is open, so `{ S: 'a', N: '1' }` satisfies a bare
 * `{ S: string }` and reaches a service that refuses it. Excess property checking does not catch it
 * either, because each key is known to some member of the union. The AWS SDK's `AttributeValue` has
 * this hole; a codec whose entire job is emitting valid attributes should not.
 */
export type ExactlyOne<T> = {
    [K in keyof T]-?: { readonly [key in K]-?: T[key] } & {
        readonly [other in Exclude<keyof T, K>]?: never
    }
}[keyof T]

/** The members of an AttributeValue, and what a value carries under each. */
export interface AttributeCarries {
    readonly S: string
    readonly N: string
    readonly B: Uint8Array
    readonly SS: readonly string[]
    readonly NS: readonly string[]
    readonly BS: readonly Uint8Array[]
    readonly M: { readonly [name: string]: AttributeValue }
    readonly L: readonly AttributeValue[]
    readonly BOOL: boolean
    readonly NULL: boolean
}

/** The name of a member. */
export type AttributeName = keyof AttributeCarries

/** One value, which is exactly one member. */
export type AttributeValue = ExactlyOne<AttributeCarries>

/** One value, known to be the named member. */
export type Attribute<K extends AttributeName> = {
    readonly [key in K]-?: AttributeCarries[key]
} & {
    readonly [other in Exclude<AttributeName, K>]?: never
}

/** An item, as DynamoDB carries it. */
export type AttributeMap = { readonly [name: string]: AttributeValue }

/**
 * An item to *read*, which is a wider thing than one to write.
 *
 * `AttributeMap` says every attribute is there. A precise row type says which attributes are there
 * and marks the rest optional — and an optional property carries `| undefined`, which no index
 * signature of `AttributeValue` accepts. So `fromItem(toItem(entity))` did not typecheck, though it
 * is the round trip the whole thing exists for.
 *
 * Reading already treats a missing attribute and one holding `undefined` the same way, so this is
 * the parameter being as wide as the implementation, not a loosening of it.
 */
export type StoredItem = {
    readonly [name: string]: AttributeValue | undefined
}

/**
 * One member, as the exact attribute that carries it.
 *
 * The counterpart of {@link memberOf}, and the one place the exactness is asserted. `{ S: value }`
 * is not an {@link Attribute} on its own — {@link ExactlyOne} wants the other members shut out —
 * so every construction site used to end in `as Attribute<'S'>`. Here the pairing of name and value
 * is *checked*, and there are twenty-five fewer assertions to get wrong.
 *
 * The result distributes, because {@link Attribute} does not: `Attribute<'SS' | 'NS'>` asks for
 * both members at once and is no attribute at all, where a value whose member is decided at runtime
 * — a set choosing `SS`, `NS` or `BS` from its element — is one of them and not the intersection.
 */
export const carrying = <K extends AttributeName>(
    name: K,
    value: AttributeCarries[K],
): Carrying<K> => ({ [name]: value }) as Carrying<K>

/** {@link Attribute}, distributed over a name that is not yet decided. */
export type Carrying<K extends AttributeName> = K extends unknown
    ? Attribute<K>
    : never

/** The member a value is carrying, or `undefined` if it carries none. */
export const memberOf = (value: AttributeValue): AttributeName | undefined => {
    // `for..in` rather than `Object.keys`: an attribute is read on every decode of every nesting
    // point, and the key array is allocated only to be walked once and dropped
    for (const name in value) {
        if (value[name as AttributeName] !== undefined)
            return name as AttributeName
    }
    return undefined
}

// ── the stored shape, as a type you can write down ───────────────────
//
// A schema says what an entity is; these say what the *table* holds. Written by hand they pin the
// shape a table already has — checked into the repo, diffed in review, and readable without
// adopting a codec at all. Derived from a codec (see `Encoded`) they say the same thing, which is
// what makes the pair a fixed point rather than a comment.

/** A string, as stored. */
export type S = Attribute<'S'>
/** A number, as stored — DynamoDB carries the digits as a string. */
export type N = Attribute<'N'>
/** Binary, as stored. */
export type B = Attribute<'B'>
/** A boolean, as stored. */
export type BOOL = Attribute<'BOOL'>
/** Null, as stored — an attribute that is present and holds nothing. */
export type NULL = Attribute<'NULL'>
/** A string set. */
export type SS = Attribute<'SS'>
/** A number set. */
export type NS = Attribute<'NS'>
/** A binary set. */
export type BS = Attribute<'BS'>

/**
 * A list, of anything or of one thing.
 *
 * `L` on its own is a list of any attribute; `L<S>` is a list of strings. Parameterised because the
 * difference between `L` and `SS` is the difference between an ordered list and a set, and a shape
 * that cannot say which is not pinning much.
 */
export type L<
    Of extends AttributeValue | readonly AttributeValue[] = AttributeValue,
> = {
    /**
     * A tuple where `Of` is one, and a homogeneous list otherwise.
     *
     * `array(string)` writes `L<S>` — any number of strings — and `tuple(string, decimal)` writes
     * `L<[S, N]>`, which says one string then one number. The bracketed check is what keeps a union
     * `Of` a list of that union rather than a union of lists.
     */
    readonly L: [Of] extends [readonly AttributeValue[]]
        ? Of
        : readonly (Of & AttributeValue)[]
} & { readonly [other in Exclude<AttributeName, 'L'>]?: never }

/**
 * A map, of anything or of a named shape.
 *
 * `M<{ id: S; note?: S }>` is a nested object with a known shape, optional attributes included —
 * which is why the parameter admits `undefined` per key rather than requiring {@link AttributeMap}.
 */
export type M<
    Of extends Readonly<
        Record<string, AttributeValue | undefined>
    > = AttributeMap,
> = { readonly M: Of } & {
    readonly [other in Exclude<AttributeName, 'M'>]?: never
}
