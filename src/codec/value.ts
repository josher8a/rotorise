/**
 * The value side, under the pair.
 *
 * Thirteen helpers that both `codec.ts` and `denote.ts` need, in the one module that can hold them.
 *
 * **They are here for a structural reason, and the reason is worth stating because the grouping is
 * not thematic.** `denote.ts` builds every constructor's pair and `codec.ts`'s constructors take
 * their pair from it, which is one import direction. A *value* `denote.ts` reached back for in
 * `codec.ts` would close that direction into a cycle. A **type** is free across it, because
 * `import type` is erased, so every type these signatures name still lives where it was declared
 * and only the values moved.
 *
 * What they have in common is the level: each answers a question about a **value** or an
 * **attribute**, never about a term. Classifying a value, naming the shape a refusal reports,
 * reading the names an item carries, pulling a member out of an attribute, comparing two
 * alternatives, asking whether a codec already owns the null point.
 *
 * Three helpers that look like these are **not** here — `literalCodec`, `encodeUnknown` and
 * `decodeUnknown`. Each builds a pair: the first reaches `codecOfTerm`, and the other two are
 * `opaque`'s two halves. They belong with the other pair builders and go there in the next pass.
 */

import type {
    Attribute,
    AttributeName,
    AttributeValue,
    StoredItem,
} from './attribute'
import { DynamoNumber, memberOf } from './attribute'
import type { LiteralValue, Option, Shape } from './codec'
import type { Result } from './result'
import { CodecError, failed } from './result'

/**
 * A value read as a bare record of attributes, or nothing.
 *
 * Only a plain object can be an object option's value. An array, a `Set`, a `Uint8Array` and a class
 * instance all have keys `Object.keys` will happily list, and matching an object option on those
 * would pick one that cannot encode them.
 */
export const asRecord = (
    value: unknown,
): Record<string, unknown> | undefined => {
    if (typeof value !== 'object' || value === null) return undefined
    const proto = Object.getPrototypeOf(value) as object | null
    return proto === Object.prototype || proto === null
        ? (value as Record<string, unknown>)
        : undefined
}

/** The kind of a value, read as coarsely as {@link carries} declares it. */
export const shapeOf = (value: unknown): Shape | undefined =>
    typeof value === 'string'
        ? 'string'
        : typeof value === 'number'
          ? 'number'
          : typeof value === 'boolean'
            ? 'boolean'
            : value === null
              ? 'null'
              : value instanceof Uint8Array
                ? 'binary'
                : value instanceof Set
                  ? 'set'
                  : Array.isArray(value)
                    ? 'array'
                    : asRecord(value)
                      ? 'map'
                      : undefined

/**
 * A value rendered for a message, where **rendering it is the part that can fail**.
 *
 * `String(value)` reaches the value's own `toString`, `valueOf` or `Symbol.toPrimitive`, and all
 * three are the caller's code. `Object.create(null)` has none of them and `String` throws
 * `TypeError: Cannot convert object to primitive value`; an object whose `toString` throws does the
 * same. Measured before this was written: a null-prototype value reached `string`, `number`,
 * `decimal`, `boolean`, `binary` and both literal forms, and **all seven threw a `TypeError` out of
 * `encode`** rather than returning a `CodecError`.
 *
 * That is Rule 14 inverted at the one place whose whole job is to describe a failure: an expected
 * refusal became a throw, and it became one *inside the refusal path*. So the conversion is caught
 * here, at the seam that runs the caller's code, and a value that cannot render is named by its
 * shape alone. No total renderer exists to write instead — `toString` is arbitrary user code.
 */
export const rendered = (value: unknown): string => {
    try {
        return String(value)
    } catch {
        // its own `toString` threw, or it has none; `JSON.stringify` reads the properties directly
        try {
            return JSON.stringify(value) ?? 'a value that cannot be rendered'
        } catch {
            return 'a value that cannot be rendered'
        }
    }
}

/**
 * A value's kind, for a message about a value that should not have arrived.
 *
 * The five ground `encode`s all refuse the same way and want to say the same thing about what they
 * were handed. `shapeOf` answers `undefined` for what it cannot place — a `bigint`, a `Map`, a
 * function — and `typeof` is the honest withLegacyRead there rather than a guess.
 */
export const describeShape = (value: unknown): string =>
    `${shapeOf(value) ?? typeof value} \`${rendered(value)}\``

/**
 * The names a value has, which is all the object matcher reads.
 *
 * A key whose value is `undefined` is not a name. That is the same rule in both directions —
 * `{ gift: undefined }` encodes without `gift`, and an item with no `gift` attribute decodes without
 * it — so matching an option on it would pick one the other direction cannot reach.
 */
export const namesOf = (held: Record<string, unknown>) => {
    const names = new Set<string>()
    for (const name in held) {
        if (held[name] !== undefined) names.add(name)
    }
    return names
}

/**
 * Whether an object option can describe exactly this set of attribute names.
 *
 * Two conditions, and both matter for the law: every name present must be one the option declares
 * (otherwise encoding would drop data), and every attribute it requires must be present (otherwise
 * it is simply not this one).
 *
 * Named for what it is, which used to be `admits` — and it is emphatically **not** {@link accepts},
 * §3's `Adm`. It is a test on *names* alone, the `keysOk` the model's `optionSemOf` uses for object
 * options, and it says nothing about whether the values at those names are admissible. Two things
 * called `admits` in one file was one name for two questions.
 */
export const namesFit = (option: Option, names: ReadonlySet<string>) => {
    const declares = option.declares
    if (!declares) return false
    for (const name of names) if (!declares.has(name)) return false
    for (const name of option.requires) if (!names.has(name)) return false
    return true
}

type AttributeCarriesOf<K extends AttributeName> = Attribute<K>[K]

export const expect = <K extends AttributeName>(
    name: K,
    attribute: AttributeValue,
): Result<AttributeCarriesOf<K>> => {
    const carried = (attribute as Record<string, unknown>)[name]
    return carried === undefined
        ? new CodecError(
              `expected attribute member '${name}', found '${memberOf(attribute) ?? 'none'}'`,
          )
        : (carried as AttributeCarriesOf<K>)
}

/**
 * Two alternatives, compared the way the base compares them: bytes for `binary`, digits for
 * `number`, `===` otherwise.
 *
 * The two object carriers need a case each, because `===` on them is reference identity and an
 * alternative a caller wrote is never the same object as the value that arrives. `DynamoNumber`
 * normalises at construction, so comparing the digits is comparing the numbers.
 */
export const sameLiteral = (one: LiteralValue, other: unknown): boolean =>
    one instanceof Uint8Array
        ? other instanceof Uint8Array &&
          one.length === other.length &&
          one.every((byte, at) => byte === other[at])
        : one instanceof DynamoNumber
          ? other instanceof DynamoNumber && one.digits === other.digits
          : one === other

/**
 * An alternative as a message names it: text in quotes, digits bare, bytes in hex.
 *
 * **The last arm cannot be `String(one)`.** This takes an `unknown`, because it names the value
 * that *failed* a literal as well as the alternatives that literal admits, and a value reaching
 * `encode` past its type can be anything. `rendered` is where that conversion is made safe, and
 * its docstring carries the measurement.
 */
export const namedLiteral = (one: unknown): string =>
    typeof one === 'string'
        ? `'${one}'`
        : one instanceof Uint8Array
          ? `0x${[...one].map((byte) => byte.toString(16).padStart(2, '0')).join('')}`
          : one instanceof DynamoNumber
            ? one.digits
            : rendered(one)

/**
 * Whether this stand-in has to be *copied* on each read that uses it, decided once.
 *
 * The declaration holds **one** value — that is what makes §3 `(withLegacyRead)`'s premise checkable
 * where the declaration is — so handing that object out is handing every row the same object, and
 * one caller's `.push` becomes every other caller's default. `structuredClone` is the platform's,
 * so a copy costs no dependency.
 *
 * Two reasons not to copy, and both are settled here rather than per read.
 *
 * A **primitive** cannot be mutated, so sharing one is safe and copying it is waste — and most
 * stand-ins are primitives.
 *
 * And a value `structuredClone` **refuses**. Ordinarily there is none: a stand-in is a value the
 * inner codec accepts, so it comes from the value language — arrays, plain objects, `Set`,
 * `Uint8Array` — and all of those clone. A `custom` term is the exception, because its admission
 * asks the caller's own pair, so a hand-written codec can legitimately admit a class instance with
 * methods or anything else holding a function. Rather than throw a `DataCloneError` out of a
 * `decode` months later, the clone is attempted once at the declaration; where it fails the value
 * is shared, which is the old behaviour confined to the one case that forces it.
 */
export const copiedPerRead = (value: unknown): boolean => {
    if (typeof value !== 'object' || value === null) return false
    try {
        structuredClone(value)
        return true
    } catch {
        return false
    }
}

export const readTag = (
    item: StoredItem,
    discriminator: string,
): Result<string> => {
    const attribute = item[discriminator]
    if (attribute === undefined) {
        return new CodecError(
            `'${discriminator}' chooses the variant and the item has no such attribute`,
        )
    }
    const member = memberOf(attribute)
    if (member !== 'S' && member !== 'N') {
        return new CodecError(
            `'${discriminator}' chooses the variant, so it must be carried as 'S' or 'N', not '${member ?? 'none'}'`,
        )
    }
    return attribute[member] as string
}

/**
 * The assignment a stored item carries: one tag per discriminator.
 *
 * A record and not a tuple, because the keys have no order — see `Term`'s `dunion` row.
 */
export const readTags = (
    item: StoredItem,
    ks: readonly string[],
): Result<Readonly<Record<string, string>>> => {
    const out: Record<string, string> = {}
    for (const name of ks) {
        const one = readTag(item, name)
        if (failed(one)) return one
        out[name] = one
    }
    return out
}
