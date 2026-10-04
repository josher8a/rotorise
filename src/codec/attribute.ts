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

import { CodecError, type Result } from './result'

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

// ── what an `N` carries ──────────────────────────────────────────────
//
// `Carries('N')` is not `string`. Every term that writes or reads an `N` owes the same predicate,
// and it lives here rather than beside any one of them: it is a property of the carrier, the way
// `Attr.n : WFNumeral` is in `formal/Calculus/Dynamo/Domain.lean`, not of the codec that happens to use it.

/**
 * What DynamoDB **accepts** in an `N`: optional sign, digits, optional point, optional exponent;
 * at most 38 significant digits; magnitude zero or `1e-130 … 9.9…e125`. §1's `Numerals`, and the
 * same predicate as `Numeral.WF` in `formal/Calculus/Dynamo/Domain.lean`.
 */
const NUMERAL = /^[+-]?(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/

export const isNumeral = (s: string): boolean => {
    const m = NUMERAL.exec(s)
    if (!m) return false
    const int = m[1] as string
    const frac = m[2] ?? ''
    const mantissa = int + frac
    const lead = mantissa.length - mantissa.replace(/^0+/, '').length
    const significant = mantissa.replace(/^0+/, '').replace(/0+$/, '')
    if (significant.length > 38) return false
    if (significant.length === 0) return true // zero, however it is spelled
    const exponent = int.length - 1 - lead + Number(m[3] ?? '0')
    return exponent >= -130 && exponent <= 125
}

/**
 * What DynamoDB **hands back**, which is a smaller set: it normalises every `N` it accepts —
 * trimming leading and trailing zeros, dropping `+`, expanding exponents, and keeping one spelling
 * of zero. Measured, not assumed: `codec.dynamodb.spec.ts` puts each form into a real table and reads it
 * back, and `Numeral.Stored` in `formal/Calculus/Dynamo/Lang/Store.lean` is the same set.
 */
export const isStoredNumeral = (s: string): boolean =>
    s !== '-0' && /^-?(?:0|[1-9]\d*)(?:\.\d*[1-9])?$/.test(s) && isNumeral(s)

// ── the carrier `N` actually has ─────────────────────────────────────
//
// The two predicates above are properties of the carrier rather than of any codec, and until now
// there was no carrier for them to be properties OF: `N` was carried as `string` at every surface,
// so the predicate had to be re-checked at each boundary and the type never said it had passed.
// `DynamoNumber` is that carrier. It is what `formal/Calculus/Dynamo/Domain.lean` calls `WFNumeral`.

/**
 * **An exact DynamoDB number.** The carrier `N` actually has: a numeral the service accepts,
 * validated once at construction and carried with the proof implicit in the type.
 *
 * Nothing here rounds. The digits are the value, so 38 significant digits survive, where a JS
 * `number` carries about 15. Construct one with {@link DynamoNumber.from} or
 * {@link DynamoNumber.fromNumber}; there is no public constructor, because an unvalidated
 * `DynamoNumber` is the thing this type exists to make unrepresentable.
 *
 * **Three carriers write `N`, and they are not interchangeable.** `dynamoNumber` holds this type
 * and is exact. `number` holds a JS float and is lossy by construction. `decimal` holds a string
 * and is exact but compares as text. A caller picks the carrier and takes its cost, which is why
 * all three are on the surface rather than one being the others' spelling.
 */
export class DynamoNumber {
    /**
     * The numeral text, in the form the store returns. Always {@link isStoredNumeral}, because
     * the constructor is the only way in and it normalises.
     */
    readonly digits: string

    private constructor(digits: string) {
        this.digits = digits
    }

    /**
     * **The spelling the store would return, expanded from the digits.** Not through a JS number:
     * `String(Number(...))` writes exponent form at or above `1e21` and below `1e-6` — `'1e+21'`,
     * `'1e-7'` — and the store returns neither, while DynamoDB carries magnitudes to `1e125`.
     *
     * Total on anything {@link isNumeral} accepts. The value does not change, so the significant
     * digits and the magnitude are the ones that already passed.
     */
    private static normalise(numeral: string): string {
        const parts = /^([+-]?)(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/.exec(
            numeral,
        )
        // unreachable: every caller has already passed `isNumeral`, which is this shape
        if (!parts) return numeral
        const sign = parts[1] === '-' ? '-' : ''
        const whole = parts[2] as string
        // where the point sits in `digits`, counted from the left, after the exponent moves it
        let point = whole.length + Number(parts[4] ?? '0')
        let digits = whole + (parts[3] ?? '')

        const lead = digits.length - digits.replace(/^0+/, '').length
        digits = digits.slice(lead).replace(/0+$/, '')
        point -= lead

        // every digit was a zero, and the store keeps one spelling of it
        if (!digits) return '0'

        return (
            sign +
            (point <= 0
                ? `0.${'0'.repeat(-point)}${digits}`
                : point >= digits.length
                  ? digits + '0'.repeat(point - digits.length)
                  : `${digits.slice(0, point)}.${digits.slice(point)}`)
        )
    }

    /**
     * From numeral text. Refuses text DynamoDB will not accept — the wrong shape, more than 38
     * significant digits, or a magnitude outside `1e-130 … 9.9…e125`.
     *
     * **The digits are normalised here**, so `from('1.50')` and `from('1.5')` are one value and
     * `from('1e5').toString()` is `'100000'`. The store normalises every `N` it accepts, so a
     * carrier holding any other spelling holds one the table will not give back, and every
     * comparison and round trip downstream would have to know that. This is the one place that
     * can know it.
     *
     * A codec that must refuse a denormal spelling rather than re-spell it — {@link decimal} does,
     * because it hands the caller back text — checks {@link isStoredNumeral} on the text before
     * building one of these.
     */
    static from(digits: string): Result<DynamoNumber> {
        return isNumeral(digits)
            ? new DynamoNumber(DynamoNumber.normalise(digits))
            : new CodecError(
                  `'${digits}' is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125`,
              )
    }

    /**
     * From a JS number. Refuses `NaN`, `±Infinity`, and any value whose decimal form DynamoDB
     * will not accept.
     *
     * **This is the lossy boundary and it is the only one.** The float has already rounded before
     * this is called, so the `DynamoNumber` is exact about a value that may not be the one meant.
     * Where that matters, carry the digits and use {@link DynamoNumber.from}.
     */
    static fromNumber(value: number): Result<DynamoNumber> {
        return Number.isFinite(value)
            ? DynamoNumber.from(String(value))
            : new CodecError(
                  `${String(value)} is not a number DynamoDB stores: it has no NaN and no Infinity`,
              )
    }

    /** The numeral text, as the store holds it. Exact. */
    toString(): string {
        return this.digits
    }

    /**
     * As a JS number. **Lossy** above about 15 significant digits, and named so rather than
     * offered as `valueOf`, so that a rounding conversion never happens implicitly.
     */
    toNumber(): number {
        return Number(this.digits)
    }

    /**
     * Equality, and there is only one kind here.
     *
     * Carrying `N` as text makes two of them: `'1.50'` and `'1.5'` are one number and two
     * numerals, so a text carrier answers "different" where a caller means "same" and needs a
     * second comparison beside the first. Normalising at construction is what removes the second
     * question rather than answering it.
     */
    equals(other: DynamoNumber): boolean {
        return this.digits === other.digits
    }
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
     * `array(string)` writes `L<S>` — any number of strings — and `list(string, decimal)` writes
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

/**
 * How deep DynamoDB nests document types.
 *
 * `docs/dynamo-datatypes.md:130`: *"The document types are list and map. These data types can be
 * nested within each other, to represent complex data structures up to 32 levels deep."* So this
 * counts **`L` and `M` only** — a scalar or a set is not a document type and cannot contain one, so
 * neither adds a level, and a set at the deepest legal level is legal.
 *
 * The other two limits in that reference are not this one and are not checkable here. Element count
 * is unbounded (`:132`, `:185` — *"There is no limit on the number of values in a list or a map"*),
 * so a wide attribute is exact rather than lucky. Item size (400 KB) is a sum over every attribute
 * name and value in a row, so it is checkable where an *item* is assembled and nowhere inside one
 * attribute's codec.
 *
 * **The boundary is the one thing the reference does not settle.** Its sentence does not say
 * whether a scalar sitting inside 32 lists is the 32nd level or the 33rd. This takes the reading
 * the sentence states literally — at most 32 nested *document types*, the leaf not being one — so
 * 32 nested lists holding a string is accepted and 33 is refused. If a live table disagrees it will
 * disagree by exactly one, and this constant with the two `> MAX_DOCUMENT_NESTING` tests are the
 * whole of what has to change.
 */
export const MAX_DOCUMENT_NESTING = 32

/**
 * Nothing, or why one more `L`/`M` would put a document past what DynamoDB stores.
 *
 * The reason and not the error, because {@link CodecError} lives in `./result`, which already
 * imports this file — and because the bound and its wording belong wherever the carrier is
 * described, the way `isNumeral` does. Four walkers ask it and there is one of it.
 *
 * Asked on the way *in*, before recursing, which is what makes a pathological input a refusal
 * rather than a crash: a 20 000-deep array exhausted the call stack before anything looked at it,
 * and a `RangeError` is not what callers of this library handle.
 *
 * **Where it is asked.** Every codec that writes an `L` or an `M` asks it with the level it writes
 * at. A typed container gets the level from its parent, adds one, and hands the sum to each child,
 * so the count is compositional: no codec walks a finished attribute. `opaque` and `native` ask it
 * per level of the data they walk, because nobody declared that data. A recursive entity takes its
 * depth from the value, and the container that would write the 33rd level refuses, with its path.
 *
 * **Where it is not.** A public `encode` starts the count at `0`, so a value written at a nested
 * path through `at` counts from that path and not from the root of the item.
 */
export const tooDeeplyNested = (enclosing: number): string | undefined =>
    enclosing >= MAX_DOCUMENT_NESTING
        ? `nesting reaches ${enclosing + 1} levels of list and map, and DynamoDB stores at most ${MAX_DOCUMENT_NESTING} — the write would be rejected`
        : undefined
