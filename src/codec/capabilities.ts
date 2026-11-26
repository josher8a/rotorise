/**
 * The codec of a term, with the capabilities that the term decides.
 *
 * `codecOfTerm` and `equip` are one recursion. `equip` reads the codec of each slot of an object
 * term. So the memo, the capabilities and the builders that they call live in one module, and a
 * module above this one builds a codec at load with no order to keep.
 *
 * **The capabilities are the literal call, `.spec` and `.rest`.** Each is a function of the term.
 * A codec that a slice or a meet builds from a term is therefore the codec that the caller wrote.
 */
import type { Attribute, AttributeValue } from './attribute'
import { DynamoNumber, isStoredNumeral } from './attribute'
import type { AnyCodec, AttributeCodec } from './build'
import type { Pair } from './denote'
import {
    codecAtLevel,
    codecWithPair,
    heldPair,
    judged,
    judgedBy,
    judgeWall,
    literalOf,
    literalTermOf,
    pairOfCodec,
    seedPair,
    termOf,
} from './denote'
import type { Result } from './result'
import { CodecError, failed, orThrow } from './result'
import type { Body, LiteralBase, LiteralValue, Term } from './term'
import { describeShape, namedLiteral, sameLiteral } from './value'

/**
 * **One codec per term, for the life of the term.**
 *
 * A term is immutable by design and frozen at construction, so a codec built from one is a function
 * of it and can be built once. The freeze is what the cache rests on: a mutation fails loudly
 * instead of poisoning it.
 */
const codecs = new WeakMap<Term, AttributeCodec<never, AttributeValue>>()

/**
 * The codec of a term, built once, with the capabilities that {@link equip} adds. A term that the
 * judgment refuses throws.
 */
export const codecOfTerm = <T, A extends AttributeValue>(
    def: Term,
): AttributeCodec<T, A> => {
    const built = codecs.get(def)
    if (built) return built as unknown as AttributeCodec<T, A>
    judged(def)
    const made = equip(
        codecAtLevel<never, AttributeValue>(Object.freeze(def), 0),
        def,
    ) as AttributeCodec<never, AttributeValue>
    codecs.set(def, made)
    return made as unknown as AttributeCodec<T, A>
}

/**
 * A literal at a named base — the one builder every literal in this library goes through.
 *
 * The premises of the rule `(literal)`, checked where the rule states them:
 *
 * - **`ℓ` is non-empty.** Checked by each caller, because the message wants to name the
 *   constructor the caller actually wrote.
 * - **`ℓ` is homogeneous at the base.** Free in the model, where a literal holds one value of
 *   `k.Carrier`, and not free here, because a spread of a plain array defeats the type. So it is a
 *   construction-time refusal.
 * - **`ℓ ⊆ D`** at `number`. The carrier `DynamoNumber` discharges it where the value is made.
 *
 * Each premise is decided when the codec is built, because `ℓ` is data this library owns.
 */
export const literalCodec = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): AttributeCodec<T, AttributeValue> => {
    /**
     * **`ℓ ⊆ D`** — the premise on the numeric base, and the defect that made it more than
     * bookkeeping. `literal(NaN)` produced `{ N: 'NaN' }` and `literal(1e400)` produced
     * `{ N: 'Infinity' }`, both reachable with no cast and both rejected by the service.
     *
     * **The carrier discharges it, and there is nothing left to check here.** A numeric
     * alternative is a `DynamoNumber`, which cannot be built from a value the service refuses, so
     * the refusal happens where the value is made. The `decimal` premise went the same way, and it
     * was narrower still: a stored spelling is what the carrier normalises to.
     */
    const { def, pair } = literalOf(base, allowed)
    return codecOfPair<T, AttributeValue>(def, pair)
}

/**
 * The slots of an object term, as a caller reads them: the codec of each field term, and the
 * field itself, `{ codec, def }`, where the mark is not `req`. The rest is the codec of the open
 * term. Each codec is the one that `codecOfTerm` gives the term, so a slot is the codec that the
 * caller wrote, from one source.
 */
export const slotsOf = (body: Body) => ({
    spec: Object.fromEntries(
        Object.entries(body.fields).map(([name, f]) => {
            const codec = codecOfTerm(f.t)
            return [name, f.mark === 'req' ? codec : { codec, def: f }]
        }),
    ),
    rest: body.rest && codecOfTerm(body.rest),
})

/**
 * The alternatives of a literal call, checked: non-empty and pairwise distinct.
 *
 * **A literal of the model holds one value**, `Term.literal k v`. A call of several values is a
 * union of one-value literals, and `literalTermOf` builds that union. A repeated value gives a union
 * of two options that admits one value. {@link constantOf} reads a union as a term that decides no
 * constant, so `string('dog', 'dog')` would decide none where `string('dog')` decides one. The call
 * refuses the repeat, so one set of values has one term. TypeScript cannot say distinctness of a
 * tuple, so the refusal is at construction, and this is where it lives.
 *
 * Compared with {@link sameLiteral}, which compares the way the base compares: bytes for `binary`,
 * `===` otherwise.
 */
export const someAlternatives = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
    former: string = base,
): readonly T[] => {
    if (allowed.length === 0) {
        throw new CodecError(
            `a literal admits one of a non-empty set of values, and \`${former}()\` names none; pass the values, or use \`${former}\` itself if anything is admissible`,
        )
    }
    // the values rather than the indices, so the pair is two `T`s and not two lookups the checker
    // has to be told about; `at` recovers the position the message names
    for (const [i, one] of allowed.entries()) {
        for (const [after, other] of allowed.slice(i + 1).entries()) {
            if (sameLiteral(one, other)) {
                const at = i + 1 + after
                throw new CodecError(
                    `a literal's alternatives are distinct, and \`${former}()\` names the same value at positions ${i} and ${at}; a call of several values is a union of one-value literals, and a repeat makes a union of two options that admits one value and decides no constant`,
                )
            }
        }
    }
    return allowed
}

export const literalCapability =
    (base: LiteralBase, former: string = base) =>
    (...allowed: readonly LiteralValue[]) =>
        literalCodec(base, someAlternatives(base, allowed, former))

/**
 * **The capabilities that a term decides**, added to the codec that `codecOfTerm` denotes for it.
 *
 * - The literal call: the four bases at the term of the base (`string('A')`), the two numeric
 *   adapters at the term of the adapter (`decimal('1.5')`, `number(5)`).
 * - `.spec` and `.rest`: the slots of an object term.
 *
 * The constants are the codecs that this gives for their own term, so a codec that a slice or a meet
 * builds from a term is the codec that the caller wrote. `opaque` is not here: its call chooses
 * among three codecs by a policy, and the canonical term holds no policy, so the policy would be a
 * fact outside the term.
 */
export const equip = (codec: AnyCodec, term: Term): unknown => {
    if (term.kind === 'object') {
        // read at the first use: a scope binds its names after the terms that name them are built
        let slots: ReturnType<typeof slotsOf> | undefined
        const read = () => {
            slots ??= slotsOf(term.body)
            return slots
        }
        return Object.defineProperties(
            { ...codec },
            {
                spec: { enumerable: true, get: () => read().spec },
                rest: { enumerable: true, get: () => read().rest },
            },
        )
    }
    return literalEquip(codec, term)
}

/** The literal call of a term that has one, over the codec of the term. */
const literalEquip = (codec: AnyCodec, term: Term): unknown => {
    const call = literalCallOf(term)
    return call === undefined ? codec : Object.assign(call, codec)
}

/**
 * The codec of a term, from the pair that the constructor of its kind holds, with the literal call
 * that the constructor names. The judgment of a ground term and of a literal choice has no premise
 * that the constructor leaves open, so this skips it, and no switch over the other kinds is reached.
 */
export const codecOfPair = <T, A extends AttributeValue>(
    def: Term,
    pair: Pair,
    call?: (...allowed: never[]) => AnyCodec,
): AttributeCodec<T, A> => {
    const built = codecs.get(def)
    if (built) return built as unknown as AttributeCodec<T, A>
    seedPair(def, pair)
    const bare = codecWithPair<never, AttributeValue>(
        Object.freeze(def),
        pair,
        0,
    )
    const made = call === undefined ? bare : Object.assign(call, bare)
    codecs.set(def, made)
    return made as unknown as AttributeCodec<T, A>
}

/** The codec of a ground term that has the literal call of its own kind. */
export const codecOfGround = <T, A extends AttributeValue>(
    def: Term & { readonly kind: 'string' | 'boolean' | 'binary' },
    pair: Pair,
): AttributeCodec<T, A> => codecOfPair(def, pair, literalCapability(def.kind))

/**
 * The literal call that a term has, or nothing. Each call is a function of its own: the carrier
 * takes the properties of the codec, so one function shared by two terms would carry the `def` of
 * the last.
 */
export const literalCallOf = (
    term: Term,
): ((...allowed: never[]) => AnyCodec) | undefined => {
    switch (term.kind) {
        case 'string':
        case 'boolean':
        case 'binary':
            return literalCapability(term.kind)
        case 'number':
            return literalCapability('number', 'dynamoNumber')
        case 'held':
            if (term.inner.kind !== 'number') return undefined
            if (term.via === 'decimalText' && term.outer.kind === 'string')
                return (...allowed) => decimalCall(...allowed)
            return term.via === 'float'
                ? (...allowed) => numberCall(...allowed)
                : undefined
        default:
            return undefined
    }
}

/**
 * An adapter over {@link dynamoNumber}, one conversion wide, on both halves. `held` is built in
 * `adapters.ts`, which imports this file, so the term is built directly here; the two are the same
 * construction.
 *
 * `outer` is the base the adapter hands to the caller, as a write occupancy. The conversion
 * checks the held side itself: `storedOnly` refuses a value that is not a string, and the carrier
 * refuses a value that is not a number. The term of `number` holds a `DynamoNumber`, so the term
 * cannot be the membership test for a JS float.
 */
export const numericAdapter = <T>(
    inner: AnyCodec,
    outer: Term,
    into: (value: T) => Result<DynamoNumber>,
    outOf: (held: DynamoNumber) => Result<T>,
    via?: 'decimalText' | 'float',
): AttributeCodec<T, Attribute<'N'>> => {
    const term: Extract<Term, { kind: 'held' }> = {
        kind: 'held',
        inner: termOf(inner),
        outer,
        f: into,
        g: outOf,
        ...(via ? { via } : {}),
    }
    // the judgment and the pair come from the kind alone, so a bundle of a numeric adapter holds
    // no switch over the other kinds
    judgedBy(term, judgeWall(term))
    return codecOfPair<T, Attribute<'N'>>(
        term,
        heldPair(pairOfCodec(inner), term),
        literalCallOf(term),
    )
}

/**
 * The digits a caller wrote, refused rather than re-spelled.
 *
 * **The type is checked here and not by `isStoredNumeral`.** That predicate tests a pattern, and a
 * pattern coerces: `['1']` and any object whose `toString` spells a numeral both match it, so
 * `decimal` admitted values its own type excludes and wrote them as `N`. The predicate is right to
 * stay a predicate on `string` — the emitter recognises it by reference — so the boundary is here.
 */
export const storedOnly = (value: string): Result<DynamoNumber> =>
    typeof value !== 'string'
        ? new CodecError(
              `${describeShape(value)} is not a string, and \`decimal\` holds the digits as text — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
          )
        : isStoredNumeral(value)
          ? DynamoNumber.from(value)
          : new CodecError(
                `'${value}' is not a numeral DynamoDB stores unchanged; it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
            )

/** The literal call of {@link decimal}: the digits are refused unless they are the stored spelling. */
export const decimalCall = (...allowed: readonly string[]) => {
    const stored = allowed.map((one) => orThrow(storedOnly(one)))
    return numericAdapter<string>(
        literalCapability('number', 'decimal')(...stored),
        // the held side is the texts the adapter hands the caller, so the view is exact
        literalTermOf(
            'string',
            stored.map((held) => held.toString()),
        ),
        storedOnly,
        (held) => held.toString(),
        'decimalText',
    )
}

/** A JS number, as the carrier refuses it. */
export const asFloat = (value: number): Result<DynamoNumber> =>
    DynamoNumber.fromNumber(value)

/**
 * The alternatives a numeric literal names, refused at the caller's level first.
 *
 * **Two refusals, and the adapter owes both.** A value that is not a number at all is
 * `literalTerm`'s sentence one base down, and it is about the caller's type. A number outside what
 * `N` holds is the carrier's. The conversion runs before the native literal is built, so without
 * this the carrier would answer for the type and `number(0, 'A')` would report a `NaN` rule.
 *
 * **Every value outside the range is named, not the first.** A caller who writes three bad
 * alternatives fixes three. One bad alternative keeps the carrier's own sentence, which already
 * says which rule it broke.
 */
export const numericAlternatives = (
    allowed: readonly number[],
): readonly DynamoNumber[] => {
    const held: DynamoNumber[] = []
    const outside: number[] = []
    let firstRefusal: CodecError | undefined
    for (const one of allowed) {
        if (typeof one !== 'number') {
            throw new CodecError(
                `\`number(...)\` admits number values, and ${namedLiteral(one)} is not one`,
            )
        }
        const carried = asFloat(one)
        if (failed(carried)) {
            outside.push(one)
            firstRefusal ??= carried
        } else {
            held.push(carried)
        }
    }
    if (outside.length === 1 && firstRefusal) throw firstRefusal
    if (outside.length > 1) {
        throw new CodecError(
            `${outside.map(namedLiteral).join(', ')} are not numbers DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN and no Infinity`,
        )
    }
    return held
}

/**
 * …and back, refused where the rounding leaves the range `N` holds.
 *
 * `N` carries 38 significant digits and a JS `number` about 15, so reading rounds. Rounding is this
 * codec's declared cost and not a failure. Rounding *out of the range DynamoDB stores* is a
 * different fact: the value read back is one this same codec would refuse to write, so the round
 * trip breaks on a numeral the service genuinely returns. The write half already refuses it, and
 * this half says the same thing rather than hand back a number that cannot go home.
 */
export const asJsNumber = (held: DynamoNumber): Result<number> => {
    const value = held.toNumber()
    return failed(DynamoNumber.fromNumber(value))
        ? new CodecError(
              `'${held.toString()}' rounds to ${String(value)}, which is outside what DynamoDB stores, so \`number\` cannot write it back; read this attribute with \`dynamoNumber\` or \`decimal\`, which do not round`,
          )
        : value
}

/** The literal call of {@link number}: each alternative is refused at the caller's level first. */
export const numberCall = (...allowed: readonly number[]) =>
    numericAdapter<number>(
        literalCapability('number')(...numericAlternatives(allowed)),
        { kind: 'number' },
        asFloat,
        asJsNumber,
        'float',
    )
