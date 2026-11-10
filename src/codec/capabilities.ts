/**
 * The codec of a term, with the capabilities that the term decides.
 *
 * `codecOfTerm` and `equip` are one recursion. `equip` reads the codec of each slot of an object
 * term, and the set builder builds a term and asks `codecOfTerm` for the codec. So the memo, the
 * capabilities and the builders that they call live in one module, and a module above this one
 * builds a codec at load with no order to keep.
 *
 * **The capabilities are the literal call, `.set()`, `.spec` and `.rest`.** Each is a function of
 * the term. A codec that a slice or a meet builds from a term is therefore the codec that the
 * caller wrote.
 */
import type { Attribute, AttributeValue } from './attribute'
import { DynamoNumber, isStoredNumeral } from './attribute'
import type { AnyCodec, AttributeCodec } from './build'
import { codecAtLevel, judged, literalTermOf, termOf } from './denote'
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
 * - **`ℓ` is homogeneous at the base.** Free in the model — `NEFinset k.Carrier` — and not free
 *   here, because a spread of a plain array defeats the type. So it is a construction-time refusal.
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
    return codecOfTerm<T, AttributeValue>(literalTermOf(base, allowed))
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
 * **The `.set()` of a codec**: the set of the codec that carries it, or, where the codec has a
 * literal call, the set of the literal at the alternatives that the call names. One function for
 * each codec that has a `.set()`: the bases, the two numeric adapters, a refinement and an entry of
 * a scope. A repeated value refuses here as it refuses at `string('dog', 'dog')`.
 *
 * The thunk reads the codec that carries the `.set()`, and not the one that was handed in:
 * `.set()` records its element in `def`, so two copies of one codec would give two definitions
 * that differ by a property nobody can see.
 *
 * **This is the one set builder, and it is internal.** Every set in the surface comes through
 * here: `string.set()` and the other bases, and everything that reduces to a base through
 * {@link equip}, such as `amount.set()` where `amount = refine(decimal, isAmount)`. The capability
 * propagates, so a free-standing form said nothing that `.set()` cannot say. The set is the
 * finite-powerset lift of the term of the element, so a restriction, a literal and an adapter each
 * ride at the element, and `price.set()` decodes back as prices. The member of the element, `SS`,
 * `NS` or `BS`, decides the wire set.
 *
 * **Order is not preserved.** DynamoDB returns a set in an order that the service chooses, so both
 * directions sort. `decode ∘ encode = id` holds only for canonical values; for the rest the law is
 * {@link checkStable}. If order carries meaning, use `array(...)`. **Empty is not representable**: `encode` throws where the service
 * refuses.
 */
export const setOf =
    (carrier: () => AnyCodec, literal?: (...allowed: never[]) => AnyCodec) =>
    (...allowed: readonly unknown[]) =>
        codecOfTerm({
            kind: 'set',
            elem: (allowed.length > 0 && literal !== undefined
                ? literal(...(allowed as never[]))
                : carrier()
            ).def,
        })

/**
 * The rule `(literal)`'s `ℓ`, checked: non-empty and pairwise distinct.
 *
 * **The model gets three guarantees from a type and the host's type gives two.** `ls` is a
 * `NEFinset k.Carrier`, so the base indexes the alternatives, `n ≥ 1` holds, and no two are equal —
 * all three from `NEFinset`. `term.ts`'s {@link Literal} buys the first from a discriminated union
 * over the base and the second from a tuple head. **TypeScript cannot say the third**, so it is a
 * refusal at construction, and this is where it lives.
 *
 * Distinctness is not tidiness. `NEFinset` is a *set*, so `literal(k, {'A','A'})` and
 * `literal(k, {'A'})` are one term in the model and two definitions here — and the second names a
 * cardinality the first does not, which is what {@link constantOf} reads to answer whether a literal
 * has exactly one value. A repeated alternative makes a two-element `ls` that admits one value,
 * and the constant would go unrecognised.
 *
 * Compared with {@link sameLiteral}, which compares the way the base compares: bytes for `binary`,
 * `===` otherwise.
 */
export const someAlternatives = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): readonly T[] => {
    if (allowed.length === 0) {
        throw new CodecError(
            `a literal admits one of a non-empty set of values, and \`${base}()\` names none; pass the values, or use \`${base}\` itself if anything is admissible`,
        )
    }
    // the values rather than the indices, so the pair is two `T`s and not two lookups the checker
    // has to be told about; `at` recovers the position the message names
    for (const [i, one] of allowed.entries()) {
        for (const [after, other] of allowed.slice(i + 1).entries()) {
            if (sameLiteral(one, other)) {
                const at = i + 1 + after
                throw new CodecError(
                    `a literal's alternatives are a *set*, and \`${base}()\` names the same value at positions ${i} and ${at}; the model's \`NEFinset\` cannot hold it twice, and a repeat makes a two-value literal that admits one — which stops it reading as a constant`,
                )
            }
        }
    }
    return allowed
}

export const literalCapability =
    (base: LiteralBase) =>
    (...allowed: readonly LiteralValue[]) =>
        literalCodec(base, someAlternatives(base, allowed))

/**
 * **The capabilities that a term decides**, added to the codec that `codecOfTerm` denotes for it.
 *
 * - The literal call: the four bases at the term of the base (`string('A')`), the two numeric
 *   adapters at the term of the adapter (`decimal('1.5')`, `number(5)`).
 * - `.set()`: the bases that have a set (`boolean` has none), the two numeric adapters, and a
 *   refinement of any term. `set` refuses an element that names no member of `S`, `N` or `B`.
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
    if (term.kind === 'refine') {
        const capable: AnyCodec = {
            ...codec,
            set: setOf(() => capable),
        } as AnyCodec
        return capable
    }
    const call = literalCallOf(term)
    if (call === undefined) return codec
    const carrier = Object.assign(call, codec) as unknown as AnyCodec
    return term.kind === 'boolean'
        ? carrier
        : Object.assign(carrier, { set: setOf(() => carrier, call) })
}

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
        case 'number':
        case 'boolean':
        case 'binary':
            return literalCapability(term.kind) as (
                ...allowed: never[]
            ) => AnyCodec
        case 'held':
            if (term.inner.kind !== 'number') return undefined
            if (term.via === 'decimalText' && term.outer.kind === 'string')
                return (...allowed) => decimalCall(...(allowed as string[]))
            return term.via === 'float'
                ? (...allowed) => numberCall(...(allowed as number[]))
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
    inner: Term,
    outer: Term,
    into: (value: T) => Result<DynamoNumber>,
    outOf: (held: DynamoNumber) => Result<T>,
    via?: 'decimalText' | 'float',
): AttributeCodec<T, Attribute<'N'>> =>
    codecOfTerm<T, Attribute<'N'>>({
        kind: 'held',
        inner,
        outer,
        f: into as (value: never) => unknown,
        g: outOf as (held: never) => unknown,
        ...(via ? { via } : {}),
    })

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
        termOf(literalCapability('number')(...stored) as AnyCodec),
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
        termOf(
            literalCapability('number')(
                ...numericAlternatives(allowed),
            ) as AnyCodec,
        ),
        { kind: 'number' },
        asFloat,
        asJsNumber,
        'float',
    )
