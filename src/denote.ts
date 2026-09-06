/**
 * What a term means: every constructor's pair, and the memo that keeps one per term.
 *
 * `Combinators.lean`'s combinators, one for one, plus the two devices the host has and the model
 * does not — the **item view**, which is a pair over a map's contents rather than over an
 * attribute, and the codec cache that makes a term's codec unique.
 *
 * **One import direction.** `codec.ts`'s constructors take their pair from here, and nothing here
 * reaches back for a value in `codec.ts` — a value that did would close the direction into a
 * cycle, which is why `value.ts` exists. Types are free across the boundary, because `import type`
 * is erased, so every type these signatures name still lives where it was declared.
 *
 * **One item pair per term.** An object term builds its body pair once; `denote`'s map-writing row
 * wraps that pair, and the codec's `.item` hands out the same one. They were two objects before
 * `579ed89`, `item.encode === codec.encode` answered `false`, and nothing said which of the two a
 * caller was running. The memo is keyed on the frozen term for the reason `codecOfTerm`'s is: the
 * term is the datum, a pair built from it is a function of it, and the freeze is what makes the
 * key stable rather than probable.
 */

import type { AttributeMap, AttributeName, AttributeValue } from './attribute'
import {
    carrying,
    isNumeral,
    isStoredNumeral,
    memberOf,
    tooDeeplyNested,
} from './attribute'
import type { Codec } from './build'
import { codec } from './build'
import type {
    AnyCodec,
    AnyDeclaration,
    AttributeCodec,
    Declared,
    LiteralBase,
    LiteralValue,
    Option,
    opaque,
    Refinement,
    Rng,
    SetBase,
    Shape,
} from './codec'
import type { Result } from './result'
import { andThen, CodecError, every, everyEntry, failed } from './result'
import type { Body, Literal, Predicate, Term } from './term'
import { member as termMember } from './term'
import {
    asRecord,
    copiedPerRead,
    describeShape,
    expect,
    namedLiteral,
    namesFit,
    namesOf,
    ownsNull,
    readTag,
    sameLiteral,
    shapeOf,
} from './value'

/**
 * Which member each base stores a literal in.
 *
 * Not injective: `number` and `decimal` both store `N`. That is exactly why the base has to be
 * recorded — the member cannot recover it, and neither can the JS type of the values, since a
 * `decimal` literal's alternatives are text.
 */
export const literalMember: { readonly [B in LiteralBase]: AttributeName } = {
    string: 'S',
    number: 'N',
    decimal: 'N',
    boolean: 'BOOL',
    binary: 'B',
}

/** Which kind of JS value each base's alternatives are — the mirror, and not the same partition. */
export const literalShape: { readonly [B in LiteralBase]: Shape } = {
    string: 'string',
    number: 'number',
    // a decimal is held as a string and stored as `N`, which is the whole point of it
    decimal: 'string',
    boolean: 'boolean',
    binary: 'binary',
}

/**
 * A literal at a named base — the one builder every literal in this library goes through.
 *
 * The premises §3 states on `(literal)`, checked where the rule states them:
 *
 * - **`ℓ` is non-empty.** Checked by each caller, because the message wants to name the
 *   constructor the caller actually wrote.
 * - **`ℓ` is homogeneous at the base.** Free in the model — `NEFinset k.Carrier` — and not free
 *   here, because a spread of a plain array defeats the type. So it is a construction-time refusal.
 * - **`ℓ ⊆ D`** at the two bases that write an `N`. `number` reads through `Number.prototype
 *   .toString`; `decimal` is text already and has to be in the form the service returns, or the
 *   literal is one this codec could write and never read back.
 *
 * All three are decided when the codec is built, because `ℓ` is data this library owns.
 */
export const literalCodec = <T extends LiteralValue>(
    base: LiteralBase,
    allowed: readonly T[],
): AttributeCodec<T, AttributeValue> => {
    const term = literalTerm(base, allowed)

    /**
     * **`ℓ ⊆ D`** — the premise on the numeric bases, and the defect that made it more than
     * bookkeeping. `literal(NaN)` produced `{ N: 'NaN' }` and `literal(1e400)` produced
     * `{ N: 'Infinity' }`, both reachable with no cast and both rejected by the service.
     */
    if (base === 'number') {
        const outside = (allowed as readonly number[]).filter(
            (one) => !isNumeral(String(one)),
        )
        if (outside.length) {
            throw new CodecError(
                `a numeric literal is stored as 'N', and ${outside
                    .map(namedLiteral)
                    .join(
                        ', ',
                    )} ${outside.length === 1 ? 'is not a number' : 'are not numbers'} DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN or Infinity`,
            )
        }
    }

    /**
     * The same premise at `decimal`, and it is *narrower* than `number`'s, for the reason
     * {@link decimal} gives: the service normalises what it accepts, and this codec's read side is
     * the identity on the digits, so an alternative in any other form is one that could be written
     * and would come back as a different string.
     */
    if (base === 'decimal') {
        const outside = (allowed as readonly string[]).filter(
            (one) => !isStoredNumeral(one),
        )
        if (outside.length) {
            throw new CodecError(
                `a decimal literal is stored as 'N' in the form DynamoDB returns, and ${outside
                    .map(namedLiteral)
                    .join(
                        ', ',
                    )} ${outside.length === 1 ? 'is' : 'are'} not: it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
            )
        }
    }

    return codecOfTerm<T, AttributeValue>(term)
}

/**
 * A literal's alternatives, indexed by the base that carries them — {@link Literal}'s five variants.
 *
 * **`ℓ` is homogeneous at the base**, and the check is what narrows: a loop that tests each element
 * and then spreads the array teaches the checker nothing, so it ends in a cast. A type predicate is
 * the same test with the narrowing kept, and the count is how the refusal survives — `filter` drops
 * what fails, so a shorter answer is an alternative that was not this base's.
 *
 * Non-emptiness is a throw and not a refusal: every caller checks it first, so that the message can
 * name the constructor the caller wrote.
 */
const literalTerm = (
    base: LiteralBase,
    allowed: readonly LiteralValue[],
): Literal => {
    const [first, ...rest] = allowed
    if (first === undefined) {
        throw new Error(
            `\`${base}()\` names no alternative, and every caller refuses that first`,
        )
    }
    const wrong = (): never => {
        const outside = allowed.filter(
            (one) => shapeOf(one) !== literalShape[base],
        )
        throw new CodecError(
            `\`${base}(...)\` admits ${literalShape[base]} values, and ${outside
                .map(namedLiteral)
                .join(', ')} ${outside.length === 1 ? 'is' : 'are'} not one`,
        )
    }
    const tail = <T extends LiteralValue>(
        is: (one: LiteralValue) => one is T,
    ): readonly T[] => {
        const kept = rest.filter(is)
        return kept.length === rest.length ? kept : wrong()
    }
    switch (base) {
        case 'string':
        case 'decimal': {
            if (typeof first !== 'string') return wrong()
            const ls = tail((one): one is string => typeof one === 'string')
            return { kind: 'literal', base, ls: [first, ...ls] }
        }
        case 'number': {
            if (typeof first !== 'number') return wrong()
            const ls = tail((one): one is number => typeof one === 'number')
            return { kind: 'literal', base, ls: [first, ...ls] }
        }
        case 'boolean': {
            if (typeof first !== 'boolean') return wrong()
            const ls = tail((one): one is boolean => typeof one === 'boolean')
            return { kind: 'literal', base, ls: [first, ...ls] }
        }
        case 'binary': {
            if (!(first instanceof Uint8Array)) return wrong()
            const ls = tail(
                (one): one is Uint8Array => one instanceof Uint8Array,
            )
            return { kind: 'literal', base, ls: [first, ...ls] }
        }
    }
}

/**
 * A caller's {@link Refinement}, asked of a value that arrived from outside its type.
 *
 * **One cast, and it is the same crossing {@link accepts} makes.** `Refinement.is` is published as
 * `(value: never) => boolean`, because a refinement's input type is existential at this position:
 * the caller wrote the predicate at the codec's held type, and the question here is whether an
 * `unknown` belongs to that type. The type cannot prove it, because that is the question. So the
 * cast is written once, where the crossing happens, rather than at each caller.
 */
const satisfies = (q: Refinement, value: unknown): boolean =>
    q.is(value as never)

/**
 * §3 `(refine)`'s `q`, run: whether a value satisfies a {@link Predicate}.
 *
 * `members` is `inL`, compared the way the base compares. `each` is `liftQ`: the value is a `Set`
 * and every element satisfies the element's predicate. `closure` is the caller's function.
 */
export const holds = (q: Predicate): ((value: unknown) => boolean) => {
    switch (q.kind) {
        case 'members': {
            const ls: readonly LiteralValue[] = q.literal.ls
            return (value) => ls.some((one) => sameLiteral(one, value))
        }
        case 'each': {
            const element = holds(q.of)
            return (value) => value instanceof Set && [...value].every(element)
        }
        case 'closure':
            return (value) => satisfies(q.q, value)
    }
}

/** …and why a value does not, naming the element that failed where the predicate is `each`. */
const refusedBy = (q: Predicate, value: unknown): CodecError => {
    switch (q.kind) {
        case 'members': {
            const ls: readonly LiteralValue[] = q.literal.ls
            return new CodecError(
                `${namedLiteral(value)} is not one of ${ls
                    .map(namedLiteral)
                    .join(', ')}`,
            )
        }
        case 'each': {
            if (!(value instanceof Set)) {
                return new CodecError(
                    `${describeShape(value)} is not a \`Set\`, and a set is written from one — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                )
            }
            // labelled where it failed, as `every` labels a list: the position is the subject
            const elements = [...value]
            const at = elements.findIndex((one) => !holds(q.of)(one))
            return refusedBy(q.of, elements[at]).under(at)
        }
        case 'closure':
            return new CodecError(`${JSON.stringify(value)} is not ${q.q.what}`)
    }
}

/** The wire set and the element member a set base stores — four bases onto three wire sets. */
const setWire: {
    readonly [B in SetBase]: readonly ['S' | 'N' | 'B', 'SS' | 'NS' | 'BS']
} = {
    string: ['S', 'SS'],
    number: ['N', 'NS'],
    decimal: ['N', 'NS'],
    binary: ['B', 'BS'],
}

/**
 * The one tag a `dunion` option answers to, read off the option's own `d` field.
 *
 * `discriminatedUnion` refuses an option that does not name `d` with a one-valued literal at
 * `string`, `number` or `decimal`, so the throw below is that invariant and not a case a
 * declaration can reach. `readTag` reads a stored tag back as text, so a numeric tag is its text.
 */
export const variantTag = (d: string, option: Term): string => {
    const field = option.kind === 'object' ? option.body.fields[d] : undefined
    const t = field?.mark === 'req' ? field.t : undefined
    if (
        t?.kind !== 'literal' ||
        t.base === 'boolean' ||
        t.base === 'binary' ||
        t.ls.length !== 1
    ) {
        throw new CodecError(
            `a discriminated union's options each name '${d}' with a one-valued literal, and this option does not. \`discriminatedUnion\` refuses that at the declaration, so this term was not built by it`,
        )
    }
    return String(t.ls[0])
}

/**
 * The two halves a term denotes, with neither half's type known.
 *
 * A term does not carry the TypeScript type its codec has — `{ kind: 'string' }` says `S` and says
 * nothing about `string` — so {@link denote} answers in the erased pair and {@link codecOfTerm}
 * puts the type back on, once, where the constructor knows it.
 */
export type Pair = {
    readonly encode: (value: never) => Result<AttributeValue>
    readonly decode: (attribute: AttributeValue) => Result<unknown>
}

/**
 * §3's ground terms, as one construction — the model's `pointCodec` under this library's word.
 *
 * A prism pair, which `src/` has no name of its own for; §3 calls what it builds a *ground term*,
 * so that is the word here.
 *
 * A payload carried between a value constructor and an attribute constructor, both prisms. The
 * prism laws are §2's laws in disguise, which is why `lawful_pointCodec` needs no hypothesis about
 * either side beyond the member it stamps: `out_into` is the round trip **(R)** and `into_out` is
 * canonizability **(C)**.
 *
 * The shape test is `accepts`', not a second one: `shapeOf` is the function that row calls, so
 * the two cannot drift into disagreeing about what a string is.
 */
export const groundCodec = (
    shape: Shape,
    member: AttributeName,
    noun: string,
    writes: string,
): Pair => ({
    encode: (value) =>
        shapeOf(value) === shape
            ? carrying(member, value as never)
            : new CodecError(
                  `${describeShape(value)} is not ${noun}, and \`${shape}\` writes ${writes} — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
              ),
    decode: (attribute) => expect(member, attribute),
})

/**
 * **A pair between a value shape and a member, with the payload transformed on the way.**
 *
 * The model calls this `carriedCodec`, and so does this file: `carrying` is already the word here
 * for building an attribute out of a payload, and this is the codec that word describes.
 * {@link groundCodec} is the degenerate case, where the payload passes through untouched.
 *
 * The transform is the whole of what distinguishes the products from each other. `array` and
 * `record` hand it {@link every}, a traversal — the model's `entrywise` — and differ only in what
 * they traverse. `tuple` aligns first. `object` guards and filters first. `set` is the one product
 * that is not an instance, because its attribute side is a choice among three wire sets rather than
 * one member.
 */
export const carriedCodec = <Payload, Written, Read>(
    holds: (value: unknown) => value is Payload,
    member: AttributeName,
    refuse: (value: unknown) => CodecError,
    into: (payload: Payload) => Result<Written>,
    outOf: (carried: Read) => Result<unknown>,
): Pair => ({
    // two casts, one reason: `member` is a *value* here, so the type checker cannot tie it to the
    // payload types either side of it. The model takes the two prisms as arguments and gets that
    // tie for free; this takes a member and a pair of transforms, and the row is what says they
    // agree — `'L'` with a list, `'M'` with a map
    encode: (value: unknown) =>
        holds(value)
            ? andThen(into(value), (written) =>
                  carrying(member, written as never),
              )
            : refuse(value),
    decode: (attribute) =>
        andThen(expect(member, attribute), (carried) => outOf(carried as Read)),
})

/**
 * §4's body: the declared fields and the policy for everything else, as one pair over a bare item.
 *
 * The model's `objectCodecCore`, and `objectCodecCore_eq` is the lemma. It is *not* a
 * {@link carriedCodec} instance on its own — it writes a bare map rather than an `M` — which is
 * exactly the distinction `.item` exposes: §5 says a codec writes the attributes of that codec, and
 * `object` writes the members of `object` like any other, offering `.item` for the one place that
 * writes no map. So `denote`'s row wraps this in the member and `.item` takes it as it is.
 *
 * **A field's mark is read here and nowhere else.** `fieldSem` in the model is the function that
 * turns `Field` into a presence rule; here it is the three-way `mark`, read once per field per
 * direction, and there is no second place that asks what `optional` means.
 *
 * Whether a stand-in must be *copied* per read is settled once, at the declaration, rather than
 * asked per item: {@link copiedPerRead} is a fact about this runtime and not about the term, which
 * is why it lives in the compiled form and not in {@link Field}.
 */
export const bodySem = ({ fields: of, rest }: Body): ItemPair => {
    const declared: Declared[] = []
    for (const name in of) {
        const field = of[name]
        if (field === undefined) continue
        declared.push({
            name,
            codec: codecOfTerm(field.t),
            optional: field.mark === 'optional',
            absent:
                field.mark === 'fallback'
                    ? { value: field.v, copy: copiedPerRead(field.v) }
                    : undefined,
        })
    }
    const restCodec = typeof rest === 'string' ? undefined : codecOfTerm(rest.t)
    return {
        encode: (held) => {
            const out: Record<string, AttributeValue> = {}
            for (const { name, codec: attribute, optional } of declared) {
                const value = held[name]
                if (value === undefined) {
                    if (optional) continue
                    return new CodecError(
                        `'${name}' is required and was not given`,
                    )
                }
                const written = attribute.encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
            }
            if (restCodec) {
                for (const name in held) {
                    const value = held[name]
                    if (name in of || value === undefined) continue
                    const written = restCodec.encode(value as never)
                    if (failed(written)) return written.under(name)
                    out[name] = written
                }
            }
            return out
        },
        /**
         * Attributes the spec does not mention are dropped. A row written before a field existed
         * decodes without it, which is why `encode ∘ decode` is not identity on items.
         */
        decode: (item) => {
            const out: Record<string, unknown> = {}
            for (const {
                name,
                codec: attributeCodec,
                optional,
                absent,
            } of declared) {
                const attribute = item[name]
                if (attribute === undefined) {
                    if (optional) continue
                    if (absent) {
                        out[name] = absent.copy
                            ? structuredClone(absent.value)
                            : absent.value
                        continue
                    }
                    return new CodecError(
                        `'${name}' is required and the item has no such attribute`,
                    )
                }
                const read = attributeCodec.decode(attribute)
                if (failed(read)) return read.under(name)
                out[name] = read
            }
            if (rest === 'drop') return out
            for (const name in item) {
                if (name in of) continue
                if (!restCodec) {
                    return new CodecError(
                        `'${name}' is not an attribute this codec declares; the schema and the data have drifted apart`,
                    )
                }
                const read = restCodec.decode(item[name] as AttributeValue)
                if (failed(read)) return read.under(name)
                out[name] = read
            }
            return out
        },
    }
}

/**
 * §3 `(held)`: a pair reached through an adapter — the model's `Codec.through`.
 *
 * The word is `held`'s, because that is what this library calls the term. `f` sits in front of `e`
 * and `g` sits behind `p`, so the adapter changes what the value is *held* as and leaves what it is
 * *stored* as alone. §5 turns on the asymmetry: the readable side sees through it and the writable
 * one cannot, which is the one row where the two sides of a term part in that direction.
 *
 * **A throw is a refusal like any other.** The two functions are the caller's, so either may throw
 * rather than return, and the guard is what makes that a value the way §2's error channel is one
 * rather than an exception escaping a codec.
 */
export const heldThrough = (
    inner: AnyCodec,
    adapt: {
        readonly encode: (value: never) => unknown
        readonly decode: (held: never) => unknown
    },
): Pair => {
    const guarded =
        <A, B>(convert: (value: A) => B, direction: 'writing' | 'reading') =>
        (value: A): Result<B> => {
            try {
                return convert(value)
            } catch (thrown) {
                return new CodecError(
                    `the conversion for ${direction} this attribute threw: ${
                        thrown instanceof Error
                            ? thrown.message
                            : String(thrown)
                    }`,
                )
            }
        }
    const into = guarded(adapt.encode, 'writing')
    const outOf = guarded(adapt.decode, 'reading')
    return {
        encode: (value) =>
            andThen(into(value), (held) => inner.encode(held as never)),
        decode: (attribute) => {
            // `failed` rather than `andThen`, because a {@link Pair}'s read answers `unknown` and
            // `Result<unknown>` *is* `unknown` — the failure channel is not visible in that type,
            // so the test has to be made rather than inferred
            const read = inner.decode(attribute)
            return failed(read) ? read : outOf(read as never)
        },
    }
}

/**
 * §3 `(refine)`: a pair narrowed by a predicate on **values** — the model's `Codec.restrict`.
 *
 * Both halves gate on the *same* predicate applied to the same value, which is what makes each law
 * restrict rather than need re-proving. The read side asks *after* the base has read, because §5
 * says `q` tests the value a read **produces**: no set of attributes bounds it, so the gate cannot
 * be moved in front of the base's own row.
 *
 * **The predicate runs on the way in too**, which is what closed the last row of
 * `admits ⟺ encode`. It used to run on `decode` only, on the argument that a row is data somebody
 * else wrote while an argument is typed — and the type is the narrow one, so a value failing the
 * predicate arrived past it. That is true of every gate here and was not a reason to skip this one:
 * a brand whose predicate is not checked is a brand a cast can forge, and admission ran the
 * predicate itself all along.
 */
export const restrict = (
    base: AnyCodec,
    holds: (value: never) => boolean,
    refuse: (value: unknown) => CodecError,
): Pair => ({
    encode: (value) => (holds(value) ? base.encode(value) : refuse(value)),
    decode: (attribute) => {
        const read = base.decode(attribute)
        return failed(read) || holds(read as never) ? read : refuse(read)
    },
})

/**
 * §3 `(union)`'s resolution: which option an input is for, and the pair that follows.
 *
 * The model's `altCodec` over `select`, and `lawful_altCodec` is the lemma. It takes the
 * options already read as {@link Option} records because two views need the same answer —
 * the attribute pair `denote` returns, and the *item* pair an all-object union also offers —
 * and a sum resolved twice by two copies of one rule is the drift this phase exists to end.
 * So the resolution is the return value and the pair is one of its uses.
 */
export const altSem = (
    all: readonly Option[],
): {
    readonly pair: Pair
    readonly only: <A>(
        survives: (option: Option) => boolean,
        named: string,
        through: (option: Option) => Result<A>,
    ) => Result<A>
    readonly onlyAdmitting: <A>(
        survives: (option: Option) => boolean,
        named: string,
        value: unknown,
        through: (option: Option) => Result<A>,
    ) => Result<A>
    readonly naming: (
        label: string,
        names: ReadonlySet<string> | undefined,
    ) => string
} => {
    /** Every option, for a message that says what was available. */
    const listed = () => all.map((option) => option.describe).join(' | ')

    const ambiguous = (first: Option, second: Option, what: string) =>
        new CodecError(
            `${first.describe} and ${second.describe} both admit ${what}; these options cannot be told apart, so give them a discriminator and use discriminatedUnion`,
        )

    const unmatched = (what: string) =>
        new CodecError(`no option admits ${what}; options are ${listed()}`)

    /**
     * What was being matched, named by the names it had.
     *
     * The names are the actionable half of both messages — "no option admits this item" says nothing
     * a reader can act on, while the set of attributes it turned up with says exactly which option
     * was expected to declare them. A value that is not a record has no names, and then there is
     * nothing to add.
     */
    const naming = (label: string, names: ReadonlySet<string> | undefined) =>
        names
            ? `${label} with attributes ${[...names].map((x) => `'${x}'`).join(', ') || '(none)'}`
            : label

    /**
     * The one option this could be, or why there is not exactly one.
     *
     * Two steps, and both are needed. The **kind** filter comes first and is the only step that can
     * be trusted on its own: an option that takes a string cannot be the one for a number, and an
     * option that writes `S` cannot read an `N`. If it leaves one option, that option *is* the answer
     * — so a failure past that point is its error, reported as itself rather than swallowed into "no
     * option matched".
     *
     * If it leaves several, they are **tried**, and exactly one must succeed. The first step alone
     * would not do: `string('A')` and `string('B')` take the same kind of value and are never
     * ambiguous.
     *
     * **This is the read side only now.** Attempting was once the only thing available on both
     * sides, because encoding did not validate and a permissive option would "succeed" on a value
     * only its neighbour meant. The write side decides instead — {@link onlyAdmitting} — and this
     * one still attempts because there is no `AdmA` in `src/` to decide a stored attribute with.
     */
    const only = <A>(
        survives: (option: Option) => boolean,
        named: string,
        through: (option: Option) => Result<A>,
    ): Result<A> => {
        const candidates = all.filter(survives)
        if (candidates.length === 0) return unmatched(named)
        if (candidates.length === 1) return through(candidates[0] as Option)

        let first: Option | undefined
        let carried: Result<A> | undefined
        for (const option of candidates) {
            const attempt = through(option)
            if (failed(attempt)) continue
            if (first) return ambiguous(first, option, named)
            first = option
            carried = attempt
        }
        return first ? (carried as Result<A>) : unmatched(named)
    }

    /**
     * The same, **decided rather than attempted** — the write side only.
     *
     * `only` finds its answer by encoding through every survivor and keeping the one that did not
     * fail. That was the only thing available while `encode` did not validate, and it is why this
     * union used to report ambiguity that was not there: a resolver that decides by *trying*
     * inherits every looseness of everything it tries, and then reports the result as a property of
     * the declaration. `union([held(decimal, dateAdapter), string])` could not encode a `Date` for
     * exactly that reason, and the fix was `string` refusing one.
     *
     * {@link accepts} is the decision. §3's `Adm`, proved exact at all 21 constructors, and
     * `codec.laws.spec.ts` holds `accepts(c, v) ⟺ !failed(c.encode(v))` over its whole table —
     * so on the values in play this selects the same option `only` would have found by attempting,
     * and says *why* rather than discovering it. Two differences that are improvements rather than
     * equivalences: a `held` option whose adapter **throws** on a value it does not own is filtered
     * out here instead of propagating, and an ambiguity is reported without first writing one of
     * the two answers.
     *
     * **The read side keeps attempting**, because there is nothing to decide with: the model has
     * `AdmA` on the attribute side and `src/` has no port of it. That asymmetry is the reason this
     * is a second function rather than a flag on the first.
     */
    const onlyAdmitting = <A>(
        survives: (option: Option) => boolean,
        named: string,
        value: unknown,
        through: (option: Option) => Result<A>,
    ): Result<A> => {
        const candidates = all.filter(
            // admission **is** "encode succeeds", which is the law `codec.laws.spec.ts` states
            // over the whole table. Asking the option's own encode terminates: it is one level
            // down, and the direction that would not is an `encode` consulting admission
            (option) => survives(option) && accepts(option.codec, value),
        )
        if (candidates.length === 0) return unmatched(named)
        if (candidates.length > 1) {
            return ambiguous(
                candidates[0] as Option,
                candidates[1] as Option,
                named,
            )
        }
        return through(candidates[0] as Option)
    }

    /** Which options a value could be for: an object option by its names, anything else by kind. */
    const forValue =
        (shape: Shape | undefined, names: ReadonlySet<string> | undefined) =>
        (option: Option) =>
            option.declares
                ? shape === 'map' && !!names && namesFit(option, names)
                : !option.carries || !shape || option.carries.includes(shape)

    type T = unknown

    /** The same, from the stored side, where the member carried is what filters. */
    const read = (attribute: AttributeValue): Result<T> => {
        const member = memberOf(attribute)
        const carriedMap =
            member === 'M'
                ? (attribute as { readonly M: AttributeMap }).M
                : undefined
        const names = carriedMap ? namesOf(carriedMap) : undefined
        return only(
            (option) =>
                option.declares
                    ? member === 'M' && !!names && namesFit(option, names)
                    : option.member === undefined ||
                      member === undefined ||
                      option.member === member,
            naming('this attribute', names),
            (option) => option.codec.decode(attribute) as Result<T>,
        )
    }
    const write = (value: unknown): Result<AttributeValue> => {
        const held = asRecord(value)
        return onlyAdmitting(
            forValue(shapeOf(value), held ? namesOf(held) : undefined),
            naming('this value', held ? namesOf(held) : undefined),
            value,
            (option) => option.codec.encode(value as never),
        ) as Result<AttributeValue>
    }

    return {
        pair: { encode: write as Pair['encode'], decode: read },
        only,
        onlyAdmitting,
        naming,
    }
}
/**
 * §3 `(dunion)`: the tag chooses the variant, and the choice is a **lookup** rather than an attempt.
 *
 * The model's `OptionSem.byTag`, and `lawful_dunionCodec` is the lemma. Its (U) is a theorem rather
 * than an obligation, which §5 states as the reason `(dunion)` is not a second kind of sum: reading
 * a label off an input is something an option cannot be wrong about.
 *
 * `Object.hasOwn` and not a truthiness test: `byVariant` is a plain object, so a tag of `toString`
 * or `constructor` reaches `Object.prototype` and comes back as a variant that has no `decode`. The
 * tag is read off the *stored* item, so that is reachable from data this library does not control,
 * and it surfaced as a raw `TypeError` — the one thing every other failure here is careful not to
 * be.
 */
export const byTagSem = <V>(
    discriminator: string,
    byVariant: Readonly<Record<string, V>>,
): {
    readonly pick: (tag: string) => Result<V>
    readonly tagOf: (item: Readonly<Record<string, unknown>>) => Result<string>
} => ({
    pick: (tag) => {
        const variant = Object.hasOwn(byVariant, tag)
            ? (byVariant[tag] as V | undefined)
            : undefined
        return (
            variant ??
            new CodecError(
                `'${tag}' is not a variant of '${discriminator}'; expected ${Object.keys(
                    byVariant,
                )
                    .map((x) => `'${x}'`)
                    .join(', ')}`,
            )
        )
    },
    tagOf: (item) => {
        const tag = item[discriminator]
        return tag === undefined
            ? new CodecError(
                  `'${String(discriminator)}' chooses the variant and was not given`,
              )
            : String(tag)
    },
})

/**
 * The two directions over a bare attribute map — a term's reading with the top-level `M` taken off.
 *
 * §5's split, as a type: a codec writes the attributes of that codec, and the top-level map belongs
 * to the *view* rather than to the codec. This is the view's half, and `denote`'s rows are that
 * half carried into an `'M'`.
 */
export type ItemPair = {
    readonly encode: (
        held: Record<string, unknown>,
    ) => Result<Record<string, AttributeValue>>
    readonly decode: (
        item: Readonly<Record<string, AttributeValue>>,
    ) => Result<Record<string, unknown>>
}

/**
 * The terms that have a whole-item reading: an object, and a union of objects by tag.
 *
 * Not `untagged`. An undiscriminated union's item reading is built by {@link union} from its
 * resolved options, and `denote`'s `untagged` row asks {@link altSem} for the *attribute* pair, so
 * nothing here needs one.
 */
export type ItemTerm = Extract<Term, { readonly kind: 'object' | 'dunion' }>

/**
 * **One item pair per term, for the life of the term** — {@link codecOfTerm}'s counterpart.
 *
 * Every `object(...)` used to build **two** body pairs and keep both: one in the constructor for
 * `.item`, and a second inside `denote` when the codec was first used. They were separate objects,
 * `item.encode === codec.encode` answered `false`, and nothing said which of the two a caller was
 * running. Both come from here now, so a term has one item reading and the map-writing pair wraps
 * that one.
 *
 * The memo is keyed on the frozen term for the reason `codecOfTerm`'s is: the term is the datum, a
 * pair built from it is a function of it, and the freeze is what makes the key stable rather than
 * probable.
 */
const itemPairs = new WeakMap<ItemTerm, ItemPair>()

export const itemSem = (def: ItemTerm): ItemPair => {
    const built = itemPairs.get(def)
    if (built) return built
    const made = def.kind === 'object' ? bodySem(def.body) : taggedItemSem(def)
    itemPairs.set(Object.freeze(def), made)
    return made
}

/**
 * §3 `(dunion)`'s item reading: the tag chooses the variant, and the variant reads the whole item.
 *
 * **Every variant is an object**, which is why this recurses into {@link itemSem} rather than
 * asking a codec for its `.item`. {@link discriminatedUnion} refuses an option whose `spec` does
 * not name the discriminator with a literal, and only an object codec has a `spec` shaped that way
 * — so a variant's term is an `attributes` term at every tag. The throw below is that invariant,
 * not a case a declaration can reach.
 */
export const taggedItemSem = (
    def: Extract<Term, { readonly kind: 'dunion' }>,
): ItemPair => {
    const byTag: Record<string, ItemPair> = {}
    for (const option of def.options) {
        if (option.kind !== 'object') {
            throw new CodecError(
                `a discriminated union's variants are object codecs, and one option is a \`${option.kind}\`. \`discriminatedUnion\` refuses that at the declaration, so this term was not built by it`,
            )
        }
        byTag[variantTag(def.d, option)] = itemSem(option)
    }
    const { pick, tagOf } = byTagSem(def.d, byTag)
    return {
        encode: (held) =>
            andThen(andThen(tagOf(held), pick), (variant) =>
                variant.encode(held),
            ),
        decode: (item) =>
            andThen(andThen(readTag(item, def.d), pick), (variant) =>
                variant.decode(item),
            ),
    }
}

/**
 * **What a term means**, as one function on the definition.
 *
 * Every constructor's pair comes from here, so there is one description of what a term denotes
 * rather than one per constructor beside a definition that says the same thing. The model's
 * `denote` is this function and the rows below answer to its combinators one for one.
 *
 * **A definition's children are terms, and no row here reaches into a child codec's pair.** Where a
 * row needs one it calls `codecOfTerm`, which memoises on the frozen term and answers the codec
 * that was already built, so recovering a child costs a lookup rather than a construction. The
 * checker holds this rather than a reader: every child position of a `Term` is a `Term`, so
 * `def.elem.encode` is a type error and not a habit to avoid.
 *
 * **There is no `default`, and that is the guard.** Every `Term` kind has a row, so the switch
 * is exhaustive and the type checker knows it — a new kind with no row makes `def` something other
 * than `never` at the end of the switch and stops the build. A thrown default would replace that
 * with a runtime message, which is the weaker of the two and the one a test has to go looking for.
 * It is the same move as `_everyKindHasALevel`: a fact the documents assert, turned into a build
 * error instead of something a reader is asked to re-derive.
 */
export const denote = (def: Term): Pair => {
    switch (def.kind) {
        case 'string':
            return groundCodec('string', 'S', 'a string', "an 'S'")
        case 'boolean':
            return groundCodec('boolean', 'BOOL', 'a boolean', "a 'BOOL'")
        case 'binary':
            return groundCodec('binary', 'B', 'a `Uint8Array`', "a 'B'")
        /**
         * §3 `(array)`: a list carried into an `L`, with the element's pair run entrywise.
         * `arrayCodec_eq` is the lemma, and the traversal is `every` here where the model writes
         * `entrywise` — one word for one concept, and this file already had it.
         *
         * The element's own methods are handed over rather than a closure around them: a closure
         * per call to encode a list is a closure per list in every item written. And `every`
         * iterates whatever is iterable, so a string arrived as its characters until the shape was
         * asked first — which is what the term's `array` row asks, and now what this asks too.
         */
        case 'array': {
            const items = codecOfTerm(def.elem)
            return carriedCodec(
                (value): value is readonly never[] => Array.isArray(value),
                'L',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not an array, and \`array\` writes an 'L' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (list) => every(list, items.encode),
                (carried: readonly AttributeValue[]) =>
                    every(carried, items.decode),
            )
        }
        /**
         * §3 `(record)`: the same construction as `array` at the other product.
         * `recordCodec_e_eq` is the lemma, and the two rows differ in exactly three things — the
         * shape they test, the member they carry, and whether the traversal walks positions or
         * entries. `every` and `everyEntry` are the two traversals; the model writes `entrywise`
         * once and instantiates it twice.
         *
         * `Object.entries('abc')` is `[['0','a'], …]`, so a string was written as a map keyed by
         * index until the shape was asked first. `asRecord` is the test the `record` row uses on
         * both sides, so the two cannot drift about what a plain object is.
         */
        case 'record': {
            const values = codecOfTerm(def.val)
            return carriedCodec(
                (value): value is Record<string, never> =>
                    asRecord(value) !== undefined,
                'M',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not a plain object, and \`record\` writes an 'M' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (held) => everyEntry(held, values.encode),
                (carried: Readonly<Record<string, AttributeValue>>) =>
                    everyEntry(carried, values.decode),
            )
        }
        /**
         * §3 `(tuple)` and `(tuple-tail)` in one row, which is what the constructor carries.
         * `tupleCodec_eq` is the lemma and `align_eq_some` is what settles the tail: the arity
         * test comes **before** the positions, because a list of the wrong length has no
         * entrywise reading at all. `align` is the model's name for that step; here it is the two
         * length tests, and they are the same fact — a tuple with a tail aligns at *at least* its
         * fixed arity, one without at exactly it.
         *
         * A `Uint8Array` of the right length has the right `length` and is not a tuple, which is
         * what the length tests alone could not say. The term's `tuple` row asks `Array.isArray`
         * before it counts, and so does this, which is what makes the arity messages mean what
         * they say.
         */
        case 'tuple': {
            const items = def.elems.map((element) => codecOfTerm(element))
            const tail = def.tail
            /** `align`: the arity test, which comes before any position is read. */
            const aligned = (
                length: number,
                say: (arity: number) => string,
            ): CodecError | undefined =>
                (tail ? length < items.length : length !== items.length)
                    ? new CodecError(`${say(items.length)}, found ${length}`)
                    : undefined
            const atLeast = tail ? 'at least ' : ''
            const tailItems = tail ? codecOfTerm(tail) : undefined
            const at = (index: number) =>
                items[index] ?? (tailItems as AnyCodec)
            return carriedCodec(
                (value): value is readonly never[] => Array.isArray(value),
                'L',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not an array, and \`tuple\` writes an 'L' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (held) =>
                    aligned(
                        held.length,
                        (arity) => `expected ${atLeast}${arity} elements`,
                    ) ?? every(held, (one, index) => at(index).encode(one)),
                (carried: readonly AttributeValue[]) =>
                    aligned(
                        carried.length,
                        (arity) => `expected a list of ${atLeast}${arity}`,
                    ) ?? every(carried, (one, index) => at(index).decode(one)),
            )
        }
        /**
         * §3 `(set)`, and the one product that is **not** a {@link carriedCodec}. The model says
         * why: its attribute side is a choice among three wire sets rather than one member, so
         * there is no single `A` prism to carry a payload into. `setCodec_restrict` is the lemma
         * that keeps `refine` and a literal readable through — a restriction of the elements is a
         * restriction of the set, and the two write the same attribute.
         *
         * Which set follows from the base that indexes the term, and the element's pair is the
         * base's own. A restricted element is a `refine` around this row, never inside it.
         *
         * **Empty is refused in both directions, and the read side is the one that matters.**
         * DynamoDB never stores an empty `SS`, so an item carrying one was written by something
         * else; decoding it would hand back a value this codec's own `encode` refuses, which is
         * the pair's two halves disagreeing about what it holds — **(C)** failing.
         *
         * `value.size` is `undefined` on anything that is not a `Set`, so `=== 0` was false for a
         * string and `[...value]` then spread it into its characters: `string.set()` wrote
         * `{ SS: ['a','b','c'] }` for `'abc'`. The `set` row asks `instanceof Set` first.
         */
        case 'set': {
            const inner = codecOfTerm({ kind: def.base })
            const [member, setMember] = setWire[def.base]
            const carried = (value: unknown): Result<string | Uint8Array> =>
                andThen(
                    inner.encode(value as never),
                    (written) =>
                        (written as Record<string, unknown>)[member] as
                            | string
                            | Uint8Array,
                )
            return {
                encode: (value: unknown) =>
                    !(value instanceof Set)
                        ? new CodecError(
                              `${describeShape(value)} is not a \`Set\`, and a ${setMember} is written from one — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                          )
                        : value.size === 0
                          ? new CodecError(
                                `DynamoDB has no empty ${setMember}; omit the attribute or use array(...)`,
                            )
                          : andThen(every([...value], carried), (written) =>
                                // sorted so what is stored does not depend on insertion order;
                                // deduplicated already, because a `Set` is
                                carrying(
                                    setMember,
                                    [...new Set(written)].sort() as never,
                                ),
                            ),
                decode: (attribute) =>
                    andThen(
                        andThen(expect(setMember, attribute), (members) =>
                            (members as readonly unknown[]).length === 0
                                ? new CodecError(
                                      `DynamoDB has no empty ${setMember}, so this attribute was not written by it; a set this codec would refuse to write is not one it can read`,
                                  )
                                : every(members as readonly unknown[], (raw) =>
                                      inner.decode(
                                          carrying(member, raw as never),
                                      ),
                                  ),
                        ),
                        (read) => new Set(read),
                    ),
            }
        }
        /**
         * §4's object: {@link bodySem} carried into an `M`. The row is the wrapper and the body is
         * the content, which is the split §5 states — a codec writes the attributes of that codec,
         * and `.item` is the one place that writes no map.
         */
        case 'object': {
            const body = itemSem(def)
            return carriedCodec(
                (value): value is Record<string, unknown> =>
                    asRecord(value) !== undefined,
                'M',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not a plain object, and an object writes an 'M' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                body.encode,
                (carried: Readonly<Record<string, AttributeValue>>) =>
                    body.decode(carried),
            )
        }
        /** §3 `(held)`. `lawful_through` is the lemma; the adapter is data the term carries. */
        case 'held':
            return heldThrough(codecOfTerm(def.inner), {
                encode: def.f,
                decode: def.g,
            })
        /** §3 `(refine)`. `lawful_restrict` is the lemma; `q` is data the term carries. */
        case 'refine':
            return restrict(codecOfTerm(def.inner), holds(def.q), (value) =>
                refusedBy(def.q, value),
            )
        /**
         * §3 `(legacy)`: the current reading, extended by an older one — the model's
         * `Codec.extendRead`, and `lawful_extendRead` is the lemma. The write side is untouched,
         * which is the whole of what makes it a migration rather than a union: `legacy` adds no
         * way to *write*, only a second way to read.
         *
         * The current encoding is tried first and on its own, so the path every row written since
         * the migration takes allocates nothing — no `[current, ...older]` to walk and no list of
         * reasons collected for a failure that did not happen.
         *
         * §3 `(legacy)`'s first premise, `ran(r) ⊆ dom(e)`, is checked here and nowhere earlier:
         * `older` is a function, so what it returns is known only once it has answered. Without
         * the check the row decodes and the write-back refuses, which is **(C)** broken at the
         * migrated row and reported at the next write instead of at this read.
         */
        case 'legacy': {
            const current = codecOfTerm(def.inner)
            const older = def.r
            return {
                encode: (value) => current.encode(value),
                decode: (attribute) => {
                    const read = current.decode(attribute)
                    if (!failed(read)) return read
                    const older_ = older(attribute)
                    if (!failed(older_)) {
                        if (!accepts(current, older_)) {
                            return new CodecError(
                                `an older encoding read this attribute as ${describeShape(older_)}, which the current encoding cannot write. A migration has to land on values that can be written back, or the row reads and then refuses on the way out`,
                            )
                        }
                        return older_
                    }
                    return new CodecError(
                        `no encoding could read this attribute; tried the current one and one older: ${read} | ${older_}`,
                    )
                },
            }
        }
        /**
         * §3 `(nullable)`: the null point adjoined, **unless the subterm already owns it** —
         * `Codec.withNull` with the guard, and `lawful_withNull` is the lemma.
         *
         * Without the guard the wrapper's `NULL` branch shadows the subterm and **(R)** fails on a
         * term the specification proves lawful: `nullable(held(nullable(string), adapter))`, where
         * the adapter maps `'SENTINEL'` to `null`, writes `{ NULL: true }` for `'SENTINEL'` and
         * reads back `null`. The value written is not the value read.
         *
         * Where the guard does *not* fire, null-honesty is a theorem rather than an assumption: an
         * inner that wrote `⟨NULL, ∗⟩` would read it straight back by **(R)** and so would own the
         * point, and one that read some attribute to `null` would write the point by **(C)** and
         * own it again. §3's guard is what turned two premises into consequences.
         *
         * **The question is asked once, at first use rather than at construction**, because
         * `lazy` exists: a recursive declaration forces its thunk when probed, and at
         * module-evaluation time that is a reference to a binding that does not exist yet.
         */
        case 'nullable': {
            const inner = codecOfTerm(def.inner)
            let owns: boolean | undefined
            const ownsInner = () => (owns ??= ownsNull(inner))
            return {
                encode: (value) =>
                    value === null && !ownsInner()
                        ? carrying('NULL', true)
                        : inner.encode(value),
                decode: (attribute) =>
                    memberOf(attribute) === 'NULL' && !ownsInner()
                        ? null
                        : inner.decode(attribute),
            }
        }
        /**
         * §3 `(lazy)`: the pair of the term the thunk resolves to, forced on use.
         *
         * The row recurses on the **value**, never on the term, which is what makes it terminate:
         * `def.get()` is forced once per level of the value, and a value is finite. The model's
         * `Term.lazy` carries a plain `Term` rather than a thunk — a closure adds no constructible
         * term and defeats the termination checker — so the two constructors are not the same
         * object, and §5 keeps the document's `lazy` unanalysable for that reason while the model's
         * answers the subterm's.
         */
        case 'lazy':
            return {
                encode: (value) => codecOfTerm(def.get()).encode(value),
                decode: (attribute) => codecOfTerm(def.get()).decode(attribute),
            }
        /**
         * §3 `(custom)`: the pair the term carries, returned. The row does not describe the set
         * the codec admits — the two functions *are* what decides it, which is the model's own
         * move at `custom` and the reason admission asks them rather than reading a row.
         */
        case 'custom':
            return { encode: def.ce, decode: def.cp }
        /**
         * §3 `(union)`: the sum, resolved by unique admission. `lawful_altCodec` is the lemma and
         * `altSem` is the resolution — one rule, serving both the attribute pair here and the item
         * pair an all-object union also offers.
         *
         * **The write side decides and the read side attempts**, and that asymmetry is the model's.
         * Admission is `Adm`, proved exact at every constructor, so the writable side selects by
         * asking rather than by trying; the readable side has no `AdmA` in this library to ask, so
         * it tries. §5 says the same thing from the other end — the two families are independent,
         * and a pair separated on one side only is not separated.
         */
        case 'union':
            return altSem(def.options.map(optionOfTerm)).pair
        /**
         * §3 `(dunion)`: the variants' lookup, carried into an `M`. The tag is read off the item on
         * both sides — `tagOfV` and `tagOfA` in the model — so neither half attempts a variant it
         * was not sent to.
         */
        case 'dunion': {
            const body = itemSem(def)
            return carriedCodec(
                (value): value is Record<string, unknown> =>
                    asRecord(value) !== undefined,
                'M',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not a plain object, and a discriminated union writes an 'M' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                body.encode,
                (carried: Readonly<Record<string, AttributeValue>>) =>
                    body.decode(carried),
            )
        }
        /**
         * §3 `(opaque)`: the recursive union of everything self-identifying, at whichever numeric
         * policy the term names. `lawful_opaqCodecω` is the lemma, and it is a *theorem* rather
         * than an obligation — the model's `Obligations (.opaq _)` is `True`, which is what makes
         * `opaque` a well-behaved `custom`: the same analysis with the opposite warranty. A
         * `custom` carries a premise its author owes; this carries none, because the calculus
         * proves the laws for it.
         *
         * The pair is this library's own recursion rather than a fixpoint built here, and the row
         * asks it. §5's rows do the same for the same reason: no syntactic set names
         * `opaqCodecω`'s domain, because it recurses on the *input's own depth*.
         */
        case 'opaq': {
            const numbers = def.lossy ? 'lossy' : 'refuse'
            return {
                encode: (value: unknown) => encodeUnknown(value, numbers),
                decode: (attribute) => decodeUnknown(attribute, numbers),
            }
        }
        /**
         * §3 `(literal)`, and it is **not** a sixth ground term: `literalCodec k ls` is
         * `(baseCodec k).restrict (inL k ls)`, the base's pair narrowed to membership of `ℓ`. The
         * base is the index, so the row reaches it by denoting `{ kind: base }` — the five bases
         * are exactly five term kinds.
         *
         * **What the base's own read gate buys, stated where it is now free.** The hand-written
         * row re-checked `isNumeral` before consulting `ℓ`, because `Number` is far more permissive
         * than an `N` — it reads `''`, whitespace, `0x10` and `0b11`, none of which DynamoDB hands
         * back, and membership in `ℓ` does not filter them out: `number(0, 1, 2)` read `{ N: '' }`
         * as `0`. Going through the base means that gate is the base's, asked once, and the row no
         * longer restates it.
         *
         * **At `number` the predicate is on the read value and not on the stored text**, which is
         * the model's `inL` at that base and the one place §5's two literal rules part: a string
         * literal's stored text *is* its value, a numeric literal's is not.
         */
        case 'literal': {
            const allowed: readonly LiteralValue[] = def.ls
            /**
             * `inL`, answering with the **member of `ℓ`** rather than with `true`.
             *
             * The model's is a `Bool` and it does not need to be more: Lean has no reference
             * identity, so two `ByteArray`s with the same octets *are* one value and `p` returning
             * "the value" is unambiguous. JS has two objects for that one value, and returning the
             * declared one is how this language spells the model's answer — a `decode` that handed
             * back the array off the wire would answer with a value the type says is one of `ℓ`
             * and `===` says is not.
             */
            const member = (value: unknown): LiteralValue | undefined =>
                allowed.find((one) => sameLiteral(one, value as LiteralValue))
            const refuse = (value: unknown) =>
                new CodecError(
                    `${namedLiteral(value as LiteralValue)} is not one of ${allowed
                        .map(namedLiteral)
                        .join(', ')}`,
                )
            const base = denote({ kind: def.base })
            return {
                encode: (value: unknown) =>
                    member(value) === undefined
                        ? refuse(value)
                        : base.encode(value as never),
                decode: (attribute) =>
                    andThen(base.decode(attribute), (read) => {
                        const found = member(read)
                        return found === undefined ? refuse(read) : found
                    }),
            }
        }
        /**
         * §3 `(decimal)`. The held set is §1's `Numerals` and not every string: the grammar, the
         * 38 significant digits and the magnitude range are checked on **both** halves.
         * `lawful_decimalCodec` is its own lemma, and the model gives the read side's check the
         * same reason this one has — an ill-formed numeral admitted by `p` would name a value `e`
         * then refuses, and that is **(C)** failing.
         *
         * This is the term whose *value* is text and whose *member* is `N`, which is why §5 has it
         * writing `.str` while storing `N`, and why the write occupancy of `set(decimal)` is a set
         * of strings. The row carries the value across unchanged; only the member differs.
         *
         * `isStoredNumeral` stringifies what it is given — `isStoredNumeral(['1'])` is `true` — so
         * the kind is checked first, which is what the term's `decimal` row says and what this row
         * did not say before it moved here.
         */
        case 'decimal':
            return {
                encode: (value: unknown) =>
                    typeof value === 'string' && isStoredNumeral(value)
                        ? carrying('N', value)
                        : new CodecError(
                              `'${value}' is not a numeral DynamoDB stores unchanged; it accepts at most 38 significant digits, magnitude 1e-130 to 9.9e125, and returns the normalised form (no leading or trailing zeros, no exponent, no '+')`,
                          ),
                decode: (attribute) =>
                    andThen(expect('N', attribute), (carried) =>
                        isStoredNumeral(carried)
                            ? carried
                            : new CodecError(
                                  `'${carried}' is not a numeral in the form DynamoDB stores, so this attribute was not written by it`,
                              ),
                    ),
            }
        /**
         * §3 `(number)`. The held set is `D` — §1's numeral domain — and not every double, so
         * both halves gate. `lawful_numberCodec` is its own lemma rather than the ground one's,
         * and the model's row is written out for the same reason this one is.
         *
         * **The second gate is not redundant**, and the model records the same fact from the same
         * direction: `p` gates on the **round-tripped** value rather than on the stored digits,
         * because `ofDec` rounds and a numeral at the top of the range can round *up* past it.
         * Gating on the digits would admit a value `e` then refuses, which is **(C)** failing.
         * `Number('9.9999999999999999999999999999999999999E+125')` is that numeral here.
         */
        case 'number':
            return {
                // `value.toString()` is defined on everything, so the numeral gate alone accepted
                // the *string* `'5'` as readily as the number `5`. The `number` row asks the
                // kind first; so does this
                // annotated `unknown` rather than left to infer `never` from {@link Pair}: the
                // erased pair says a caller may pass anything, and this row narrows what it is
                encode: (value: unknown) =>
                    typeof value === 'number' && isNumeral(value.toString())
                        ? carrying('N', value.toString())
                        : new CodecError(
                              `${value} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125, and has no NaN or Infinity`,
                          ),
                decode: (attribute) =>
                    andThen(expect('N', attribute), (carried) => {
                        if (!isNumeral(carried)) {
                            return new CodecError(
                                `'${carried}' is not a numeral, so this attribute was not written by DynamoDB`,
                            )
                        }
                        const read = Number(carried)
                        return isNumeral(read.toString())
                            ? read
                            : new CodecError(
                                  `'${carried}' reads back as ${read}, which is outside the range DynamoDB stores`,
                              )
                    }),
            }
        /**
         * **The `NULL` point, and it is not a {@link groundCodec} here.** The reason is this
         * library's and not the model's: `lawful_nullCodec` *is* `lawful_pointCodec`, at the
         * prisms `nullV` and `nullA`, whose payload is `Unit` — "a prism with a trivial payload,
         * which is what makes `null` an instance of the same shape as the three that carry data".
         * So the model has one construction for all four.
         *
         * `groundCodec` is not that construction. It is a shape test and a `carrying`, which
         * carries the *value* into the member — and `NULL`'s payload is the constant `true`, which
         * no value supplies. Being generic over it would mean taking the prism pair as arguments
         * rather than a shape and a member, which is a larger construction than four rows.
         *
         * `encode` checks, though the type already says so: the admissible set is one value and
         * this library owns it, so an unchecked `encode` would write `NULL` for anything that
         * reached it — a pair whose `e` is defined outside its own held set. A literal checks for
         * the same reason.
         */
        case 'null':
            return {
                encode: (value) =>
                    value === null
                        ? carrying('NULL', true)
                        : new CodecError(
                              `${JSON.stringify(value)} is not null, and this codec holds nothing else`,
                          ),
                decode: (attribute) =>
                    andThen(expect('NULL', attribute), () => null),
            }
    }
}

/**
 * A term, as the codec it denotes — the one place the erased pair gets its type back.
 *
 * `denote` answers about the term, and a term does not carry the type its codec has, so exactly one
 * cast stands between the two. It is here rather than at each constructor because twenty-one casts
 * with one reason between them is one reason nobody reads. `build.ts`'s `codec` is still the single
 * construction site: this hands it a pair instead of two hand-written halves.
 */
/**
 * **One codec per term, for the life of the term.**
 *
 * A term is immutable by design and frozen at construction, so a codec built from one is a function
 * of it and can be built once. The tree already assumes identity per term in at least one place —
 * `testing.ts`'s `unionsIn` is "keyed on the *definition* rather than the codec, which is what stops
 * a `lazy` cycle: a recursive entity hands back the codec it already walked, and its def is the same
 * object" — and this makes that true rather than probable. The freeze is what the cache rests on: a
 * mutation fails loudly instead of poisoning it.
 */
const codecs = new WeakMap<Term, AttributeCodec<never, AttributeValue>>()

/**
 * A declaration's term, refusing a §4 field where a term is wanted.
 *
 * `optional(c)` and `fallback(c, v)` denote a `Field`, and no `Term` position accepts one — which
 * the positional guards refuse in the *type* at every site that could go wrong. This is the runtime
 * half, at the one place a child is taken from a codec a caller handed over.
 */
export const termOf = (declared: AnyDeclaration): Term => {
    // a declaration and not a codec, which is what keeps the refusal below reachable: a codec's
    // definition is a term, so a parameter of `AnyCodec` would make this a branch the checker
    // says cannot be taken, and the caller it is for is the one that arrived past a cast
    const def = declared.def
    if ('mark' in def) {
        throw new CodecError(
            `\`${def.mark}\` marks a *field* — whether a name may be absent — and this position takes a term. The type says so too; this call reached here past a cast`,
        )
    }
    return def
}

export const codecOfTerm = <T, A extends AttributeValue>(
    def: Term,
): AttributeCodec<T, A> => {
    const built = codecs.get(def)
    if (built) return built as unknown as AttributeCodec<T, A>
    const made = buildCodec<T, A>(Object.freeze(def))
    codecs.set(def, made as unknown as AttributeCodec<never, AttributeValue>)
    return made
}

const buildCodec = <T, A extends AttributeValue>(
    def: Term,
): AttributeCodec<T, A> =>
    codec<T, A>({
        def,
        ...(denote(def) as Pick<Codec<T, A>, 'encode' | 'decode'>),
        // **Derived, not a second fact.** `arbitrary` and `shrink` are on the published codec, and
        // a caller may reasonably read one — building a second `custom` from the first's generator
        // is what `codec.shrink.spec.ts` does. The definition owns them; this exposes what it owns.
        // Only `custom` carries them, because only `custom` is a term whose generation is the
        // caller's to state: `refine`'s lives in `refined.arbitrary`, where the def readers find it.
        ...(def.kind === 'custom'
            ? {
                  arbitrary: def.arbitrary as
                      | ((rng: Rng, size: number) => T)
                      | undefined,
                  shrink: def.shrink as
                      | ((value: T) => readonly T[])
                      | undefined,
              }
            : {}),
    })

/** Only plain objects round-trip; anything with a prototype loses it. */
const isPlainObject = (value: object) => {
    const prototype = Object.getPrototypeOf(value)
    return prototype === Object.prototype || prototype === null
}

const unrecoverable = (what: string, instead: string) =>
    new CodecError(
        `${what} cannot be stored as an unknown attribute, because decoding could not tell it apart from what it decodes to. ${instead}`,
    )

/**
 * Encodes a value whose type is recoverable from what is stored, and refuses one whose is not.
 *
 * The domain is deliberately narrow, so that `decode ∘ encode = id` holds for everything accepted.
 * Accepted: `null`, `string`, `boolean`, `Uint8Array`, a non-empty `Set` of strings or of binary,
 * arrays, and plain objects — recursively. A `number` only under `'lossy'`; see
 * {@link opaque.Numbers} for why that one cannot be decided here.
 */
export const encodeUnknown = (
    value: unknown,
    numbers: opaque.Numbers,
    /** How many `L`/`M` this value already sits inside. See {@link MAX_DOCUMENT_NESTING}. */
    enclosing = 0,
): Result<AttributeValue> => {
    if (value === null) return carrying('NULL', true)
    if (typeof value === 'string') return carrying('S', value)
    if (typeof value === 'boolean') return carrying('BOOL', value)
    if (value instanceof Uint8Array) return carrying('B', value)

    if (typeof value === 'number') {
        if (!Number.isFinite(value)) {
            return new CodecError(`DynamoDB has no number for ${value}`)
        }
        if (numbers === 'refuse') {
            return unrecoverable(
                'a number',
                "Reading it back is undecidable without a schema: as a `number` it rounds, and as a `string` it re-encodes as `S`, changing the attribute's stored type. Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`.",
            )
        }
        /**
         * **Writing an `N` means writing a numeral.** `Number.isFinite` is not that test: §1's
         * `Carries('N')` is `Numerals`, bounded by 38 significant digits and magnitude
         * `1e-130 … 9.9…e125`, and `5e-324` is a perfectly finite double outside it — the
         * specification's own example of the bound going unchecked.
         *
         * `number` has gated on this since the numeral domain was tightened and `literal` since
         * its `ℓ ⊆ D` premise. `opaque` is the third term that writes an `N` from a JS number and
         * it was checking only that the number existed, which let it write an attribute §1's `𝔸`
         * has no point for. Same obligation, same gate: `ran(e) ⊆ 𝔸`.
         */
        return isNumeral(String(value))
            ? carrying('N', String(value))
            : new CodecError(
                  `${value} is not a number DynamoDB stores: it takes at most 38 significant digits and magnitude 1e-130 to 9.9e125`,
              )
    }

    if (typeof value === 'bigint') {
        return unrecoverable(
            'a bigint',
            'It shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`.',
        )
    }

    if (Array.isArray(value)) {
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            every(value, (x) => encodeUnknown(x, numbers, enclosing + 1)),
            (written) => carrying('L', written),
        )
    }

    if (value instanceof Set) {
        const members = [...value]
        if (members.length === 0) {
            return new CodecError('DynamoDB has no empty set')
        }
        if (members.every((x) => typeof x === 'string')) {
            return carrying('SS', (members as string[]).sort())
        }
        if (members.every((x) => x instanceof Uint8Array)) {
            return carrying('BS', members as Uint8Array[])
        }
        return unrecoverable(
            'a set of numbers',
            'NS decodes as strings, because its members are decimal strings. Use a set of strings, or `array(number)` if the order does not matter to you.',
        )
    }

    if (value instanceof Map) {
        return unrecoverable(
            'a Map',
            'DynamoDB has one map member, `M`, and it decodes as a plain object. Pass an object, or use `record(...)` to state the value type.',
        )
    }

    if (typeof value === 'object') {
        if (!isPlainObject(value)) {
            return unrecoverable(
                `an instance of ${value.constructor?.name ?? 'a class'}`,
                'Only plain objects survive: `M` carries the own enumerable properties and nothing that says how to rebuild the instance. Convert it first — a `Date`, for example, is faithful as an ISO string.',
            )
        }
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            everyEntry(value as Record<string, unknown>, (v, k) =>
                v === undefined
                    ? new CodecError(
                          `'${k}' is undefined, and DynamoDB has no attribute holding undefined. Omit the key, or use \`optional(...)\` on a declared attribute.`,
                      )
                    : encodeUnknown(v, numbers, enclosing + 1),
            ),
            (written) => carrying('M', written),
        )
    }

    return unrecoverable(`a ${typeof value}`, 'No DynamoDB member carries it.')
}

export const decodeUnknown = (
    attribute: AttributeValue,
    numbers: opaque.Numbers,
): Result<unknown> => {
    const member = memberOf(attribute)
    switch (member) {
        case 'NULL':
            return null
        case 'S':
            return attribute[member]

        /**
         * A number exactly when the stored digits are that number's own shortest form, and the raw
         * string otherwise.
         *
         * `String(n)` is the shortest representation that reads back as `n`, so everything this
         * codec wrote comes back as the number it was. Anything wider — `'1.50'`, a
         * thirty-eight-digit decimal, `'9007199254740993'` — was written by something else with more
         * precision than a float holds, and is handed back untouched rather than quietly rounded.
         */
        case 'N': {
            const carried = attribute.N as string
            if (numbers === 'refuse') {
                return unrecoverable(
                    `the stored number '${carried}'`,
                    "Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`.",
                )
            }
            /**
             * The same two gates `number` reads through, and the second is not redundant for
             * the same reason: `Number('9.9…E+125')` rounds *up* past the maximum, so a numeral
             * the store holds can read back as a value nothing here can write.
             *
             * Without them this decoded `{ N: 'abc' }` to `NaN` and `{ N: '1e400' }` to
             * `Infinity` — values its own `encode` refuses, which is **(C)** failing. `Number`
             * reads far more than an `N` carries: `''` and whitespace are `0`, `'0x10'` is `16`.
             */
            if (!isNumeral(carried)) {
                return new CodecError(
                    `'${carried}' is not a numeral, so this attribute was not written by DynamoDB`,
                )
            }
            const read = Number(carried)
            return isNumeral(String(read))
                ? read
                : new CodecError(
                      `'${carried}' reads back as ${read}, which is outside what DynamoDB stores, so it cannot be written again`,
                  )
        }
        case 'B':
        case 'BOOL':
            return attribute[member]

        /**
         * **A member this codec cannot write is a member it cannot read.**
         *
         * `opaque` has no `NS` write path at all — a numeric `Set` is refused, because reading
         * one back is undecidable without a schema. Reading `NS` anyway produced a
         * `Set<string>`, and re-encoding that wrote `SS`: a numeric set attribute silently
         * becoming a string one on a read-modify-write, which is **(MP)** — the law `opaque`'s
         * `N` refusal already exists to protect, one member over.
         *
         * The general form is a corollary of §2 and is proved in the model
         * (`Calculus.Lawful.no_read_without_write`): a codec is a *pair*, and (MP) holds the
         * halves together, so if `e` never produces a member then no attribute carrying it can
         * be in `dom(p)`. Note which law does the work — (C) is satisfied here, the value
         * round-trips, and only the stored type changes. `μ = ⊤` is exactly where (MP) is the
         * only law left watching.
         */
        case 'NS':
            return unrecoverable(
                'a stored set of numbers',
                "`NS` has no counterpart this codec can write — a set of numbers is refused on the way in, because nothing without a schema says which of its members a JS number holds faithfully. Reading it would mean re-encoding it as `SS` and changing the attribute's stored type. Declare the attribute with `number.set()` or `decimal.set()`.",
            )
        case 'SS':
        case 'BS': {
            // as in `set`: encode has no empty set to offer, so decode has none to return
            const members = attribute[member] as readonly unknown[]
            return members.length === 0
                ? new CodecError(
                      `DynamoDB has no empty ${member}, so this attribute was not written by it`,
                  )
                : new Set(members)
        }
        case 'L':
            return every(attribute.L ?? [], (x) => decodeUnknown(x, numbers))
        case 'M':
            return everyEntry(attribute.M ?? {}, (v) =>
                decodeUnknown(v, numbers),
            )
        default:
            return new CodecError('an AttributeValue carrying no member')
    }
}

/**
 * The kind of JavaScript value this codec encodes from, where the kind alone decides.
 *
 * The mirror of `member`, and it exists for a reason worth stating: **encoding does not
 * validate**. A codec's input is typed, so `number` given `'x'` writes `{ N: 'x' }` rather than
 * failing — which means "it encoded" is no evidence that an option was the right one, and a union
 * cannot be resolved by trying each option and seeing what sticks.
 *
 * What it *can* be resolved by is this, first: `union([string, number])` given `'x'` has one option
 * that takes a string. Trying is still needed after it, because two options can take the same kind of
 * value and still be disjoint — `string('A')` and `string('B')` both take a string, and exactly one
 * of them accepts `'A'`.
 *
 * `undefined` means the kind does not decide: `opaque` takes anything, and asking a `lazy` would
 * force the resolution it exists to defer.
 *
 * **Not replaced by `occV`, and the reason is one row.** `occV` reads the term and this reads the
 * codec, so the obvious deletion is to collapse `occV`'s three set families to `'set'` and delete
 * this. Measured at 35 constructors, the two agree at 34. The row that differs is `opaque` at the
 * `refuse` policy: this answers `undefined` and the collapse answers every kind but `number`, which
 * is **sharper and correct** — `opaque.encode(1)` genuinely fails and `opaque('lossy').encode(1)`
 * does not. §5 is where that distinction is drawn: a `⊤` covers *unknown* and *everything*, and the
 * model takes `opaque` as a closed form while this reads it as unknown.
 *
 * So the substitution is not a refactor, it is a behaviour change at the union resolver — an
 * `opaque` option would be filtered by kind where today it is always attempted. Same answer on
 * every union in the corpus, different work and a different message where it is the only option.
 * That is a decision about resolution, not about vocabulary, and it is the owner's.
 */
export const carries = (codec: AnyCodec): readonly Shape[] | undefined => {
    const def = codec.def
    switch (def.kind) {
        case 'refine':
            return carries(codecOfTerm(def.inner))
        case 'legacy':
            return carries(codecOfTerm(def.inner))
        // and this one deliberately does *not* read through. An adapter exists precisely to change
        // the kind of value held — `held(string.set(), ...)` takes an array where `string.set()` takes
        // a `Set` — so the inner codec's answer would be the wrong one. Nothing about the definition
        // says what the outer kind is, so it says so by not answering, and a union falls back to
        // trying it
        case 'held':
            return undefined
        case 'nullable': {
            const inner = carries(codecOfTerm(def.inner))
            return inner && [...inner, 'null']
        }
        case 'union': {
            const shapes = new Set<Shape>()
            for (const variant of def.options) {
                const of = carries(codecOfTerm(variant))
                if (!of) return undefined
                for (const shape of of) shapes.add(shape)
            }
            return [...shapes]
        }
        // the same fact from the other side of the pair, and the two sides do not agree base for
        // base: `decimal(...)` takes a string and writes an `N`, exactly as bare `decimal` does
        case 'literal':
            return [literalShape[def.base]]
        default: {
            const one = carriedBy[def.kind]
            return one && [one]
        }
    }
}

/**
 * **Admission is "encode succeeds"**, and that is the law rather than a shortcut.
 *
 * `codec.laws.spec.ts` states `accepts(c, v) ⟺ !failed(c.encode(v))` over its whole table and pool,
 * both ways, and the reader this replaces existed only because encoding did not validate — a
 * codec's input is typed, so `string.encode(5)` once wrote `{ S: 5 }`. Every row validates now, so
 * the description and the thing described are one question and asking it is the only honest form.
 *
 * **One cast, at the one place it belongs.** A codec's `encode` is typed to its own held set and
 * this takes an `unknown`, which is precisely a value arriving from outside that type — the
 * question being whether it belongs. Four callers share this cast rather than writing it four
 * times.
 *
 * Asking terminates: an option's `encode` is one level below the union's. The direction that would
 * not is an `encode` that consults admission, which is why `opaque` and `custom` always asked their
 * pair instead of describing it.
 */
export const accepts = (codec: AnyCodec, value: unknown): boolean => {
    try {
        return !failed(codec.encode(value as never))
    } catch {
        // **The catch is what makes this equal to the reader it replaces**, and it was found by
        // running the law's own table: `admits` classified the value's shape *before* dispatching,
        // so it answered `false` for a `null` handed to an object codec. `encode` is typed to its
        // held set and reaches for `value.a`, which throws. A `TypeError` here is a value outside
        // the codec's type arriving past that type, which is exactly "not admitted" — Rule 14's
        // boundary: a throw from code that assumes its input becomes a value in the code that does
        // not.
        return false
    }
}

/** …and the read side, which the deleted reader asked of the definition and this asks of the pair. */
export const readsBack = (
    codec: AnyCodec,
    attribute: AttributeValue,
): boolean => {
    try {
        return !failed(codec.decode(attribute as never))
    } catch {
        return false
    }
}

/**
 * Everything about an option that the **term** decides, which is everything but `item`.
 *
 * `denote`'s `untagged` row builds its options from the definition and asks {@link altSem} for the
 * attribute pair, and that pair reads `codec`, `member`, `carries`, `declares` and `requires` — it
 * never reads `item`. So the resolution is a function of the terms, and this is it.
 *
 * **The names come from the fields, not from a `spec`.** An object option's `declares` and
 * `requires` used to be read off `.item.spec`, asking each declared codec whether its definition
 * kind was `optional`. A `spec` is a caller's argument and a `Field`'s `mark` is what that argument
 * became, so the same two sets are read from the term here — `fieldOf` is the function that turns
 * one into the other, and a mark is closed where a definition kind is not. That question had its
 * own predicate, and this was its last caller, so the predicate goes too.
 *
 * That is also what makes this safe on a term-built codec, and the old form was not. It classified
 * an option as an object by finding `.item` on the codec, and only the object a *constructor*
 * returns carries one; a codec built from a term has none, so every object variant would have been
 * classified as a ground option and the union would have resolved by attempting instead of by
 * names. Nothing would have failed loudly. Here the term decides, and every codec has one.
 */
export const optionOfTerm = (def: Term): Option => {
    const codec = codecOfTerm(def)
    if (def.kind !== 'object') {
        return {
            codec,
            member: termMember(def),
            carries: carries(codec),
            item: undefined,
            declares: undefined,
            requires: [],
            describe: def.kind,
        }
    }
    const declares = new Set<string>()
    const requires: string[] = []
    const fields = def.body.fields
    for (const name in fields) {
        declares.add(name)
        if (fields[name]?.mark !== 'optional') requires.push(name)
    }
    return {
        codec,
        member: 'M',
        carries: ['map'],
        item: undefined,
        declares,
        requires,
        describe: `{ ${[...declares]
            .map((name) =>
                fields[name]?.mark === 'optional' ? `${name}?` : name,
            )
            .join(', ')} }`,
    }
}

/** Which kind of value each kind of codec takes, where the kind alone decides. */
export const carriedBy: { readonly [K in Term['kind']]?: Shape } = {
    string: 'string',
    // a decimal is stored as `N` and *held* as a string, which is the whole point of it
    decimal: 'string',
    number: 'number',
    boolean: 'boolean',
    binary: 'binary',
    null: 'null',
    set: 'set',
    array: 'array',
    tuple: 'array',
    record: 'map',
    object: 'map',
    dunion: 'map',
}
