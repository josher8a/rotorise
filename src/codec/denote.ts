/**
 * What a term means: every constructor's pair, and the memo that keeps one per term.
 *
 * the combinator modules' combinators, one for one, plus the two devices the host has and the model
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
    DynamoNumber,
    isNumeral,
    memberOf,
    tooDeeplyNested,
} from './attribute'
import type { Codec } from './build'
import { codec } from './build'
import type {
    AnyCodec,
    AttributeCodec,
    Declared,
    LiteralBase,
    LiteralValue,
    ObjectSlot,
    Option,
    opaque,
    Refinement,
    Shape,
} from './codec'
import type { Result } from './result'
import { andThen, CodecError, every, everyEntry, failed } from './result'
import type {
    Alternatives,
    Body,
    Field,
    Literal,
    Predicate,
    Term,
} from './term'
import {
    alwaysWritten,
    isOpaqueSugar,
    literalAlternatives,
    literalForm,
    occV,
    storedAlternatives,
    member as termMember,
} from './term'
import {
    asRecord,
    copiedPerRead,
    describeShape,
    expect,
    namedLiteral,
    namesOf,
    rendered,
    sameLiteral,
    shapeOf,
} from './value'

/**
 * Which member each base stores a literal in.
 *
 * Injective again. `decimal` was the second base at `N`, and it is an adapter over `number` now
 * rather than a base of its own, so the member recovers the base.
 */
export const literalMember: { readonly [B in LiteralBase]: AttributeName } = {
    string: 'S',
    number: 'N',
    boolean: 'BOOL',
    binary: 'B',
}

/** Which kind of JS value each base's alternatives are — the mirror, and not the same partition. */
export const literalShape: { readonly [B in LiteralBase]: Shape } = {
    string: 'string',
    // a numeric alternative is a `DynamoNumber`, which is what the carrier is
    number: 'number',
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
 * **One literal, or a union of them.** A literal carries one value, so several alternatives are a
 * union of singletons — a certified union, because two singletons with different values are
 * disjoint.
 *
 * The builder stays a builder rather than asking the caller to write the union: measured on a
 * twenty-six alternative discriminator, the hand-written union costs the type checker 26.8 times
 * what this form costs, and this form is flat in the number of alternatives. So the union is what
 * the term is and the call is what the caller writes.
 */
const literalTermOf = (
    base: LiteralBase,
    allowed: readonly LiteralValue[],
): Term => {
    const one = allowed[0]
    if (one !== undefined && allowed.length === 1) return literalTerm(base, one)
    return {
        kind: 'union',
        options: allowed.map((value) => literalTerm(base, value)),
    }
}

/**
 * One literal's value, indexed by the base that carries it — {@link Literal}'s five variants.
 *
 * **`ℓ` is homogeneous at the base**, and the check is what narrows: a `typeof` test the checker
 * reads is the same test as a cast, with the narrowing kept. One value rather than a list, so
 * there is no tail to filter and the refusal names the value it read.
 */
const literalTerm = (base: LiteralBase, value: LiteralValue): Literal => {
    const wrong = (): never => {
        throw new CodecError(
            `\`${base}(...)\` admits ${literalShape[base]} values, and ${namedLiteral(value)} is not one`,
        )
    }
    switch (base) {
        case 'string':
            return typeof value === 'string'
                ? { kind: 'literal', base, v: value }
                : wrong()
        case 'number':
            return value instanceof DynamoNumber
                ? { kind: 'literal', base, v: value }
                : wrong()
        case 'boolean':
            return typeof value === 'boolean'
                ? { kind: 'literal', base, v: value }
                : wrong()
        case 'binary':
            return value instanceof Uint8Array
                ? { kind: 'literal', base, v: value }
                : wrong()
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
 * `members` is `inL`, compared the way the base compares. `closure` is the caller's function.
 */
export const holds = (q: Predicate): ((value: unknown) => boolean) => {
    switch (q.kind) {
        case 'members': {
            const ls: readonly LiteralValue[] = q.literal.ls
            return (value) => ls.some((one) => sameLiteral(one, value))
        }
        case 'closure':
            return (value) => satisfies(q.q, value)
    }
}

/** …and why a value does not. */
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
        case 'closure': {
            // `JSON.stringify` throws on a `bigint` and on a cycle, and a refusal is a value, so the
            // message falls back to the value's shape rather than throwing past the caller
            let named: string
            try {
                named = JSON.stringify(value)
            } catch {
                named = describeShape(value)
            }
            return new CodecError(`${named} is not ${q.q.what}`)
        }
    }
}

/** The wire set that holds an element of each scalar member: `setMember`. */
const setWire = { S: 'SS', N: 'NS', B: 'BS' } as const

/**
 * **A member's assignment: one tag per key, read off the member's own body.**
 *
 * The model states no rule here: the tag table is a host index over a `Term.union`, and no term
 * carries it. What the model does carry is the member's own body, as `Calculus.Body.spec`, and
 * this reads the same field data one question further — the field is `req`, its term is a
 * `literal`, and it pins exactly one alternative.
 *
 * **`req` only.** A `withLegacyRead` discriminator would fill an absent tag with a default, and the
 * index would then key a member on a value no item carries. `Calculus.Body.spec` marks a
 * `withLegacyRead` field required, so the model's own clause keeps one where this refuses it: the two
 * rules differ because this one writes a tag and the model's writes none.
 *
 * One divergence, and it is the one the model writes down rather than fixes: the model reads a
 * `number` literal's tag set as empty, because `Calculus.Double` is an axiom with no closed terms.
 * The host builds a numeric tag and reads it back as its text, and `src/codec/lean.ts` refuses to
 * emit one and says why. Narrowing this to the model's two bases would take a tag the published
 * surface admits today.
 */
export const assignmentOf = (
    ks: readonly string[],
    body: Body,
): Result<Readonly<Record<string, string>>> => {
    const out: Record<string, string> = {}
    for (const name of ks) {
        const field = body.fields[name]
        if (field === undefined) {
            return new CodecError(
                `every option must name '${name}' with a literal at \`string\`, \`number\` or \`decimal\`, and one of them declares no '${name}' — a tag is carried as 'S' or 'N', and without one a lookup cannot find the variant`,
            )
        }
        if (field.mark !== 'req') {
            return new CodecError(
                `every option must name '${name}' with a literal at \`string\`, \`number\` or \`decimal\`, and one of them declares it \`${field.mark}\` — a tag that can be absent or defaulted names no variant, which is why the model reads a tag off a \`req\` field alone`,
            )
        }
        // a union of same-base literals is what `string('a', 'b')` builds, and it names as many
        // tags as it has options — which the arity refusal below is what answers
        const alts = storedAlternatives(field.t)
        if (
            alts === undefined ||
            alts.base === 'boolean' ||
            alts.base === 'binary'
        ) {
            return new CodecError(
                `every option must name '${name}' with a literal at \`string\`, \`number\` or \`decimal\`, and one of them does not — a tag is carried as 'S' or 'N', and without one a lookup cannot find the variant`,
            )
        }
        if (alts.ls.length !== 1) {
            return new CodecError(
                `'${name}' names ${alts.ls.length} values at one option (${alts.ls.join(', ')}), and a variant answers to exactly one tag — split it into one option per value`,
            )
        }
        out[name] = String(alts.ls[0])
    }
    return out
}

/**
 * **Two assignments are equal when they agree at every key**, decided by walking the keys and
 * not by a rendering.
 *
 * No sort, no join, no `JSON.stringify`. A rendering would be an encoding, and an encoding of a
 * key set is an order: the thing the term is built not to carry. This reads the keys the caller
 * gave in whatever order the array happens to hold them, and the answer does not depend on it.
 */
export const sameAssignment = (
    ks: readonly string[],
    a: Readonly<Record<string, string>>,
    b: Readonly<Record<string, string>>,
): boolean => ks.every((name) => a[name] === b[name])

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
 * The transform is the whole of what distinguishes the products from each other. `array` hands
 * it {@link every}, a traversal — the model's `entrywise`. `tuple` aligns first. `object` guards
 * and filters first. `set` is the one product that is not an instance, because its attribute side
 * is a choice among three wire sets rather than one member.
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
            optional: !alwaysWritten(field),
            keyed: field.mark === 'undefinable',
            absent:
                field.mark === 'fallback'
                    ? { value: field.v, copy: copiedPerRead(field.v) }
                    : undefined,
        })
    }
    const restCodec = rest && codecOfTerm(rest)
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
            for (const name in held) {
                const value = held[name]
                if (name in of || value === undefined) continue
                // a closed body refuses an undeclared name on both sides, as the model's body does.
                // A write that dropped the name read back a different value, and a union that
                // admits by attempt reads this refusal to tell two closed options apart
                if (!restCodec) {
                    return new CodecError(
                        `'${name}' is not an attribute this codec declares`,
                    )
                }
                const written = restCodec.encode(value as never)
                if (failed(written)) return written.under(name)
                out[name] = written
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
                keyed,
                absent,
            } of declared) {
                const attribute = item[name]
                if (attribute === undefined) {
                    // before the skip: the key survives an omitted attribute
                    if (keyed) {
                        out[name] = undefined
                        continue
                    }
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
    // the base writes first, so the predicate sees only a value of the base's type, and a value the
    // base refuses is refused by the refinement. The model's `restrict` asks `q` first, and the
    // two orders agree because the model's `q` is total
    encode: (value) => {
        const written = base.encode(value)
        return !failed(written) && holds(value) ? written : refuse(value)
    },
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
     * The option this is for, or why no option is.
     *
     * Two steps. The **kind** filter comes first and is the only step that can be trusted on its
     * own: an option that writes `S` cannot read an `N`. If it leaves one option, that option *is*
     * the answer, so a failure past that point is its error, reported as itself rather than
     * swallowed into "no option matched".
     *
     * If it leaves several, they are **tried**, and the first that succeeds answers. The options of
     * every union this library builds are compatible, so two that both read an attribute read it
     * to one value, and the order is not observable. `union` shows it at the declaration, `opaque`'s
     * options are compatible by kind, and a slice keeps restrictions of compatible options.
     *
     * **This is the read side.** The write side decides instead, {@link onlyAdmitting}, and this
     * one attempts because there is no `AdmA` in `src/` to decide a stored attribute with.
     */
    const only = <A>(
        survives: (option: Option) => boolean,
        named: string,
        through: (option: Option) => Result<A>,
    ): Result<A> => {
        const candidates = all.filter(survives)
        if (candidates.length === 0) return unmatched(named)
        if (candidates.length === 1) return through(candidates[0] as Option)
        for (const option of candidates) {
            const attempt = through(option)
            if (!failed(attempt)) return attempt
        }
        return unmatched(named)
    }

    /**
     * The model's option row, `Adm`: every option is admitted by {@link accepts}, an object option
     * included. The names present select nothing, because a name set that fits two options can
     * hold a value that only one of them encodes. Asking the option's own admission terminates:
     * it is one level down, and the direction that would not is an `encode` consulting admission.
     */
    const admitOption = (option: Option, value: unknown) =>
        accepts(option.codec, value)

    /**
     * The same, **decided rather than attempted** — the write side only. The first option that
     * admits the value writes it, and compatibility makes every admitting option write it to one
     * attribute.
     *
     * {@link accepts} is the decision for every option, and {@link admitOption} is that one row. §3's `Adm`,
     * proved exact at all 21 constructors, and `codec.laws.spec.ts` holds
     * `accepts(c, v) ⟺ !failed(c.encode(v))` over its whole table — so on the values in play this
     * selects the same option `only` would have found by attempting, and says *why* rather than
     * discovering it. A `held` option whose adapter **throws** on a value it does not own is
     * filtered out here instead of propagating.
     *
     * **The read side attempts**, because there is nothing to decide with: the model has `AdmA` on
     * the attribute side and `src/` has no port of it. The model's `AdmA` of an option is that attempt, an
     * object option included. That asymmetry is the reason this is a second function rather than a
     * flag on the first.
     */
    const onlyAdmitting = <A>(
        survives: (option: Option) => boolean,
        named: string,
        value: unknown,
        through: (option: Option) => Result<A>,
    ): Result<A> => {
        const candidates = all.filter(
            (option) => survives(option) && admitOption(option, value),
        )
        const first = candidates[0]
        return first === undefined ? unmatched(named) : through(first)
    }

    /**
     * Which options a value could be for, by kind. The names present select nothing: an object
     * option is admitted by attempt, as the model's `Adm` admits every option.
     */
    const forValue = (shape: Shape | undefined) => (option: Option) =>
        option.declares
            ? shape === 'map'
            : !shape || option.carries.includes(shape)

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
                    ? member === 'M'
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
            forValue(shapeOf(value)),
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
 * The assignment chooses the member, and the choice is a **lookup** rather than an attempt.
 *
 * **The index is the host's, and the model has no such term.** A dissection is a `Term.union` of
 * members whose structures are disjoint, certified by `Calculus.certPair`; this table is an index
 * built over that union, so nothing in the model states it and nothing in the model needs it. What
 * makes the lookup answer the same question the union answers is the refusal at construction: two
 * members carrying one assignment are refused, so at most one member is reached either way.
 *
 * **A list and a scan.** Membership is decided by {@link sameAssignment}. An index keyed by a
 * rendered string would put an order on the keys to build the rendering, and a key set has none.
 * The members of one dissection are few, so the scan costs what the walk over the keys costs.
 */
export const byTagSem = <V>(
    ks: readonly string[],
    members: readonly (readonly [Readonly<Record<string, string>>, V])[],
): {
    readonly pick: (assignment: Readonly<Record<string, string>>) => Result<V>
    readonly tagOf: (
        item: Readonly<Record<string, unknown>>,
    ) => Result<Readonly<Record<string, string>>>
} => ({
    pick: (assignment) => {
        const found = members.find(([one]) =>
            sameAssignment(ks, one, assignment),
        )
        if (found !== undefined) return found[1]
        // **which discriminator was wrong, decided without an order.** A key whose tag no member
        // carries is wrong on its own, so it is named with the tags that would have matched.
        // Where every key matches some member and no member carries them all, the combination is
        // what failed, and that is what the message says
        for (const name of ks) {
            const carried = members.map(([one]) => one[name] as string)
            if (!carried.includes(assignment[name] as string)) {
                const expected = [...new Set(carried)]
                    .map((tag) => `'${tag}'`)
                    .join(', ')
                return new CodecError(
                    `'${assignment[name]}' is not a variant of '${name}'; expected ${expected}`,
                )
            }
        }
        const wrote = ks
            .map((name) => `${name}='${assignment[name]}'`)
            .join(', ')
        return new CodecError(
            `no variant carries ${wrote}; each tag names a variant and no variant names them together`,
        )
    },
    tagOf: (item) => {
        const out: Record<string, string> = {}
        for (const name of ks) {
            const tag = item[name]
            if (tag === undefined) {
                return new CodecError(
                    `'${name}' chooses the variant and was not given`,
                )
            }
            out[name] = String(tag)
        }
        return out
    },
})

/**
 * **The members of a dissection, as a set.** Every member's assignment, read off its own body, and
 * a refusal where two members carry one assignment.
 *
 * **The index must be a lookup, and that is what this refuses.** Two members carrying one
 * assignment leave the table unable to say which member an item reaches. The model states nothing
 * here, because no term carries the table; the refusal is the host's alone, and it is stated at
 * construction because the type cannot state it.
 *
 * Reached by both spellings — `mdunion` at the declaration, and {@link taggedItemSem} at a bare
 * term — so a term that was not built through the constructor meets the same rule.
 */
export const membersOf = <V>(
    ks: readonly string[],
    bodies: readonly (readonly [Body, V])[],
): Result<readonly (readonly [Readonly<Record<string, string>>, V])[]> => {
    const out: (readonly [Readonly<Record<string, string>>, V])[] = []
    for (const [body, value] of bodies) {
        const assignment = assignmentOf(ks, body)
        if (failed(assignment)) return assignment
        const clash = out.find(([one]) => sameAssignment(ks, one, assignment))
        if (clash !== undefined) {
            // one template at every arity: at one key this reads `'type' = 'A'`, which is what the
            // one-key refusal always said, and at several it reads the whole assignment
            const wrote = ks
                .map((name) => `'${name}' = '${assignment[name]}'`)
                .join(' and ')
            return new CodecError(
                `two options answer to ${wrote}, and a lookup reaches only one of them — give them distinct values`,
            )
        }
        out.push([assignment, value] as const)
    }
    return out
}

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
 * The term that has a whole-item reading: an object.
 *
 * **It used to be two**, an object and a union of objects by tag. There is one sum now, so a union
 * of objects reads a whole item the way every union does: {@link union} builds that reading from
 * its resolved options, and `denote`'s union row asks {@link altSem} for the *attribute* pair. A
 * tagged builder keeps a tag table, and that table is its own index over the union rather than a
 * second way for a term to mean something.
 */
export type ItemTerm = Extract<Term, { readonly kind: 'object' }>

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
    const made = bodySem(def.body)
    itemPairs.set(Object.freeze(def), made)
    return made
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
         * §3 `(list)`: the one positional container, with the arity test before any position.
         *
         * `arrayCodec_eq` and `tupleCodec_eq` are the lemmas for the two builder shapes, and
         * `align_eq_some` is what settles the spread: the arity test comes **before** the
         * positions, because a list of the wrong length has no entrywise reading at all. `align`
         * is the model's name for that step; here it is the two length tests, and they are the
         * same fact — a list with a spread aligns at *at least* its declared positions, one
         * without at exactly them.
         *
         * A `Uint8Array` of the right length has the right `length` and is not a list, which is
         * what the length tests alone could not say. The term's `list` row asks `Array.isArray`
         * before it counts, and so does this, which is what makes the arity messages mean what
         * they say.
         *
         * The element codecs are handed over rather than closed over per call: a closure per call
         * to encode a list is a closure per list in every item written. `every` iterates whatever
         * is iterable, so a string arrived as its characters until the shape was asked first.
         *
         * The shape word comes from the term, because the term is what says which shape it is:
         * no declared position and one spread is what `array` builds, an empty suffix is what
         * `tuple` builds, and everything else only `list` can spell.
         */
        case 'list': {
            const pre = def.pre.map((element) => codecOfTerm(element))
            const suf = def.suf.map((element) => codecOfTerm(element))
            const spread = def.spread ? codecOfTerm(def.spread) : undefined
            const declared = pre.length + suf.length
            const shape =
                declared === 0 && spread
                    ? 'array'
                    : suf.length === 0
                      ? 'tuple'
                      : 'list'
            /** `align`: the arity test, which comes before any position is read. */
            const aligned = (
                length: number,
                say: (arity: number) => string,
            ): CodecError | undefined =>
                (spread ? length < declared : length !== declared)
                    ? new CodecError(`${say(declared)}, found ${length}`)
                    : undefined
            const atLeast = spread ? 'at least ' : ''
            /**
             * The codec at one position, which needs the **length** as well as the index: the
             * suffix aligns from the right, so which positions it holds depends on how long the
             * value is. The prefix and the suffix cannot overlap here, because `aligned` has
             * already turned down every length below `declared`.
             */
            const at = (index: number, length: number): AnyCodec =>
                index < pre.length
                    ? (pre[index] as AnyCodec)
                    : index >= length - suf.length
                      ? (suf[index - (length - suf.length)] as AnyCodec)
                      : (spread as AnyCodec)
            return carriedCodec(
                (value): value is readonly never[] => Array.isArray(value),
                'L',
                (value) =>
                    new CodecError(
                        `${describeShape(value)} is not an array, and \`${shape}\` writes an 'L' — a codec's input is typed, so this is a value that reached \`encode\` past its type`,
                    ),
                (held) =>
                    aligned(
                        held.length,
                        (arity) => `expected ${atLeast}${arity} elements`,
                    ) ??
                    every(held, (one, index) =>
                        at(index, held.length).encode(one),
                    ),
                (carried: readonly AttributeValue[]) =>
                    aligned(
                        carried.length,
                        (arity) => `expected a list of ${atLeast}${arity}`,
                    ) ??
                    every(carried, (one, index) =>
                        at(index, carried.length).decode(one),
                    ),
            )
        }
        /**
         * §3 `(set)`, and the one product that is **not** a {@link carriedCodec}. The model says
         * why: its attribute side is a choice among three wire sets rather than one member, so
         * there is no single `A` prism to carry a payload into.
         *
         * The set is the lift of its element's codec: each member is written and read through the
         * element, so a restriction, a literal and an adapter at the element run on every member.
         * Which wire set follows from the element's member, which {@link set} checked is `S`, `N`
         * or `B`, the DynamoDB set obligation.
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
            const inner = codecOfTerm(def.elem)
            const one = termMember(def.elem)
            if (one !== 'S' && one !== 'N' && one !== 'B') {
                throw new CodecError(
                    `a set holds strings, numbers or binary, and this element writes ${one ? `'${one}'` : 'no single member'}`,
                )
            }
            const member = one
            const setMember = setWire[one]
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
         * §3 `(withLegacyRead)`: the current reading, extended by an older one — the model's
         * `Codec.extendRead`, and `lawful_extendRead` is the lemma. The write side is untouched,
         * which is the whole of what makes it a migration rather than a union: `withLegacyRead` adds no
         * way to *write*, only a second way to read.
         *
         * The current encoding is tried first and on its own, so the path every row written since
         * the migration takes allocates nothing — no `[current, ...older]` to walk and no list of
         * reasons collected for a failure that did not happen.
         *
         * §3 `(withLegacyRead)`'s first premise, `ran(r) ⊆ dom(e)`, is checked here and nowhere earlier:
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
         * A thunk: the pair of the term the thunk resolves to, forced on use.
         *
         * The row recurses on the **value**, never on the term, which is what makes it terminate:
         * `def.get()` is forced once per level of the value, and a value is finite. The model has no
         * thunk: a thunk that closes a cycle is the variable of a binder there (`Term.mu`), and any
         * other thunk is the term it returns.
         *
         * **A refusal inside the thunk is a value.** The thunk is caller code, and a builder in the
         * thunk refuses with a `CodecError` at the first use. The row returns that refusal. Every
         * other throw propagates, because an overflow or a defect of the caller is not a refusal.
         */
        case 'lazy': {
            const resolved = (): Term | CodecError => {
                try {
                    return def.get()
                } catch (thrown) {
                    if (thrown instanceof CodecError) return thrown
                    throw thrown
                }
            }
            return {
                encode: (value) => {
                    const t = resolved()
                    return t instanceof CodecError
                        ? t
                        : codecOfTerm(t).encode(value)
                },
                decode: (attribute) => {
                    const t = resolved()
                    return t instanceof CodecError
                        ? t
                        : codecOfTerm(t).decode(attribute)
                },
            }
        }
        /**
         * §3 `(union)`: the join, resolved by the first option that admits. `lawful_altCodec` is the lemma and
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
         * §5's bottom: the codec that admits no value.
         *
         * `Codec.empty` on the model's side, whose laws hold vacuously because both domains are
         * empty. A refusal in both directions and a value rather than a throw, as every other row.
         */
        case 'never':
            return {
                encode: () =>
                    new CodecError(
                        '`never` admits no value, so there is nothing to write through it',
                    ),
                decode: () =>
                    new CodecError(
                        '`never` admits no value, so no stored attribute reads back through it',
                    ),
            }
        /**
         * §3 `(opaque)`: the recursive union of everything self-identifying, and total: a number
         * is a `DynamoNumber`. The two numeric policies are `held` over this row. `lawful_opaqCodecω` is the lemma, and it is a *theorem* rather
         * than an obligation — the model's `Obligations (.opaq _)` is `True`, which is what makes
         * `opaque` a well-behaved `custom`: the same analysis with the opposite warranty. A
         * `custom` carries a premise its author owes; this carries none, because the calculus
         * proves the laws for it.
         *
         * The pair is this library's own recursion rather than a fixpoint built here, and the row
         * asks it. §5's rows do the same for the same reason: no syntactic set names
         * `opaqCodecω`'s domain, because it recurses on the *input's own depth*.
         */
        case 'opaq':
            return {
                encode: (value: unknown) => encodeUnknown(value),
                decode: (attribute) => decodeUnknown(attribute),
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
            const allowed: readonly LiteralValue[] = [def.v]
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
                // **The carrier is `DynamoNumber`**, which proves the numeral gate at construction
                // and is already in the spelling the store returns, so this row asks the kind and
                // nothing else. It is DynamoDB's own `N` and the one native numeric term;
                // `number` and `decimal` are adapters over it and carry their own conversions
                encode: (value: unknown) =>
                    value instanceof DynamoNumber
                        ? carrying('N', value.digits)
                        : new CodecError(
                              `${rendered(value)} is not a DynamoNumber; build one with DynamoNumber.from or DynamoNumber.fromNumber`,
                          ),
                decode: (attribute) =>
                    andThen(expect('N', attribute), (carried) =>
                        isNumeral(carried)
                            ? DynamoNumber.from(carried)
                            : new CodecError(
                                  `'${carried}' is not a numeral, so this attribute was not written by DynamoDB`,
                              ),
                    ),
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
 * @anchored
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
 * `optional(c)` and `withLegacyRead({ current: c, whenMissing: v })` denote a `Field`, and no `Term` position accepts one — which
 * the positional guards refuse in the *type* at every site that could go wrong. This is the runtime
 * half, at the one place a child is taken from a codec a caller handed over.
 */
export const termOf = (declared: ObjectSlot): Term => {
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
    // **A codec is its pair and its term, and nothing else.** `arbitrary` and `shrink` were copied
    // onto the object here for `custom`, which made one fact reachable two ways; they are on the
    // term, `arbitraryOf` and `shrinkOf` read them there, and a caller that wants to share a
    // generator names it rather than reading it back off a pair.
    codec<T, A>({
        def,
        ...(denote(def) as Pick<Codec<T, A>, 'encode' | 'decode'>),
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
 * The canonical `opaque`, and **total on the wire**: every attribute has one value here. The
 * domain is exactly the values whose type is recoverable, so `decode ∘ encode = id` holds for
 * everything accepted. Accepted: `null`, `string`, `boolean`, `Uint8Array`, a `DynamoNumber`, a
 * non-empty `Set` of strings, of binary or of `DynamoNumber`s, arrays, and plain objects,
 * recursively. A JS number is refused, because a float is not the exact number that `N` stores.
 */
export const encodeUnknown = (
    value: unknown,
    /** How many `L`/`M` this value already sits inside. See {@link MAX_DOCUMENT_NESTING}. */
    enclosing = 0,
): Result<AttributeValue> => {
    if (value === null) return carrying('NULL', true)
    if (typeof value === 'string') return carrying('S', value)
    if (typeof value === 'boolean') return carrying('BOOL', value)
    if (value instanceof Uint8Array) return carrying('B', value)
    if (value instanceof DynamoNumber) return carrying('N', value.digits)

    if (typeof value === 'number') {
        return new CodecError(
            "a JS number is a binary64 float, and `opaque` holds a number exactly, as a `DynamoNumber`. Build one with `DynamoNumber.from` or `DynamoNumber.fromNumber`, declare the attribute with `dynamoNumber` or `number`, or opt in with `opaque('lossy')`.",
        )
    }

    if (typeof value === 'bigint') {
        return unrecoverable(
            'a bigint',
            'It writes `N` and reads back as a `DynamoNumber`, so `1n` would not come back as `1n`. Pass `DynamoNumber.from(value.toString())`.',
        )
    }

    if (Array.isArray(value)) {
        const deep = tooDeeplyNested(enclosing)
        if (deep) return new CodecError(deep)
        return andThen(
            every(value, (x) => encodeUnknown(x, enclosing + 1)),
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
        if (members.every((x) => x instanceof DynamoNumber)) {
            // the digits are normal, so two members that are one number have one spelling
            const digits = members.map((x) => (x as DynamoNumber).digits)
            return new Set(digits).size === digits.length
                ? carrying('NS', digits.sort())
                : new CodecError(
                      'this set holds one number two times, as two `DynamoNumber`s, and an `NS` holds each number one time',
                  )
        }
        return new CodecError(
            'a set writes `SS`, `BS` or `NS`, and each holds one kind: every member a string, every member binary, or every member a `DynamoNumber`',
        )
    }

    if (value instanceof Map) {
        return unrecoverable(
            'a Map',
            'DynamoDB has one map member, `M`, and it decodes as a plain object. Pass an object, or use `object([string, optional(...)])` to state the value type.',
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
                    : encodeUnknown(v, enclosing + 1),
            ),
            (written) => carrying('M', written),
        )
    }

    return unrecoverable(`a ${typeof value}`, 'No DynamoDB member carries it.')
}

/** The stored digits as a `DynamoNumber`, behind the numeral gate that `number` reads through. */
const storedNumber = (carried: string): Result<DynamoNumber> =>
    isNumeral(carried)
        ? DynamoNumber.from(carried)
        : new CodecError(
              `'${carried}' is not a numeral, so this attribute was not written by DynamoDB`,
          )

/**
 * Reads every attribute back, and a number as the `DynamoNumber` that the store holds.
 *
 * `N` and `NS` read exactly: the canonical `opaque` writes both, so a read-modify-write keeps the
 * stored type. A `Set` of `DynamoNumber`s re-encodes as the `NS` it came from.
 */
export const decodeUnknown = (attribute: AttributeValue): Result<unknown> => {
    const member = memberOf(attribute)
    switch (member) {
        case 'NULL':
            return null
        case 'S':
            return attribute[member]
        case 'N':
            return storedNumber(attribute.N as string)
        case 'B':
        case 'BOOL':
            return attribute[member]
        case 'NS': {
            const carried = attribute.NS ?? []
            return carried.length === 0
                ? new CodecError(
                      'DynamoDB has no empty NS, so this attribute was not written by it',
                  )
                : andThen(every(carried, storedNumber), (read) => new Set(read))
        }
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
            return every(attribute.L ?? [], (x) => decodeUnknown(x))
        case 'M':
            return everyEntry(attribute.M ?? {}, (v) => decodeUnknown(v))
        default:
            return new CodecError('an AttributeValue carrying no member')
    }
}

/**
 * **A numeric policy of `opaque`, as a walk that changes the number leaves and nothing else.**
 *
 * Each policy is a `held` over the canonical `opaque`. `f` walks the caller's value to the
 * canonical value, and `g` walks the read value back. Both keep the path labels of
 * `every` and `everyEntry`. The walk refuses each value that the policy refused before it was a
 * `held`, with the same text. The canonical codec then refuses the rest, with the same text again.
 *
 * `f` stops at the nesting limit and hands the value on unchanged, so a cyclic value reaches the
 * canonical codec, which refuses it at that depth.
 */
const numberPolicy = (numbers: opaque.Numbers) => {
    const refuseText =
        "Declare the attribute with `number` or `decimal`, or opt in with `opaque('lossy')`."

    const into = (value: unknown, enclosing: number): Result<unknown> => {
        if (typeof value === 'number') {
            if (!Number.isFinite(value)) {
                return new CodecError(`DynamoDB has no number for ${value}`)
            }
            if (numbers === 'refuse') {
                return unrecoverable(
                    'a number',
                    `Reading it back is undecidable without a schema: as a \`number\` it rounds, and as a \`string\` it re-encodes as \`S\`, changing the attribute's stored type. ${refuseText}`,
                )
            }
            /**
             * **Writing an `N` means writing a numeral.** `Number.isFinite` is not that test: §1's
             * `Carries('N')` is `Numerals`, bounded by 38 significant digits and magnitude
             * `1e-130 … 9.9…e125`, and `5e-324` is a finite double outside it. The digits that
             * reach the store are the normal form of `DynamoNumber`, which is the form the store
             * returns: `1e21` is stored `1000000000000000000000`.
             */
            return isNumeral(String(value))
                ? DynamoNumber.from(String(value))
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
        // the canonical codec writes a `DynamoNumber`, and a policy holds a JS number or none
        if (value instanceof DynamoNumber) {
            return unrecoverable(
                'an instance of DynamoNumber',
                'Only plain objects survive: `M` carries the own enumerable properties and nothing that says how to rebuild the instance. Convert it first — a `Date`, for example, is faithful as an ISO string.',
            )
        }
        if (Array.isArray(value)) {
            return tooDeeplyNested(enclosing)
                ? value
                : every(value, (x) => into(x, enclosing + 1))
        }
        if (value instanceof Set) {
            const members = [...value]
            return members.length === 0 ||
                members.every((x) => typeof x === 'string') ||
                members.every((x) => x instanceof Uint8Array)
                ? value
                : unrecoverable(
                      'a set of numbers',
                      'NS decodes as strings, because its members are decimal strings. Use a set of strings, or `array(number)` if the order does not matter to you.',
                  )
        }
        if (
            typeof value === 'object' &&
            value !== null &&
            isPlainObject(value)
        ) {
            return tooDeeplyNested(enclosing)
                ? value
                : everyEntry(value as Record<string, unknown>, (v) =>
                      v === undefined ? v : into(v, enclosing + 1),
                  )
        }
        return value
    }

    const outOf = (read: unknown): Result<unknown> => {
        if (read instanceof DynamoNumber) {
            if (numbers === 'refuse') {
                return unrecoverable(
                    `the stored number '${read.digits}'`,
                    refuseText,
                )
            }
            /**
             * The second gate is not redundant: `Number('9.9…E+125')` rounds *up* past the
             * maximum, so a numeral the store holds can read back as a value nothing here can
             * write, which is **(C)** failing.
             */
            const number = Number(read.digits)
            return isNumeral(String(number))
                ? number
                : new CodecError(
                      `'${read.digits}' reads back as ${number}, which is outside what DynamoDB stores, so it cannot be written again`,
                  )
        }
        if (Array.isArray(read)) return every(read, outOf)
        /**
         * **A member this policy cannot write is a member it cannot read.** A numeric `Set` is
         * refused on the way in, so an `NS` has no write path, and reading one would re-encode
         * as `SS`. That is **(MP)** failing, and `Calculus.Alg.Lawful.no_read_without_write` proves
         * the general form.
         */
        if (read instanceof Set) {
            return [...read].some((x) => x instanceof DynamoNumber)
                ? unrecoverable(
                      'a stored set of numbers',
                      "`NS` has no counterpart this codec can write — a set of numbers is refused on the way in, because nothing without a schema says which of its members a JS number holds faithfully. Reading it would mean re-encoding it as `SS` and changing the attribute's stored type. Declare the attribute with `number.set()` or `decimal.set()`.",
                  )
                : read
        }
        if (
            typeof read === 'object' &&
            read !== null &&
            !(read instanceof Uint8Array)
        ) {
            return everyEntry(read as Record<string, unknown>, outOf)
        }
        return read
    }

    return {
        f: (value: unknown) => into(value, 0),
        g: (read: unknown) => outOf(read),
    }
}

const canonicalOpaque: Term = { kind: 'opaq' }

/**
 * **The held side of `opaque('refuse')`**: every slot but `number`, as a union of the terms that
 * write one slot each. `'refuse'` takes no JS number, so a union reads its write side as before
 * it was a `held`. The term is a write occupancy only: `f` checks the held side itself.
 */
const everyButNumber: Term = {
    kind: 'union',
    options: [
        { kind: 'string' },
        { kind: 'boolean' },
        { kind: 'binary' },
        { kind: 'null' },
        { kind: 'set', elem: { kind: 'string' } },
        { kind: 'set', elem: { kind: 'number' } },
        { kind: 'set', elem: { kind: 'binary' } },
        { kind: 'list', pre: [], spread: canonicalOpaque, suf: [] },
        { kind: 'object', body: { fields: {}, rest: canonicalOpaque } },
    ],
}

const policyTerm = (numbers: opaque.Numbers): Term => {
    const { f, g } = numberPolicy(numbers)
    return {
        kind: 'held',
        inner: canonicalOpaque,
        outer: numbers === 'lossy' ? canonicalOpaque : everyButNumber,
        f,
        g,
        via: numbers === 'lossy' ? 'opaqueLossy' : 'opaqueRefuse',
    }
}

/**
 * The terms of `opaque`: the canonical one, and a `held` for each numeric policy.
 *
 * One object per term, so the codec cache and the identity of `def` hold across calls.
 */
export const opaqueTerms: {
    readonly canonical: Term
    readonly lossy: Term
    readonly refuse: Term
} = {
    canonical: canonicalOpaque,
    lossy: policyTerm('lossy'),
    refuse: policyTerm('refuse'),
}

/**
 * `occV`'s answer, coarsened to the alphabet a **value** can be classified into.
 *
 * `occV` reads a term and answers a {@link SetSlot}, which splits the three wire set families because
 * a term carries its base. A value does not: `shapeOf` sees a `Set` and answers `'set'`, since
 * telling `strSet` from `numSet` means inspecting the elements and **an empty `Set` belongs to no
 * family at all**. So the two alphabets stay two, and this is the one-way map between them — from
 * the term's to the value's, which is the only direction that is total.
 *
 * **This replaced a second walk of the term.** `carries` answered the same question by recursing
 * over the definition itself, and the two were kept in agreement by hand. Measured at 35
 * constructors before the swap, they agreed at 34. The row that differed was `opaque`: the reader
 * answered `undefined` — *unknown* — where `occV` gives the model's closed form, every constructor
 * at `lossy` and every one but the numeric at `refuse`. `occV` is right, and the difference is now
 * the desired behaviour rather than a divergence: a lone `opaque` that refuses numbers is filtered
 * out on a number instead of attempted and failed, and `f083188` refused the unions where that
 * filtering would have decided anything else.
 */
export const valueKinds = (t: Term): readonly Shape[] => {
    const slots = occV(t)
    const out: Shape[] = []
    for (const slot of slots) {
        const shape: Shape =
            slot === 'strSet' || slot === 'numSet' || slot === 'binSet'
                ? 'set'
                : slot
        if (!out.includes(shape)) out.push(shape)
    }
    return out
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
 * A term's kind, as the **constructor the caller wrote**.
 *
 * A refusal names the option to remove, so it has to use the caller's vocabulary rather than the
 * model's. One kind differs: `Term.opaq` is written `opaque(...)`. Everything else is spelled the
 * same on both sides.
 *
 * Reached by `union`'s refusal, which is the one message that names an option by its kind. A
 * numeric policy of `opaque` is a `held`, and the caller wrote `opaque`, so it takes the same name.
 * The `opaq` row became reachable when the guard stopped exempting an `opaque` option: the message
 * read "opaq and string both take the same kind of value", naming something no caller had typed.
 *
 * **An adapter names the value it takes, not the combinator.** `number` and `decimal` are
 * `held` over one carrier, so the kind alone answered "held", which names nothing the caller
 * wrote. The held side is the slot the caller's value lands in, so it is the kind of value
 * the option takes, and a refusal that lists the options is asking exactly that. An adapter
 * whose held side is `opaque` keeps the combinator's name, which is all this can honestly
 * say about one.
 *
 * **A literal option names its alternatives.** Two options at one form differ only in their
 * literals, so a refusal that names the form alone names both options with one word.
 */
const namedKind = (t: Term): string => {
    const pinned = literalAlternatives(t)
    return t.kind === 'opaq' || (t.kind === 'held' && isOpaqueSugar(t.via))
        ? 'opaque'
        : pinned !== undefined
          ? namedLiterals(literalForm(pinned.base, undefined), pinned)
          : t.kind !== 'held' || t.outer.kind === 'opaq'
            ? t.kind
            : namedAdapter(t.inner, t.outer)
}

/** A literal form with its alternatives, as the caller writes the call. */
const namedLiterals = (form: string, alts: Alternatives): string =>
    `${form}(${alts.ls.map(namedLiteral).join(', ')})`

/**
 * An adapter over a ground base, named by its form and the literals that the caller wrote.
 * The held side holds the caller's literals where the held side pins them: `decimal('1', '2.5')`
 * stores numerals and holds the texts. Otherwise the stored literals are the caller's. An adapter
 * over no ground base names the kinds of its held side. @see {@link namedKind}
 */
const namedAdapter = (inner: Term, outer: Term): string => {
    const stored = literalAlternatives(inner)
    const base = heldBase(inner) ?? stored?.base
    if (base === undefined) return occV(outer).join(' | ')
    const written = literalAlternatives(outer) ?? stored
    const form = literalForm(base, outer)
    return written === undefined ? form : namedLiterals(form, written)
}

/** The ground base a declared adapter carries, where it carries one. @see {@link namedKind} */
const heldBase = (t: Term): LiteralBase | undefined =>
    t.kind === 'literal'
        ? t.base
        : t.kind === 'string' ||
            t.kind === 'number' ||
            t.kind === 'boolean' ||
            t.kind === 'binary'
          ? t.kind
          : t.kind === 'refine' || t.kind === 'legacy'
            ? heldBase(t.inner)
            : undefined

/**
 * Everything about an option that the **term** decides, which is everything but `item`.
 *
 * `denote`'s `untagged` row builds its options from the definition and asks {@link altSem} for the
 * attribute pair, and that pair reads `codec`, `member`, `carries` and `declares` — it never reads
 * `item`. So the resolution is a function of the terms, and this is it.
 *
 * **The names come from the fields, not from a `spec`.** A `spec` is a caller's argument and a
 * `Field`'s `mark` is what that argument became, so `declares` and the names a message marks
 * optional are read from the term here. The names select no option: every option is attempted.
 * `declares` marks an object option, which the kind filter reads as a map, and a message names.
 *
 * The term decides, and every codec has one. The object a *constructor* returns carries `.item`
 * and a codec built from a term does not, so a test on `.item` would classify a term-built object
 * option as a ground option.
 */
export const optionOfTerm = (def: Term): Option => {
    const codec = codecOfTerm(def)
    /**
     * **A union of objects is an object option too**, and its names are its members' taken
     * together. A message names them: a name that every member always writes is named as
     * required, and any other name as optional. The names select nothing.
     */
    if (
        def.kind === 'union' &&
        def.options.length > 0 &&
        def.options.every((o) => o.kind === 'object')
    ) {
        const bodies = def.options.map(
            (o) => (o as Extract<Term, { kind: 'object' }>).body,
        )
        const declares = new Set<string>()
        for (const body of bodies) {
            for (const name in body.fields) declares.add(name)
        }
        const requires = [...declares].filter((name) =>
            bodies.every((body) => {
                const field = body.fields[name]
                return !!field && alwaysWritten(field)
            }),
        )
        return {
            codec,
            member: 'M',
            carries: ['map'],
            item: undefined,
            declares,
            describe: `${namedKind(def)} { ${[...declares]
                .map((name) => (requires.includes(name) ? name : `${name}?`))
                .join(', ')} }`,
        }
    }
    if (def.kind !== 'object') {
        return {
            codec,
            member: termMember(def),
            carries: valueKinds(def),
            item: undefined,
            declares: undefined,
            describe: namedKind(def),
        }
    }
    const declares = new Set<string>()
    const fields = def.body.fields
    for (const name in fields) declares.add(name)
    return {
        codec,
        member: 'M',
        carries: ['map'],
        item: undefined,
        declares,
        // an open block holds every undeclared name, and `...` names it
        describe: `{ ${[
            ...[...declares].map((name) =>
                alwaysWritten(fields[name] as Field) ? name : `${name}?`,
            ),
            ...(def.body.rest === undefined ? [] : ['...']),
        ].join(', ')} }`,
    }
}
