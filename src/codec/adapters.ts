import type { ErrorMessage } from '../utils'
import type { AttributeValue } from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    AttributeOf,
    Decoded,
    Free,
    FreeOf,
} from './build'
import { codecOfTerm } from './capabilities'
import { termOf } from './denote'
import type { CycleEntryOf } from './pathModel'
import type { Result } from './result'
import { CodecError, failed, HeldSideRefusal } from './result'
import type { StandardInput, StandardSchemaV1 } from './standard'
import type {
    Field,
    fillMarker,
    HeldT,
    Rng,
    Term,
    TermMark,
    TermOf,
} from './term'
import { thrownReason } from './value'

/** What {@link refine} takes beside the inner codec and the predicate. */
export type RefineOptions<Narrow> = {
    /**
     * Values satisfying `is`.
     *
     * Optional, but supply it when the inner codec's values rarely pass: generation falls back
     * to filtering, and a predicate that rejects most of what it sees wastes the search.
     */
    readonly arbitrary?: (rng: Rng, size: number) => Narrow
    /** Named in the error when a stored value fails the check. */
    readonly describe?: string
    /**
     * Told when filtering keeps less than half of what it generates, instead of `console.warn`.
     *
     * Only ever called from an arbitrary, so only ever during a property run.
     */
    readonly onThinSearch?: (what: string, rate: number) => void
}

// ── reading what is already there ───────────────────────────────────

/**
 * A field that stands in a value where the attribute is absent.
 *
 * Not a codec, for the reason {@link OptionalCodec} records. The fill value is the marker's payload at
 * the type level and `def.value` at run time, and the run-time side is the one {@link fill}
 * checks against the rule `(fill)`.
 */
export type MissingCodec<
    T,
    A extends AttributeValue = AttributeValue,
    // the codec the mark is about, carried rather than erased to `AttributeCodec<T, A>`. A brand
    // sits on the codec — `constant` is the one that matters here — and erasing to the two type
    // arguments drops it before a derivation over the spec can ask
    C = AttributeCodec<T, A>,
> = {
    readonly [fillMarker]: T
    readonly codec: C
    readonly def: Extract<Field, { readonly mark: 'fill' }>
}

/** The refusal of a fill value that the codec it fills cannot write, or `undefined` where it writes. */
export const fillRefusal = (
    filledCodec: AnyCodec,
    value: unknown,
): CodecError | undefined => {
    try {
        const written = filledCodec.encode(value as never)
        return failed(written) ? written : undefined
    } catch (thrown) {
        // a value outside the codec's type, which the codec reached past that type: as `accepts` reads it
        return new CodecError(thrownReason(thrown))
    }
}

/**
 * The refusal in the type of a wall argument whose term reaches an entry on a cycle. The overload
 * of `fill` carries no refusal, because a fill value alone builds no wall. A `fill` over a `legacy` read refuses
 * through the wall of `legacy`.
 */
export type WallOver<W extends string, C> = [CycleEntryOf<TermOf<C>>] extends [
    never,
]
    ? unknown
    : ErrorMessage<`\`${W}\` reads '${CycleEntryOf<TermOf<C>> & string}', an entry on a cycle. A wall reaches no cycle`>

/**
 * The same stored attribute, held as something else.
 *
 * Two words this library keeps apart: an attribute is **stored** as `S`, `N`, `SS` — and it is
 * **held**, in your code, as a `string`, a `Date`, an array. Every other combinator changes the first
 * or narrows the second. This one changes only the second, by naming the two halves of the
 * conversion, and leaves what the table holds exactly as it was.
 *
 * **Two restrictions, and a conversion between them.** `inner` restricts the stored side and
 * `outer` restricts the held side, which is the shape of `z.codec(in, out, { decode, encode })`.
 * The held type derives from `outer`, and `encode` and `decode` only transform.
 *
 * @example
 * ```ts
 * // stored as SS, held as an array
 * const tags = held(string.set(), array(string), {
 *     encode: (tags) => new Set(tags),
 *     decode: (tags) => [...tags],
 * })
 *
 * // stored as S, held as a Date, restricted by a schema of another library
 * const when = held(string, z.date(), {
 *     encode: (at) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * **The held side is checked on both halves.** `encode` runs only on a value that `outer` admits,
 * and the value that `decode` returns must pass `outer` too. A value outside `outer` is refused by
 * name, as a base codec refuses a value past its type, and the caller's `encode` never runs on it.
 * The model states the same codec: `through` the conversion, then restricted by the write domain of
 * `outer` on both halves, so the codec is lawful for every `outer`.
 *
 * **`outer` has two forms.** A codec of this library admits a value where its `encode` succeeds,
 * which is the admission `accepts` asks, and the term records the codec's term as the held side.
 * A schema of another library implements Standard Schema v1, and admits a value where `validate`
 * returns no issues. `validate` answers synchronously here, because a codec does. A `Promise` or a
 * throw becomes a refusal.
 *
 * **The held type of a foreign schema is its input.** `validate` takes an input, so the held value
 * that `decode` returns and `encode` takes is the input type of the schema. A schema that transforms
 * has an output type that `validate` refuses, and the output is not a held type.
 *
 * **A foreign schema records the top as the held side.** The library cannot read which kinds of
 * value a foreign schema admits, so the write occupancy of this `held` is every kind. A `union`
 * with such an option has no certificate on the write side, and refuses where the other option
 * writes a kind. The runtime check still runs, so the codec refuses what the schema refuses.
 *
 * **Narrow the stored side in `inner`.** A conversion that can fail is two things at once, and
 * they compose better apart: narrow the inner codec first, so the failure is reported where the
 * value is actually wrong and with a message about it.
 *
 * ```ts
 * held(refine(string, isIsoDate, { describe: 'an ISO timestamp' }), z.date(), {
 *     encode: (at) => at.toISOString(),
 *     decode: (at) => new Date(at),
 * })
 * ```
 *
 * The pair must round-trip — `decode(encode(x))` equal to `x`, and `encode(decode(y))` equal to `y` —
 * or the codec's own law does not hold either. `checkRoundTrip` over a spec holding one is what
 * establishes it, and generation reaches through: without a stated `arbitrary`, values are generated
 * for the inner codec and handed out through `decode`, so the pair produced what is generated. A
 * stated `arbitrary` generates the held value itself, so the round trip checks that value.
 *
 * **Nothing here checks it, and nothing here can.** The model carries it as `IsoCancels` — a
 * premise, in both directions: `g(f v) = v` wherever `f v` lands writable, and `f(g v) = v` on the
 * writable values themselves. It is a premise there for the same reason it is unchecked here. One
 * direction quantifies over the *held* type. Without a stated `arbitrary` that type has none except
 * `decode` itself, so every value this library could make is already in the pair's image; and probing the other at
 * construction is worse than not probing it, because a legitimate adapter is an isomorphism on the
 * values its inner codec describes and *throws* off them.
 *
 * So this is a written obligation, and `checkIso` is how a caller discharges it: it generates for
 * the inner codec and checks `encode(decode(y))`, which is the half a table depends on. The
 * failure mode it catches, unrefused today and pinned in `codec.laws.spec.ts`, is an adapter that
 * *normalises* — `{ encode: v => v.toUpperCase(), decode: v => v }` reads `'a'` back as `'A'`,
 * and every read-modify-write on that row rewrites the value.
 */
export const held = <
    const C extends AnyCodec,
    const O extends AnyCodec | StandardSchemaV1,
>(
    inner: C & WallOver<'held', C>,
    outer: O & WallOver<'held', O>,
    adapt: {
        /**
         * The value, as the inner codec holds it. Runs on the way to the table, on a value that
         * `outer` admits.
         *
         * Return a {@link CodecError} where the conversion has nothing to hand over — a value
         * outside the range the inner codec describes, or text that does not parse. That is a
         * refusal like any other and reaches the caller as one.
         */
        readonly encode: (value: HeldOf<O>) => Result<NoInfer<Decoded<C>>>
        /** What the inner codec read, as you hold it. Runs on the way back. Refuses the same way. */
        readonly decode: (held: Decoded<C>) => Result<NoInfer<HeldOf<O>>>
        /**
         * **How to generate one of these, where the pair is partial.**
         *
         * Omit both and the adapter derives them from the inner codec: a value is generated
         * there and handed out through `decode`, and a value is shrunk there and handed back.
         * That is right while the conversion accepts everything the inner codec produces.
         *
         * State them when it does not. A conversion that refuses part of the inner codec's range
         * makes the derived arbitrary offer values the pair never makes, so a property run fails
         * on the arbitrary instead of on the codec.
         */
        readonly arbitrary?: (rng: Rng, size: number) => HeldOf<O>
        /** How to shrink one, where the pair is partial. Derived from the inner codec otherwise. */
        readonly shrink?: (value: HeldOf<O>) => readonly HeldOf<O>[]
    },
): AttributeCodec<HeldOf<O>, AttributeOf<C>> &
    TermMark<
        HeldT<
            TermOf<C>,
            O extends StandardSchemaV1 ? ['opaq'] : TermOf<O>,
            ['caller'],
            O extends StandardSchemaV1 ? [StandardInput<O>] : []
        >
    > &
    Free<FreeOf<C> | FreeOf<O>> => {
    const side = heldSide(outer)
    const innerTerm = termOf(inner as unknown as AnyCodec)
    /**
     * **A half that cannot convert returns a `CodecError`**, and the signature says so. A refusal
     * is a value here, as it is everywhere else on this surface, so nothing about declining a
     * conversion is special and no caller has to catch.
     *
     * The two halves are still the one place in a codec where code this library did not write
     * runs, so the throw stays contained as a backstop rather than as the contract. A conversion
     * is ordinary code and ordinary code throws — `new Set(4)` for an adapter typed to take an
     * array, a `.toISOString()` on something that is not a `Date`. A codec that let that escape
     * would make every caller defensive about it, and one already was: a union tries an option to
     * find out whether it is the right one, and had to catch, which meant it also swallowed
     * failures that were nothing to do with an adapter.
     *
     * The check of `outer` runs inside the two halves, and not in `denote`'s row. The term
     * language carries a number as a `DynamoNumber`, so the term of `number` is a sound write
     * occupancy for the JS float adapter and a wrong membership test for it. A library adapter
     * checks the held side in its own conversion, and this checks the side the caller named.
     */
    return codecOfTerm<HeldOf<O>, AttributeOf<C>>({
        kind: 'held',
        inner: innerTerm,
        outer: side.term,
        f: (value: HeldOf<O>) =>
            side.admit(value, 'encode') ?? adapt.encode(value),
        g: (read: Decoded<C>) => {
            const out = adapt.decode(read)
            return failed(out) ? out : (side.admit(out, 'decode') ?? out)
        },
        arbitrary: adapt.arbitrary,
        shrink: adapt.shrink as
            | ((value: never) => readonly unknown[])
            | undefined,
    })
}

/**
 * The held type of a `held`: the input of a foreign schema, or what a codec decodes. A schema that
 * transforms has an output that `validate` refuses, so the held value is the type that `validate`
 * accepts.
 */
export type HeldOf<O> = O extends StandardSchemaV1
    ? StandardInput<O>
    : Decoded<O>

/**
 * **The held side of a `held`**: the term it records, and the check that runs on each half.
 *
 * `admit` answers `undefined` for a value the side admits, and a refusal that names the side
 * otherwise. `at` names the half, because the value that `decode` returns is the caller's defect
 * and a value handed to `encode` past its type is the defect of the code that called.
 */
export const heldSide = (
    outer: AnyCodec | StandardSchemaV1,
): {
    readonly term: Term
    readonly admit: (
        value: unknown,
        at: 'encode' | 'decode',
    ) => CodecError | undefined
} => {
    const refused = (at: 'encode' | 'decode', side: string, why: string) =>
        new HeldSideRefusal(
            at === 'encode'
                ? `the held side of this \`held\`, ${side}, refuses the value before \`encode\` runs: ${why}`
                : `the held side of this \`held\`, ${side}, refuses the value that \`decode\` returned: ${why}`,
        )
    if (!('~standard' in outer)) {
        return {
            term: termOf(outer),
            // the admission `accepts` asks, encoded once so the refusal keeps the codec's reason.
            // `accepts` catches a throw for the same reason: an object codec reaches for `value.a`
            admit: (value, at) => {
                let written: unknown
                try {
                    written = outer.encode(value as never)
                } catch (thrown) {
                    written = new CodecError(thrownReason(thrown))
                }
                return failed(written)
                    ? refused(at, 'a codec of this library', written.reason)
                    : undefined
            },
        }
    }
    const { vendor, validate } = outer['~standard']
    const side = `a ${vendor} schema`
    return {
        /**
         * **The top, because the held side is not this library's to rule.** A foreign schema has
         * a runtime face, `validate`, and no static face: nothing here can read which kinds of
         * value it admits. `opaque` is the term that admits every kind, so the write occupancy is
         * the honest upper bound, and a certificate that needs a smaller one is refused. The
         * runtime check below still restricts the codec to what the schema admits.
         */
        term: { kind: 'opaq' },
        admit: (value, at) => {
            // the boundary: `validate` is code of another library, so a throw and a malformed
            // answer each become a refusal here, and nothing past this line catches
            try {
                const answer = validate(value)
                if (answer instanceof Promise) {
                    return refused(
                        at,
                        side,
                        '`validate` answered with a Promise, and a codec answers synchronously, so the value has no verdict',
                    )
                }
                return answer.issues === undefined
                    ? undefined
                    : refused(
                          at,
                          side,
                          answer.issues
                              .map((issue) => issue.message)
                              .join('; ') ||
                              'the schema reported an issue with no message',
                      )
            } catch (thrown) {
                return refused(
                    at,
                    side,
                    `\`validate\` threw: ${thrownReason(thrown)}`,
                )
            }
        },
    }
}

/**
 * One direction, which is all an older encoding is ever asked for.
 *
 * `legacy` never writes through `older` — that is the whole of what makes it a migration rather than
 * a union — so asking for a whole codec there asked for a half nobody calls. It also *forced* one:
 * an older encoding whose held type differs from the current one has to be adapted, and {@link held}
 * requires both halves, so adapting a reader meant writing an encode path that is dead by
 * construction. Every `AttributeCodec<T>` is one of these, so nothing that worked stops working.
 *
 * @example
 * ```ts
 * // stored as N now; some rows still hold the digits as B, from a migration nobody finished
 * legacy({
 *     current: decimal,
 *     older: { decode: (at) => andThen(binary.decode(at), (b) => decoder.decode(b)) },
 * })
 * ```
 */
export type Reader<T> = {
    readonly decode: (attribute: AttributeValue) => Result<T>
}

/**
 * Reads any of several encodings, writes only `current`.
 *
 * A table holds every shape it has ever held. Reading tolerantly and writing canonically converges:
 * old rows stay readable and every write moves one closer. `decode ∘ encode = id` survives because
 * encode only ever produces `current`.
 *
 * Deliberately breaks {@link checkMembersStable} — changing what is stored *is* the migration — so
 * an index key cannot use it: DynamoDB rejects a write whose index key has the wrong type.
 *
 * @example
 * **One older encoding.** A table that has held three needs two of these, nested — and `legacy` is
 * itself a {@link Reader}, so it nests directly:
 *
 * ```ts
 * legacy({ current: decimal, older: legacy({ current: string, older: fromBytes }) })
 * ```
 *
 * Not a union: {@link union} requires its options to read back as *different* types so that a value
 * says which one it is, and every encoding of one attribute reads back as the same type by
 * definition. Which is the whole difference between the two — a union asks "which of these is it",
 * a migration asks "can any of these still read it".
 *
 * ```ts
 * // stored as N today, and as S in rows written before that; always written as N
 * rate: legacy({ current: decimal, older: string })
 * ```
 *
 * **Two things the rule `(legacy)` asks of the older reader**, and only one of them is checkable.
 *
 * `ran(r) ⊆ dom(e)` — a migration lands on values the current encoding can *write*. This is
 * checked, per read, as soon as the older reader has answered, because that is the earliest
 * anything can know what it returns. The model reads the same way (`Codec.extendRead`), so there
 * the containment is the construction and not a premise. Unchecked it read a row and refused on
 * the way out, which is **(C)** broken at the migrated row and reported at some later write.
 *
 * Coherence (`ReadsCoherently`) — where both readers read an attribute, and the current encoding
 * can write the older answer, they agree — is **not**
 * checkable, and the reason is sharper than that. The current encoding is tried first and the older one only on its
 * failure, here and in the model (`Codec.extendRead`), so on `dom(p_current)` the older reader is
 * never consulted and a disagreement has no observable consequence at all. What the premise buys
 * is that the *ordering does not matter*: with it, and only with it, this presentation equals the order-free
 * union of `p` and the checked older reading. Without it the reading depends on declaration
 * order, which is the one thing that resolution never does. So it is a written obligation, and the thing to check is that two
 * readers of one attribute agree — nothing in this library will tell you they do not.
 *
 * A missing object attribute is {@link fill}, and `fill(legacy({ current, older }), value)` is both.
 */
export const legacy = <const C extends AnyCodec>(options: {
    readonly current: C & WallOver<'legacy', C>
    readonly older: Reader<Decoded<C>>
}): AttributeCodec<Decoded<C>, AttributeOf<C> & AttributeValue> &
    TermMark<['legacy', TermOf<C>]> &
    Free<FreeOf<C>> =>
    codecOfTerm<Decoded<C>, AttributeOf<C> & AttributeValue>({
        kind: 'legacy',
        inner: termOf(options.current),
        r: options.older.decode,
    })
