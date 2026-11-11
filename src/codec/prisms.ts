import type { ErrorMessage } from '../utils'
import type { MissingCodec, RefineOptions } from './adapters'
import { fillRefusal } from './adapters'
import type {
    Attribute,
    AttributeValue,
    BS,
    DynamoNumber,
    NS,
    SS,
} from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    AttributeOf,
    Decoded,
    Free,
    FreeOf,
} from './build'
import {
    asFloat,
    asJsNumber,
    codecOfTerm,
    numericAdapter,
    storedOnly,
} from './capabilities'
import { termOf } from './denote'
import type { IsUnion } from './derivedItem'
import type { SetCapable } from './products'
import { CodecError } from './result'
import type {
    BaseT,
    FloatText,
    FloatTexts,
    FreeTerm,
    HeldT,
    LiteralBase,
    LitT,
    NumText,
    NumTexts,
    Rng,
    TermMark,
    TermOf,
} from './term'
import { unboundRefs } from './term'

export type LitsT<
    K extends string,
    L extends readonly unknown[],
> = L extends readonly [infer One]
    ? LitT<K, One>
    : ['union', { -readonly [I in keyof L]: LitT<K, L[I]> }]
export type DecimalT = HeldT<BaseT<'number'>, BaseT<'string'>, 'decimalText'>
export type FloatT<I> = HeldT<I, BaseT<'number'>, ['caller', 'asFloat']>
export type EveryButNumberT = [
    'union',
    [
        BaseT<'string'>,
        BaseT<'boolean'>,
        BaseT<'binary'>,
        BaseT<'null'>,
        ['set', BaseT<'string'>],
        ['set', BaseT<'number'>],
        ['set', BaseT<'binary'>],
        ['list', [], ['some', ['opaq']], []],
        ['object', ['mk', Record<never, never>, ['some', ['opaq']]]],
    ],
]

// ── scalars ─────────────────────────────────────────────────────────

/**
 * The bases a native set can be built from — `SetBase`.
 *
 * `boolean` is the one base with no set: DynamoDB has `SS`, `NS` and `BS`, and no `BOOLS`. Four
 * bases onto three wire members, because `number` and `decimal` are both real and neither is a
 * legacy spelling of the other.
 */
export type SetBase = Exclude<LiteralBase, 'boolean'>

/**
 * **The constant that the term of a codec decides**, the type of {@link constantOf}, row for row: a
 * literal of one value, and a `held` over a literal of one value, a caller's adapter included. The
 * answer is the pair of the text that the literal names and the value that the codec decodes to, or
 * `never` where the term decides none. The text tells two variants apart where their decoded types
 * are one type, because the value of a caller's adapter is caller code and the type cannot read it.
 * A literal whose value type is a union, a union of literals and any other term decide none.
 */
export type ConstantOf<C> = TermOf<C> extends [
    'prim',
    ['literal', string, infer V],
]
    ? ConstantPair<V, Decoded<C>>
    : TermOf<C> extends [
            'held',
            false,
            ['prim', ['literal', string, infer V]],
            unknown,
            [unknown, false],
            unknown,
        ]
      ? ConstantPair<V, Decoded<C>>
      : never
export type ConstantPair<V, D> = IsUnion<V> extends true ? never : [V, D]

/**
 * A string, as `S`. Exact in both directions: DynamoDB does not normalise strings.
 *
 * ```ts
 * string              // any string
 * string('A')         // exactly 'A', and its type says so
 * string('A', 'B')    // one of two
 * string.set()        // SS
 * string.set('A', 'B')// SS whose members are checked
 * ```
 *
 * Callable *and* a codec, the same {@link opaque} trick and for the same reason: `string.encode`
 * and `string('A')` are one name for one ground term, rather than a codec and a constructor that
 * have to be kept in step.
 */
export type StringCodec = AttributeCodec<string, Attribute<'S'>> &
    TermMark<BaseT<'string'>> & {
        <const T extends string>(
            only: T,
        ): AttributeCodec<T, Attribute<'S'>> & TermMark<LitT<'string', T>>
        <const L extends readonly string[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'S'>> &
            TermMark<LitsT<'string', L>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<string>, SS> &
                TermMark<['set', BaseT<'string'>]>
            <const L extends readonly string[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, SS> &
                TermMark<['set', LitsT<'string', L>]>
        }
    }

/* ── the terms, denoted ───────────────────────────────────────────────────────────────── */

/** @see {@link StringCodec} */
export const string: StringCodec = codecOfTerm({
    kind: 'string',
}) as unknown as StringCodec

/**
 * **`N` itself, and the one native numeric term.** DynamoDB's own number, held as
 * {@link DynamoNumber}: exact to 38 significant digits, validated once at construction, and
 * already in the spelling the store returns.
 *
 * ```ts
 * dynamoNumber                       // an exact number
 * dynamoNumber(DynamoNumber.from('1.5'))   // …and a literal at it
 * dynamoNumber.set()                 // NS
 * ```
 *
 * **Three carriers write `N`, and the other two are adapters over this one.** They are no longer
 * terms of their own: a JS float and a decimal string are two ways a caller may hold this, not two
 * things the service stores.
 *
 * | codec | holds | exact | what it costs |
 * | --- | --- | --- | --- |
 * | `dynamoNumber` | {@link DynamoNumber} | yes, 38 digits | the caller builds one |
 * | {@link decimal} | `string` | yes, 38 digits | text the caller re-validates, and refuses a denormal spelling |
 * | {@link number} | JS `number` | no, about 15 digits | rounding, by construction |
 */
export const dynamoNumber: AttributeCodec<DynamoNumber, Attribute<'N'>> &
    TermMark<BaseT<'number'>> & {
        <const T extends DynamoNumber>(
            only: T,
        ): AttributeCodec<T, Attribute<'N'>> &
            TermMark<LitT<'number', NumText<T>>>
        // a tuple, because inference unions no two object candidates: `readonly T[]` reads `T` off
        // the first numeral, and refuses a second numeral with another text
        <const T extends readonly DynamoNumber[]>(
            ...allowed: T
        ): AttributeCodec<T[number], Attribute<'N'>> &
            TermMark<LitsT<'number', NumTexts<T>>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<DynamoNumber>, NS> &
                TermMark<['set', BaseT<'number'>]>
            <const T extends readonly DynamoNumber[]>(
                ...allowed: T
            ): AttributeCodec<ReadonlySet<T[number]>, NS> &
                TermMark<['set', LitsT<'number', NumTexts<T>>]>
        }
    } = codecOfTerm({ kind: 'number' }) as never

/**
 * The refusal in the type of a decimal literal that is not the stored spelling: the run time of
 * {@link decimal} refuses the text that {@link DynamoNumber.from} gives another print. A text that
 * is no literal reads as the stored spelling, so a spread of `string[]` stays legal.
 */
export type StoredSpelling<T extends string> = string extends T
    ? unknown
    : [
            NumText<
                Extract<ReturnType<typeof DynamoNumber.from<T>>, DynamoNumber>
            >,
        ] extends [T]
      ? unknown
      : ErrorMessage<`[decimal] '${T}' is not the spelling DynamoDB stores, which returns the normalised form: no leading or trailing zeros, no exponent, no '+'`>

/**
 * A decimal held as a string, stored as `N`. The codec for money — nothing becomes a JS number, so
 * nothing rounds.
 *
 * **An adapter over {@link dynamoNumber}, not a base of its own.** `decimal` was a second ground
 * base at `N` and is a change of carrier now: the same number, handed to the caller as text.
 *
 * **Only the form DynamoDB stores.** It normalises what it accepts — `'1.50'` becomes `'1.5'`,
 * `'007'` becomes `'7'`, `'1e5'` becomes `'100000'` — and this codec hands back the digits, so
 * anything else would come back as a different string from the one written. That is a round trip
 * failing across the database, where neither the type nor the law suite can see it, so it is
 * refused at the point where it is still local: `encode` rejects a denormal numeral rather than
 * quietly rewriting it, because rewriting is how you lose track of which value was meant.
 *
 * That refusal is this codec's and not the carrier's. {@link DynamoNumber} normalises, because it
 * holds a number; this hands back text, so it refuses instead.
 *
 * `'1.50'` is not a price this codec will write. `'1.5'` is. Where exact digits matter more than
 * numeric ordering — trailing zeros that mean something — use {@link string}.
 */
export type DecimalCodec = AttributeCodec<string, Attribute<'N'>> &
    TermMark<DecimalT> & {
        <const T extends string>(
            only: T & StoredSpelling<T>,
        ): AttributeCodec<T, Attribute<'N'>> &
            TermMark<HeldT<LitT<'number', T>, LitT<'string', T>, 'decimalText'>>
        <const L extends readonly string[]>(
            ...allowed: L & { [I in keyof L]: StoredSpelling<L[I]> }
        ): AttributeCodec<L[number], Attribute<'N'>> &
            TermMark<
                HeldT<LitsT<'number', L>, LitsT<'string', L>, 'decimalText'>
            >
        readonly set: {
            (): AttributeCodec<ReadonlySet<string>, NS> &
                TermMark<['set', DecimalT]>
            <const L extends readonly string[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, NS> &
                TermMark<
                    [
                        'set',
                        HeldT<
                            LitsT<'number', L>,
                            LitsT<'string', L>,
                            'decimalText'
                        >,
                    ]
                >
        }
    }
export const decimal: DecimalCodec = numericAdapter<string>(
    { kind: 'number' },
    { kind: 'string' },
    storedOnly,
    (held) => held.toString(),
    'decimalText',
) as never

/**
 * A JS number, stored as `N`. Lossy by construction — `N` carries 38 digits, `number` about 15.
 * Right for enums, counts and flags; wrong for money, which is {@link decimal}.
 *
 * **An adapter over {@link dynamoNumber}, not a base of its own**, and the conversion is where the
 * loss is: the float has already rounded before this codec sees it. `number.set()` and
 * `decimal.set()` are two carriers over one wire set: each is the set of its adapter.
 */
export type NumberCodec = AttributeCodec<number, Attribute<'N'>> &
    TermMark<FloatT<BaseT<'number'>>> & {
        <const T extends number>(
            only: T,
        ): AttributeCodec<T, Attribute<'N'>> &
            TermMark<FloatT<LitT<'number', FloatText<T>>>>
        <const L extends readonly number[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'N'>> &
            TermMark<FloatT<LitsT<'number', FloatTexts<L>>>>
        readonly set: {
            (): AttributeCodec<ReadonlySet<number>, NS> &
                TermMark<['set', FloatT<BaseT<'number'>>]>
            <const L extends readonly number[]>(
                ...allowed: L
            ): AttributeCodec<ReadonlySet<L[number]>, NS> &
                TermMark<['set', FloatT<LitsT<'number', FloatTexts<L>>>]>
        }
    }
export const number: NumberCodec = numericAdapter<number>(
    { kind: 'number' },
    { kind: 'number' },
    asFloat,
    asJsNumber,
    'float',
) as never

/**
 * A boolean, as `BOOL`.
 *
 * `boolean(true)` is a literal at `BOOL`, which nothing on the old surface could spell —
 * `literal(...)` took a string or a number and there was no third option. There is deliberately no
 * `boolean.set()`: DynamoDB has `SS`, `NS` and `BS`, and no set of booleans.
 */
export type BooleanCodec = AttributeCodec<boolean, Attribute<'BOOL'>> &
    TermMark<BaseT<'boolean'>> & {
        <const T extends boolean>(
            only: T,
        ): AttributeCodec<T, Attribute<'BOOL'>> & TermMark<LitT<'boolean', T>>
        <const L extends readonly boolean[]>(
            ...allowed: L
        ): AttributeCodec<L[number], Attribute<'BOOL'>> &
            TermMark<LitsT<'boolean', L>>
    }

/** @see {@link BooleanCodec} */
export const boolean: BooleanCodec = codecOfTerm({
    kind: 'boolean',
}) as unknown as BooleanCodec

/**
 * The `NULL` point: the one value `null`, stored as `⟨NULL, ∗⟩`.
 *
 * Named `nullValue` because `null` is a keyword and `NULL` is already the attribute type. It says
 * what it holds, which is the whole of it — one value.
 *
 * What it is for: a tombstone, and a payload-free option of a discriminated union. Before it, a
 * schema could say "this attribute is a string" or "this attribute is optional", and could not say
 * "this attribute is exactly `NULL`" — the value language had `null` and the attribute domain had
 * `NULL`, and no codec denoted either. That gap was found by asking whether `nullable(c)` could be
 * written as `union(c, nullValue)`; it could not, because the right-hand side was not expressible.
 *
 * Distinct from {@link nullable}, which *adds* `null` to another codec's held set. This holds
 * nothing else.
 *
 * Not callable, and there is nothing for it to be: the model's `GroundKind.null` has carrier `Unit`,
 * so `literal .null` can say nothing this codec does not already say.
 */
export const nullValue: AttributeCodec<null, Attribute<'NULL'>> &
    TermMark<BaseT<'null'>> = codecOfTerm({
    kind: 'null',
})

/**
 * Binary, as `B`.
 *
 * `binary(bytes)` compares **by bytes**, not by reference — two `Uint8Array`s holding the same
 * octets are the same alternative, and a decoded value comes back as the member of `ℓ` rather than
 * as the array that was read off the wire.
 */
export type BinaryCodec = AttributeCodec<Uint8Array, Attribute<'B'>> &
    TermMark<BaseT<'binary'>> & {
        // a `Uint8Array` has no literal type: the bytes are unknown text at the type level
        (
            only: Uint8Array,
        ): AttributeCodec<Uint8Array, Attribute<'B'>> &
            TermMark<LitT<'binary', string>>
        (
            ...allowed: readonly Uint8Array[]
        ): AttributeCodec<Uint8Array, Attribute<'B'>> &
            TermMark<['union', LitT<'binary', string>[]]>
        readonly set: {
            (): AttributeCodec<ReadonlySet<Uint8Array>, BS> &
                TermMark<['set', BaseT<'binary'>]>
            (
                ...allowed: readonly Uint8Array[]
            ): AttributeCodec<ReadonlySet<Uint8Array>, BS> &
                TermMark<['set', ['union', LitT<'binary', string>[]]]>
        }
    }

/** @see {@link BinaryCodec} */
export const binary: BinaryCodec = codecOfTerm({
    kind: 'binary',
}) as unknown as BinaryCodec

// ── narrowing ───────────────────────────────────────────────────────

/**
 * Narrows what a codec decodes to, checking it on the way in.
 *
 * Where a brand gets applied. `decimal` cannot stand in for a `Price` because `decode` returns a
 * bare `string` — and a row is data somebody else wrote, so running the brand's own predicate is
 * the right way to get one back, rather than asserting.
 *
 * @example
 * ```ts
 * const price = refine(decimal, isPrice, {
 *     // `decimal` generates negatives, which are not Prices; say what a valid one looks like
 *     arbitrary: (rng) => pick(rng, ['0', '1', '0.5']) as Price,
 * })
 * const petId = refine(string, isPetId)
 * ```
 *
 * **The obligation is `is`, and it is yours.** Like `held`'s pair and `custom`'s two functions,
 * `refine` is sound *iff* the predicate honestly decides `Narrow` — nothing here can check that,
 * because `Narrow` is a type and `is` is a claim about it. Both directions run the predicate:
 *
 * - **`decode` runs `is`.** A stored value was never type-checked — a row is data somebody else
 *   wrote — so the predicate is the only thing between the database and `Narrow`.
 * - **`encode` runs `is`.** The argument is a `Narrow` by its type, and a value that an `as` upstream
 *   forces past the type is refused with a `CodecError` of kind `refused`, and never written. This is
 *   `Codec.restrict` of the model, which restricts the graph in both directions.
 */
export type Refined<
    T,
    A extends AttributeValue,
    Tm = FreeTerm,
> = AttributeCodec<T, A> & SetCapable<T, A, Tm>

/**
 * A codec narrowed by a predicate. The term `['refine', Tm, () => Narrow]` keeps the term under
 * the predicate, so the members of a slice and the walk of `at` read a literal through a
 * refinement. It keeps the narrowed type too, so a path and a scope decode the brand that the
 * predicate proves. The type sits behind a function, where a walk of the term stops: a recursive
 * type names its own term.
 */
export function refine<
    Wide,
    Narrow extends Wide,
    A extends AttributeValue,
    Tm = FreeTerm,
    F extends string = never,
>(
    inner: AttributeCodec<Wide, A> & TermMark<Tm> & Free<F>,
    is: (value: Wide) => value is Narrow,
    options?: RefineOptions<Narrow>,
): Refined<Narrow, A, ['refine', Tm, () => Narrow]> &
    TermMark<['refine', Tm, () => Narrow]> &
    Free<F>
export function refine<Wide, Narrow extends Wide, A extends AttributeValue>(
    inner: AttributeCodec<Wide, A>,
    is: (value: Wide) => value is Narrow,
    options: RefineOptions<Narrow> = {},
): Refined<Narrow, A, unknown> {
    const what = options.describe ?? 'the expected form'

    /**
     * Generation falls back to filtering the inner codec's values, and reports when that thins the
     * search badly.
     *
     * `decimal` generates negatives, which are not prices, and fractions, which are not sequence numbers —
     * so a run of a hundred cases can quietly be a run of forty. The declaration is not the place to
     * fix that: a predicate is what a brand *is*, and demanding an example of one beside it would
     * tax every codec for something only a property run cares about. But a run that has been halved
     * without saying so is worth a word, and this can only be reached from an arbitrary, so the word
     * only ever lands in a test.
     */
    // `member` reads through a refinement, which is what lets a set of a brand work; `constantOf`
    // does not, because the predicate may be exactly what rejects the constant.
    //
    // `equip` carries `.set()` across the refinement, and it is the whole of why the brand
    // survives: `amount.set()` decodes as `ReadonlySet<Price>` because the set is built from
    // `amount`, where the predicate that produces a `Price` already lives.
    return codecOfTerm<Narrow, A>({
        kind: 'refine',
        inner: termOf(inner as unknown as AnyCodec),
        q: {
            is: is as (value: never) => boolean,
            what,
            arbitrary: options.arbitrary as
                | ((rng: Rng, size: number) => unknown)
                | undefined,
            onThinSearch: options.onThinSearch,
        },
    }) as unknown as Refined<Narrow, A, unknown>
}

/**
 * Reads a missing attribute as a value, and writes the attribute always.
 *
 * Not {@link optional}: the entity always has it, the *data* may not — a row written before the
 * attribute existed. Replaces `item.channel ?? 'IN_STORE'` at every read site.
 *
 * **The fill value must be writable by the codec it fills**, and that is checked here, at the
 * declaration. The model carries it as the premise `hfill` of `carrier_objectCodec`: the fill value of a
 * `.fill` slot is in the write domain of its codec. The premise exists because the proof failed
 * without it: a row missing the attribute reads back as the fill value, and if the inner codec cannot write that value the item cannot be written back —
 * **(C)** broken at the read, with the refusal surfacing on some later write rather than at the
 * declaration responsible for it. `fill(string('A'), 'B')` is the whole of it.
 *
 * The fill value is a **value and not a thunk**, which is what makes the check possible here rather
 * than on whichever read happens to need it first. A fill value that the codec writes through a
 * {@link ref} that no scope binds is checked by the {@link scope} that binds the name. It does not become shared state for that: the
 * declaration holds one value and each read that needs one gets a copy of it, so a mutable fill value
 * still cannot leak between entities. The copy keeps the class of each value, because a decode must
 * be writable: a `DynamoNumber` is shared, being immutable. Primitives are handed over as they are,
 * being unable to leak anything.
 */
export const fill = <const C extends AnyCodec>(
    // the *argument's own* type, not a re-declared `AttributeCodec<T, A>`: the guard has to see the
    // marker the caller passed, and a parameter written in terms of inferred `T` and `A` reconstructs
    // a plain codec that never carries one
    inner: C,
    // `NoInfer` so the codec is the only thing that says what it holds. Inferring from both sites
    // unified them, and a fill value written `'A'` widens to `string`, which then refused the very
    // codec it fills — invisible while the entity was declared first and pinned it itself
    value: NoInfer<Decoded<C>>,
): MissingCodec<Decoded<C>, AttributeOf<C> & AttributeValue, C> &
    TermMark<['fill', TermOf<C>]> &
    Free<FreeOf<C>> => {
    // The rule `(fill)`: the fill value must be *writable*, or a row missing the name decodes to a
    // value the item cannot be written back as — (C) broken at the read, with the refusal arriving
    // on the next write instead of at the declaration that caused it. Decidable from the
    // declaration alone, which is why the fill value is a value and not a thunk
    const filledCodec = inner as unknown as AnyCodec
    // **A fill value that the codec writes through an unbound `ref` is checked by the scope**, on the
    // closed copy, because the write reads through the ref
    if (unboundRefs([termOf(filledCodec)]).size === 0)
        checkFill(filledCodec, value)
    const attribute = inner as unknown as AttributeCodec<Decoded<C>>
    return {
        codec: attribute,
        def: { mark: 'fill', t: termOf(inner), v: value },
    } as unknown as MissingCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue,
        C
    > &
        TermMark<['fill', TermOf<C>]> &
        Free<FreeOf<C>>
}

/** Throws the refusal of a fill value that the codec it fills cannot write. */
export const checkFill = (filledCodec: AnyCodec, value: unknown): void => {
    const refusal = fillRefusal(filledCodec, value)
    if (refusal) {
        throw new CodecError(
            `The fill value of \`fill\` must be a value the codec it fills can write, and this \`${filledCodec.def.kind}\` refuses the fill value: ${refusal.message}. A row missing the attribute would read back as the fill value and then refuse on the way out`,
        )
    }
}
/**
 * The inner term of an adapter of the library, as `decimal('1')` and `number(1)` build, or `never`.
 * A caller's adapter (`['caller']`) pins nothing at the type: its decoded type is the caller's.
 */
export type LibraryInner<N> = N extends [
    'held',
    unknown,
    infer I,
    unknown,
    [infer G, unknown],
    ...unknown[],
]
    ? [G] extends [['caller']]
        ? never
        : I
    : never

/**
 * **The term that admits no value**, the bottom that the meet and the slice return.
 *
 * `Term.never` on both sides. The model types it — `TOp.rule` gives it the held set `HNever`,
 * which is `False` — and denotes it as `Codec.empty`, whose laws hold vacuously because both
 * domains are empty.
 *
 * **A constructor rather than a `discriminatedUnion` over no options.** The derived form works and
 * costs a structural test: an empty option list is a term a caller can build by accident, so every
 * rule reading it as the bottom reads that accident as intent, and the term carries a discriminator
 * no value will ever name. `discriminatedUnion` stays refused on an empty list — that list is a
 * typo or a `map` over an empty array — and this is the one name that reaches the bottom.
 *
 * It is the zero of `union`: an empty option is compatible with every option
 * (`Closed.pairwiseCompat_never_left`, `Closed.pairwiseCompat_never_right`), so `union([X, never])` is `X`.
 */
export const never: AttributeCodec<never, never> & TermMark<['never']> =
    codecOfTerm<never, never>({ kind: 'never' })
