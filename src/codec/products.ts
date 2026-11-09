import type { ErrorMessage } from '../utils'
import type { AttributeValue, L } from './attribute'
import type {
    AnyCodec,
    AnySpread,
    AttributeCodec,
    AttributeOf,
    Decoded,
    Free,
    FreeOf,
    IsNeverSlot,
    ListTermOf,
    SetAttribute,
    SetOf,
} from './build'
import { codecOfTerm, termOf } from './denote'
import type { WidensRead } from './pathModel'
import { CodecError } from './result'
import type {
    ElementMark,
    ElementsMark,
    elementsMarker,
    FreeTerm,
    spreadMarker,
    Term,
    TermMark,
    TermOf,
} from './term'

/** The declared positions of a list with no spread, or `never`. */
export type FixedElements<C> = C extends {
    readonly [elementsMarker]?: infer Cs extends readonly unknown[]
}
    ? true extends HasSpreadIn<Cs>
        ? never
        : Cs
    : never
/**
 * The positions of a list that come before a spread, or all of them where it has no spread, or
 * `never` for a codec that is no list. The run time reads the same positions: `pre` of the term.
 */
export type LeadingElements<C> = C extends {
    readonly [elementsMarker]?: infer Cs extends readonly unknown[]
}
    ? Leading<Cs>
    : never
export type Leading<Cs extends readonly unknown[]> = Cs extends readonly [
    infer Head,
    ...infer Tail,
]
    ? Head extends AnySpread
        ? []
        : [Head, ...Leading<Tail>]
    : []
export type HasSpreadIn<Cs extends readonly unknown[]> =
    Cs[number] extends infer E ? (E extends AnySpread ? true : false) : false

/**
 * **The `.set()` of a codec**: the set of the codec that carries it, or, where the codec has a
 * literal call, the set of the literal at the alternatives that the call names. One function for
 * each codec that has a `.set()`: the bases, the two numeric adapters, a refinement and an entry of
 * a scope. A repeated value refuses here as it refuses at `string('dog', 'dog')`.
 *
 * The thunk reads the codec that carries the `.set()`, and not the one that was handed in:
 * `.set()` records its element in `def`, so two copies of one codec would give two definitions
 * that differ by a property nobody can see.
 */
export const setOf =
    (carrier: () => AnyCodec, literal?: (...allowed: never[]) => AnyCodec) =>
    (...allowed: readonly unknown[]) =>
        set(
            allowed.length > 0 && literal !== undefined
                ? literal(...(allowed as never[]))
                : carrier(),
        )

// ── collections ─────────────────────────────────────────────────────

/**
 * A non-empty set, stored as the native set its members belong to.
 *
 * **The one set builder, and it is internal.** Every set in the surface comes through here:
 * `string.set()` and the other bases via {@link setOf}, and everything that reduces to a base via
 * {@link equip} — `amount.set()` where `amount = refine(decimal, isAmount)`.
 * It was exported as `set(element)` and is not any more: the capability propagates, so a
 * free-standing form said nothing `.set()` cannot, and having two spellings of one combinator on
 * the surface meant two things to keep in step. It stays a function rather than being inlined
 * because it is where both halves of the rule `(set)`'s premise are checked, and they are checked once.
 *
 * Which set follows from the element's member: `SS`, `NS` or `BS`. Taking a codec rather than being
 * fixed to strings is what makes `price.set()` decode back as prices.
 *
 * **Order is not preserved.** A DynamoDB set comes back in an order the service chooses, so both
 * directions sort. `decode ∘ encode = id` therefore holds only for canonical values; for the rest
 * the law is {@link checkStable}. If order carries meaning use `array(...)`.
 *
 * **Empty is not representable** — encode throws rather than writing what the service refuses.
 */
export const set = <const C extends AnyCodec>(
    element: C,
): AttributeCodec<ReadonlySet<Decoded<C>>, SetOf<C>> => {
    type T = Decoded<C>
    const inner = element as unknown as AttributeCodec<T>
    // the element is the element's own term, so a restriction, a literal and an adapter each ride
    // at the element, and the set is its finite-powerset lift
    const term: Term = { kind: 'set', elem: inner.def }
    return codecOfTerm<ReadonlySet<T>, SetOf<C>>(term)
}

/**
 * A homogeneous positional container, as `L`.
 *
 * `list(spread(c))` says the same thing, and this says it in one word for the common case. A
 * `never` element is admitted rather than refused: the spread is not a slot, so an array of
 * nothing is the empty list, which is a value.
 */
export const array = <const C extends AnyCodec>(element: C): ArrayOver<C> => {
    type T = Decoded<C>
    return codecOfTerm<readonly T[], L<AttributeOf<C>>>({
        kind: 'list',
        pre: [],
        spread: termOf(element as unknown as AnyCodec),
        suf: [],
    })
}

/** The codec that {@link array} returns, and the one that a scope rebuilds below a `ref`. */
export type ArrayOver<C extends AnyCodec> = AttributeCodec<
    readonly Decoded<C>[],
    L<AttributeOf<C>>
> &
    TermMark<['list', [], ['some', TermOf<C>], []]> &
    Free<FreeOf<C>> &
    ElementMark<C>

/**
 * Whether any **declared** position of a list is `never`.
 *
 * The spread is not asked, because the spread is not a slot: a value of exactly the declared
 * length omits every spread position, so a spread at the bottom is the list of its declared
 * positions and that is a value. The model's `Term.list` admits a value of exactly the declared
 * length for the same reason, so a spread at `never` leaves its held set non-empty.
 */
export type ListNeverSlot<Cs extends readonly unknown[]> = Cs extends readonly [
    infer H,
    ...infer T extends readonly unknown[],
]
    ? H extends AnySpread
        ? ListNeverSlot<T>
        : IsNeverSlot<H> extends true
          ? true
          : ListNeverSlot<T>
    : false

/**
 * Nothing, or why this list can hold no value.
 *
 * **The model types a list with a `never` position and gives it an empty held set, which is
 * correct there.** The host refuses it instead, because a position nothing fills makes the whole
 * list unconstructible and `never` already names that term: a declaration with two spellings, one
 * of them a trap, is the shape a constructor should not have.
 *
 * The spread is exempt, and that is the same rule read the other way: it is not a slot, so a list
 * whose spread is `never` is the list of its declared positions, and that is a value.
 */
export type NoNeverSlot<Cs extends readonly unknown[]> =
    ListNeverSlot<Cs> extends true
        ? ErrorMessage<'[list] a declared position is `never`, so nothing fills it and the list holds no value at all. Use `never` itself if that is what you meant'>
        : unknown

/**
 * A positional container: the elements in order, with at most one {@link spread} among them.
 *
 * The call reads as the type it builds. `list(string, spread(decimal), boolean)` is
 * `readonly [string, ...string[], boolean]`, position for position, so a reader checks the
 * declaration against the type without splitting it into parts first.
 *
 * **A spread may sit anywhere, and only once.** It used to have to go last, because the only
 * container that took one was a tuple and a tuple had no suffix. A list has one, so "last" was
 * never the rule: the rule is *once*, and {@link SpreadOnce} states it. Every position after the
 * spread is a fixed element aligned from the right.
 *
 * A value of length `n` is held when `n` is at least the declared positions: the prefix aligns
 * from the left, the suffix from the right, and the middle goes through the spread.
 *
 * @example
 * ```ts
 * list(string, decimal, spread(boolean))  // readonly [string, string, ...boolean[]]
 * list(string, spread(decimal), boolean)  // readonly [string, ...string[], boolean]
 * list(string, decimal)                   // readonly [string, string]
 * list(spread(string))                    // readonly string[], as `array` gives
 * ```
 */
export const list = <const Cs extends readonly (AnyCodec | AnySpread)[]>(
    // asked of the union of the elements rather than mapped over them: one instantiation instead
    // of one per position, and the diagnostic lands on the call either way. Mapping cost +10%
    // across this repo, measured
    ...elements: Cs & SpreadOnce<Cs> & NoNeverSlot<Cs>
): ListCodec<Cs> => {
    const all = elements as readonly unknown[]

    /**
     * `SpreadOnce` refuses a second spread in the *type*, and a cast defeats the type.
     *
     * The cast is the path that matters: with two spreads the first was read as the spread and
     * the second as a fixed element, so the declaration held a shape nobody wrote.
     */
    const spreads = all.filter(isSpread)
    if (spreads.length > 1) {
        throw new CodecError(
            'a list has at most one spread, and this one has ' +
                `${spreads.length} — the positions after the spread are fixed elements`,
        )
    }

    const at = all.findIndex(isSpread)
    const marked = at === -1 ? undefined : (all[at] as AnySpread)

    // as with `map`, the cast keeps the shape each position writes, which
    // `Attribute<'L'>` would flatten to "some list"
    return codecOfTerm({
        kind: 'list',
        pre: (at === -1 ? all : all.slice(0, at)).map((c) =>
            termOf(c as AnyCodec),
        ),
        ...(marked ? { spread: termOf(marked.spread) } : {}),
        suf: (at === -1 ? [] : all.slice(at + 1)).map((c) =>
            termOf(c as AnyCodec),
        ),
    }) as unknown as ListCodec<Cs>
}

/** The codec that {@link list} returns, and the one that a slice at a position rebuilds. */
export type ListCodec<Cs extends readonly unknown[]> = AttributeCodec<
    ListOf<Cs>,
    L<ListWrites<Cs>>
> &
    TermMark<ListTermOf<Cs>> &
    Free<FreeOf<Cs[number]>> &
    ElementsMark<Cs>

/**
 * The elements split at the one spread: what comes before it, what it marks, and what comes after.
 *
 * Accumulated into `Pre` rather than inferred at a fixed position, because the spread may sit
 * anywhere. The accumulator makes the recursion tail-recursive, which is the form TypeScript
 * unrolls to a thousand elements instead of fifty.
 */
export type Split<
    Cs extends readonly unknown[],
    Pre extends readonly unknown[] = [],
> = Cs extends readonly [infer H, ...infer T]
    ? H extends AnySpread
        ? H extends { readonly spread: infer S }
            ? { pre: Pre; spread: S; suf: T }
            : never
        : Split<T, [...Pre, H]>
    : { pre: Pre; spread: undefined; suf: [] }

/**
 * What a list holds: the prefix by position, the spread by repetition, then the suffix by position.
 *
 * Written as two branches on the spread rather than as one type with an empty rest, because
 * `...never[]` in the middle of a tuple type is not the empty middle — it is a tuple no value
 * inhabits.
 */
export type ListOf<Cs extends readonly unknown[]> = Split<Cs> extends {
    pre: infer P extends readonly unknown[]
    spread: infer S
    suf: infer F extends readonly unknown[]
}
    ? S extends AnyCodec
        ? readonly [
              ...{ [I in keyof P]: Decoded<P[I]> },
              ...Decoded<S>[],
              ...{ [I in keyof F]: Decoded<F[I]> },
          ]
        : readonly [
              ...{ [I in keyof P]: Decoded<P[I]> },
              ...{ [I in keyof F]: Decoded<F[I]> },
          ]
    : never

/**
 * The same split, on the stored side.
 *
 * Both sides match the *marker* and then extract with {@link Decoded} and {@link AttributeOf},
 * rather than inferring through `SpreadCodec<…>`. Inferring is the trap: `AttributeCodec` names
 * its value on both sides, so `SpreadCodec<unknown, infer A>` matches nothing and this fell to the
 * fixed-arity branch — a list with a spread typed as though the spread were one element. Silently,
 * because a fixed `[S, N, N]` *is* assignable to `readonly [S, N, ...N[]]`, so an assignment could
 * not tell.
 */
export type ListWrites<Cs extends readonly unknown[]> = Split<Cs> extends {
    pre: infer P extends readonly unknown[]
    spread: infer S
    suf: infer F extends readonly unknown[]
}
    ? S extends AnyCodec
        ? readonly [
              ...{ [I in keyof P]: AttributeOf<P[I]> },
              ...(AttributeOf<S> & AttributeValue)[],
              ...{ [I in keyof F]: AttributeOf<F[I]> },
          ]
        : readonly [
              ...{ [I in keyof P]: AttributeOf<P[I]> },
              ...{ [I in keyof F]: AttributeOf<F[I]> },
          ]
    : never

/**
 * Nothing, or why a spread is not an attribute.
 *
 * An item's members are reached by *name*, so `optional` and `fill` belong here — both are
 * statements about a name. `spread` is a statement about a *position*, and there are no positions
 * in a map, so it is the one marker an object member cannot be.
 */
export type NoSpreadMember<Spec> = [
    Extract<Spec[keyof Spec], { readonly [spreadMarker]: true }>,
] extends [never]
    ? unknown
    : ErrorMessage<'`spread(...)` is a position in a list, not an attribute: an item has names and not positions'>

/** A field whose mark makes it a slot, declared at a term that holds no value. */
export type NoNeverField<Spec> = [
    {
        [K in keyof Spec]: IsNeverSlot<Spec[K]> extends true ? K : never
    }[keyof Spec],
] extends [never]
    ? unknown
    : ErrorMessage<`[object] '${{
          [K in keyof Spec]: IsNeverSlot<Spec[K]> extends true ? K : never
      }[keyof Spec] &
          string}' is declared at \`never\` and the row always writes it, so the object holds no value at all. Mark it \`optional\`, or use \`never\` itself`>

/**
 * Nothing, or why a list carries more than one spread.
 *
 * A spread says "and then any number of these", and a second one has no reading: the positions
 * between the two belong to both. Checked by splitting at the first spread and asking whether
 * anything *after* it is marked, which is one instantiation over the tail rather than one per
 * position.
 */
export type SpreadOnce<Cs extends readonly unknown[]> = Split<Cs> extends {
    suf: infer F extends readonly unknown[]
}
    ? [Extract<F[number], { readonly [spreadMarker]: true }>] extends [never]
        ? unknown
        : ErrorMessage<'a list has at most one `spread(...)` — the positions after it are fixed elements'>
    : unknown

/**
 * A list's repeating positions: *and then any number of these*.
 *
 * The counterpart of `...T[]` in a tuple type, and restricted the same way — it is meaningful only
 * among the elements of a {@link list}, and only once, because the positions between two spreads
 * belong to both. Every other place refuses it, and the type says so rather than a runtime check
 * discovering it.
 *
 * @example
 * ```ts
 * list(string, decimal, spread(boolean))  // readonly [string, string, ...boolean[]]
 * list(string, spread(decimal), boolean)  // readonly [string, ...string[], boolean]
 * list(spread(string))                    // readonly string[], stored as L with no minimum
 * ```
 */
export const spread = <const C extends AnyCodec>(element: C): SpreadOver<C> =>
    ({ spread: element as unknown as AnyCodec }) as unknown as SpreadCodec<
        Decoded<C>,
        AttributeOf<C> & AttributeValue
    >

/**
 * Whether this is a spread marker rather than an element — the runtime half of `spreadMarker`.
 *
 * `spreadMarker` is a `declare const` symbol, so it exists in the type and nowhere else, and
 * {@link list} needs an answer at run time. One own property, checked by name.
 */
export const isSpread = (element: unknown): element is AnySpread =>
    typeof element === 'object' &&
    element !== null &&
    'spread' in element &&
    // and it is not a codec, which is decidable now that every codec carries a definition: a
    // marker is a position and has no `encode` to call
    !('def' in element)

/**
 * A list's repeating position: the element codec, marked for a position.
 *
 * **Not a codec, and it used to say it was.** This was `AttributeCodec<T, A> & { …marker }`, which
 * claimed a marker has an `encode` and a `decode` — true only because the marker was built by
 * spreading its element, so a bare one encoded as its element by accident. A spread is a
 * *position*, and a list is the only thing that has one. It unwraps the marker at construction.
 * Nothing else may be given one, and the type no longer offers a caller the two halves to call.
 */
export type SpreadCodec<T, A extends AttributeValue = AttributeValue> = {
    readonly [spreadMarker]: true
    readonly spread: AttributeCodec<T, A>
}

/** The marker that {@link spread} returns, and the one that a scope rebuilds below a `ref`. */
export type SpreadOver<C extends AnyCodec> = SpreadCodec<
    Decoded<C>,
    AttributeOf<C> & AttributeValue
> &
    TermMark<TermOf<C>> &
    Free<FreeOf<C>> &
    ElementMark<C>

/**
 * `.set()`, where the codec it sits on can be a set's element.
 *
 * The capability {@link set} decides at runtime, stated at the type. Each codec type carries its
 * term `Tm`, so the gate reads two facts. The attribute is `S`, `N` or `B`, the three that a stored
 * set is built from. The term reaches no `legacy`, because a read widening has no set in the model
 * ({@link WidensRead}). A `ref` in the term names an entry that the type cannot read, and the
 * refusal in {@link set} decides there.
 *
 * **One member at a time, and each test non-distributive.** Two shorter spellings were tried and
 * both admit `refine(union([string, number]), p).set()`, which is a set of an element writing two
 * members and cannot exist:
 *
 * - `[A] extends [Attribute<'S'> | Attribute<'N'> | Attribute<'B'>]` — a union of admissible
 *   attributes is assignable to a union of them, so it passes.
 * - the same without the tuples, distributing — each arm passes on its own, and the result is
 *   `{ set: () => SS } | { set: () => NS }`, a union whose members all have a `set`, so calling it
 *   is allowed.
 *
 * Asking each member separately, with `[A] extends [...]` so the question is about `A` whole, is
 * what refuses the union: it is not `Attribute<'S'>`, not `Attribute<'N'>` and not
 * `Attribute<'B'>`, so it falls through.
 *
 * `Record<never, never>` rather than `{}` in the last branch: an intersection with it is the codec
 * unchanged, and `{}` means "anything but null", which would make the intersection accept a `.set`
 * this type is declining to give.
 */
export type SetCapable<T, A extends AttributeValue, Tm = FreeTerm> = [
    SetAttribute<A>,
] extends [never]
    ? Record<never, never>
    : WidensRead<Tm> extends true
      ? Record<never, never>
      : {
            readonly set: () => AttributeCodec<
                ReadonlySet<T>,
                SetAttribute<A>
            > &
                TermMark<['set', Tm]>
        }
