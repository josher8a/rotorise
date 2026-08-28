/**
 * The laws, as tests.
 *
 * Split from the codecs deliberately. Everything here runs against a codec somebody else built, in
 * a test somebody else wrote — none of it is reachable from encoding or decoding a row. Shipping it
 * in the main entry meant every consumer carried a property-testing harness to production, and
 * `sideEffects: false` could not shake it out of a CommonJS `require`.
 *
 * Import it where it belongs:
 *
 * ```ts
 * import { checkRoundTrip, rngFrom } from 'rotorise/testing'
 * ```
 *
 * The generators themselves stay on the codecs — `arbitrary` and `shrink` are a codec describing
 * what it can carry, which is a fact about the codec and not about testing. What moved is the
 * machinery that *drives* them.
 *
 * ── which laws these are ───────────────────────────────────────────────────────────────────────
 *
 * They have names in the literature, and the names are worth knowing because they explain *which*
 * law is checked here and which deliberately is not.
 *
 * A codec is an **embedding-projection pair** into `AttributeValue`, the universal domain every
 * stored value lives in — the reading of types as retracts of one domain goes back to Scott (1972)
 * and is standard in denotational semantics. An e-p pair `(e, p)` satisfies two laws, and only the
 * first is an equality:
 *
 * ```
 * p ∘ e = id        decode ∘ encode = id          → checkRoundTrip
 * e ∘ p ⊑ id        encode ∘ decode ⊑ id          → checkStable
 * ```
 *
 * The `⊑` is the whole subtlety, and it is why {@link checkStable} asks what it asks. Taken as an
 * equality the second law is *false* here and should be: `set` sorts and deduplicates, `decimal`
 * normalises, so `encode(decode({ SS: ['b', 'a'] }))` is `{ SS: ['a', 'b'] }` — the same set, not the
 * same bytes. So stability is checked *modulo* the equivalence "decodes to the same entity", which is
 * exactly a **quotient lens** — a bidirectional transformation well behaved modulo an equivalence the
 * programmer controls, the equivalence being induced by a **canonizer** (Foster, Pilkiewicz and
 * Pierce, ICFP 2008). Sorting a set and normalising digits are canonizers.
 *
 * {@link checkIso} is the one place the second law *is* an equality, because a {@link held} adapter
 * claims a true isomorphism rather than a retraction — and it checks the direction
 * `checkRoundTrip` cannot reach.
 *
 * The lens laws for the asymmetric case are Foster, Greenwald, Moore, Pierce and Schmitt's GetPut /
 * PutGet (TOPLAS 2007); there are a dozen variants and a taxonomy of them if the distinctions matter.
 */
import type { AttributeMap, AttributeValue } from './attribute'
import { memberOf } from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    CodecDef,
    ItemCodec,
    RestPolicy,
    Rng,
} from './codec'
import { CodecError, failed, opaque, writes } from './codec'

/** mulberry32 — small, fast, and good enough to search a value space. */
export const rngFrom = (seed: number): Rng => {
    let a = seed >>> 0
    return () => {
        a = (a + 0x6d2b79f5) >>> 0
        let t = Math.imul(a ^ (a >>> 15), 1 | a)
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296
    }
}

// ── the law, as a test ──────────────────────────────────────────────

/**
 * `decode(encode(value))` — the law, applied once.
 */
export const roundTrip = <T>(
    itemCodec_: {
        unsafeEncode: (item: T) => AttributeMap
        unsafeDecode: (item: AttributeMap) => T
    },
    value: T,
): T => itemCodec_.unsafeDecode(itemCodec_.unsafeEncode(value))

/** The minimum a codec must expose to be checked. */
export type Checkable<T> = {
    unsafeEncode: (item: T) => AttributeMap
    unsafeDecode: (item: AttributeMap) => T
    /** What the codec is, which is what {@link arbitraryOf} generates from. */
    def?: CodecDef
}

/**
 * How a value failed, to the precision needed to know it is still the same failure.
 *
 * Shrinking must preserve the failure mode. A candidate that throws where the original merely
 * returned the wrong value is not a smaller counterexample — it is a different bug, and following it
 * loses the one that was found. So a reduction is accepted only when it fails the same way.
 */
type Failure =
    | { readonly kind: 'mismatch'; readonly returned: unknown }
    | { readonly kind: 'threw'; readonly message: string }

/**
 * The same kind of failure, and for a throw the same message.
 *
 * A mismatch is compared by kind alone: the returned value is what shrinking is *trying* to change,
 * so requiring it to stay the same would refuse every reduction.
 */
const sameFailure = (a: Failure, b: Failure) =>
    a.kind === b.kind &&
    (a.kind !== 'threw' || a.message === (b as { message: string }).message)

const failureOf = <T>(
    subject: Pick<Checkable<T>, 'unsafeEncode' | 'unsafeDecode'>,
    value: T,
    equals: (a: unknown, b: unknown) => boolean,
): Failure | undefined => {
    let returned: T
    try {
        returned = subject.unsafeDecode(subject.unsafeEncode(value))
    } catch (cause) {
        return { kind: 'threw', message: String(cause) }
    }
    return equals(returned, value) ? undefined : { kind: 'mismatch', returned }
}

/**
 * Reduces a counterexample while it keeps failing the same way.
 *
 * Greedy: take the first candidate that still fails and restart from it, so each pass is bounded by
 * how many reductions a value offers rather than by their product. `budget` caps total candidates
 * tried, because a deeply nested value can offer a great many.
 */
const shrinkCounterexample = <T>(
    subject: Pick<Checkable<T>, 'unsafeEncode' | 'unsafeDecode' | 'def'>,
    value: T,
    failure: Failure,
    equals: (a: unknown, b: unknown) => boolean,
    refine: (value: T) => T,
    filter: (value: T) => boolean,
    budget = 2000,
): { value: T; steps: number } => {
    if (!subject.def) return { value, steps: 0 }
    let best = value
    let steps = 0
    let spent = 0

    for (let progress = true; progress && spent < budget; ) {
        progress = false
        for (const raw of shrinkOf(
            subject as unknown as AnyCodec,
            best,
        ) as readonly T[]) {
            if (spent++ >= budget) break
            const candidate = refine(raw)
            // refinement can undo a reduction; a candidate equal to what we have is not progress
            if (!filter(candidate) || equals(candidate, best)) continue
            const candidateFailure = failureOf(subject, candidate, equals)
            if (candidateFailure && sameFailure(failure, candidateFailure)) {
                best = candidate
                steps++
                progress = true
                break
            }
        }
    }
    return { value: best, steps }
}

export type CheckOptions<T = unknown> = {
    /** How many values to try. */
    count?: number
    /** Reported with any counterexample, and enough to reproduce it exactly. */
    seed?: number
    /** Bounds recursion depth in nested structures. */
    size?: number
    /**
     * How two decoded entities are compared.
     *
     * Defaults to {@link structuralEquals}. On Node, `util.isDeepStrictEqual` is the more thorough
     * choice and is a drop-in — it is not imported here because a `node:` import would make this
     * package Node-only, and Rotorise has no dependencies:
     *
     * ```ts
     * import { isDeepStrictEqual } from 'node:util'
     * checkRoundTrip(Pet, { equals: isDeepStrictEqual })
     * ```
     */
    equals?: (a: unknown, b: unknown) => boolean
    /**
     * Restores invariants that hold between attributes.
     *
     * Attributes are generated independently, so nothing keeps them consistent with each other: an
     * a `Pet` can come out with an index attribute set while its status says the index should not
     * exist. That does not affect the round-trip law — a codec does not care whether an entity makes
     * business sense — but it makes every other property unassertable, and it means a derived key
     * can never be exercised. Repair here rather than discard: it costs one pass instead of an
     * unbounded number of retries.
     *
     * Applied to generated values *and* to every shrink candidate, so a reported counterexample is
     * always an entity that could actually exist.
     */
    refine?: (value: T) => T
    /**
     * A precondition. Values failing it are discarded and regenerated.
     *
     * Prefer {@link CheckOptions.refine} where the invariant can be repaired; a filter that rejects
     * most values wastes the search, and one that rejects all of them is reported rather than spun on.
     */
    filter?: (value: T) => boolean
}

/**
 * `decode ∘ encode = id`, over generated entities.
 *
 * Generation is driven by the codec rather than the TypeScript type — see
 * {@link AttributeCodec.arbitrary} — so `decimal` yields normalised decimals and `set(string)`
 * never yields the empty set. A structurally free generator would produce values DynamoDB itself
 * rejects and blame the codec.
 *
 * Deterministic: the same seed reproduces a counterexample from CI.
 */
export const checkRoundTrip = <T>(
    subject: Checkable<T>,
    {
        count = 100,
        seed = 0x5eed,
        size = 4,
        equals = structuralEquals,
        refine = (value: T) => value,
        filter = () => true,
    }: CheckOptions<T> = {},
): void => {
    const rng = rngFrom(seed)
    const maxDiscards = Math.max(100, count * 10)
    let discards = 0

    for (let i = 0; i < count; i++) {
        const value = refine(
            arbitraryOf(subject as unknown as AnyCodec, rng, size) as T,
        )
        if (!filter(value)) {
            if (++discards > maxDiscards) {
                throw new CodecError(
                    `filter rejected ${discards} values with seed ${seed}; it is too narrow to search with, or refine should repair instead`,
                )
            }
            i--
            continue
        }
        const failure = failureOf(subject, value, equals)
        if (!failure) continue

        const { value: minimal, steps } = shrinkCounterexample(
            subject,
            value,
            failure,
            equals,
            refine,
            filter,
        )
        const minimalFailure = failureOf(subject, minimal, equals) ?? failure
        const reduced =
            steps === 0
                ? ''
                : `\n  (shrunk in ${steps} step${steps === 1 ? '' : 's'} from ${JSON.stringify(value)})`

        throw new CodecError(
            minimalFailure.kind === 'threw'
                ? `unsafeDecode(unsafeEncode(x)) threw at case ${i} with seed ${seed}: ${minimalFailure.message}\n  x = ${JSON.stringify(minimal)}${reduced}`
                : `unsafeDecode(unsafeEncode(x)) !== x at case ${i} with seed ${seed}\n  x        = ${JSON.stringify(minimal)}\n  returned = ${JSON.stringify(minimalFailure.returned)}${reduced}`,
        )
    }
}

/**
 * `decode ∘ encode ∘ decode = decode` — the weaker law that survives a lossy attribute.
 *
 * DynamoDB normalises `N` (`'1.50'` → `'1.5'`) and reorders sets, so `decode ∘ encode = id` is
 * false for those. What holds is that one pass through storage reaches a fixed point. The
 * `parse(print(parse(s))) = parse(s)` of tolerant parsers, and the law to assert for a table whose
 * rows predate the current codec.
 */
export const checkStable = <T>(
    subject: Pick<Checkable<T>, 'unsafeEncode' | 'unsafeDecode'>,
    items: readonly AttributeMap[],
    equals: (a: unknown, b: unknown) => boolean = structuralEquals,
): void => {
    for (const [i, item] of items.entries()) {
        const once = subject.unsafeDecode(item)
        const twice = subject.unsafeDecode(subject.unsafeEncode(once))
        if (!equals(twice, once)) {
            throw new CodecError(
                `unsafeDecode(unsafeEncode(unsafeDecode(item))) !== unsafeDecode(item) at item ${i}\n  once  = ${JSON.stringify(once)}\n  twice = ${JSON.stringify(twice)}`,
            )
        }
    }
}

/**
 * The member each attribute carries, recursively — the shape of an item without its values.
 */
const membersOf = (value: AttributeValue): unknown => {
    const member = memberOf(value)
    if (member === 'M') {
        return {
            M: Object.fromEntries(
                Object.entries(value.M ?? {}).map(([k, v]) => [
                    k,
                    membersOf(v),
                ]),
            ),
        }
    }
    if (member === 'L') return { L: (value.L ?? []).map(membersOf) }
    return member
}

/**
 * The three ways to encode an attribute agree.
 *
 * ```
 * encodePartial(x)           = encode(x)              for a complete x
 * encodePartial({ k: x[k] }) = { k: encode(x)[k] }
 * field(k).encode(x[k])      = encode(x)[k]
 * ```
 *
 * `encode` builds a `PutItem`, `encodePartial` an `UpdateItem`, `field(k).encode` one
 * `ExpressionAttributeValues` entry. Nothing structural forces them to agree, and a divergence means
 * a row that reads back differently depending on how it was last touched.
 *
 * Invisible to {@link checkRoundTrip}: each path round-trips perfectly on its own.
 */
export const checkEncodePaths = <T, Spec>(
    subject: ItemCodec<T, Spec>,
    {
        count = 100,
        seed = 0x5eed,
        size = 4,
        equals = structuralEquals,
        refine = (value: T) => value,
    }: CheckOptions<T> = {},
): void => {
    const rng = rngFrom(seed)
    const fail = (what: string, i: number, a: unknown, b: unknown) => {
        throw new CodecError(
            `${what} at case ${i} with seed ${seed}\n  ${JSON.stringify(a)}\n  ${JSON.stringify(b)}`,
        )
    }

    for (let i = 0; i < count; i++) {
        const value = refine(
            arbitraryOf(subject as unknown as AnyCodec, rng, size) as T,
        )
        const full = subject.unsafeEncode(value)

        if (!equals(subject.unsafeEncode(value), full)) {
            fail(
                'unsafeEncode is not deterministic',
                i,
                full,
                subject.unsafeEncode(value),
            )
        }
        if (!equals(subject.unsafeEncodePartial(value), full)) {
            fail(
                'unsafeEncodePartial of a complete entity differs from unsafeEncode',
                i,
                subject.unsafeEncodePartial(value),
                full,
            )
        }

        // read wide on purpose: an item codec now types what it writes attribute by attribute, and
        // this walks whatever names the entity happens to carry — which is not something a precise
        // shape can be indexed by, nor something the harness should have to know in advance
        const written = full as AttributeMap

        for (const name of Object.keys(value as Record<string, unknown>)) {
            const attribute = written[name]
            if (attribute === undefined) continue
            const one = (value as Record<string, unknown>)[name]

            const alone = subject.unsafeEncodePartial({
                [name]: one,
            } as Partial<T>) as unknown as AttributeMap
            if (!equals(alone[name], attribute)) {
                fail(
                    `unsafeEncodePartial of '${name}' alone differs from unsafeEncode`,
                    i,
                    alone[name],
                    attribute,
                )
            }

            const viaField = (
                subject.field(name as keyof Spec) as unknown as AnyCodec
            ).unsafeEncode(one as never)
            if (!equals(viaField, attribute)) {
                fail(
                    `field('${name}').unsafeEncode differs from unsafeEncode`,
                    i,
                    viaField,
                    attribute,
                )
            }
        }
    }
}

/**
 * `member ∘ encode ∘ decode = member` — a read-modify-write leaves every attribute in its member.
 *
 * The part of `encode ∘ decode = id` that has to hold. An attribute that goes in as `N` and comes
 * back as `S` has changed what queries work against it: numeric sort keys stop ordering, and
 * nothing throws.
 *
 * Invisible to {@link checkRoundTrip} and {@link checkStable} — both compare decoded values, which
 * an `N`-to-`S` rewrite leaves untouched.
 */
export const checkMembersStable = <T>(
    subject: Pick<Checkable<T>, 'unsafeEncode' | 'unsafeDecode'> & {
        rest?: RestPolicy<unknown>
    },
    items: readonly AttributeMap[],
    equals: (a: unknown, b: unknown) => boolean = structuralEquals,
): void => {
    // under `'drop'` an undeclared attribute is *meant* to be absent from a re-encode, and saying so
    // here is the difference between a policy and an unexplained gap in the law
    const drops = (subject.rest ?? 'drop') === 'drop'

    for (const [i, item] of items.entries()) {
        const rewritten = subject.unsafeEncode(subject.unsafeDecode(item))
        for (const [name, attribute] of Object.entries(item)) {
            const after = rewritten[name]
            if (after === undefined) {
                if (drops) continue
                throw new CodecError(
                    `'${name}' was dropped on a read-modify-write at item ${i}, and this codec does not drop`,
                )
            }
            const before = membersOf(attribute)
            if (!equals(membersOf(after), before)) {
                throw new CodecError(
                    `'${name}' changed member on a read-modify-write at item ${i}: ${JSON.stringify(before)} became ${JSON.stringify(membersOf(after))}`,
                )
            }
        }
    }
}

/**
 * Compares two decoded entities.
 *
 * Covers what decoding actually produces: `Set` from the native set members, `Uint8Array` from `B`,
 * plus arrays and plain objects. `Set` matters in particular — {@link unknown} decodes
 * `SS`/`NS`/`BS` into one, and a comparator that walks own enumerable keys reports every `Set` as
 * equal to every other, because a `Set` has none.
 *
 * Pass `util.isDeepStrictEqual` instead where the extra breadth is wanted; see {@link CheckOptions}.
 */
export const structuralEquals = (a: unknown, b: unknown): boolean => {
    if (Object.is(a, b)) return true

    if (a instanceof Uint8Array || b instanceof Uint8Array) {
        return (
            a instanceof Uint8Array &&
            b instanceof Uint8Array &&
            a.length === b.length &&
            a.every((x, i) => x === b[i])
        )
    }

    if (a instanceof Date || b instanceof Date) {
        return (
            a instanceof Date &&
            b instanceof Date &&
            a.getTime() === b.getTime()
        )
    }

    if (a instanceof Set || b instanceof Set) {
        if (!(a instanceof Set) || !(b instanceof Set) || a.size !== b.size) {
            return false
        }
        const remaining = [...b]
        return [...a].every((x) => {
            const at = remaining.findIndex((y) => structuralEquals(x, y))
            if (at < 0) return false
            remaining.splice(at, 1)
            return true
        })
    }

    if (a instanceof Map || b instanceof Map) {
        if (!(a instanceof Map) || !(b instanceof Map) || a.size !== b.size) {
            return false
        }
        return [...a].every(
            ([k, v]) => b.has(k) && structuralEquals(v, b.get(k)),
        )
    }

    if (Array.isArray(a) || Array.isArray(b)) {
        return (
            Array.isArray(a) &&
            Array.isArray(b) &&
            a.length === b.length &&
            a.every((x, i) => structuralEquals(x, b[i]))
        )
    }

    if (
        typeof a === 'object' &&
        typeof b === 'object' &&
        a !== null &&
        b !== null
    ) {
        const ka = Object.keys(a)
        const kb = Object.keys(b)
        return (
            ka.length === kb.length &&
            ka.every(
                (k) =>
                    Object.hasOwn(b, k) &&
                    structuralEquals(
                        (a as Record<string, unknown>)[k],
                        (b as Record<string, unknown>)[k],
                    ),
            )
        )
    }

    return false
}

// ── generating, by what a codec is ──────────────────────────────────
//
// The codecs carry a {@link CodecDef} saying what they are; the generators live here and dispatch
// on it. That is the whole reason for the def: a generator baked into every codec ships to
// production whether or not anything ever runs a property test, and no bundler can shake a closure
// out of an object that is always constructed.

/** Shorter, then simpler: `'a#b'` before `'a'` before `''`. */
const shrinkString = (value: string): readonly string[] => {
    if (value === '') return []
    const out = ['', value.slice(0, Math.floor(value.length / 2))]
    if (value.length > 1) out.push(value.slice(1), value.slice(0, -1))
    if (value !== value.toLowerCase()) out.push(value.toLowerCase())
    return [...new Set(out)].filter((x) => x !== value)
}

/** Toward zero, keeping the sign only while it still matters. */
const shrinkNumber = (value: number): readonly number[] =>
    [
        0,
        Math.trunc(value / 2),
        value < 0 ? -value : Number.NaN,
        Math.trunc(value),
    ].filter((x) => Number.isFinite(x) && Math.abs(x) < Math.abs(value))

const shrinkDecimal = (value: string): readonly string[] => {
    const n = Number(value)
    if (!Number.isFinite(n) || n === 0) return value === '0' ? [] : ['0']
    const candidates = ['0', '1', String(Math.trunc(n))]
    return [...new Set(candidates)].filter(
        (x) => x !== value && Math.abs(Number(x)) <= Math.abs(n),
    )
}

/** One element dropped, then one element shrunk. Never below `min` in length. */
const shrinkSequence = <T>(
    value: readonly T[],
    element: ((x: T) => readonly T[]) | undefined,
    min: number,
): readonly (readonly T[])[] => {
    const out: (readonly T[])[] = []
    if (value.length > min) {
        // straight to the minimum first, since that is the biggest reduction on offer
        out.push(value.slice(0, min))
        for (let i = 0; i < value.length; i++) {
            out.push([...value.slice(0, i), ...value.slice(i + 1)])
        }
    }
    if (element) {
        for (let i = 0; i < value.length; i++) {
            for (const smaller of element(value[i] as T)) {
                out.push([...value.slice(0, i), smaller, ...value.slice(i + 1)])
            }
        }
    }
    return out
}

const pickFrom = <T>(rng: Rng, values: readonly T[]): T =>
    values[Math.floor(rng() * values.length)] as T

const someString = (rng: Rng) =>
    pickFrom(rng, ['', 'a', 'xy', 'a#b', '0', 'n', 'a b', '-1'])

/** Already in DynamoDB's normal form, so no digits are trimmed on the way through. */
const someDecimal = (rng: Rng) =>
    pickFrom(rng, [
        '0',
        '1',
        '-1',
        '1.5',
        '0.1',
        '-0.25',
        '12345678901234567890',
    ])

const someUnknown = (
    rng: Rng,
    size: number,
    numbers: opaque.Numbers,
): unknown => {
    const scalars: unknown[] = [
        null,
        someString(rng),
        rng() < 0.5,
        Uint8Array.from([Math.floor(rng() * 256)]),
    ]
    // a number is in the domain only once the caller has said what to do with `N`
    if (numbers === 'lossy') {
        scalars.push(pickFrom(rng, [0, 1, -1, 1.5, 0.1, -0.25, 1e20, 1e21]))
    }
    const scalar = () => pickFrom(rng, scalars)
    if (size <= 0) return scalar()
    return pickFrom(rng, [
        scalar(),
        Array.from({ length: Math.floor(rng() * 3) }, () =>
            someUnknown(rng, size - 1, numbers),
        ),
        Object.fromEntries(
            Array.from({ length: Math.floor(rng() * 3) }, (_, i) => [
                `k${i}`,
                someUnknown(rng, size - 1, numbers),
            ]),
        ),
        new Set([someString(rng), someString(rng)].sort()),
    ])
}

const shrinkUnknown = (value: unknown): readonly unknown[] => {
    if (value === null) return []
    if (typeof value === 'string') return [null, ...shrinkString(value)]
    if (typeof value === 'number') return [null, ...shrinkNumber(value)]
    if (typeof value === 'boolean') return value ? [null, false] : [null]
    if (value instanceof Uint8Array) {
        return value.length === 0 ? [null] : [null, new Uint8Array(0)]
    }
    if (Array.isArray(value)) {
        return [null, ...shrinkSequence(value, shrinkUnknown, 0)]
    }
    if (value instanceof Set) {
        // never to empty: DynamoDB refuses an empty set, so it is not a smaller counterexample
        return [
            null,
            ...shrinkSequence([...value], undefined, 1).map(
                (x) => new Set(x as unknown[]),
            ),
        ]
    }
    if (typeof value === 'object') {
        return [
            null,
            ...Object.keys(value).map((k) => {
                const { [k]: _dropped, ...rest } = value as Record<
                    string,
                    unknown
                >
                return rest
            }),
        ]
    }
    return [null]
}

/** How many draws before rejection sampling gives up on a predicate. */
const SAMPLE_LIMIT = 200

/** Below this keep-rate, a property run is quietly smaller than it looks. */
const THIN_SEARCH = 0.5

/**
 * Draws from a wider codec until the predicate accepts.
 *
 * Runs only from a generator, so only during a property run. A predicate that rejects most draws
 * does not fail — it silently shrinks the search — so it says so once; `onThinSearch` routes that
 * somewhere other than the console.
 */
const bySampling = <Wide, Narrow extends Wide>(
    draw: (rng: Rng, size: number) => Wide,
    is: (value: Wide) => value is Narrow,
    what: string,
    onThinSearch?: (what: string, rate: number) => void,
): ((rng: Rng, size: number) => Narrow) => {
    let attempts = 0
    let accepted = 0
    let warned = false

    return (rng, size) => {
        for (let i = 0; i < SAMPLE_LIMIT; i++) {
            attempts++
            const candidate = draw(rng, size)
            if (!is(candidate)) continue

            accepted++
            if (
                !warned &&
                accepted >= 20 &&
                accepted / attempts < THIN_SEARCH
            ) {
                warned = true
                const rate = accepted / attempts
                onThinSearch?.(what, rate) ??
                    console.warn(
                        `[rotorise] generating ${what} keeps ${Math.round(rate * 100)}% of what it tries, so a property run is smaller than it looks. Pass \`arbitrary\` to refine(...) to say what one looks like.`,
                    )
            }
            return candidate
        }
        throw new CodecError(
            `could not generate a value matching ${what} in ${SAMPLE_LIMIT} tries; pass \`arbitrary\` to say what one looks like`,
        )
    }
}

/**
 * A rejection sampler per refinement, not per call.
 *
 * The sampler counts how much of what it draws survives the predicate, and a fresh one every call
 * counts to one and forgets — so a thin search would never be reported. Keyed on the def, which is
 * the codec's identity here.
 */
const samplers = new WeakMap<object, (rng: Rng, size: number) => unknown>()

const definitionOf = (codec: AnyCodec): CodecDef => {
    const def = codec.def
    if (!def) {
        throw new CodecError(
            'this codec carries neither a generator of its own nor a definition to generate from',
        )
    }
    return def
}

/**
 * A value the codec can carry.
 *
 * Dispatches on {@link CodecDef}, so a codec kind that grows a generator grows it here rather than
 * in the codec itself. `size` bounds recursion.
 */
export const arbitraryOf = (
    codec: AnyCodec,
    rng: Rng,
    size: number,
): unknown => {
    // a codec may carry its own, which is the escape hatch for one built by hand
    if (codec.arbitrary) return codec.arbitrary(rng, size)
    const def = definitionOf(codec)
    switch (def.kind) {
        case 'string':
            return someString(rng)
        case 'literal':
            return def.allowed.length
                ? pickFrom(rng, def.allowed)
                : someString(rng)
        case 'decimal':
            return someDecimal(rng)
        case 'number':
            return pickFrom(rng, [0, 1, -1, 42, 1000, -7])
        case 'numeric':
            return pickFrom(rng, [0, 1, 2, 3])
        case 'boolean':
            return rng() < 0.5
        case 'binary':
            return Uint8Array.from(
                Array.from({ length: Math.floor(rng() * 4) }, () =>
                    Math.floor(rng() * 256),
                ),
            )
        case 'opaque':
            return someUnknown(rng, size, def.numbers)
        case 'held':
            /**
             * Generated for the inner codec and handed out through `decode`, so what is generated is
             * always something the pair produced — a generator for the *outer* type could invent a
             * value `encode` never makes, and the round-trip would fail on the generator rather than
             * on the codec.
             *
             * The conversion is called raw, where the codec guards it. Here the input is correct by
             * construction, so a throw is a bug in the adapter and belongs at the top of a property
             * run rather than folded into a value.
             */
            return def.adapt.decode(arbitraryOf(def.inner, rng, size) as never)
        case 'set': {
            /**
             * Deduplicated by what is *stored*, as the codec does — two values that write the same
             * member are one member of the set, so a generator that did not deduplicate by the stored
             * form would produce a set the codec cannot carry back unchanged.
             *
             * The stored form is computed once per value and kept as the map key. It is an
             * `encode`, and reading it from inside the comparator ran that encode
             * `O(n log n)` times — as did re-asking `writes` which member the element writes, a
             * recursive walk of the element's definition, once per value.
             */
            const member = writes(def.element)
            const count = 1 + Math.floor(rng() * 3)
            const byStored = new Map<string, unknown>()
            for (let i = 0; i < count; i++) {
                const value = arbitraryOf(def.element, rng, size)
                const written = def.element.unsafeEncode(
                    value as never,
                ) as Record<string, unknown>
                byStored.set(String(member ? written[member] : written), value)
            }
            return new Set(
                [...byStored.keys()].sort().map((key) => byStored.get(key)),
            )
        }
        case 'array':
            return Array.from({ length: Math.floor(rng() * 3) }, () =>
                arbitraryOf(def.element, rng, Math.max(0, size - 1)),
            )
        case 'tuple': {
            const fixed = def.elements.map((element) =>
                arbitraryOf(element, rng, Math.max(0, size - 1)),
            )
            if (!def.tail) return fixed
            // a tail has no arity to hit, so its length is generated like a list's
            const tail = def.tail
            return [
                ...fixed,
                ...Array.from({ length: Math.floor(rng() * 3) }, () =>
                    arbitraryOf(tail, rng, Math.max(0, size - 1)),
                ),
            ]
        }
        case 'record':
            return Object.fromEntries(
                Array.from(
                    { length: size <= 0 ? 0 : Math.floor(rng() * 3) },
                    (_, i) => [`k${i}`, arbitraryOf(def.value, rng, size - 1)],
                ),
            )
        case 'attributes': {
            const out: Record<string, unknown> = {}
            /**
             * The attributes the spec does not name, where a policy says what they hold.
             *
             * Generated *first*, so a declared name always wins the collision — the spec is the
             * authority on a name it declares, and an undeclared value standing in for one would test
             * the wrong codec.
             */
            if (def.rest) {
                for (let extra = Math.floor(rng() * 3); extra > 0; extra--) {
                    out[`rest${extra}`] = arbitraryOf(
                        def.rest,
                        rng,
                        Math.max(0, size - 1),
                    )
                }
            }
            for (const name in def.of) {
                const attribute = def.of[name] as AnyCodec
                if (
                    attribute.def?.kind === 'optional' &&
                    (size <= 0 || rng() < 0.5)
                ) {
                    continue
                }
                out[name] = arbitraryOf(attribute, rng, size)
            }
            return out
        }
        case 'tagged': {
            const names = Object.keys(def.variants)
            return arbitraryOf(
                def.variants[pickFrom(rng, names)] as AnyCodec,
                rng,
                size,
            )
        }
        case 'untagged':
            return arbitraryOf(pickFrom(rng, def.variants), rng, size)
        case 'refine': {
            if (def.refined.arbitrary) return def.refined.arbitrary(rng, size)
            let sample = samplers.get(def)
            if (!sample) {
                sample = bySampling(
                    (r: Rng, sz: number) => arbitraryOf(def.inner, r, sz),
                    def.refined.is as (value: unknown) => value is unknown,
                    def.refined.what,
                    def.refined.onThinSearch,
                )
                samplers.set(def, sample)
            }
            return sample(rng, size)
        }
        case 'nullable':
            return rng() < 0.25 ? null : arbitraryOf(def.inner, rng, size)
        case 'optional':
        case 'fallback':
            return arbitraryOf(def.inner, rng, size)
        case 'legacy':
            return arbitraryOf(def.current, rng, size)
        case 'lazy':
            // one level shallower each time, which is what stops a recursive entity generating
            // forever: the optional attribute that recurses is dropped once the budget runs out
            return arbitraryOf(def.get(), rng, size - 1)
        case 'custom':
            throw new CodecError(
                'a codec written by hand generates nothing unless it says how; give it `arbitrary`',
            )
        default:
            throw new CodecError(
                'a branch has no one codec to generate from; reach for the variant you mean',
            )
    }
}

/**
 * Values simpler than this one, cheapest reduction first.
 *
 * The counterpart of {@link arbitraryOf}, dispatching on the same {@link CodecDef}.
 */
export const shrinkOf = (
    codec: AnyCodec,
    value: unknown,
): readonly unknown[] => {
    if (codec.shrink) return codec.shrink(value as never)
    const def = definitionOf(codec)
    const shrinkAt = (inner: AnyCodec) => (x: unknown) => shrinkOf(inner, x)

    switch (def.kind) {
        case 'string':
            return shrinkString(value as string)
        case 'literal': {
            const at = def.allowed.indexOf(value as string)
            return def.allowed.slice(0, Math.max(0, at))
        }
        case 'decimal':
            return shrinkDecimal(value as string)
        case 'number':
        case 'numeric':
            return shrinkNumber(value as number)
        case 'boolean':
            return value ? [false] : []
        case 'binary': {
            const bytes = value as Uint8Array
            return bytes.length === 0
                ? []
                : [new Uint8Array(0), bytes.slice(0, bytes.length - 1)]
        }
        case 'opaque':
            return shrinkUnknown(value)
        case 'held':
            // shrunk on the inner side, where the definition knows how, and handed back out
            return shrinkOf(def.inner, def.adapt.encode(value as never)).map(
                (shrunk) => def.adapt.decode(shrunk as never),
            )
        case 'set':
            // shrunk as a sequence and handed back as a set, which is what it is
            return shrinkSequence(
                [...(value as ReadonlySet<unknown>)],
                shrinkAt(def.element),
                1,
            ).map((shrunk) => new Set(shrunk as readonly unknown[]))
        case 'array':
            return shrinkSequence(
                value as readonly unknown[],
                shrinkAt(def.element),
                0,
            )
        case 'tuple':
            // the fixed arity cannot reduce, so only those elements do. A tail could also shorten,
            // and does not: dropping one changes the length, which the fixed part forbids reasoning
            // about here — the elements are where a counterexample actually lives
            return def.elements.flatMap((element, i) =>
                shrinkOf(element, (value as readonly unknown[])[i]).map(
                    (smaller) => {
                        const copy = [...(value as readonly unknown[])]
                        copy[i] = smaller
                        return copy
                    },
                ),
            )
        case 'record': {
            const held = value as Record<string, unknown>
            const keys = Object.keys(held)
            const out: Record<string, unknown>[] = []
            for (const k of keys) {
                const { [k]: _dropped, ...rest } = held
                out.push(rest)
            }
            for (const k of keys) {
                for (const smaller of shrinkOf(def.value, held[k])) {
                    out.push({ ...held, [k]: smaller })
                }
            }
            return out
        }
        case 'attributes': {
            const held = value as Record<string, unknown>
            const out: Record<string, unknown>[] = []
            // dropping a whole attribute is the bigger reduction, so try it first
            for (const name in def.of) {
                if ((def.of[name] as AnyCodec).def?.kind !== 'optional')
                    continue
                if (!(name in held)) continue
                const { [name]: _dropped, ...rest } = held
                out.push(rest)
            }
            for (const name in def.of) {
                if (!(name in held)) continue
                for (const smaller of shrinkOf(
                    def.of[name] as AnyCodec,
                    held[name],
                )) {
                    out.push({ ...held, [name]: smaller })
                }
            }
            return out
        }
        case 'tagged': {
            const held = value as Record<string, unknown>
            const chosen = def.variants[String(held[def.discriminator])]
            return chosen ? shrinkOf(chosen, value) : []
        }
        case 'untagged': {
            const names = new Set(
                Object.keys(value as Record<string, unknown>).filter(
                    (k) => (value as Record<string, unknown>)[k] !== undefined,
                ),
            )
            const chosen = def.variants.find((variant) => {
                const of = variant.def
                if (of?.kind !== 'attributes') return false
                return [...names].every((name) => name in of.of)
            })
            return chosen ? shrinkOf(chosen, value) : []
        }
        case 'refine':
            return shrinkOf(def.inner, value).filter(
                def.refined.is as (x: unknown) => boolean,
            )
        case 'nullable':
            return value === null ? [] : [null, ...shrinkOf(def.inner, value)]
        case 'optional':
        case 'fallback':
            return shrinkOf(def.inner, value)
        case 'legacy':
            return shrinkOf(def.current, value)
        case 'lazy':
            return shrinkOf(def.get(), value)
        // a branch has no one codec to shrink through, which is why `at` refuses it; a hand-written
        // codec shrinks only if it said how, and `shrink` above is where that was read
        default:
            return []
    }
}

// ── conforming to the marshaller you already have ────────────────────

/** Where two encodings first disagree, and what each put there. */
export type Difference = {
    readonly path: readonly (string | number)[]
    readonly ours: unknown
    readonly theirs: unknown
}

/**
 * The first place two values differ, depth first.
 *
 * Reported as a path rather than a whole-object diff, because the answer a migration needs is
 * "which attribute changes" and a thirty-attribute item printed twice does not say.
 */
export const firstDifference = (
    ours: unknown,
    theirs: unknown,
    path: readonly (string | number)[] = [],
): Difference | undefined => {
    if (structuralEquals(ours, theirs)) return undefined

    if (Array.isArray(ours) && Array.isArray(theirs)) {
        if (ours.length !== theirs.length) return { path, ours, theirs }
        for (let i = 0; i < ours.length; i++) {
            const deeper = firstDifference(ours[i], theirs[i], [...path, i])
            if (deeper) return deeper
        }
        return { path, ours, theirs }
    }

    const bothPlain =
        typeof ours === 'object' &&
        ours !== null &&
        !Array.isArray(ours) &&
        typeof theirs === 'object' &&
        theirs !== null &&
        !Array.isArray(theirs) &&
        !(ours instanceof Set) &&
        !(theirs instanceof Set) &&
        !(ours instanceof Uint8Array) &&
        !(theirs instanceof Uint8Array)

    if (bothPlain) {
        const left = ours as Record<string, unknown>
        const right = theirs as Record<string, unknown>
        for (const key of new Set([
            ...Object.keys(left),
            ...Object.keys(right),
        ])) {
            const deeper = firstDifference(left[key], right[key], [
                ...path,
                key,
            ])
            if (deeper) return deeper
        }
    }

    return { path, ours, theirs }
}

/** What a hand-written marshaller does, as little of it as this needs to know. */
export type Reference<T> = {
    /** The entity, as this marshaller stores it. */
    readonly marshall: (entity: T) => AttributeMap
    /** A stored item, as this marshaller reads it. Optional; only read parity needs it. */
    readonly unmarshall?: (item: AttributeMap) => unknown
}

/**
 * Checks a codec against the marshaller a table was written with.
 *
 * The question adoption actually turns on, asked over generated entities rather than the handful
 * anyone thinks to try. Two halves, and the second matters more:
 *
 * - **write parity** — the codec stores what the marshaller stored, so a row written after the
 *   change is the same row.
 * - **read parity** — the codec reads what the marshaller wrote, so the table full of rows that
 *   already exists still decodes to the same entities. A codec can be right about every future
 *   write and still be unable to read the past.
 *
 * A divergence is reported as a path — `at breed.coat` — because "which attribute changes" is the
 * answer a migration needs, and two thirty-attribute items printed side by side is not it.
 */
export const checkAgainst = <T>(
    subject: Checkable<T>,
    reference: Reference<T>,
    {
        count = 100,
        seed = 0x5eed,
        size = 4,
        refine = (value: T) => value,
        filter = () => true,
    }: {
        readonly count?: number
        readonly seed?: number
        readonly size?: number
        readonly refine?: (value: T) => T
        readonly filter?: (value: T) => boolean
    } = {},
): void => {
    const rng = rngFrom(seed)
    for (let i = 0; i < count; i++) {
        const entity = refine(
            arbitraryOf(subject as unknown as AnyCodec, rng, size) as T,
        )
        if (!filter(entity)) continue

        // the throwing pair, as the rest of this file uses: a codec that cannot encode what it
        // generated is a failure of the run, not a difference to report
        const ours = subject.unsafeEncode(entity)
        const theirs = reference.marshall(entity)

        const written = firstDifference(ours, theirs)
        if (written) {
            throw new CodecError(
                `write parity: the codec and the reference store this differently${where(written)}\n  entity  = ${JSON.stringify(entity)}\n  ours    = ${JSON.stringify(written.ours)}\n  theirs  = ${JSON.stringify(written.theirs)}`,
            )
        }

        if (!reference.unmarshall) continue
        const read = firstDifference(
            subject.unsafeDecode(theirs),
            reference.unmarshall(theirs),
        )
        if (read) {
            throw new CodecError(
                `read parity: the codec and the reference read this row differently${where(read)}\n  ours    = ${JSON.stringify(read.ours)}\n  theirs  = ${JSON.stringify(read.theirs)}`,
            )
        }
    }
}

const where = (difference: Difference): string =>
    difference.path.length === 0
        ? ''
        : ` at ${difference.path
              .map((segment, i) =>
                  typeof segment === 'number'
                      ? `[${segment}]`
                      : i === 0
                        ? segment
                        : `.${segment}`,
              )
              .join('')}`

// ── laws between codecs ─────────────────────────────────────────────

/** Rendered for a message. `Set`s and typed arrays do not survive `JSON.stringify` on their own. */
const show = (value: unknown): string =>
    value instanceof Set
        ? `Set(${JSON.stringify([...value])})`
        : value instanceof Uint8Array
          ? `Uint8Array(${JSON.stringify([...value])})`
          : (JSON.stringify(value) ?? String(value))

/**
 * Two codecs that cannot be told apart by anything a caller can do.
 *
 * The primitive that makes a combinator's laws checkable rather than argued about. Both directions
 * are compared, and so are their *failures*: two codecs that agree on every value they carry but
 * disagree about which values they refuse are not the same codec.
 *
 * Values are generated from `a`, so the caller should pass the more constrained one first where they
 * differ — but the law being checked usually makes them equally constrained, and where it does not,
 * a one-sided check is still the one worth having: it asks whether the *rewritten* form is a faithful
 * replacement for the original.
 *
 * @example
 * ```ts
 * // adapting by the identity is the identity
 * checkEquivalent(held(string, { encode: (v: string) => v, decode: (v) => v }), string)
 *
 * // two adapters compose into one
 * checkEquivalent(
 *     held(held(decimal, inner), outer),
 *     held(decimal, { encode: (v) => inner.encode(outer.encode(v)), decode: ... }),
 * )
 * ```
 */
export const checkEquivalent = <T>(
    a: AttributeCodec<T>,
    b: AttributeCodec<T>,
    {
        count = 100,
        seed = 0x5eed,
        size = 4,
        equals = structuralEquals,
    }: Pick<CheckOptions<T>, 'count' | 'seed' | 'size' | 'equals'> = {},
): void => {
    const rng = rngFrom(seed)
    for (let i = 0; i < count; i++) {
        const value = arbitraryOf(a as unknown as AnyCodec, rng, size) as T

        const written = a.encode(value)
        const alsoWritten = b.encode(value)
        if (failed(written) !== failed(alsoWritten)) {
            throw new CodecError(
                `these codecs disagree about whether ${show(value)} can be written, with seed ${seed}: ${
                    failed(written) ? `the first refused it (${written})` : ''
                }${failed(alsoWritten) ? `the second refused it (${alsoWritten})` : ''}`,
            )
        }
        if (failed(written) || failed(alsoWritten)) continue
        if (!equals(written, alsoWritten)) {
            throw new CodecError(
                `these codecs write ${show(value)} differently, with seed ${seed}: ${show(written)} against ${show(alsoWritten)}`,
            )
        }

        const read = a.decode(written)
        const alsoRead = b.decode(written)
        if (failed(read) !== failed(alsoRead)) {
            throw new CodecError(
                `these codecs disagree about whether ${show(written)} can be read, with seed ${seed}`,
            )
        }
        if (failed(read) || failed(alsoRead)) continue
        if (!equals(read, alsoRead)) {
            throw new CodecError(
                `these codecs read ${show(written)} differently, with seed ${seed}: ${show(read)} against ${show(alsoRead)}`,
            )
        }
    }
}

/**
 * That a {@link held} adapter is the isomorphism it claims to be.
 *
 * `held` asks one thing of a caller and cannot check it: that the two halves invert each other. This
 * checks the half that is checkable — `encode(decode(i))` against `i`, over values generated for the
 * codec underneath — and it is the half a table depends on. An adapter that loses information on the
 * way back in reads a row and writes back something else, which is data loss on a read-modify-write
 * and nothing else in the harness would catch it.
 *
 * The other direction, `decode(encode(t))` for every `t`, is not reachable: there is no generator for
 * the held type except `decode` itself, so every value the harness can make is already in its image.
 * `checkRoundTrip` over a spec holding the adapter covers what that leaves.
 *
 * @example
 * ```ts
 * checkIso(set(string), {
 *     encode: (tags: readonly string[]) => new Set(tags),
 *     decode: (tags) => [...tags],
 * })
 * ```
 */
export const checkIso = <C extends AnyCodec, T>(
    inner: C,
    adapt: {
        readonly encode: (value: T) => unknown
        readonly decode: (held: never) => T
    },
    {
        count = 100,
        seed = 0x5eed,
        size = 4,
        equals = structuralEquals,
    }: Pick<CheckOptions<T>, 'count' | 'seed' | 'size' | 'equals'> = {},
): void => {
    const rng = rngFrom(seed)
    for (let i = 0; i < count; i++) {
        const held = arbitraryOf(inner, rng, size)
        const back = adapt.encode(adapt.decode(held as never))
        if (!equals(back, held)) {
            throw new CodecError(
                `this adapter is not an isomorphism, with seed ${seed}: ${show(held)} came back as ${show(back)}`,
            )
        }
    }
}
