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
    ItemCodec,
    LiteralValue,
    RestPolicy,
    Rng,
    SetBase,
} from './codec'
import { CodecError, carries, codecOfTerm, failed, opaque } from './codec'
import { holds, readsBack, variantTag } from './denote'
import type { Field, Predicate, Term } from './term'
import { member as termMember } from './term'
import { shapeOf } from './value'

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
    /**
     * What the codec is, which is what {@link arbitraryOf} generates from.
     *
     * A {@link Term}: a checkable is generated for and round tripped, which is a codec's pair,
     * and a field has none — so handing one here is the defect the type refuses rather than a case
     * the generator would have to answer.
     */
    def?: Term
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
 * {@link AttributeCodec.arbitrary} — so `decimal` yields normalised decimals and `string.set()`
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
 * **(C), the law nothing else here checks.**
 *
 * `p a = some v ⟹ e v is defined` — whatever a codec reads, it can write back. Everything else in
 * this module generates *values* and round-trips them, so `decode` only ever sees attributes that
 * `encode` produced. That is the wrong direction for (C): the attribute that breaks it is by
 * definition one `encode` would never make.
 *
 * Three defects lived in that gap and all three shipped. `set` refused the empty set on the way in
 * and returned it on the way out. `decimal` accepted `'1.50'`, which DynamoDB stores as `'1.5'`, so
 * an item could be read and not written back. `numeric` cast a read without checking it. None was
 * reachable from a generated value; each needed an attribute nobody would write, which is what this
 * builds.
 *
 * The corpus is every encoded item, plus one **named mutation** at a time at every position in it.
 * The names are the point: a counterexample says which shape found it, and each shape is a class of
 * defect this project has actually had rather than a random perturbation.
 *
 * A failure to *decode* is never reported — refusing a mutated attribute is exactly right, and is
 * what most of these do. What is reported is a mutation that decodes and then cannot be encoded.
 */
export const checkDecodesAreWritable = <T>(
    subject: Checkable<T>,
    {
        count = 100,
        seed = 0x5eed,
        size = 4,
        refine,
        filter,
    }: CheckOptions<T> = {},
): void => {
    const rng = rngFrom(seed)
    for (let i = 0; i < count; i++) {
        const raw = arbitraryOf(subject as never, rng, size) as T
        const value = refine ? refine(raw) : raw
        if (filter && !filter(value)) continue

        let encoded: AttributeMap
        try {
            encoded = subject.unsafeEncode(value)
        } catch {
            continue // a value the codec declines to write says nothing about (C)
        }

        for (const { what, item } of mutations(encoded)) {
            let read: T
            try {
                read = subject.unsafeDecode(item)
            } catch {
                continue // refusing it is the correct answer, and the common one
            }
            try {
                subject.unsafeEncode(read)
            } catch (error) {
                throw new CodecError(
                    `(C) fails: this attribute decodes and the value it yields cannot be encoded.\n` +
                        `  mutation = ${what}\n` +
                        `  seed     = ${seed}, case ${i}\n` +
                        `  item     = ${JSON.stringify(item)}\n` +
                        `  decoded  = ${JSON.stringify(read)}\n` +
                        `  encoding it again said: ${(error as Error).message}`,
                )
            }
        }
    }
}

/** One mutated attribute, and the name of the shape that made it. */
type Mutation = { readonly what: string; readonly item: AttributeMap }

/**
 * The shapes worth trying, each a class of defect rather than a random perturbation.
 *
 * Applied one at a time and one position at a time: a corpus of single-shape deviations from a
 * real item, so a counterexample is as close to a working item as it can be while still being
 * wrong. Nothing here is a shape DynamoDB itself produces — that is the point, since an item that
 * came from somewhere else is exactly what a decoder exists to be suspicious of.
 */
const SHAPES: readonly {
    readonly what: string
    readonly to: (value: AttributeValue) => AttributeValue | undefined
}[] = [
    {
        // `set`'s encode refused this and its decode returned it for as long as both existed
        what: 'an empty set',
        to: (v) => {
            const m = memberOf(v)
            if (m === 'SS') return { SS: [] }
            if (m === 'NS') return { NS: [] }
            if (m === 'BS') return { BS: [] }
            return undefined
        },
    },
    {
        // the form DynamoDB normalises away, which `decimal` was writing and reading
        what: 'a denormalised N',
        to: (v) =>
            memberOf(v) === 'N' ? { N: `${v.N as string}0` } : undefined,
    },
    {
        what: 'an N with a leading zero',
        to: (v) =>
            memberOf(v) === 'N' ? { N: `0${v.N as string}` } : undefined,
    },
    {
        what: 'an N past the magnitude DynamoDB stores',
        to: (v) => (memberOf(v) === 'N' ? { N: '1e126' } : undefined),
    },
    {
        what: 'an N that is not a number at all',
        to: (v) => (memberOf(v) === 'N' ? { N: 'NaN' } : undefined),
    },
    {
        what: 'an empty list',
        to: (v) => (memberOf(v) === 'L' ? { L: [] } : undefined),
    },
    {
        what: 'an empty map',
        to: (v) => (memberOf(v) === 'M' ? { M: {} } : undefined),
    },
    {
        what: 'a string where a number was stored',
        to: (v) => (memberOf(v) === 'N' ? { S: v.N as string } : undefined),
    },
]

/** Every position in an attribute, as a function that rebuilds the whole with one replaced. */
const positions = (
    value: AttributeValue,
): readonly {
    readonly at: AttributeValue
    readonly rebuild: (replacement: AttributeValue) => AttributeValue
}[] => {
    const here = [{ at: value, rebuild: (r: AttributeValue) => r }]
    const member = memberOf(value)
    if (member === 'L') {
        const items = value.L ?? []
        return here.concat(
            items.flatMap((child, index) =>
                positions(child).map(({ at, rebuild }) => ({
                    at,
                    rebuild: (r: AttributeValue) => ({
                        L: items.map((x, j) => (j === index ? rebuild(r) : x)),
                    }),
                })),
            ),
        )
    }
    if (member === 'M') {
        const entries = Object.entries(value.M ?? {})
        return here.concat(
            entries.flatMap(([key, child]) =>
                positions(child).map(({ at, rebuild }) => ({
                    at,
                    rebuild: (r: AttributeValue) => ({
                        M: Object.fromEntries(
                            entries.map(([k, x]) => [
                                k,
                                k === key ? rebuild(r) : x,
                            ]),
                        ),
                    }),
                })),
            ),
        )
    }
    return here
}

const mutations = (item: AttributeMap): readonly Mutation[] => {
    const out: Mutation[] = []
    for (const [key, attribute] of Object.entries(item)) {
        for (const { at, rebuild } of positions(attribute)) {
            for (const { what, to } of SHAPES) {
                const replaced = to(at)
                if (!replaced) continue
                out.push({
                    what: `${what}, at '${key}'`,
                    item: { ...item, [key]: rebuild(replaced) },
                })
            }
        }
        // and the attribute missing altogether, which `optional` and `fallback` must survive
        const { [key]: _dropped, ...without } = item
        out.push({ what: `'${key}' absent`, item: without })
    }
    return out
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
// The codecs carry a {@link Term} saying what they are; the generators live here and dispatch
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

/**
 * A value the codec can carry.
 *
 * Dispatches on {@link Term}, so a codec kind that grows a generator grows it here rather than
 * in the codec itself. `size` bounds recursion.
 */
export const arbitraryOf = (
    codec: AnyCodec,
    rng: Rng,
    size: number,
): unknown => {
    // a codec may carry its own, which is the escape hatch for one built by hand
    if (codec.arbitrary) return codec.arbitrary(rng, size)
    const def = codec.def
    switch (def.kind) {
        case 'string':
            return someString(rng)
        // `ℓ` is non-empty by construction now — every constructor that builds one refuses
        // an empty admissible set — so there is no fallback branch to take
        case 'literal': {
            const ls: readonly LiteralValue[] = def.ls
            return pickFrom(rng, ls)
        }
        case 'decimal':
            return someDecimal(rng)
        case 'number':
            return pickFrom(rng, [0, 1, -1, 42, 1000, -7])
        case 'boolean':
            return rng() < 0.5
        case 'null':
            return null
        case 'binary':
            return Uint8Array.from(
                Array.from({ length: Math.floor(rng() * 4) }, () =>
                    Math.floor(rng() * 256),
                ),
            )
        case 'opaq':
            return someUnknown(rng, size, def.lossy ? 'lossy' : 'refuse')
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
            return def.g(
                arbitraryOf(codecOfTerm(def.inner), rng, size) as never,
            )
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
            const element = codecOfTerm({ kind: def.base })
            return someSet(rng, element, () => arbitraryOf(element, rng, size))
        }
        case 'array':
            return Array.from({ length: Math.floor(rng() * 3) }, () =>
                arbitraryOf(codecOfTerm(def.elem), rng, Math.max(0, size - 1)),
            )
        case 'tuple': {
            const fixed = def.elems.map((element) =>
                arbitraryOf(codecOfTerm(element), rng, Math.max(0, size - 1)),
            )
            if (!def.tail) return fixed
            // a tail has no arity to hit, so its length is generated like a list's
            const tail = def.tail
            return [
                ...fixed,
                ...Array.from({ length: Math.floor(rng() * 3) }, () =>
                    arbitraryOf(codecOfTerm(tail), rng, Math.max(0, size - 1)),
                ),
            ]
        }
        case 'record':
            return Object.fromEntries(
                Array.from(
                    { length: size <= 0 ? 0 : Math.floor(rng() * 3) },
                    (_, i) => [
                        `k${i}`,
                        arbitraryOf(codecOfTerm(def.val), rng, size - 1),
                    ],
                ),
            )
        case 'object': {
            const { fields, rest } = def.body
            const out: Record<string, unknown> = {}
            /**
             * The attributes the spec does not name, where a policy says what they hold.
             *
             * Generated *first*, so a declared name always wins the collision — the spec is the
             * authority on a name it declares, and an undeclared value standing in for one would test
             * the wrong codec.
             */
            // only a rest *codec* puts undeclared names in the entity; `drop` and `refuse` both
            // leave nothing to generate, and are now told apart from a codec rather than guessed
            const restCodec =
                typeof rest === 'string' ? undefined : codecOfTerm(rest.t)
            if (restCodec) {
                for (let extra = Math.floor(rng() * 3); extra > 0; extra--) {
                    out[`rest${extra}`] = arbitraryOf(
                        restCodec,
                        rng,
                        Math.max(0, size - 1),
                    )
                }
            }
            for (const name in fields) {
                const field = fields[name]
                if (field === undefined) continue
                if (field.mark === 'optional' && (size <= 0 || rng() < 0.5)) {
                    continue
                }
                out[name] = arbitraryOf(codecOfTerm(field.t), rng, size)
            }
            return out
        }
        case 'dunion':
        case 'union':
            return arbitraryOf(
                codecOfTerm(pickFrom(rng, def.options)),
                rng,
                size,
            )
        case 'refine': {
            const q = def.q
            /**
             * A set over a restricted element is `refine(set(b), each(p))`, one `refine` per
             * predicate. Sampling whole sets against membership would almost never land, so the
             * elements are generated against the element predicates and the set is assembled the
             * way the `set` row assembles one.
             */
            if (q.kind === 'each') {
                const { base, elements } = restrictedSet(def)
                const element = codecOfTerm({ kind: base })
                return someSet(rng, element, () =>
                    someElement(rng, size, element, elements),
                )
            }
            if (q.kind === 'members') {
                const ls: readonly LiteralValue[] = q.literal.ls
                return pickFrom(rng, ls)
            }
            if (q.q.arbitrary) return q.q.arbitrary(rng, size)
            let sample = samplers.get(def)
            if (!sample) {
                sample = bySampling(
                    (r: Rng, sz: number) =>
                        arbitraryOf(codecOfTerm(def.inner), r, sz),
                    q.q.is as (value: unknown) => value is unknown,
                    q.q.what,
                    q.q.onThinSearch,
                )
                samplers.set(def, sample)
            }
            return sample(rng, size)
        }
        case 'nullable':
            return rng() < 0.25
                ? null
                : arbitraryOf(codecOfTerm(def.inner), rng, size)
        case 'legacy':
            return arbitraryOf(codecOfTerm(def.inner), rng, size)
        case 'lazy':
            // one level shallower each time, which is what stops a recursive entity generating
            // forever: the optional attribute that recurses is dropped once the budget runs out
            return arbitraryOf(codecOfTerm(def.get()), rng, size - 1)
        case 'custom':
            if (def.arbitrary) return def.arbitrary(rng, size)
            throw new CodecError(
                'a codec written by hand generates nothing unless it says how; give it `arbitrary`',
            )
    }
}

/**
 * A set, deduplicated by what is *stored*, as the codec does — two values that write the same
 * member are one member of the set, so a generator that did not deduplicate by the stored form
 * would produce a set the codec cannot carry back unchanged.
 */
const someSet = (
    rng: Rng,
    element: AnyCodec,
    one: () => unknown,
): ReadonlySet<unknown> => {
    const member = termMember(element.def)
    const count = 1 + Math.floor(rng() * 3)
    const byStored = new Map<string, unknown>()
    for (let i = 0; i < count; i++) {
        const value = one()
        const written = element.unsafeEncode(value as never) as Record<
            string,
            unknown
        >
        byStored.set(String(member ? written[member] : written), value)
    }
    return new Set([...byStored.keys()].sort().map((key) => byStored.get(key)))
}

/**
 * The base and the element predicates of a restricted set, peeled from `refine(…, each(p))` down
 * to the `set` the refinements wrap. `.set()` builds nothing else with an `each`.
 */
const restrictedSet = (
    t: Term,
): { readonly base: SetBase; readonly elements: readonly Predicate[] } => {
    if (t.kind === 'set') return { base: t.base, elements: [] }
    if (t.kind === 'refine' && t.q.kind === 'each') {
        const inner = restrictedSet(t.inner)
        return { base: inner.base, elements: [t.q.of, ...inner.elements] }
    }
    throw new CodecError(
        `\`each\` restricts a set, and this \`${t.kind}\` is not one; \`.set()\` builds every \`each\`, so this term was not built by it`,
    )
}

/**
 * One element of a restricted set: a member of the literal where there is one, the closure's own
 * generator where it gave one, and the base sampled against every predicate otherwise.
 */
const someElement = (
    rng: Rng,
    size: number,
    base: AnyCodec,
    elements: readonly Predicate[],
): unknown => {
    const admitted = (value: unknown) => elements.every((q) => holds(q)(value))
    for (const q of elements) {
        if (q.kind === 'members') {
            const ls: readonly LiteralValue[] = q.literal.ls
            return pickFrom(rng, ls.filter(admitted))
        }
    }
    for (const q of elements) {
        if (q.kind === 'closure' && q.q.arbitrary)
            return q.q.arbitrary(rng, size)
    }
    const what = elements
        .map((q) => (q.kind === 'closure' ? q.q.what : q.kind))
        .join(' and ')
    return bySampling(
        (r: Rng, sz: number) => arbitraryOf(base, r, sz),
        (value: unknown): value is unknown => admitted(value),
        what,
        undefined,
    )(rng, size)
}

/**
 * Values simpler than this one, cheapest reduction first.
 *
 * The counterpart of {@link arbitraryOf}, dispatching on the same {@link Term}.
 */
export const shrinkOf = (
    codec: AnyCodec,
    value: unknown,
): readonly unknown[] => {
    if (codec.shrink) return codec.shrink(value as never)
    const def = codec.def
    const shrinkAt = (inner: AnyCodec) => (x: unknown) => shrinkOf(inner, x)

    switch (def.kind) {
        case 'string':
            return shrinkString(value as string)
        /**
         * Towards the first alternative, which is the smallest one the schema names.
         *
         * `indexOf` rather than a comparison, and at `binary` that is reference equality — which
         * holds, because a literal's `decode` answers with the member of `ℓ` rather than with the
         * array it read. A value that is not in `ℓ` shrinks to nothing, which is right: nothing
         * smaller is admissible.
         */
        case 'literal': {
            const ls: readonly unknown[] = def.ls
            return ls.slice(0, Math.max(0, ls.indexOf(value)))
        }
        case 'decimal':
            return shrinkDecimal(value as string)
        case 'number':
            return shrinkNumber(value as number)
        case 'boolean':
            return value ? [false] : []
        // one value, so nothing smaller
        case 'null':
            return []
        case 'binary': {
            const bytes = value as Uint8Array
            return bytes.length === 0
                ? []
                : [new Uint8Array(0), bytes.slice(0, bytes.length - 1)]
        }
        case 'opaq':
            return shrinkUnknown(value)
        case 'held':
            // shrunk on the inner side, where the definition knows how, and handed back out
            return shrinkOf(codecOfTerm(def.inner), def.f(value as never)).map(
                (shrunk) => def.g(shrunk as never),
            )
        case 'set':
            // shrunk as a sequence and handed back as a set, which is what it is
            return shrinkSequence(
                [...(value as ReadonlySet<unknown>)],
                shrinkAt(codecOfTerm({ kind: def.base })),
                1,
            ).map((shrunk) => new Set(shrunk as readonly unknown[]))
        case 'array':
            return shrinkSequence(
                value as readonly unknown[],
                shrinkAt(codecOfTerm(def.elem)),
                0,
            )
        case 'tuple':
            // the fixed arity cannot reduce, so only those elements do. A tail could also shorten,
            // and does not: dropping one changes the length, which the fixed part forbids reasoning
            // about here — the elements are where a counterexample actually lives
            return def.elems.flatMap((element, i) =>
                shrinkOf(
                    codecOfTerm(element),
                    (value as readonly unknown[])[i],
                ).map((smaller) => {
                    const copy = [...(value as readonly unknown[])]
                    copy[i] = smaller
                    return copy
                }),
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
                for (const smaller of shrinkOf(codecOfTerm(def.val), held[k])) {
                    out.push({ ...held, [k]: smaller })
                }
            }
            return out
        }
        case 'object': {
            const fields = def.body.fields
            const held = value as Record<string, unknown>
            const out: Record<string, unknown>[] = []
            // dropping a whole attribute is the bigger reduction, so try it first
            for (const name in fields) {
                if (fields[name]?.mark !== 'optional') continue
                if (!(name in held)) continue
                const { [name]: _dropped, ...rest } = held
                out.push(rest)
            }
            for (const name in fields) {
                const field = fields[name]
                if (field === undefined || !(name in held)) continue
                for (const smaller of shrinkOf(
                    codecOfTerm(field.t),
                    held[name],
                )) {
                    out.push({ ...held, [name]: smaller })
                }
            }
            return out
        }
        case 'dunion': {
            const held = value as Record<string, unknown>
            const tag = String(held[def.d])
            const chosen = def.options.find(
                (option) => variantTag(def.d, option) === tag,
            )
            return chosen ? shrinkOf(codecOfTerm(chosen), value) : []
        }
        case 'union': {
            const names = new Set(
                Object.keys(value as Record<string, unknown>).filter(
                    (k) => (value as Record<string, unknown>)[k] !== undefined,
                ),
            )
            const chosen = def.options.find(
                (option) =>
                    option.kind === 'object' &&
                    [...names].every((name) => name in option.body.fields),
            )
            return chosen ? shrinkOf(codecOfTerm(chosen), value) : []
        }
        case 'refine':
            return shrinkOf(codecOfTerm(def.inner), value).filter(holds(def.q))
        case 'nullable':
            return value === null
                ? []
                : [null, ...shrinkOf(codecOfTerm(def.inner), value)]
        case 'legacy':
            return shrinkOf(codecOfTerm(def.inner), value)
        case 'lazy':
            return shrinkOf(codecOfTerm(def.get()), value)
        // a branch has no one codec to shrink through, which is why `at` refuses it; a hand-written
        // codec shrinks only if it said how, and `shrink` above is where that was read
        // a hand-written codec shrinks only where the caller said how, and the caller said it in
        // the definition — the same place its pair and its generator live
        case 'custom':
            return def.shrink ? def.shrink(value as never) : []
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
 * checkIso(string.set(), {
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

// ── (U): exactly one option admits each input, per side ──────────────

/**
 * **(U), the last row of the conformance table.**
 *
 * `docs/codec-formalization.md` §5 states it as *for each union input: exactly one option admits it,
 * per side*, and `Calculus.UniqueAdmission` is that sentence in the model:
 *
 * ```
 * ∀ o ∈ os, ∀ t a, o.e t = some a → os.filter (·.admitA a) = [o] ∧ os.filter (·.admitV t) = [o]
 * ```
 *
 * So the inputs are not arbitrary: they are **canonical pairs** — a value one option can write, and
 * the attribute it writes it to. That is what makes the property checkable at all, and it is why
 * this generates per *option* rather than per union.
 *
 * **Admission is read off the definition, never off the union's own matcher.** A test that asked
 * `union` which option it picked would be checking the implementation against itself. What is asked
 * here is what the model asks:
 *
 * - an **object** option admits by *names* — every name present declared, every required name
 *   present (`keysOk`, `OptionSem.byNames`). It is never tried, because `object({ a })` will happily
 *   encode `{ a, b }` and lose `b`, so "it encoded" is not evidence.
 * - a **tagged** option admits by its discriminator's stored value (`OptionSem.byTag`).
 * - anything else admits by *being defined* on the input (`OptionSem.byAttempt`) — not by the kind
 *   filter the implementation uses first. Where the two differ, this reports it, and that difference
 *   is the whole reason to run it.
 *
 * Every union reachable from the subject is checked, not only the outermost one: (U) is a condition
 * on a union node, and the interesting ones are nested inside an entity.
 *
 * A failure to *encode* is never reported — an option that declines a value it generated has simply
 * produced no canonical pair. What is reported is a pair that two options claim, or none, or one
 * that is not the option that wrote it.
 */
export const checkUniqueAdmission = (
    subject: AnyCodec,
    {
        count = 50,
        seed = 0x5eed,
        size = 4,
    }: Pick<CheckOptions, 'count' | 'seed' | 'size'> = {},
): void => {
    const sites = unionsIn(subject)
    if (sites.length === 0) {
        throw new CodecError(
            '(U) is a condition on a union, and this codec has none — nothing was checked, which is not the same as passing',
        )
    }
    const rng = rngFrom(seed)
    for (const site of sites) {
        for (const option of site.options) {
            for (let i = 0; i < count; i++) {
                let value: unknown
                try {
                    value = arbitraryOf(option.codec, rng, size)
                } catch {
                    break // an option that cannot generate says nothing about (U)
                }
                const attribute = written(option.codec, value)
                if (!attribute) continue // no canonical pair, nothing to say

                const claim = (
                    side: string,
                    admitted: readonly UnionOption[],
                ) => {
                    if (
                        admitted.length === 1 &&
                        (admitted[0] as UnionOption).codec === option.codec
                    ) {
                        return
                    }
                    throw new CodecError(
                        `(U) fails on the ${side} side of ${site.describe}: ` +
                            (admitted.length === 0
                                ? 'no option admits a pair its own option wrote.'
                                : admitted.length > 1
                                  ? `${admitted.length} options admit it — ${admitted.map((o) => o.describe).join(' and ')}.`
                                  : `the option that admits it is ${(admitted[0] as UnionOption).describe}, which is not the one that wrote it.`) +
                            `\n  wrote by  = ${option.describe}` +
                            `\n  seed      = ${seed}, case ${i}` +
                            `\n  value     = ${show(value)}` +
                            `\n  attribute = ${show(attribute)}` +
                            `\n  options   = ${site.options.map((o) => o.describe).join(' | ')}`,
                    )
                }

                claim(
                    'write',
                    site.options.filter((o) => o.admitsValue(value)),
                )
                claim(
                    'read',
                    site.options.filter((o) => o.admitsAttribute(attribute)),
                )
            }
        }
    }
}

/** One union node, and its options as the model's `OptionSem`s. */
type UnionSite = {
    readonly describe: string
    readonly options: readonly UnionOption[]
}

/** An option's two admission functions and the pair they belong to — `OptionSem`. */
type UnionOption = {
    readonly codec: AnyCodec
    readonly describe: string
    readonly admitsValue: (value: unknown) => boolean
    readonly admitsAttribute: (attribute: AttributeValue) => boolean
}

/** The attribute a codec writes for a value, or nothing — `e v = some a`, as a partial function. */
const written = (
    codec: AnyCodec,
    value: unknown,
): AttributeValue | undefined => {
    try {
        const out = codec.encode(value as never)
        return failed(out) ? undefined : (out as AttributeValue)
    } catch {
        return undefined
    }
}

/**
 * Whether a codec reads an attribute at all — `p a` is defined.
 *
 * **Asking the codec, which is what the question is.** This was `admitsAttribute`, a reader that
 * walked the definition and answered the same thing; the reader is gone, and the six lines it
 * shared with `lean.ts`'s read-verdict generator are one call in each place. The cast is the
 * mirror of `accepts`': a codec's `decode` is typed to its own attribute and this asks about one
 * that may not be, and a `decode` that throws on it answers `false` rather than escaping — which
 * is what `checkUniqueAdmission`'s planted write-only option depends on.
 */
const reads = readsBack

/** A value read as a bare record of names, as the object matcher reads one. */
const recordOf = (value: unknown): Record<string, unknown> | undefined => {
    if (typeof value !== 'object' || value === null) return undefined
    const proto = Object.getPrototypeOf(value) as object | null
    return proto === Object.prototype || proto === null
        ? (value as Record<string, unknown>)
        : undefined
}

/** The map an attribute carries, where it carries one. */
const mapOf = (attribute: AttributeValue): AttributeMap | undefined =>
    memberOf(attribute) === 'M'
        ? ((attribute as { readonly M: AttributeMap }).M ?? {})
        : undefined

/** `keysOk`: every name present is declared, and every required name is present. */
const keysOk = (
    names: readonly string[],
    declares: ReadonlySet<string>,
    requires: readonly string[],
): boolean =>
    names.every((name) => declares.has(name)) &&
    requires.every((name) => names.includes(name))

/** An object option's spec, as the pair `keysOk` needs. */
const declaration = (of: Readonly<Record<string, Field>>) => {
    const declares = new Set<string>()
    const requires: string[] = []
    for (const name in of) {
        declares.add(name)
        if (of[name]?.mark !== 'optional') requires.push(name)
    }
    return { declares, requires }
}

/** `OptionSem.byNames` — an object option decides by names, never by being attempted. */
const byNames = (
    codec: AnyCodec,
    of: Readonly<Record<string, Field>>,
): UnionOption => {
    const { declares, requires } = declaration(of)
    return {
        codec,
        describe: `{ ${[...declares]
            .map((name) => (requires.includes(name) ? name : `${name}?`))
            .join(', ')} }`,
        admitsValue: (value) => {
            const held = recordOf(value)
            return (
                !!held &&
                keysOk(
                    Object.keys(held).filter((k) => held[k] !== undefined),
                    declares,
                    requires,
                )
            )
        },
        admitsAttribute: (attribute) => {
            const map = mapOf(attribute)
            return !!map && keysOk(Object.keys(map), declares, requires)
        },
    }
}

/** `OptionSem.byTag` — a `(dunion)` option is admitted by its discriminator. */
const byTag = (
    codec: AnyCodec,
    discriminator: string,
    tags: readonly string[],
): UnionOption => ({
    codec,
    describe: `'${discriminator}' of ${tags.map((t) => `'${t}'`).join(' | ')}`,
    admitsValue: (value) => {
        const held = recordOf(value)
        const tag = held?.[discriminator]
        return (
            (typeof tag === 'string' || typeof tag === 'number') &&
            tags.includes(String(tag))
        )
    },
    admitsAttribute: (attribute) => {
        /**
         * The discriminator sits under the `M`, where every other option's attributes sit.
         *
         * This used to read it at the *top* of what `e` produced, and had to: a `(dunion)`
         * definition carried its variants as **item** codecs, so the option here wrote an item
         * rather than an `'M'`, and reading through `mapOf` found nothing. The definition carries
         * terms now and the option is the codec the term denotes, which writes its map like any
         * other codec — so a union's options are all read at one level and the exception is gone.
         */
        const map = mapOf(attribute)
        const carried = map?.[discriminator]
        if (!carried) return false
        const member = memberOf(carried)
        if (member !== 'S' && member !== 'N') return false
        return tags.includes(
            String((carried as Record<string, unknown>)[member]),
        )
    },
})

/**
 * A ground option: the `κ` filter, and then the attempt.
 *
 * `codec-calculus.md` §5 is explicit that an option admits `t` when "the `κ`/name filter passes
 * **and** `eᵢ(t)` is defined", and that is what this reads. The model's `OptionSem.byAttempt` drops
 * the first conjunct — `FIDELITY.md` D1 records that `κ` is never consulted by the denotation — and
 * the difference used to be visible: **`union([string, number])` violated (U) under the model's
 * reading and satisfied it under the specification's**, because `number.encode('-1')` succeeded.
 *
 * **The two readings coincide, and by theorem rather than by luck.** `Calculus.κ_sound` is
 * `κ t = some ks → (denote t).e v = some a → Value.kind v ∈ ks` — encoding lands in `κ`. Its
 * contrapositive is that a κ failure forces an encode failure, so "the filter refuses and the
 * attempt succeeds", the only state in which the two conjuncts disagree, **cannot arise in the
 * model at all**. Where `κ` answers `⊤` there is no conjunct to fail, which is the same vacuity
 * this function reads off an absent `carries`.
 *
 * A sentence here used to say the readings "still differ" after that divergence closed. They do
 * not, and the claim outlived its own witness by three commits: `number.encode('-1')` stopped
 * succeeding in `c37e5cf`, and nothing was put in its place.
 *
 * **What is not a theorem is the correspondence between the two sides' κ.** The model's is
 * `κ : Term → Option (List Kind)`; this library's is {@link carries}, over `Shape`, which is a
 * coarser alphabet. `κ_sound` settles the model; what settles the pair is the bridge, whose
 * union-resolution artifact states its counts in its own generated header. So this reads the
 * specification's form because the first conjunct is what a union's declaration guard is made of
 * — not because the two forms are known to select differently.
 *
 * `κ` is read off the term, which is where it lives: {@link carries} is the kinds of value a
 * term takes and {@link member} the member it stores them in, both computed from the term and
 * neither from the union's matcher. Where a term answers neither, the filter is `⊤` and admission
 * is the attempt alone — which is the honest answer for a `custom` and is how one gets caught.
 */
const byKindThenAttempt = (codec: AnyCodec): UnionOption => {
    const takes = carries(codec)
    const member = termMember(codec.def)
    return {
        codec,
        describe: codec.def?.kind ?? 'a codec',
        admitsValue: (value) => {
            const shape = shapeOf(value)
            if (takes && shape && !takes.includes(shape)) return false
            return !!written(codec, value)
        },
        admitsAttribute: (attribute) => {
            const carried = memberOf(attribute)
            if (member && carried && member !== carried) return false
            return reads(codec, attribute)
        },
    }
}

/** `optionSemOf`: an object option decides by names, anything else by attempt. */
const optionOfDef = (def: Term): UnionOption => {
    const codec = codecOfTerm(def)
    return def.kind === 'object'
        ? byNames(codec, def.body.fields)
        : byKindThenAttempt(codec)
}

/**
 * Every union reachable from a codec, outermost first.
 *
 * Keyed on the *definition* rather than the codec, which is what stops a `lazy` cycle: a recursive
 * entity hands back the codec it already walked, and its def is the same object.
 */
const unionsIn = (subject: AnyCodec): readonly UnionSite[] => {
    const out: UnionSite[] = []
    const seen = new Set<object>()

    const walk = (codec: AnyCodec | undefined, depth: number): void => {
        const def = codec?.def
        if (!def || depth < 0 || seen.has(def)) return
        seen.add(def)
        const inner = (child: AnyCodec | undefined) => walk(child, depth - 1)
        switch (def.kind) {
            case 'union':
                out.push({
                    describe: `union(${def.options
                        .map((v) => v.kind)
                        .join(', ')})`,
                    options: def.options.map(optionOfDef),
                })
                def.options.forEach((option) => inner(codecOfTerm(option)))
                return
            case 'dunion': {
                // one option per variant, and the tag is read off the variant's own `d` field —
                // `dunionCodec`'s options are `(List String × Codec)`, and a variant answers to one
                const tagged = def.options.map((option) => ({
                    tag: variantTag(def.d, option),
                    option,
                }))
                out.push({
                    describe: `discriminatedUnion('${def.d}', ${tagged
                        .map(({ tag }) => `'${tag}'`)
                        .join(', ')})`,
                    options: tagged.map(({ tag, option }) =>
                        byTag(codecOfTerm(option), def.d, [tag]),
                    ),
                })
                def.options.forEach((option) => inner(codecOfTerm(option)))
                return
            }
            case 'set':
                return inner(codecOfTerm({ kind: def.base }))
            case 'array':
                return inner(codecOfTerm(def.elem))
            case 'record':
                return inner(codecOfTerm(def.val))
            case 'tuple':
                def.elems.forEach((element) => inner(codecOfTerm(element)))
                return inner(def.tail && codecOfTerm(def.tail))
            case 'object': {
                const { fields, rest } = def.body
                Object.values(fields).forEach((field) =>
                    inner(codecOfTerm(field.t)),
                )
                return inner(
                    typeof rest === 'string' ? undefined : codecOfTerm(rest.t),
                )
            }
            case 'refine':
            case 'nullable':
            case 'held':
            case 'legacy':
                return inner(codecOfTerm(def.inner))
            case 'lazy':
                return inner(codecOfTerm(def.get()))
            default:
                return
        }
    }

    walk(subject, 12)
    return out
}
