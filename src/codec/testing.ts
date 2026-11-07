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
 * The arbitraries themselves stay on the codecs — `arbitrary` and `shrink` are a codec describing
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
 * equality the second law is *false* here and should be: `set` sorts its members, so
 * `encode(decode({ SS: ['b', 'a'] }))` is `{ SS: ['a', 'b'] }` — the same set, not the same bytes.
 * So stability is checked *modulo* the equivalence "decodes to the same entity", which is exactly a
 * **quotient lens** — a bidirectional transformation well behaved modulo an equivalence the
 * programmer controls, the equivalence being induced by a **canonizer** (Foster, Pilkiewicz and
 * Pierce, ICFP 2008). Sorting a set is a canonizer.
 *
 * {@link checkIso} is the one place the second law *is* an equality, because a {@link held} adapter
 * claims a true isomorphism rather than a retraction — and it checks the direction
 * `checkRoundTrip` cannot reach.
 *
 * The lens laws for the asymmetric case are Foster, Greenwald, Moore, Pierce and Schmitt's GetPut /
 * PutGet (TOPLAS 2007); there are a dozen variants and a taxonomy of them if the distinctions matter.
 */
import type { AttributeMap, AttributeValue } from './attribute'
import { DynamoNumber, memberOf } from './attribute'
import type {
    AnyCodec,
    AttributeCodec,
    ItemCodec,
    opaque,
    Rng,
    Segment,
} from './codec'
import { at, CodecError, codecOfTerm, failed, orThrow } from './codec'
import { accepts, holds, termOf } from './denote'
import { asPath, Disagreement } from './result'
import type { Term } from './term'
import {
    componentsOf,
    holdsNoValue,
    isOpaqueSugar,
    targetOf,
    member as termMember,
    usedTargetOf,
} from './term'

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
     * the arbitrary would have to answer.
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
 * The options of a check with their defaults, and the draw that each check reads: one value of the
 * codec, repaired by `refine`, that `filter` accepts. A value that the filter rejects, or that the
 * check cannot use, is counted by `discard`, and a run that discards too many is reported and not
 * spun on, so a filter that rejects every value cannot give a check that compares nothing.
 */
const resolved = <T>({
    count = 100,
    seed = 0x5eed,
    size = 4,
    equals = structuralEquals,
    refine = (value: T) => value,
    filter = () => true,
}: CheckOptions<T> = {}) => {
    const rng = rngFrom(seed)
    const maxDiscards = Math.max(100, count * 10)
    let discards = 0
    const discard = (why: string): void => {
        if (++discards > maxDiscards) {
            throw new CodecError(
                `${why} for ${discards} values with seed ${seed}, so the check has nothing to test; narrow the filter, or repair with refine`,
            )
        }
    }
    const next = (subject: AnyCodec) => {
        for (;;) {
            const drawn = generated<T>(subject, rng, size, refine)
            if (filter(drawn.value)) return drawn
            discard('the filter rejected the value')
        }
    }
    return { count, seed, size, equals, refine, filter, rng, discard, next }
}

/**
 * The refusal that **(C)** gives: a value that the codec's own read produced is a value that it can
 * write back, so a codec that cannot write one fails the law. `who` names the codec, and `at` the
 * case where the check numbers its cases.
 */
const unwritable = (
    who: string,
    value: unknown,
    seed: number,
    why: unknown,
    at = '',
): CodecError =>
    new CodecError(
        `(C) fails: ${who} cannot write ${show(value)}, a value its own read produced, with seed ${seed}${at}: ${why}`,
    )

/**
 * `decode ∘ encode = id`, over generated entities.
 *
 * Generation is driven by the codec rather than the TypeScript type — see
 * {@link AttributeCodec.arbitrary} — so `decimal` yields normalised decimals and `string.set()`
 * never yields the empty set. A structurally free arbitrary would produce values DynamoDB itself
 * rejects and blame the codec.
 *
 * Deterministic: the same seed reproduces a counterexample from CI.
 */
export const checkRoundTrip = <T>(
    subject: Checkable<T>,
    options: CheckOptions<T> = {},
): void => {
    const { count, seed, equals, refine, filter, next } = resolved(options)

    for (let i = 0; i < count; i++) {
        const { value } = next(subject as unknown as AnyCodec)
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
 * DynamoDB reorders the members of a set, so `encode ∘ decode = id` on an item is false for a set.
 * What holds is that one pass through storage reaches a fixed point. The
 * `parse(print(parse(s))) = parse(s)` of tolerant parsers, and the law to assert for a table whose
 * rows predate the current codec.
 *
 * An empty list is a refusal: a check that tests nothing is no green run.
 */
export const checkStable = <T>(
    subject: Pick<Checkable<T>, 'unsafeEncode' | 'unsafeDecode'>,
    items: readonly AttributeMap[],
    equals: (a: unknown, b: unknown) => boolean = structuralEquals,
): void => {
    if (items.length === 0) {
        throw new CodecError(
            'checkStable was given no item, so the check has nothing to test; give it the items of a table',
        )
    }
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
 * **(C), checked on attributes that `encode` never makes.**
 *
 * `p a = some v ⟹ e v is defined` — whatever a codec reads, it can write back. `checkAgainst` and
 * `checkEquivalent` ask (C) of a value that the read of the codec produced from a generated value.
 * The other checks here generate *values* and round-trip them, so `decode` only ever sees
 * attributes that `encode` produced. That is the wrong direction for (C): the attribute that
 * breaks it is by definition one `encode` would never make.
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
 * A refusal of a mutated attribute, a `CodecError`, is never reported: refusing it is exactly right, and
 * is what most of these do. What is reported is a mutation that decodes and then cannot be encoded,
 * and a mutation that makes `decode` throw anything but a `CodecError`, because a refusal is a value.
 * A mutation that decodes must also keep the shape of its row through `encode(decode(x))`.
 */
export const checkDecodesAreWritable = <T>(
    subject: Checkable<T>,
    options: CheckOptions<T> = {},
): void => {
    const { count, seed, discard, next } = resolved(options)
    for (let i = 0; i < count; i++) {
        const { value, throughRead } = next(subject as never)

        let encoded: AttributeMap
        try {
            encoded = subject.unsafeEncode(value)
        } catch (error) {
            // a value the pair's own read produced is one (C) says it can write back
            if (throughRead) {
                throw unwritable(
                    'the codec',
                    value,
                    seed,
                    (error as Error).message,
                    `, case ${i}`,
                )
            }
            // any other value the codec declines to write says nothing about (C)
            discard('the codec declined to write the value')
            i--
            continue
        }

        for (const { what, item } of mutations(encoded)) {
            let read: T
            try {
                read = subject.unsafeDecode(item)
            } catch (error) {
                // refusing it is the correct answer, and the common one. A refusal is a value, so
                // any other throw is a boundary that read a payload before it checked it
                if (error instanceof CodecError) continue
                throw new CodecError(
                    'a refusal is not a value: decode threw an error that is no CodecError.\n' +
                        `  mutation = ${what}\n` +
                        `  seed     = ${seed}, case ${i}\n` +
                        `  item     = ${JSON.stringify(item)}\n` +
                        `  threw    = ${error instanceof Error ? `${error.constructor.name}: ${error.message}` : 'a value that is no Error'}`,
                )
            }
            let rewritten: AttributeMap
            try {
                rewritten = subject.unsafeEncode(read)
            } catch (error) {
                throw new CodecError(
                    '(C) fails: this attribute decodes and the value it yields cannot be encoded.\n' +
                        `  mutation = ${what}\n` +
                        `  seed     = ${seed}, case ${i}\n` +
                        `  item     = ${JSON.stringify(item)}\n` +
                        `  decoded  = ${JSON.stringify(read)}\n` +
                        `  encoding it again said: ${(error as Error).message}`,
                )
            }
            const changed = shapeChange(
                subject.def,
                { M: item },
                { M: rewritten },
                '',
            )
            if (changed !== undefined) {
                throw new CodecError(
                    'a read keeps the shape of the row: encode(decode(x)) differs from x.\n' +
                        `  mutation = ${what}\n` +
                        `  seed     = ${seed}, case ${i}\n` +
                        `  item     = ${JSON.stringify(item)}\n` +
                        `  written  = ${JSON.stringify(rewritten)}\n` +
                        `  ${changed}`,
                )
            }
        }
    }
}

/**
 * The shape of an attribute: its member, and below it the size of a set, the length of a list and the
 * names of a map. No value is in it, so two numerals that read to one value are two members that
 * become one.
 */
const shapeOfAttribute = (value: AttributeValue | undefined): unknown => {
    if (value === undefined) return 'absent'
    const m = memberOf(value)
    if (m === 'SS' || m === 'NS' || m === 'BS') {
        return [m, (value[m] as readonly unknown[]).length]
    }
    if (m === 'L') return ['L', (value.L ?? []).length]
    if (m === 'M') return ['M', Object.keys(value.M ?? {}).sort()]
    return m
}

/**
 * The term below a `ref`, a `held` and a `refine`, as far as the term reads. `undefined` where the
 * term cannot be read: a name that no scope binds, or more hops than a closed term holds.
 */
const storedTerm = (t: Term): Term | undefined => {
    let at = t
    for (let hops = 0; hops < 64; hops++) {
        if (at.kind === 'ref') {
            const target = targetOf(at)
            if (target === undefined) return undefined
            at = target
        } else if (at.kind === 'held' || at.kind === 'refine') at = at.inner
        else return at
    }
    return undefined
}

/** The term of one position of a list: a declared position, or the spread. */
const elementTerm = (
    t: Term | undefined,
    at: number,
    length: number,
): Term | undefined => {
    if (t?.kind !== 'list') return undefined
    if (at < t.pre.length) return t.pre[at]
    const fromEnd = at - (length - t.suf.length)
    return fromEnd >= 0 ? t.suf[fromEnd] : t.spread
}

/**
 * Where a read changed the shape of a row, or `undefined`. **Law X**: `encode(decode(x))` keeps the
 * shape of `x` at every depth, the members, the size of each set, the length of each list and the
 * names of each map. A read that maps two stored members to one is no injective image, as the model's
 * `setImage` states, and a set that loses a member changes what the row holds.
 *
 * The walk reads the term and the two rows together. Two reads change a shape by design, and the
 * term states each one: at a map, a name that the row lacks and the term declares as `fill` is
 * written with its fill value, and at a position that the term reads through a `legacy`, the older
 * form is written in the current form, so that position is not compared. A union passes where one
 * option passes. Where the term cannot be read below a position (a name that no scope binds, or a
 * form that is no map or list), the comparison is strict there, which can report a lawful read.
 */
const shapeChange = (
    t: Term | undefined,
    before: AttributeValue | undefined,
    after: AttributeValue | undefined,
    path: string,
): string | undefined => {
    const term = t === undefined ? undefined : storedTerm(t)
    if (term?.kind === 'legacy') return undefined
    if (term?.kind === 'union') {
        const each = term.options.map((o) =>
            shapeChange(o, before, after, path),
        )
        return each.some((one) => one === undefined) ? undefined : each[0]
    }
    const was = JSON.stringify(shapeOfAttribute(before))
    const now = JSON.stringify(shapeOfAttribute(after))
    const differs = `${path === '' ? 'the row' : path} was ${was} and is ${now}`
    if (before === undefined || after === undefined) {
        return was === now ? undefined : differs
    }
    const m = memberOf(before)
    if (m === 'L' && memberOf(after) === 'L') {
        const [one, other] = [before.L ?? [], after.L ?? []]
        if (one.length !== other.length) return differs
        for (const [at, child] of one.entries()) {
            const found = shapeChange(
                elementTerm(term, at, one.length),
                child,
                other[at],
                `${path}[${at}]`,
            )
            if (found !== undefined) return found
        }
        return undefined
    }
    if (m === 'M' && memberOf(after) === 'M') {
        const [one, other] = [before.M ?? {}, after.M ?? {}]
        for (const name of new Set([
            ...Object.keys(one),
            ...Object.keys(other),
        ])) {
            const declared =
                term?.kind === 'object' && Object.hasOwn(term.body.fields, name)
                    ? term.body.fields[name]
                    : undefined
            if (one[name] === undefined && declared?.mark === 'fill') continue
            const found = shapeChange(
                declared?.t ??
                    (term?.kind === 'object' ? term.body.rest : undefined),
                one[name],
                other[name],
                `${path === '' ? '' : `${path}.`}'${name}'`,
            )
            if (found !== undefined) return found
        }
        return undefined
    }
    return was === now ? undefined : differs
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
    readonly to: (
        value: AttributeValue,
    ) => { readonly value: unknown } | undefined
}[] = [
    {
        // `set`'s encode refused this and its decode returned it for as long as both existed
        what: 'an empty set',
        to: (v) => {
            const m = memberOf(v)
            if (m === 'SS') return { value: { SS: [] } }
            if (m === 'NS') return { value: { NS: [] } }
            if (m === 'BS') return { value: { BS: [] } }
            return undefined
        },
    },
    {
        // the form DynamoDB normalises away, which `decimal` was writing and reading
        what: 'a denormalised N',
        to: (v) =>
            memberOf(v) === 'N'
                ? { value: { N: `${v.N as string}0` } }
                : undefined,
    },
    {
        what: 'an N with a leading zero',
        to: (v) =>
            memberOf(v) === 'N'
                ? { value: { N: `0${v.N as string}` } }
                : undefined,
    },
    {
        what: 'an N past the magnitude DynamoDB stores',
        to: (v) =>
            memberOf(v) === 'N' ? { value: { N: '1e126' } } : undefined,
    },
    {
        what: 'an N that is not a number at all',
        to: (v) => (memberOf(v) === 'N' ? { value: { N: 'NaN' } } : undefined),
    },
    {
        what: 'an empty list',
        to: (v) => (memberOf(v) === 'L' ? { value: { L: [] } } : undefined),
    },
    {
        what: 'an empty map',
        to: (v) => (memberOf(v) === 'M' ? { value: { M: {} } } : undefined),
    },
    {
        what: 'a string where a number was stored',
        to: (v) =>
            memberOf(v) === 'N' ? { value: { S: v.N as string } } : undefined,
    },
    {
        // two numerals that read to one value are two members that a set holds as one
        what: 'a duplicate member in two numeral forms',
        to: (v) => {
            const first = memberOf(v) === 'NS' ? v.NS?.[0] : undefined
            return first === undefined
                ? undefined
                : {
                      value: {
                          NS: [
                              first,
                              `${first}${first.includes('.') ? '' : '.'}00000000000000001`,
                          ],
                      },
                  }
        },
    },
    {
        // `String` of it throws, so a reader that renders a payload in a message throws with it
        what: 'a null-prototype object as the payload',
        to: (v) => {
            const m = memberOf(v)
            return m === 'S' || m === 'N'
                ? { value: { [m]: Object.create(null) } }
                : undefined
        },
    },
    {
        what: 'a null list entry',
        to: (v) => (memberOf(v) === 'L' ? { value: { L: [null] } } : undefined),
    },
    {
        what: 'an undefined list entry',
        to: (v) =>
            memberOf(v) === 'L' ? { value: { L: [undefined] } } : undefined,
    },
    {
        what: 'a NULL that is false',
        to: (v) =>
            memberOf(v) === 'NULL' ? { value: { NULL: false } } : undefined,
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

/**
 * A value that `decode` must refuse as a value. The one cast of the pool: no shape is a value that
 * DynamoDB produces, and the check feeds each one to `decode` on purpose, so the type of a row
 * cannot hold it.
 */
const malformed = (value: unknown): never => value as never

const mutations = (item: AttributeMap): readonly Mutation[] => {
    // the row itself is no map, which a caller of `decode` can hand it past the type
    const out: Mutation[] = [
        { what: 'the row is undefined', item: malformed(undefined) },
        { what: 'the row is null', item: malformed(null) },
    ]
    for (const [key, attribute] of Object.entries(item)) {
        for (const { at, rebuild } of positions(attribute)) {
            for (const { what, to } of SHAPES) {
                const replaced = to(at)
                if (!replaced) continue
                out.push({
                    what: `${what}, at '${key}'`,
                    item: {
                        ...item,
                        [key]: rebuild(malformed(replaced.value)),
                    },
                })
            }
        }
        // and the attribute missing altogether, which `optional` and `fill` must survive
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
 * at(k).encode(x[k])         = encode(x)[k]
 * ```
 *
 * `encode` builds a `PutItem`, `encodePartial` an `UpdateItem`, `at(item, [k]).encode` one
 * `ExpressionAttributeValues` entry. Nothing structural forces them to agree, and a divergence means
 * a row that reads back differently depending on how it was last touched.
 *
 * Invisible to {@link checkRoundTrip}: each path round-trips perfectly on its own.
 */
export const checkEncodePaths = <T, Spec>(
    subject: ItemCodec<T, Spec>,
    options: CheckOptions<T> = {},
): void => {
    const { count, seed, equals, next } = resolved(options)
    const fail = (what: string, i: number, a: unknown, b: unknown) => {
        throw new CodecError(
            `${what} at case ${i} with seed ${seed}\n  ${JSON.stringify(a)}\n  ${JSON.stringify(b)}`,
        )
    }

    for (let i = 0; i < count; i++) {
        const { value } = next(subject as unknown as AnyCodec)
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

            // the names are the names that the value carries, so the path is no tuple of the spec
            const named: readonly Segment[] = [name]
            const viaField = at(subject, named).unsafeEncode(one as never)
            if (!equals(viaField, attribute)) {
                fail(
                    `at(item, ['${name}']).unsafeEncode differs from unsafeEncode`,
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
 *
 * An empty list is a refusal: a check that tests nothing is no green run.
 */
export const checkMembersStable = <T>(
    subject: Pick<Checkable<T>, 'unsafeEncode' | 'unsafeDecode'>,
    items: readonly AttributeMap[],
    equals: (a: unknown, b: unknown) => boolean = structuralEquals,
): void => {
    if (items.length === 0) {
        throw new CodecError(
            'checkMembersStable was given no item, so the check has nothing to test; give it the items of a table',
        )
    }
    for (const [i, item] of items.entries()) {
        const rewritten = subject.unsafeEncode(subject.unsafeDecode(item))
        for (const [name, attribute] of Object.entries(item)) {
            const after = rewritten[name]
            if (after === undefined) {
                throw new CodecError(
                    `'${name}' is absent after a read-modify-write at item ${i}`,
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
// The codecs carry a {@link Term} saying what they are; the arbitraries live here and dispatch
// on it. An arbitrary baked into every codec ships to production whether or not anything ever
// runs a property test, and no bundler can shake a closure out of an object that is always
// constructed.

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

/** The shrinks of a value that a partial map gave: none where the map refused. */
const shrinkThrough = (
    mapped: unknown,
    shrink: (inner: unknown) => readonly unknown[],
): readonly unknown[] => (failed(mapped) ? [] : shrink(mapped))

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
    /** `exact` is the canonical `opaque`, which holds a number as a `DynamoNumber`. */
    numbers: opaque.Numbers | 'exact',
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
    if (numbers === 'exact') {
        scalars.push(orThrow(DynamoNumber.from(someDecimal(rng))))
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
        numbers === 'exact' && rng() < 0.5
            ? new Set([orThrow(DynamoNumber.from(someDecimal(rng)))])
            : new Set([someString(rng), someString(rng)].sort()),
    ])
}

const shrinkUnknown = (value: unknown): readonly unknown[] => {
    if (value === null) return []
    if (typeof value === 'string') return [null, ...shrinkString(value)]
    if (typeof value === 'number') return [null, ...shrinkNumber(value)]
    if (value instanceof DynamoNumber) return [null]
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
 * Runs only from an arbitrary, so only during a property run. A predicate that rejects most draws
 * does not fail — it silently shrinks the search — so it says so once; `onThinSearch` routes that
 * somewhere other than the console.
 */
const bySampling = <Wide, Narrow extends Wide, Context>(
    draw: (rng: Rng, size: number, context: Context) => Wide,
    is: (value: Wide) => value is Narrow,
    what: string,
    onThinSearch?: (what: string, rate: number) => void,
): ((rng: Rng, size: number, context: Context) => Narrow) => {
    let attempts = 0
    let accepted = 0
    let warned = false

    return (rng, size, context) => {
        for (let i = 0; i < SAMPLE_LIMIT; i++) {
            attempts++
            const candidate = draw(rng, size, context)
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
const samplers = new WeakMap<
    object,
    (rng: Rng, size: number, drew: Draws) => unknown
>()

/**
 * What one generation drew: how many values the arbitrary produced through a `held` read. A value
 * that came through a read is one the pair produced, so a codec that then declines to write it fails
 * (C) rather than declining a stranger.
 */
type Draws = { reads: number }

/**
 * A value of the codec, and whether it came through the read of the pair. One condition decides it:
 * the value is the raw draw, so a value that `refine` repaired is a stranger and a value that
 * `refine` handed back as it was is not.
 */
const generated = <T>(
    subject: AnyCodec,
    rng: Rng,
    size: number,
    refine?: (raw: T) => T,
): { readonly value: T; readonly throughRead: boolean } => {
    const drew: Draws = { reads: 0 }
    const raw = draw(subject, rng, size, drew) as T
    const value = refine ? refine(raw) : raw
    return { value, throughRead: drew.reads > 0 && value === raw }
}

/** Whether each `ref` lies on a cycle. A closed codec binds each `ref` one time. */
const onCycle = new WeakMap<Term, boolean>()
const closesCycle = (t: Term): boolean => {
    let known = onCycle.get(t)
    if (known === undefined) {
        known = componentsOf([t]).some(({ members }) => members.has(t))
        onCycle.set(t, known)
    }
    return known
}

/**
 * A value the codec can carry.
 *
 * Dispatches on {@link Term}, so a codec kind that grows an arbitrary grows it here rather than
 * in the codec itself. `size` bounds recursion.
 */
export const arbitraryOf = (codec: AnyCodec, rng: Rng, size: number): unknown =>
    draw(codec, rng, size, { reads: 0 })

const draw = (
    codec: AnyCodec,
    rng: Rng,
    size: number,
    drew: Draws,
): unknown => {
    const def = termOf(codec)
    switch (def.kind) {
        case 'string':
            return someString(rng)
        // one value, so there is nothing to pick between; several alternatives are a union of
        // literals and the union row picks the option
        case 'literal':
            return def.v
        // the base's carrier is a `DynamoNumber`, and `someDecimal` already generates the
        // stored spellings the constructor normalises to
        case 'number':
            return orThrow(DynamoNumber.from(someDecimal(rng)))
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
            return someUnknown(rng, size, 'exact')
        case 'held':
            /**
             * Without a stated `arbitrary`, generated for the inner codec and handed out through
             * `decode`, so the pair produced what is generated — an arbitrary for the *outer* type
             * could invent a value `encode` never makes, and the round-trip would fail on the
             * arbitrary rather than on the codec. A stated `arbitrary` is the caller's own choice of
             * held value, and the round trip checks that value.
             *
             * The conversion is called raw, where the codec guards it. Here the input is correct by
             * construction, so a throw is a bug in the adapter and belongs at the top of a property
             * run rather than folded into a value.
             */
            if (def.arbitrary) return def.arbitrary(rng, size)
            // a numeric policy of `opaque` generates the JS values it holds, as before it was a
            // `held`. The derived arbitrary would hand it an `NS` read, which the policy refuses
            if (def.via === 'opaqueLossy')
                return someUnknown(rng, size, 'lossy')
            if (def.via === 'opaqueRefuse')
                return someUnknown(rng, size, 'refuse')
            // the derived rule: the read of the pair, over a value of the inner codec. A read that
            // refuses the value is a partial `g`, so the draw is made again
            for (let tries = 0; tries < SAMPLE_LIMIT; tries++) {
                const read = def.g(
                    draw(codecOfTerm(def.inner), rng, size, drew) as never,
                )
                if (failed(read)) continue
                drew.reads++
                return read
            }
            throw new CodecError(
                `the read of this adapter refused ${SAMPLE_LIMIT} values of its inner codec, so a value of it cannot be generated; pass \`arbitrary\` to say what one looks like`,
            )
        case 'set': {
            /**
             * Deduplicated by what is *stored*, as the codec does — two values that write the same
             * member are one member of the set, so an arbitrary that did not deduplicate by the stored
             * form would produce a set the codec cannot carry back unchanged.
             *
             * The stored form is computed once per value and kept as the map key. It is an
             * `encode`, and reading it from inside the comparator ran that encode
             * `O(n log n)` times — as did re-asking `writes` which member the element writes, a
             * recursive walk of the element's definition, once per value.
             */
            const element = codecOfTerm(def.elem)
            return someSet(rng, element, () => draw(element, rng, size, drew))
        }
        case 'list': {
            const one = (element: Term) =>
                draw(codecOfTerm(element), rng, Math.max(0, size - 1), drew)
            const spread = def.spread
            // the declared positions have an arity to hit; the spread has none, so its length is
            // generated the way a list's always was
            // the length is drawn before the bound is read, so a draw at the bound leaves the
            // stream of the others as it was. At the bound the spread is empty, which is how a
            // recursion through a list stops
            const length = spread ? Math.floor(rng() * 3) : 0
            const middle =
                spread === undefined
                    ? []
                    : Array.from(
                          {
                              length:
                                  size <= 0 || holdsNoValue(spread)
                                      ? 0
                                      : length,
                          },
                          () => one(spread),
                      )
            return [...def.pre.map(one), ...middle, ...def.suf.map(one)]
        }
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
            // only an open block puts undeclared names in the entity; a closed body leaves
            // nothing to generate
            const restCodec = rest && codecOfTerm(rest)
            if (restCodec) {
                for (let extra = Math.floor(rng() * 3); extra > 0; extra--) {
                    out[`rest${extra}`] = draw(
                        restCodec,
                        rng,
                        Math.max(0, size - 1),
                        drew,
                    )
                }
            }
            for (const name in fields) {
                const field = fields[name]
                if (field === undefined) continue
                // a term with no value leaves no draw: the field is always sparse
                const sparse = size <= 0 || rng() < 0.5 || holdsNoValue(field.t)
                if (field.mark === 'optional' && sparse) continue
                // the key is always emitted; what varies is whether it holds a value
                if (field.mark === 'undefinable' && sparse) {
                    out[name] = undefined
                    continue
                }
                out[name] = draw(codecOfTerm(field.t), rng, size, drew)
            }
            return out
        }
        case 'union': {
            // an option that holds no value has nothing to draw, as a field of the object row; a
            // union of no inhabited option draws through its options, and the `never` row refuses
            const inhabited = def.options.filter((one) => !holdsNoValue(one))
            return draw(
                codecOfTerm(
                    pickFrom(
                        rng,
                        inhabited.length > 0 ? inhabited : def.options,
                    ),
                ),
                rng,
                size,
                drew,
            )
        }
        case 'refine': {
            const q = def.q
            if (q.arbitrary) return q.arbitrary(rng, size)
            let sample = samplers.get(def)
            if (!sample) {
                sample = bySampling(
                    (r: Rng, sz: number, context: Draws) =>
                        draw(codecOfTerm(def.inner), r, sz, context),
                    q.is as (value: unknown) => value is unknown,
                    q.what,
                    q.onThinSearch,
                )
                samplers.set(def, sample)
            }
            return sample(rng, size, drew)
        }
        case 'legacy':
            return draw(codecOfTerm(def.inner), rng, size, drew)
        case 'ref':
            // a `ref` that closes a cycle goes one level shallower each time, which is what stops a
            // recursive entity generating forever: the optional attribute that recurses is dropped
            // once the budget runs out. Any other `ref` spells its target in place, so it draws as
            // its target draws
            return draw(
                codecOfTerm(usedTargetOf(def)),
                rng,
                closesCycle(def) ? size - 1 : size,
                drew,
            )
        // the one term with no inhabitant, so a property quantified over it has no input. A throw
        // and not a value: the switch's return type admits `undefined`, and falling through would
        // hand `undefined` to a round trip as though it were a value of this codec
        case 'never':
            throw new CodecError(
                '`never` admits no value, so there is nothing to generate',
            )
        // a kind left out would draw `undefined`, as the comment above says. This arm is the build
        // error for it
        default:
            return def satisfies never
    }
}

/**
 * A set, deduplicated by what is *stored*, as the codec does — two values that write the same
 * member are one member of the set, so an arbitrary that did not deduplicate by the stored form
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
 * Values simpler than this one, cheapest reduction first.
 *
 * The counterpart of {@link arbitraryOf}, dispatching on the same {@link Term}.
 */
export const shrinkOf = (
    codec: AnyCodec,
    value: unknown,
): readonly unknown[] => {
    const def = termOf(codec)
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
        // one value, so nothing smaller is admissible; a set of alternatives is a union, and
        // the union row shrinks towards its first option
        case 'literal':
            return []
        case 'number':
            return shrinkDecimal((value as DynamoNumber).toString()).map(
                (digits) => orThrow(DynamoNumber.from(digits)),
            )
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
            // shrunk on the inner side, where the definition knows how, and handed back out.
            // A caller who stated a shrink owns the answer, because a partial pair cannot be
            // shrunk through: the inner side would hand back values the conversion refuses
            if (def.shrink) return def.shrink(value as never)
            if (isOpaqueSugar(def.via)) return shrinkUnknown(value)
            // `f` and `g` are partial maps: a value that `f` refuses has no shrink through the
            // inner codec, and a candidate that `g` refuses is no candidate
            return shrinkThrough(def.f(value as never), (inner) =>
                shrinkOf(codecOfTerm(def.inner), inner),
            ).flatMap((shrunk) => {
                const back = def.g(shrunk as never)
                return failed(back) ? [] : [back]
            })
        case 'set':
            // shrunk as a sequence and handed back as a set, which is what it is
            return shrinkSequence(
                [...(value as ReadonlySet<unknown>)],
                shrinkAt(codecOfTerm(def.elem)),
                1,
            ).map((shrunk) => new Set(shrunk as readonly unknown[]))
        case 'list':
            // with no declared position the length is free, so the sequence shrinks
            if (def.pre.length === 0 && def.suf.length === 0 && def.spread)
                return shrinkSequence(
                    value as readonly unknown[],
                    shrinkAt(codecOfTerm(def.spread)),
                    0,
                )
            // a declared arity cannot reduce, so only the declared positions do. A spread could
            // also shorten, and does not: dropping one changes the length, which the declared part
            // forbids reasoning about here — the elements are where a counterexample actually lives
            return [
                ...def.pre.map((element, i) => [element, i] as const),
                // the suffix aligns from the right, so its positions are counted back from the end
                ...def.suf.map(
                    (element, i) =>
                        [
                            element,
                            (value as readonly unknown[]).length -
                                def.suf.length +
                                i,
                        ] as const,
                ),
            ].flatMap(([element, i]) =>
                shrinkOf(
                    codecOfTerm(element),
                    (value as readonly unknown[])[i],
                ).map((smaller) => {
                    const copy = [...(value as readonly unknown[])]
                    copy[i] = smaller
                    return copy
                }),
            )
        case 'object': {
            const { fields, rest } = def.body
            const held = value as Record<string, unknown>
            const out: Record<string, unknown>[] = []
            // a name the open block holds is optional, so it drops and it shrinks through the block
            const open = Object.keys(held).filter(
                (name) => !Object.hasOwn(fields, name),
            )
            const restCodec = rest && codecOfTerm(rest)
            // dropping a whole attribute is the bigger reduction, so try it first
            if (restCodec) {
                for (const name of open) {
                    const { [name]: _dropped, ...kept } = held
                    out.push(kept)
                }
            }
            for (const name in fields) {
                const mark = fields[name]?.mark
                if (mark !== 'optional' && mark !== 'undefinable') continue
                if (!Object.hasOwn(held, name)) continue
                if (mark === 'undefinable') {
                    if (held[name] === undefined) continue
                    out.push({ ...held, [name]: undefined })
                    continue
                }
                const { [name]: _dropped, ...rest } = held
                out.push(rest)
            }
            for (const name in fields) {
                const field = fields[name]
                if (field === undefined || !Object.hasOwn(held, name)) continue
                for (const smaller of shrinkOf(
                    codecOfTerm(field.t),
                    held[name],
                )) {
                    out.push({ ...held, [name]: smaller })
                }
            }
            if (restCodec) {
                for (const name of open) {
                    for (const smaller of shrinkOf(restCodec, held[name])) {
                        out.push({ ...held, [name]: smaller })
                    }
                }
            }
            return out
        }
        case 'union': {
            // The option to shrink through is the one that admits the value, by the first match that
            // the union's own encode makes. An option behind a `ref`, a `held` or a `refine` admits
            // as an option written directly, which a match on the names of an object did not see
            const only = def.options.find((option) =>
                accepts(codecOfTerm(option), value),
            )
            return only ? shrinkOf(codecOfTerm(only), value) : []
        }
        case 'refine':
            return shrinkOf(codecOfTerm(def.inner), value).filter(holds(def.q))
        case 'legacy':
            return shrinkOf(codecOfTerm(def.inner), value)
        case 'ref':
            return shrinkOf(codecOfTerm(usedTargetOf(def)), value)
        // a term that holds no value has nothing smaller
        case 'never':
            return []
        // a kind left out would never shrink and raise no error. This arm is the build error
        default:
            return def satisfies never
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
    options: Pick<
        CheckOptions<T>,
        'count' | 'seed' | 'size' | 'refine' | 'filter'
    > = {},
): void => {
    const { count, seed, next } = resolved(options)
    for (let i = 0; i < count; i++) {
        const { value: entity, throughRead } = next(
            subject as unknown as AnyCodec,
        )

        // Refusals are part of the comparison, for the reason `checkEquivalent` gives: two
        // marshallers that store the same bytes but disagree about which values they *refuse* are
        // not the same marshaller, and that disagreement is the migration's problem — one of them
        // writes a row where the other raised. So neither side's failure ends the run; both are
        // outcomes to compare.
        const ours = attempt(() => subject.unsafeEncode(entity))
        const theirs = attempt(() => reference.marshall(entity))

        if (ours.refused !== theirs.refused) {
            throw new CodecError(
                `write parity: ${ours.refused ? 'the codec refuses what the reference stores' : 'the codec stores what the reference refuses'}\n  entity  = ${show(entity)}\n  ours    = ${ours.refused ? `refused: ${ours.why}` : show(ours.value)}\n  theirs  = ${theirs.refused ? `refused: ${theirs.why}` : show(theirs.value)}`,
            )
        }
        if (ours.refused) {
            // both refuse a value the codec's own read produced: (C) fails for the codec
            if (throughRead) {
                throw unwritable('the codec', entity, seed, ours.why)
            }
            continue
        }

        const written = firstDifference(ours.value, theirs.value)
        if (written) {
            throw new CodecError(
                `write parity: the codec and the reference store this differently${where(written)}\n  entity  = ${show(entity)}\n  ours    = ${show(written.ours)}\n  theirs  = ${show(written.theirs)}`,
            )
        }

        if (!reference.unmarshall) continue
        const row = theirs.value as AttributeMap
        const oursRead = attempt(() => subject.unsafeDecode(row))
        const theirsRead = attempt(() => reference.unmarshall?.(row))

        if (oursRead.refused !== theirsRead.refused) {
            throw new CodecError(
                `read parity: ${oursRead.refused ? 'the codec refuses a row the reference reads' : 'the codec reads a row the reference refuses'}\n  row     = ${show(row)}\n  ours    = ${oursRead.refused ? `refused: ${oursRead.why}` : show(oursRead.value)}\n  theirs  = ${theirsRead.refused ? `refused: ${theirsRead.why}` : show(theirsRead.value)}`,
            )
        }
        if (oursRead.refused) continue

        const read = firstDifference(oursRead.value, theirsRead.value)
        if (read) {
            throw new CodecError(
                `read parity: the codec and the reference read this row differently${where(read)}\n  row     = ${show(row)}\n  ours    = ${show(read.ours)}\n  theirs  = ${show(read.theirs)}`,
            )
        }
    }
}

/**
 * One side's answer, as a value either way: a reference throws where a codec returns a
 * {@link CodecError}, and the comparison branches on `refused` alone.
 */
const attempt = (
    run: () => unknown,
): {
    readonly refused: boolean
    readonly value?: unknown
    readonly why?: string
} => {
    try {
        const value = run()
        return failed(value)
            ? { refused: true, why: value.message }
            : { refused: false, value }
    } catch (error) {
        return {
            refused: true,
            why: error instanceof Error ? error.message : String(error),
        }
    }
}

const where = (difference: Difference): string =>
    difference.path.length === 0 ? '' : ` at ${asPath(difference.path)}`

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
 * checkEquivalent(held(string, string, { encode: (v) => v, decode: (v) => v }), string)
 *
 * // two adapters compose into one
 * checkEquivalent(
 *     held(held(decimal, string, inner), string, outer),
 *     held(decimal, string, { encode: (v) => inner.encode(outer.encode(v)), decode: ... }),
 * )
 * ```
 */
export const checkEquivalent = <T>(
    a: AttributeCodec<T>,
    b: AttributeCodec<T>,
    options: Pick<CheckOptions<T>, 'count' | 'seed' | 'size' | 'equals'> = {},
): void => {
    const { count, seed, equals, next } = resolved<T>(options)
    for (let i = 0; i < count; i++) {
        const { value, throughRead } = next(a as unknown as AnyCodec)

        const written = a.encode(value)
        const alsoWritten = b.encode(value)
        if (failed(written) !== failed(alsoWritten)) {
            throw new Disagreement(
                `these codecs disagree about whether ${show(value)} can be written, with seed ${seed}: ${
                    failed(written) ? `the first refused it (${written})` : ''
                }${failed(alsoWritten) ? `the second refused it (${alsoWritten})` : ''}`,
            )
        }
        if (failed(written) || failed(alsoWritten)) {
            // both refuse a value the first codec's own read produced: (C) fails for it
            if (throughRead) {
                throw unwritable('the first codec', value, seed, written)
            }
            continue
        }
        if (!equals(written, alsoWritten)) {
            throw new Disagreement(
                `these codecs write ${show(value)} differently, with seed ${seed}: ${show(written)} against ${show(alsoWritten)}`,
            )
        }

        const read = a.decode(written)
        const alsoRead = b.decode(written)
        if (failed(read) !== failed(alsoRead)) {
            throw new Disagreement(
                `these codecs disagree about whether ${show(written)} can be read, with seed ${seed}`,
            )
        }
        if (failed(read) || failed(alsoRead)) continue
        if (!equals(read, alsoRead)) {
            throw new Disagreement(
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
 * The other direction, `decode(encode(t))` for every `t`, is not reachable: without a stated
 * `arbitrary` there is none for the held type except `decode` itself, so every value the harness can
 * make is already in its image.
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
    options: Pick<CheckOptions<T>, 'count' | 'seed' | 'size' | 'equals'> = {},
): void => {
    const { count, seed, equals, next } = resolved<T>(options)
    for (let i = 0; i < count; i++) {
        const { value: held } = next(inner)
        const back = adapt.encode(adapt.decode(held as never))
        if (!equals(back, held)) {
            throw new CodecError(
                `this adapter is not an isomorphism, with seed ${seed}: ${show(held)} came back as ${show(back)}`,
            )
        }
    }
}
