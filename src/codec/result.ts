/**
 * Failure, as a value.
 *
 * Its own module because it is not a codec concept: it is the algebra every codec's two directions
 * are written in, and keeping it here is what lets the one construction site live outside `codec.ts`
 * — which is what keeps that site out of the package's public surface. See {@link build}.
 */

/**
 * Encoding for DynamoDB is not a bijection, and no library can make it one.
 *
 * Decode is not a function of the stored value alone — `{ SS }` and `{ L }` both hold strings, `N`
 * is a 38-digit decimal no JS number holds — so a marshaller without a schema is guessing.
 *
 * `decode ∘ encode = id` on entities is the law worth having. The reverse is never true: DynamoDB
 * normalises `N`, reorders sets, and old rows carry attributes no schema mentions. Declaring both
 * directions together is what makes the law testable — see {@link roundTrip}.
 */
export class CodecError extends Error {
    override readonly name = 'CodecError'

    /**
     * Where in the item it went wrong, outermost segment first.
     *
     * Empty at the point of failure and filled in as the error unwinds — each composite knows only
     * its own segment, which is exactly the one the level below cannot know. A row is data somebody
     * else wrote, and "expected 'S', found 'N'" on a thirty-attribute entity says nothing about
     * which attribute to go and look at.
     */
    path: readonly (string | number)[] = []

    /** The failure itself, without the path that was discovered on the way out. */
    readonly reason: string

    constructor(reason: string) {
        super(reason)
        this.reason = reason
    }

    /** The same failure, one level further in. */
    under(segment: string | number): this {
        this.path = [segment, ...this.path]
        this.message = `at ${asPath(this.path)}: ${this.reason}`
        return this
    }
}

/**
 * `lines[1].tender.note` — an index is bracketed, an attribute is dotted.
 *
 * One function for both directions this package writes a path in: the document path a
 * {@link LocatedCodec} hands to an expression, and the place a {@link CodecError} says it failed.
 * They were two implementations of the same six lines, which is two chances for a path pasted into
 * a query to disagree with the path an error named.
 */
export const asPath = (segments: readonly (string | number)[]): string => {
    let out = ''
    for (const segment of segments) {
        out +=
            typeof segment === 'number'
                ? `[${segment}]`
                : out === ''
                  ? segment
                  : `.${segment}`
    }
    return out
}

/**
 * A value, or the reason there is none.
 *
 * A bare union rather than a wrapper, so there is nothing to unwrap and nothing to allocate:
 * {@link CodecError} extends `Error`, and an entity never is one. The same shape `flow`'s
 * `Result<T, E>` has, so `isError(...)` narrows it without an adapter.
 */
export type Result<T> = T | CodecError

/** Whether a step failed. The whole of what a {@link Result} needs to be read. */
export const failed = (value: unknown): value is CodecError =>
    value instanceof CodecError

/**
 * The next step, if the last one succeeded.
 *
 * Named `andThen` and not `then`: a module that exports `then` has a namespace object JavaScript
 * treats as a *thenable*, so `await import(...)` calls it with `(resolve, reject)` and the module
 * never loads. Every spec in this package failed at once when it was called `then`.
 *
 * Codecs compose by threading results rather than by throwing, so a failure is an ordinary value
 * travelling back out. Nothing is caught anywhere below {@link orThrow}, which means there is no
 * hidden control flow to reason about: every place a failure can appear is a place it is named.
 */
export const andThen = <A, B>(
    value: Result<A>,
    next: (ok: A) => Result<B>,
): Result<B> => (failed(value) ? value : next(value))

/**
 * Every step, or the first failure.
 *
 * Short-circuits, and labels the failure with its index — which is what makes a bad element in a
 * list say *which* element without any of the steps knowing they are in one.
 */
export const every = <A, B>(
    items: readonly A[],
    step: (item: A, index: number) => Result<B>,
): Result<B[]> => {
    const out: B[] = []
    for (let index = 0; index < items.length; index++) {
        const next = step(items[index] as A, index)
        // the failure is labelled where it is already known to be one. A `within(segment, value)`
        // helper reads well and asks `failed` twice per value — once inside itself and once here —
        // which is twice per element of every list in every item
        if (failed(next)) return next.under(index)
        out.push(next)
    }
    return out
}

/**
 * Every entry, or the first failure, labelled with its key.
 *
 * Walks the object rather than `Object.entries` of it. Every map, record and item goes through here
 * in both directions, and the pair array is built only to be walked once and dropped.
 */
export const everyEntry = <A, B>(
    held: Record<string, A>,
    step: (value: A, key: string) => Result<B>,
): Result<Record<string, B>> => {
    const out: Record<string, B> = {}
    for (const key in held) {
        const next = step(held[key] as A, key)
        if (failed(next)) return next.under(key)
        out[key] = next
    }
    return out
}

/**
 * The value, or the failure thrown.
 *
 * The one place a {@link CodecError} becomes an exception, which is what every `unsafe` method is.
 */
export const orThrow = <T>(value: Result<T>): T => {
    if (failed(value)) throw value
    return value
}
