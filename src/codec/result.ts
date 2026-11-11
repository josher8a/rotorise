/**
 * Failure, as a value.
 *
 * Its own module because it is not a codec concept: it is the algebra every codec's two directions
 * are written in, and keeping it here is what lets the one construction site live outside the constructor
 * files — which is what keeps that site out of the package's public surface. See {@link build}.
 */

type CodecErrorKind = 'refused' | 'vacant' | 'someVariants' | 'ambiguous'

/**
 * The stack of a copy. Where the stack of the original starts with the header of the original, the
 * copy puts its own header in place of that prefix. Where the stack has another form, the copy puts
 * its header above the whole stack. The function reads no frame format.
 */
const headed = (
    stack: string | undefined,
    original: Error,
    copy: Error,
): string | undefined => {
    if (stack === undefined) return undefined
    const header = `${original.name}: ${original.message}`
    const head = `${copy.name}: ${copy.message}`
    return stack.startsWith(header)
        ? head + stack.slice(header.length)
        : `${head}\n${stack}`
}

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
     * What kind of refusal this is, for a reader that has to tell one refusal from another. `refused`
     * is any refusal that no reader tells apart. The other three are the decisions of `at` that
     * are no codec: no codec stands at the path, some variants declare it only, or the variants
     * declare it differently.
     */
    readonly kind: CodecErrorKind

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

    constructor(
        reason: string,
        kind: CodecErrorKind = 'refused',
        options?: ErrorOptions,
    ) {
        super(reason, options)
        this.reason = reason
        this.kind = kind
    }

    /**
     * The same failure, one level further in, as a copy.
     *
     * A caller owns a refusal that an adapter returns, and one refusal reaches many reads, so the
     * path goes on a copy and the error that the caller returned never changes. The copy calls no
     * constructor, because a constructor captures a new stack at each level of a refusal. The copy
     * reads the stack of the original on demand, because a read of `stack` formats the stack, and
     * a refusal that unwinds through many levels would format it at each level. The header of the
     * stack is the name and the message of the copy, so a printed stack names the path.
     */
    under(segment: string | number): this {
        return copied(this, [segment, ...this.path])
    }
}

/**
 * The copy that {@link CodecError.under} makes: the refusal at a path, with a reason. The one rule
 * of a path on a copy, so each copy gives the message `at <path>: <reason>`, or the reason alone
 * at the empty path.
 */
const copied = <E extends CodecError>(
    from: E,
    path: readonly (string | number)[],
    reason: string = from.reason,
): E => {
    const copy: E = Object.create(Object.getPrototypeOf(from))
    Object.defineProperty(copy, 'stack', {
        get: () => headed(from.stack, from, copy),
        configurable: true,
    })
    // the own fields of a subclass, such as the term of a refused recursion, stay on the copy
    Object.assign(copy, from, {
        message: path.length === 0 ? reason : `at ${asPath(path)}: ${reason}`,
        path,
        reason,
    })
    // `cause` is an own field that no enumeration lists, so the copy defines it
    if (Object.hasOwn(from, 'cause'))
        Object.defineProperty(copy, 'cause', {
            value: from.cause,
            writable: true,
            configurable: true,
        })
    return copy
}

/**
 * The refusal of a union at the path of the refusal of its option. The reason is the sentence of
 * the union. The kind, the subclass and the cause are the option's, and the path rule is `under`.
 */
export const restated = <E extends CodecError>(option: E, reason: string): E =>
    [...option.path]
        .reverse()
        .reduce<E>(
            (error, segment) => error.under(segment),
            copied(option, [], reason),
        )

/**
 * The refusal of the held side of a `held`: the value is outside the type that the caller named, and
 * the adapter never ran. The copy of a refusal keeps the subclass, so a union that reads the write
 * of a tag tells this structure ("the member does not admit the value") from the refusal of an adapter.
 */
export class HeldSideRefusal extends CodecError {}

/**
 * Two codecs that a property check found to differ. The failure is of the check and no codec
 * refused a value, so the failure is a class of its own and not a kind of {@link CodecError}.
 */
export class Disagreement extends CodecError {}

/**
 * `lines[1].tender.note` — an index is bracketed, an attribute is dotted.
 *
 * The place that a {@link CodecError} says it failed, for a person. The text addresses nothing: a
 * name that holds a `.` prints as two segments. No caller hands the text to an expression.
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
 * Sets an own data property of a record that a decode or an encode builds.
 *
 * `JSON.parse` and `Object.fromEntries` hold `__proto__` as an own data property, and a plain
 * assignment of that name runs the setter of `Object.prototype`, which drops a primitive and takes
 * an object as the prototype. Each other name takes the plain assignment.
 */
export const setOwn = <T>(
    record: Record<string, T>,
    name: string,
    value: T,
): void => {
    if (name === '__proto__') {
        Object.defineProperty(record, name, {
            value,
            writable: true,
            enumerable: true,
            configurable: true,
        })
    } else {
        record[name] = value
    }
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
        setOwn(out, key, next)
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
