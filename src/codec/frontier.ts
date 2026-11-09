import type { AttributeValue } from './attribute'
import type { AnyCodec, Decoded } from './build'
import { codec } from './build'
import type { Clause } from './clause'
import type {
    DecodeFrame,
    EncodedFrame,
    FirstFrame,
    KindOfFrames,
} from './pathModel'
import type { CodecError } from './result'
import type { Term, TermOf } from './term'
import { resolvedTerm, sameTerm } from './term'

/**
 * The entries of the flat scope of the root of a walk, as {@link flatOf} numbers them. **The map
 * holds every entry, not only the entry on the stack of the walk.** An entry that the walk reads
 * before its cycle closes is a reference in the print as well, and a read of the stack alone gave
 * a member there, which the type and the model refuse.
 */
export type Cycles = ReadonlyMap<Term, number>

/** A frontier with one codec added, where no codec of the frontier has an equal term. */
export const including = (
    frontier: readonly AnyCodec[],
    codec: AnyCodec,
): readonly AnyCodec[] =>
    frontier.some((one) => sameTerm(one.def, codec.def))
        ? frontier
        : [...frontier, codec]

/**
 * **A codec that admits no value at a path**: its term is `never`, the model's frame whose head is
 * `never` (`frameNeverC`). A declared `never` and {@link absent} are one term, so the test reads the
 * term and not the identity of {@link absent}: the frontier keeps the first codec of a term, and an
 * identity test made the verdict depend on the order of the options.
 *
 * **The test reads through each `ref`**, as the head of the model's frame does: a `ref` whose
 * target is `never` admits no value, as a `never` written in its place does.
 */
export const admitsNothing = (codec: AnyCodec): boolean =>
    resolvedTerm(codec.def)?.kind === 'never'

/**
 * The codec at a path whose walk refused. Both halves return the refusal, so
 * no value is written and no attribute is read, and the term is **`never`** for the reason that
 * {@link unresolvedAt} gives. Both halves return the one refusal, because `under` copies an error
 * and never changes the error that it receives.
 */
export const refusedAt = (refusal: CodecError): AnyCodec => {
    const refused = () => refusal
    return codec<never, AttributeValue>({
        def: { kind: 'never' },
        encode: refused,
        decode: refused,
    })
}

/**
 * **The frontier of a path, where the path type knows the codecs**: one record per member, with
 * the spec of the member, its open entry, and its decoded type. `unknown` is a frontier that the
 * type does not know, and `unknown` absorbs every union, so one unknown member makes the frontier
 * unknown. A list, an adapter and a `ref` carry no codec of a child in their types, so the
 * frontier below one is unknown.
 */
export type Member = Spoken & {
    readonly t: unknown
}

/** What an object holds: the declared fields, and the open entry. */
export type Spoken = {
    readonly spec: unknown
    readonly rest: unknown
}

/** The frontier at the root of an item: the one member that its spec declares. */
export type ItemFrontier<T, Spec, Rest> = {
    readonly spec: Spec
    readonly rest: Rest
    readonly t: T
}

/**
 * Every key any member of a union states, not only the shared ones.
 *
 * The reasoning that strips optionality: `priceIn` is a union whose CASH member has a `cardId` and
 * whose STORE_CREDIT member does not, but the path is well formed either way — writing it is how
 * you ask. The shared keys are never the interesting ones. Every key here belongs to some member,
 * so no path this admits is impossible for every variant.
 */
export type UnionKeys<T> = T extends unknown ? keyof T : never

export type ValueAt<T, K extends PropertyKey> = T extends unknown
    ? K extends keyof T
        ? T[K]
        : never
    : never

/** The members of DynamoDB that an attribute type writes: the keys that it requires. */
export type WrittenMembers<A> = A extends unknown
    ? {
          [K in keyof A]-?: undefined extends A[K] ? never : K
      }[keyof A]
    : never

/** The stored text of a literal, or `never` where the decoded type is not a literal. */
export type StoredText<D> = D extends string | number | boolean
    ? string extends D
        ? never
        : number extends D
          ? never
          : boolean extends D
            ? never
            : `${D}`
    : never

/**
 * **The members that a clause does not separate, on the decoded types**: the filter where the path
 * type knows no codec, as in the path of a `tableEntry`. A member goes where, at one key of the
 * clause, the member declares no such key and holds no index signature, or the value at the key
 * shares no value with what the clause's codec decodes.
 */
export type Narrowed<T, C> = T extends unknown
    ? true extends SeparatedAt<T, C>[keyof C]
        ? never
        : T
    : never

/** Whether the clause separates the member at each key of the clause. */
export type SeparatedAt<T, C> = {
    [K in keyof C]: K extends keyof T
        ? [T[K] & Decoded<C[K]>] extends [never]
            ? true
            : false
        : true
}

export declare const pathValue: unique symbol

/**
 * The end of a path, carrying what lives there as a phantom.
 *
 * The phantom is what lets {@link ItemCodec.at} recover the type from a path expression: a selector
 * returns `PathTerminal<Adoption>`, and `Adoption` is inferred straight back out. Optional, so it costs
 * nothing at runtime and nothing to construct.
 */
export type PathTerminal<T> = {
    toString(): string
    readonly [pathValue]?: T
}

/** The decoded type at the first frame of a place that resolves, and `never` elsewhere. */
export type TermPathValue<Fs> = KindOfFrames<Fs> extends 'resolved'
    ? DecodeFrame<FirstFrame<Fs>>
    : never
export type TermPathEncoded<Fs> = KindOfFrames<Fs> extends 'resolved'
    ? EncodedFrame<FirstFrame<Fs>>
    : never
export type ElementOf<T> = T extends readonly unknown[] ? T[number] : never
/** The decoded type of the codecs at the frames of a node. */
export type DecodeFrames<Fs> = Fs extends unknown[]
    ? { [I in keyof Fs]: DecodeFrame<Fs[I]> }[number]
    : never
export type ClauseTerms<C> = { [K in keyof C]: TermOf<C[K]> }

/**
 * **A segment of a document path**: a name, or a position of a list. The model's `Seg`: a string is
 * `.name`, and a number is `.pos`. A path is a tuple of segments, so a name in digits stays a name.
 */
export type Segment = string | number

/*
 * **Where the walk of a path stands, at the type level.** `['term', Fs, T, F, Root]` holds the
 * frames of `Term.at`, the decoded type, the frontier, and whether the walk stands at the root of an
 * item. `['path', T, F]` stands where the type knows no frame: below a key or an index that is no
 * literal, and below a codec whose type carries no term. There the decoded type and the frontier
 * type the path, as {@link PathOf} does. A located codec carries the place in its type, so `at` and
 * `narrow` continue from the place.
 */
export type Refused = 'refused'

/**
 * **The place of a path that the type does not know**: a path that is no tuple, or no string
 * literal, as a loop computes it. The type checks no segment there, and the located codec is the
 * erasure {@link AnyCodec}: `never` in, `unknown` out. A walk past such a place stays unknown.
 */
export type Wide = 'wide'

/**
 * **A document path in DynamoDB syntax, as its segments**: `'legs[1].at'` is `['legs', 1, 'at']`.
 * A name holds no `.`, `[` or `]`, and the tuple form carries such a name. A part that is no name
 * and no position is a segment that no place offers.
 */
export type ParsePath<S extends string> = S extends '' ? [] : PathParts<S>
export type PathParts<S extends string> =
    S extends `${infer Head}.${infer Tail}`
        ? [...PathPart<Head>, ...PathParts<Tail>]
        : PathPart<S>
export type PathPart<S extends string> =
    S extends `${infer Name}[${infer I}]${infer Rest}`
        ? [
              ...(Name extends '' ? [] : PathName<Name>),
              I extends `${infer N extends number}` ? N : ['no segment'],
              ...(Rest extends '' ? [] : PathPart<Rest>),
          ]
        : PathName<S>
export type PathName<S extends string> =
    S extends `${string}${'[' | ']'}${string}` ? [['no segment']] : [S]

/** The segments of a path in either form. */
export type SegmentsOf<S> = S extends string
    ? string extends S
        ? Segment[]
        : ParsePath<S>
    : S
/** The text up to the last `.`, and the part after it. */
export type LastPart<
    S extends string,
    P extends string = '',
> = S extends `${infer Head}.${infer Tail}`
    ? LastPart<Tail, `${P}${Head}.`>
    : [P, S]
/** A name that the string form can write: no `.`, `[` or `]`. */
export type PlainName<N> = N extends string
    ? string extends N
        ? never
        : N extends `${string}${'.' | '[' | ']'}${string}`
          ? never
          : N
    : never
export type Reached = {
    readonly frontier: readonly AnyCodec[]
    readonly cycles: Cycles
}

/** A segment addressing a list position, as opposed to an attribute named in digits. */
export const asIndex = /^\d+$/

/**
 * **A step of a path**: a segment, or a clause. A clause adds no segment, and narrows the frontier
 * that the walk of `at` carries.
 */
export type Step = string | number | Clause

/** The segments of a path, without its clauses. */
export const segmentsIn = (
    steps: readonly Step[],
): readonly (string | number)[] =>
    steps.flatMap((step) => (typeof step === 'object' ? [] : [step]))

/** Nothing, shared: every `get` is trapped, so the target is only an identity to hang one on. */
export const nothing = {}
