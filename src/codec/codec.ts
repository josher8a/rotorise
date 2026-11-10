export type { Reader } from './adapters'
export { held, legacy } from './adapters'
/**
 * The types that the entries publish and that a lower file owns now. A lower file owns a type
 * where its readers need the type, and this file names the type again for the entries.
 */
export type {
    AnyCodec,
    AnySpread,
    AttributeCodec,
    AttributeOf,
    Attributes,
    Decoded,
    Encoded,
    EncodedPatch,
    EncodedVariants,
    Marks,
    Nestable,
    ObjectOf,
    ObjectSlot,
    SetOf,
    Writes,
} from './build'
/**
 * Forwarded for the consumers that still name them here.
 *
 * They are `denote.ts`'s now — each answers about a term's *pair* — and this keeps the move to one
 * pass. Six of the eight go in the pass that deletes the readers; `codecOfTerm` and `termOf` stay,
 * and their callers move to the module that owns them there.
 */
export { codecOfTerm, termOf, valueKinds } from './denote'
export type {
    AnyObjectCodec,
    DerivedUnion,
    DerivedVariants,
    IsUnion,
    ObjectEntry,
    SpecsOf,
    VariantOf,
} from './derivedItem'
export type { PathTerminal, Segment } from './frontier'
export { meet } from './meet'
export { object, optional, undefinable } from './objects'
export { opaque } from './opaque'
export type {
    BinaryCodec,
    BooleanCodec,
    ConstantOf,
    Refined,
    SetBase,
    StringCodec,
} from './prisms'
export {
    binary,
    boolean,
    decimal,
    fill,
    never,
    nullValue,
    number,
    refine,
    string,
} from './prisms'
export type {
    ListOf,
    ListWrites,
    SetCapable,
    SpreadCodec,
    SpreadOnce,
} from './products'
export { array, list, spread } from './products'
// the failure algebra lives in `./result`, and is re-exported because it is part of the surface a
// caller works in: a `Result` is what every direction returns
export {
    andThen,
    CodecError,
    every,
    everyEntry,
    failed,
    orThrow,
    type Result,
} from './result'
export type {
    AllObjects,
    ItemCodec,
    ItemSpec,
    ObjectCodec,
    OptionalCodec,
    UndefinableCodec,
    UnionCodec,
    Untagged,
    UntaggedSpec,
    WrittenBy,
} from './scope'
export { ref, scope } from './scope'
export type { Precondition } from './scoped'
export type { LocatedCodec, PathOf } from './scopePath'
export { at, narrow, path, pathBuilder, preconditions } from './scopePath'
export { exclude, extract } from './scopeSlice'
export type {
    DiscriminatedCodec,
    Dissected,
    DissectedCodec,
    Dissection,
    Tagged,
    TaggedCodec,
} from './sums'
export { discriminatedUnion, item, mdunion, nullable, union } from './sums'
export type {
    LiteralBase,
    LiteralValue,
    Refinement,
    Rng,
} from './term'
export type { SetSlot, Shape } from './value'

/**
 * How a union of objects is declared: with a tag, or by the attributes each variant has.
 *
 * One parameter and one signature. Overloads would read the same at the call and cost the
 * diagnostic — `No overload matches this call` at the call site instead of a message on the
 * argument, which is what two signatures on `tableEntry` were measured to do. A union in one
 * inference slot would cost worse: a string and an array sharing a slot is how `tableEntry` came to
 * infer a codec from a separator.
 */
