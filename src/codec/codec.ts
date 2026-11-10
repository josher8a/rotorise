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
 * Forwarded for the consumers that still name them here. `codecOfTerm` is `capabilities.ts`'s, and
 * `termOf` and `valueKinds` are `denote.ts`'s: each answers about a term, and their callers move to
 * the module that owns them.
 */
export { codecOfTerm } from './capabilities'
export { termOf, valueKinds } from './denote'
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
