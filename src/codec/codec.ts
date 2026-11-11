export type { MissingCodec, Reader } from './adapters'
export { held, legacy } from './adapters'
/**
 * The types that the entries publish. A lower file declares a type where its readers need the
 * type, and this file names the type again for the entries.
 */
export type {
    AnyCodec,
    AnySpread,
    AttributeCodec,
    AttributeOf,
    Attributes,
    Closed,
    Decoded,
    Encoded,
    EncodedPatch,
    EncodedVariants,
    Free,
    Marks,
    Nestable,
    ObjectOf,
    ObjectSlot,
    SetOf,
    Writes,
} from './build'
/**
 * The values that read a term. `capabilities.ts` declares `codecOfTerm`, and `denote.ts` declares
 * `termOf` and `valueKinds`.
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
export type { DecodeObject } from './pathModel'
export type {
    BinaryCodec,
    BooleanCodec,
    ConstantOf,
    DecimalCodec,
    EveryButNumberT,
    FloatT,
    NumberCodec,
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
    ArrayOver,
    ListCodec,
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
    EntryOptionSpecs,
    EntrySpec,
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
    BaseT,
    ElementMark,
    HeldT,
    LiteralBase,
    LiteralValue,
    LitT,
    ObjectTermOf,
    OptionsMark,
    Refinement,
    Rng,
    ScopeTerms,
    TermMark,
} from './term'
export type { SetSlot, Shape } from './value'
