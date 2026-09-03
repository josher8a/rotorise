# Changelog

## Unreleased

### Added

- **`TermDef`, `FieldDef`, `RestDef`** — §4's three levels, named. `CodecDef['kind']` is a flat union
  of twenty-four names while the calculus puts a **codec**, a **field** (`optional`, `fallback`) and
  a **rest policy** (`restOf`) at three different levels. The separation was already enforced, by
  branded markers and guards at each site that could go wrong, but the level a kind belongs to was
  written down nowhere — so the flat list read as three constructors that were missing something.
  They are not missing anything; they are not codecs.

  A type-level assertion now fails the build if a kind is added that no stratum claims.

- **`nullValue`** — the `NULL` point: the one value `null`, stored as `{ NULL: true }`. A schema
  could say "this attribute is a string" or "this attribute is optional", and could not say "this
  attribute is exactly `NULL`" — a tombstone, or a payload-free option of a union. The gap was found
  in the formalization by asking whether `nullable(c)` could be written as `union(c, nullValue)`; it
  could not, because the right-hand side was not expressible.

  Distinct from `nullable`, which *adds* `null` to another codec's held set. `nullValue` holds
  nothing else. Named for what it holds because `null` is a keyword and `NULL` is already the
  attribute type.

### Changed

- **`decimal` accepts only the form DynamoDB stores.** It normalises every `N` it takes — `'1.50'`
  is stored and returned as `'1.5'`, `'007'` as `'7'`, `'1e5'` as `'100000'`, `'-0'` as `'0'` — and
  `decimal.decode` is the identity on the digits, so a denormalised numeral was written as one
  string and read back as another. A round trip broken *across storage*, where neither the types nor
  an in-memory law suite can see it. `encode` now rejects it rather than rewriting it, and `decode`
  rejects it too, since checking only the write is the one configuration that breaks the codec's
  own laws.

  **`'10.50'` is not a price this library will write; `'1.5'` is the same money.** If you format
  money for display, do it at the edge — the store does not keep the trailing zero either way. Where
  trailing zeros carry meaning, use `string`.

- **`number` refuses what DynamoDB refuses.** `NaN` and `Infinity` encoded to `{ N: 'NaN' }` and
  `{ N: 'Infinity' }`, which the service rejects on arrival; `Number('abc')` decoded to `NaN` with
  no error at all. Both halves now gate on §1's numeral bounds — at most 38 significant digits,
  magnitude `1e-130` to `9.9…e125` — and `decode` checks the value it read back rather than only the
  stored digits, because `'9.9999999999999999999999999999999999999E+125'` rounds *up* past the
  maximum.

- **`set` and `opaque` refuse an empty set on read**, as their `encode` always has.

### Removed

- **`CodecDef`'s `branch` kind.** A definition language for codecs had an entry that was not a
  codec: `branch` was manufactured while walking a path, its `encode` and `decode` both threw, and
  it existed only to carry "several variants declare this segment differently" along the walk. Every
  reader of a definition — `writes`, `carries`, `deeper`, a generator, a conformance check — had to
  carry a case for it.

  Nothing about paths changes. `at` still resolves a segment the variants agree on, still walks
  *through* a disagreement to somewhere they agree, and still defers the complaint to encode time so
  `path()` keeps working on an ambiguous path. What changed is that the unresolved terminal now
  carries **no definition** rather than a fictional one, so `def` and `writes` answer `undefined` —
  which is the truth. Only code exhaustively switching on `CodecDef['kind']` is affected.

- **`numeric()`** — removed, with no deprecation period, because it was unsound rather than
  merely redundant. It decoded with `Number(ok) as T`: a type assertion, no check, so a stored
  `7` came back typed as `0 | 1`. The calculus's `(numeric)` rule is gone with it, and the
  formalization proved before removing that `numeric(q)` and `refine(number, q)` denote the same
  codec on all four fields (`numericCodec_eq_restrict`), so nothing expressible is lost.

  Migrating:
  - `numeric<0 | 1 | 2>()` → `literal(0, 1, 2)` — an enum indexed by number, stored as `N`,
    with the admissible set checked in **both** directions. This is what `numeric()` claimed.
  - `numeric<number>()` → `number`. The type parameter was doing nothing.
  - an arbitrary subset → `refine(number, is)`, which checks it.
  - a narrowing that is genuinely the caller's to guarantee → `held`, where the caller's own
    functions belong.

- **The six definition readers leave the published surface** — `admits`, `carries`, `writes`,
  `decides`, `setBase` and `deeper`. **Breaking.** They are how this library's own union resolver
  and declaration guards ask what a term is; a caller has the codec's behaviour, which is what
  they are derived from. `admits` reached the surface in `46cb950` and the other five before it,
  all because the re-export was `export * from './codec'` — the export was never a decision
  anyone took. `src/Rotorise.ts` enumerates the twenty-four codec values now and stars only the
  types, so adding one is a line in a list, and `Rotorise.spec.ts` pins both halves: what is API
  and what is deliberately not.

## 0.3.6 — 2026-07-31

### Fixed

- **`sideEffects: false` declared in `package.json`** — the package was missing the metadata bundlers need to prove the module is side-effect free, so webpack/Rollup retained it even when no export was used. Consumers importing only `RotoriseError` (or nothing at all) can now drop the module entirely.

## 0.3.5 — 2026-03-07

### Fixed

- **3-tuple defaults accept narrowed transform parameter types** — `[key, transform, default]` specs for optional properties now accept defaults matching the transform's parameter type (e.g. `Pick<Inner, 'id'>`) instead of requiring the full entity property type. Invalid defaults like `{}` are rejected at compile time.

## 0.3.4 — 2026-03-06

### Fixed

- **`Exact<>` distributive over union Shape keys** — `Exact` now distributes correctly when the Shape type is a union, fixing type errors with discriminated union schemas (#4).

## 0.3.3 — 2026-03-06

### Fixed

- **CI pipeline fixes** — resolve CI configuration issues in the publish workflow.

## 0.3.2 — 2026-03-06

### Added

- **CI/CD pipeline** — GitHub Actions workflow for check, test, build, and tag-based npm publish (#3).

## 0.3.0 — 2026-03-06

### Breaking Changes

- **`Exact` type simplified** — `Exact<Shape, Candidate>` now only checks excess properties at the top level. Deep recursive checking of nested objects/arrays has been removed. DynamoDB key schemas are flat, so this should not affect typical usage.
- **`.key()` narrows attributes to transform parameter types** — when a spec item has a transform function, `.key()` now accepts the transform's parameter type (e.g. `Pick<Obj, 'id'>`) instead of the full entity. Callers passing full entities still work.
- **Schema keys are `readonly`** — `TableEntry` computed key fields are now `readonly`. Code that mutates computed keys on entries will get type errors.
- **Invalid schemas return `ErrorMessage<>` instead of `never`** — code checking `extends never` on schema output types may behave differently.

### Added

- **`RotoriseError`** — custom error class for all runtime errors thrown by Rotorise, enabling `catch` filtering.
- **`ErrorMessage<T>` type** — branded type for compile-time error messages in the IDE.
- **`TransformOverride`** — type-level support for narrowing `.key()` attributes based on transform parameter types.
- **Empty separator guard** — `tableEntry()({...}, '')` is now a type error via `ErrorMessage`, in addition to the existing runtime check.
- **Performance attest baselines** — new `Rotorise.attest.test.ts` with instantiation count benchmarks.
- **`files: ["dist"]`** in `package.json` — prevents source/test files from being published to npm.
- **`treeshake: true`** in tsup config — enables tree-shaking for consumers.
- **JSDoc** on `TableEntry`, `TableEntryDefinition`, and `tableEntry`.

## 0.2.5 — 2026-01-18

### Added

- **`enforceBoundary` config option** — `.key()` accepts `enforceBoundary: true` to return `undefined` when not all key segments are present, preventing partial composite keys from being written.

### Fixed

- **Skip transform on partial when attribute is missing** — when `allowPartial` is set and an attribute is `undefined`, the transform is no longer called with `undefined`.

### Changed

- Performance optimizations to `ExtractHelper` and `CompositeKeyBuilderImpl`.

## 0.2.1 — 2025-06-19

### Added

- **`TransformShape` allows optional `tag`** — the `tag` field in `TransformShape` is now optional, defaulting to the uppercased key name.

## 0.2.0 — 2025-06-18

### Added

- **`TransformShape` support** — `CompositeKeyParams` and `TableEntry` types now support `TransformShape` for rich key composition with tagged segments.

## 0.1.14 — 2025-02-28

### Added

- **Heterogeneous keys schema** — different key specs per discriminated union variant, with associated performance improvements.

### Fixed

- **`ProcessKey` type handling** — improved inference for key processing across schema variants.

## 0.1.12 — 2025-02-11

### Added

- **`NonEmptyArray<T>` utility type** — enforces at least one element in key spec arrays.
- **`Replace<T, U, V>` utility type**.

### Changed

- **`UnionToObject` inference** — switched from `infer U` to direct indexed access for more accurate union member extraction.
- **`InputSpec` excludes optional/nullable properties** as plain (non-tuple) key specs — only required, non-nullable properties can be used without a transform.

### Fixed

- **Null attribute handling in key generation** — return `undefined` instead of throwing when an attribute is `null`.
- **Transform applied even when value is missing** — `transform` is now called regardless of whether the attribute value is present, allowing transforms to handle missing values.

## 0.1.11 — 2025-01-08

### Fixed

- **`TableEntryDefinition` type parameter handling** — improved type safety for definition type parameters.

## 0.1.10 — 2024-12-31

### Added

- **Vitest and `attest` integration** — type-level testing with instantiation count tracking.
- **Utility types** for advanced TypeScript type manipulation.

### Fixed

- **Depth without `allowPartial`** — fixed issue where specifying `depth` without `allowPartial` produced incorrect results.

### Changed

- **Replace `KVPair` and `Unionize` with `UnionToObject`** — simplified internal type handling.

## 0.1.9 — 2024-10-23

### Changed

- **Key and attribute inference performance** — reduced instantiation counts for key and attribute type resolution.

## 0.1.8 — 2024-10-23

### Changed

- **`CompositeKeyParams` performance** — remove unnecessary type unions to reduce instantiation cost.

## 0.1.7 — 2024-10-23

### Fixed

- **`CompositeKeyParams` handles optional properties as `Partial`** — non-required properties are now treated as partial rather than `undefined`.

## 0.1.6 — 2024-10-15

### Fixed

- **Discriminated union null case** — fix type error when a discriminated union variant has a `null` value.

## 0.1.5 — 2024-10-15

### Added

- **Discriminated schema support** — `tableEntry` now handles discriminated union entity types.

## 0.1.4 — 2024-10-14

### Added

- **`bigint` as raw numeric key** — `bigint` values can now be used directly in key specs.

### Changed

- **Inlined type utilities** — removed `type-fest` dependency; added custom `Exact`, `SliceFromStart`, `DistributivePick`, `DistributiveOmit`, `evaluate`, and `ValueOf` types.

## 0.1.2 — 2024-06-09

### Changed

- **Build tooling** — added `tsup` config and updated package distribution settings.

## 0.1.1 — 2024-06-06

### Fixed

- **`CompositeKeyBuilder` handles literal configs** — fix type inference when config objects use `as const` literal types.

## 0.1.0 — 2024-05-31

### Added

- **Initial release** — `tableEntry()` factory, `TableEntry` and `TableEntryDefinition` types, composite key builder with configurable separator and depth.
