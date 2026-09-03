# Changelog

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
