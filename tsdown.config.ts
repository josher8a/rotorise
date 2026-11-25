import { defineConfig } from 'tsdown'

export default defineConfig({
    // one entry per thing a consumer opts into: the library, the property-testing harness, and the
    // SDK marshaller port. Neither of the last two belongs in the bundle of somebody who wants
    // neither, and both are reached by a subpath rather than by tree-shaking hopefully working
    entry: {
        Rotorise: './src/index.ts',
        testing: './src/codec/testing.ts',
        native: './src/codec/native.ts',
    },
    // each entry that bundles its own copy of a class gives a second class identity, and
    // `instanceof` across the entries then fails: a refusal of `rotorise/native` is not a
    // `CodecError` of `rotorise`, and `rotorise/testing` makes a `DynamoNumber` that `opaque` of
    // `rotorise` refuses.
    // A module that two entries import goes to a shared chunk, so one copy exists.
    // `scripts/tsc-matrix.sh` runs the entries and checks it
    format: ['esm', 'cjs'],
    outDir: 'dist',
    clean: true,
    sourcemap: false,
    // the `exports` map of package.json names `.js` and `.cjs`, `.d.ts` and `.d.cts`. By default
    // tsdown names an ES module `.mjs` and its declaration `.d.mts`
    fixedExtension: false,
    // `composite` is on in tsconfig.json for monorepo project references, but the declaration build
    // reads the program of the entries, and composite requires every file to be listed. `Rotorise.ts`
    // imports sibling modules, so the declaration build needs it off.
    // `ignoreDeprecations`: the declaration build sets `baseUrl`, and TypeScript 6 refuses `baseUrl`
    // unless the flag is set
    dts: {
        compilerOptions: {
            composite: false,
            declarationMap: false,
            ignoreDeprecations: '6.0',
        },
    },
    treeshake: true,
})
