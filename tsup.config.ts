import { defineConfig } from 'tsup'

export default defineConfig({
    // one entry per thing a consumer opts into: the library, the property-testing harness, and the
    // SDK marshaller port — neither of the last two belongs in the bundle of somebody who wants
    // neither, and both are reached by a subpath rather than by tree-shaking hopefully working
    // named, because esbuild names an output by its path under the common root, and two of the
    // three entries sit in `src/codec/` while `dist/testing.js` and `dist/native.js` are published
    entry: {
        Rotorise: './src/Rotorise.ts',
        testing: './src/codec/testing.ts',
        native: './src/codec/native.ts',
    },
    splitting: false,
    sourcemap: true,
    outDir: 'dist',
    clean: true,
    format: ['cjs', 'esm'],
    // `composite` is on in tsconfig.json for monorepo project references, but the dts worker builds
    // a program from the entry alone, and composite requires every file to be listed. Rotorise.ts
    // now imports sibling modules, so the declaration build needs it off.
    dts: { compilerOptions: { composite: false, declarationMap: false } },
    treeshake: true,
})