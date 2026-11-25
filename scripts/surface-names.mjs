// The export names of a declaration file, one per line, sorted.
//
//   node scripts/surface-names.mjs dist/Rotorise.d.ts
//
// The program of the TypeScript compiler lists the exports of the module. A declaration that the
// bundler exports in place (`export declare const x`) and an `export { a as b }` clause give the
// same answer, so the reader does not depend on the layout that the bundler writes.
import { resolve } from 'node:path'
import ts from 'typescript'

const file = resolve(process.argv[2])
const program = ts.createProgram([file], {
    noEmit: true, skipLibCheck: true, types: [],
    module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler,
})
const checker = program.getTypeChecker()
const source = program.getSourceFile(file)
const symbol = source && checker.getSymbolAtLocation(source)
if (symbol === undefined) { console.error(`surface-names.mjs: ${file} is not a module`); process.exit(2) }
for (const name of checker.getExportsOfModule(symbol).map((s) => s.name).sort()) console.log(name)
