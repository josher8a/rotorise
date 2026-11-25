// Refuses an `infer X` whose name is also a type in scope.
//
//   node scripts/infer-shadow.mjs [tsconfig.json]
//
// The declaration bundler of `tsdown` renames a type that the module declares and an import that
// collides, and it renames the use of an `infer` variable but not the binding. A name that means
// the type and the variable then leaves `Refused$1` in the use and `Refused` in the binding, and
// the consumer fails with TS2314. The guard refuses the name in the source. The compiler resolves
// the scope, so a type of the module, an import, and an enclosing `infer` are each found.
// Exit 1 on each shadow.
import { dirname, relative, resolve } from 'node:path'
import ts from 'typescript'

const configPath = resolve(process.argv[2] ?? 'tsconfig.json')
const read = ts.readConfigFile(configPath, ts.sys.readFile)
const config = ts.parseJsonConfigFileContent(read.config, ts.sys, dirname(configPath))
const program = ts.createProgram(config.fileNames, { ...config.options, noEmit: true })
const checker = program.getTypeChecker()
const root = dirname(configPath)

const shadows = []
const visit = (source) => (node) => {
    if (ts.isConditionalTypeNode(node)) {
        // a type that a module declares or imports. A type parameter is local, so the bundler
        // never renames it. An import is a type when the name that it aliases is a type.
        const isType = (s) =>
            (s.flags & ts.SymbolFlags.TypeParameter) === 0 &&
            ((s.flags & ts.SymbolFlags.Alias ? checker.getAliasedSymbol(s) : s).flags & ts.SymbolFlags.Type) !== 0
        const inScope = new Set(
            checker.getSymbolsInScope(node.parent, ts.SymbolFlags.Type | ts.SymbolFlags.Alias).filter(isType).map((s) => s.name),
        )
        const walk = (n) => {
            if (ts.isInferTypeNode(n) && inScope.has(n.typeParameter.name.text)) {
                const { line } = source.getLineAndCharacterOfPosition(n.getStart(source))
                shadows.push(`${relative(root, source.fileName)}:${line + 1}: infer ${n.typeParameter.name.text}`)
            }
            // an `infer` of a nested conditional belongs to that conditional
            if (!ts.isConditionalTypeNode(n)) ts.forEachChild(n, walk)
        }
        walk(node.extendsType)
    }
    ts.forEachChild(node, visit(source))
}
for (const source of program.getSourceFiles()) {
    if (source.isDeclarationFile || source.fileName.includes('node_modules')) continue
    if (!source.fileName.startsWith(root)) continue
    visit(source)(source)
}
if (shadows.length === 0) { console.log('infer-shadow: no infer variable shadows a type'); process.exit(0) }
for (const s of shadows) console.log(`FAIL  ${s}`)
console.log(`infer-shadow: ${shadows.length} shadow(s). Rename the infer variable.`)
process.exit(1)
