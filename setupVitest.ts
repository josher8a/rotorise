import { existsSync, readdirSync, readFileSync, statSync } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import ts from 'typescript'

/**
 * The setup of `@ark/attest` type-checks the whole project, which costs more time and memory than
 * most of the specs. A spec needs the setup where the import closure of the spec reaches
 * `@ark/attest`. The closure follows each relative import, through `import`, `export from`,
 * `import()` and `require`, as the scanner of the compiler reads them. A call with a computed
 * argument, and a relative specifier that names no file, count as a reach, so a doubt keeps the
 * setup.
 *
 * The run selects its specs from the positional arguments of the command: each argument is a
 * substring of the path of a spec, as in vitest. An argument that is a flag, an argument that
 * matches no spec, or no argument at all selects every spec, and the setup runs.
 */
const ATTEST = '@ark/attest'
const SPEC = /\.(test|spec)\.[cm]?[jt]sx?$/
const SOURCE = ['', '.ts', '.d.ts', '.mts', '.cts', '.tsx', '.js', '.mjs', '.cjs', '.json', '/index.ts', '/index.js']
const SWAP = [
    ['.js', '.ts'],
    ['.mjs', '.mts'],
    ['.cjs', '.cts'],
] as const

// A call whose argument starts with a name or a template is no literal. A comment that writes
// `import(...)` has no such argument.
const COMPUTED = /\b(?:import|require)\s*\(\s*[^'")\s.]/

/** The specifiers of a file, or null where a call has an argument that is no literal. The compiler
 * scans the text, so a comment holds no import. */
const specifiers = (text: string): string[] | null =>
    COMPUTED.test(text) ? null : ts.preProcessFile(text, true, true).importedFiles.map(f => f.fileName)

const resolveFile = (from: string, specifier: string): string | null => {
    const base = resolve(dirname(from), specifier)
    const stems = [base, ...SWAP.filter(([from]) => base.endsWith(from)).map(([from, to]) => base.slice(0, -from.length) + to)]
    for (const stem of stems)
        for (const ext of SOURCE) {
            const file = stem + ext
            if (existsSync(file) && statSync(file).isFile()) return file
        }
    return null
}

/** True where the import closure of one of the files reaches `@ark/attest`, or cannot be read. */
export const reachesAttest = (files: readonly string[]): boolean => {
    const seen = new Set<string>()
    const stack = [...files]
    for (let file = stack.pop(); file !== undefined; file = stack.pop()) {
        if (seen.has(file)) continue
        seen.add(file)
        if (file.endsWith('.json')) continue
        const specs = specifiers(readFileSync(file, 'utf8'))
        if (specs === null) return true
        for (const spec of specs) {
            if (spec === ATTEST || spec.startsWith(`${ATTEST}/`)) return true
            if (!spec.startsWith('.')) continue
            const next = resolveFile(file, spec)
            if (next === null) return true
            stack.push(next)
        }
    }
    return false
}

/** The paths of the spec files under a directory, relative to the root. */
const specsUnder = (root: string, dir: string): string[] =>
    readdirSync(join(root, dir), { withFileTypes: true }).flatMap(entry => {
        const path = join(dir, entry.name)
        if (entry.isDirectory())
            return entry.name === 'node_modules' || entry.name === 'dist' || entry.name.startsWith('.')
                ? []
                : specsUnder(root, path)
        return SPEC.test(entry.name) ? [path] : []
    })

/** The specs that the arguments select, or null where the run can select any spec. */
export const selectedSpecs = (args: readonly string[], root: string): string[] | null => {
    if (args.length === 0 || args.some(a => a.startsWith('-'))) return null
    const all = specsUnder(root, '')
    const chosen = new Set<string>()
    for (const arg of args) {
        const hit = all.filter(f => f.includes(arg))
        if (hit.length === 0) return null
        for (const f of hit) chosen.add(resolve(root, f))
    }
    return [...chosen]
}

/** The arguments of the command after the name of the runner, with the words `run` and `--run` dropped. */
const commandArgs = (argv: readonly string[]): string[] => argv.slice(2).filter(a => a !== 'run' && a !== '--run')

export default async () => {
    const root = process.cwd()
    const specs = selectedSpecs(commandArgs(process.argv), root)
    if (specs !== null && !reachesAttest(specs)) return
    const { setup } = await import(ATTEST)
    return setup({})
}

