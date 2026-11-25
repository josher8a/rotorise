// The README samples, compiled and run against the published `dist/`.
//
//   node scripts/readme-check.mjs <README.md> <work dir>
//
// `scripts/readme-check.sh` makes the work directory: `node_modules/rotorise` holds the packed
// tarball, so a sample resolves the package as a consumer does.
// `node_modules/brushless` links the copy that the repository installs, for the samples of the adapters.
//
// Each `ts` block becomes one module. The module holds the statements of earlier blocks that the
// block uses: the latest declaration of a name wins. A name that means two things inside one module
// is refused, and so is each form that the check cannot read, because a check that passes on a form
// it cannot read is a false green. The program of the TypeScript compiler reads the blocks, so a
// declaration, an import and a comment have no pattern that can mis-read them.
//
// A `// =>` comment after a statement states the value of the statement. A `// name =>` comment
// states the value of the variable `name`. The check runs the block, and compares the comment with
// the value. A block that holds a `declare const` is compiled and is not run: the sample states the
// names of a package that the repository does not depend on.
import { spawnSync } from 'node:child_process'
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { basename, join } from 'node:path'
import ts from 'typescript'

const [readmePath, work] = process.argv.slice(2)
const file = basename(readmePath)
const failures = [] // { block, line, cause }
const fail = (block, line, cause) => failures.push({ block, line, cause })

// ---- 1. the fences ---------------------------------------------------------------------------
const rows = readFileSync(readmePath, 'utf8').split('\n')
const blocks = [] // { line: README line of the first row, rows }
const notRead = new Set(['typescript', 'javascript', 'js', 'jsx', 'tsx', 'mts', 'cts', 'mjs', 'cjs'])
for (let i = 0, open = null; i < rows.length; i++) {
  const m = /^```(\S*)/.exec(rows[i])
  if (!m) { if (open) open.rows.push(rows[i]); continue }
  if (open) { if (open.lang === 'ts') blocks.push(open); open = null; continue }
  open = { lang: m[1], line: i + 2, rows: [] }
  if (notRead.has(m[1])) fail(0, i + 1, `a block tagged \`${m[1]}\` is not read. Tag it \`ts\`, or tag it \`text\``)
  if (i === rows.length - 1 || !rows.slice(i + 1).some((r) => /^```/.test(r))) { fail(0, i + 1, 'this fence has no closing fence'); open = null }
}

// ---- 2. the statements of each block ---------------------------------------------------------
// the packages that a sample can import: the package itself, and `brushless`, a dev dependency whose adapters the README shows
const readable = (mod) => mod === 'rotorise' || mod.startsWith('rotorise/') || mod === 'brushless'
const uses = (node, out) => {
  const walk = (n) => {
    if (ts.isIdentifier(n)) {
      const p = n.parent
      const label = p && ((ts.isPropertyAccessExpression(p) && p.name === n) || (ts.isPropertyAssignment(p) && p.name === n)
        || (ts.isPropertySignature(p) && p.name === n) || (ts.isQualifiedName(p) && p.right === n))
      if (!label) out.add(n.text)
    }
    ts.forEachChild(n, walk)
  }
  walk(node)
  return out
}
const bindingNames = (name, out) => {
  if (ts.isIdentifier(name)) out.push(name.text)
  else for (const el of name.elements) if (ts.isBindingElement(el)) bindingNames(el.name, out)
  return out
}
const comment = /^\s*\/\/\s*(?:(\w+)\s+)?=>\s?(.*)$/
const anyComment = /\/\/\s*(?:\w+\s+)?=>/

const parsed = blocks.map((b, bi) => {
  const text = b.rows.join('\n')
  const sf = ts.createSourceFile(`b${bi + 1}.ts`, text, ts.ScriptTarget.ES2022, true, ts.ScriptKind.TS)
  const lineOf = (pos) => b.line + sf.getLineAndCharacterOfPosition(pos).line
  const imports = new Map() // local name -> declaration text
  const statements = [] // { names, uses, text, line, node, declare, expect }
  const consumed = new Set() // README lines of the `// =>` comments that the check reads
  sf.statements.forEach((s, k) => {
    if (ts.isImportDeclaration(s)) {
      const mod = s.moduleSpecifier.text
      if (!readable(mod)) {
        fail(bi + 1, lineOf(s.getStart()), `imports \`${mod}\`. The check reads imports of \`rotorise\` and \`brushless\` only. Declare the names that the sample needs with \`declare const\``)
        return
      }
      const c = s.importClause
      if (!c) return
      const whole = s.getText(sf)
      if (c.name) imports.set(c.name.text, whole)
      if (c.namedBindings && ts.isNamespaceImport(c.namedBindings)) imports.set(c.namedBindings.name.text, whole)
      if (c.namedBindings && ts.isNamedImports(c.namedBindings)) {
        for (const el of c.namedBindings.elements) {
          const imported = (el.propertyName ?? el.name).text
          const one = `import ${c.isTypeOnly || el.isTypeOnly ? 'type ' : ''}{ ${imported}${imported === el.name.text ? '' : ` as ${el.name.text}`} } from '${mod}'`
          imports.set(el.name.text, one)
        }
      }
      return
    }
    const names = []
    if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) bindingNames(d.name, names)
    else if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s) || ts.isEnumDeclaration(s) || ts.isInterfaceDeclaration(s)
      || ts.isTypeAliasDeclaration(s) || ts.isModuleDeclaration(s)) && s.name) names.push(s.name.text)
    const own = new Set(names)
    const used = [...uses(s, new Set())].filter((n) => !own.has(n))
    const declare = !!s.modifiers?.some((m) => m.kind === ts.SyntaxKind.DeclareKeyword)
    // the comment after the statement, up to the next statement
    const from = s.getEnd()
    const to = k + 1 < sf.statements.length ? sf.statements[k + 1].getStart(sf, false) : text.length
    const tail = text.slice(from, to).split('\n')
    const startLine = lineOf(from)
    let expect = null
    for (let j = 0; j < tail.length; j++) {
      const m = comment.exec(tail[j])
      if (!m) continue
      let want = m[2]
      let n = j + 1
      while (n < tail.length && /^\s*\/\/\s{3,}\S/.test(tail[n])) { want += ` ${tail[n].replace(/^\s*\/\/\s+/, '')}`; n++ }
      if (expect) { fail(bi + 1, startLine + j, 'a second `// =>` comment follows one statement'); continue }
      expect = { name: m[1], want, line: startLine + j }
      for (let r = j; r < n; r++) consumed.add(startLine + r)
      j = n - 1
    }
    const lead = text.slice(s.getFullStart(), s.getStart(sf))
    statements.push({ names, used, lead, text: lead + s.getText(sf), line: lineOf(s.getStart(sf)), pieceLine: lineOf(s.getFullStart()), node: s, declare, expect })
  })
  // a `// =>` comment that no statement owns is a comment that the check cannot read
  b.rows.forEach((r, j) => { if (anyComment.test(r) && !consumed.has(b.line + j)) fail(bi + 1, b.line + j, 'a `// =>` comment that follows no top-level statement. The check does not read it') })
  return { bi, line: b.line, imports, statements }
})

// the text of one statement, with the value of a `// =>` comment sent to show()
const render = (st, bi) => {
  if (!st.expect) return st.text
  const { name, want, line } = st.expect
  const s = st.node
  if (ts.isVariableStatement(s)) {
    if (st.names.length !== 1 || (name && name !== st.names[0])) { fail(bi + 1, line, `the comment names \`${name ?? ''}\`, and the statement declares ${st.names.join(', ') || 'no name'}`); return st.text }
    return `${st.text}\nshow(${line}, ${JSON.stringify(want)}, ${st.names[0]})`
  }
  if (ts.isExpressionStatement(s)) {
    if (name) { fail(bi + 1, line, `the comment names \`${name}\`, and the statement is an expression`); return st.text }
    return `${st.lead}show(${line}, ${JSON.stringify(want)}, ${s.expression.getText(s.getSourceFile())})`
  }
  fail(bi + 1, line, 'a `// =>` comment follows a statement that is no expression and no variable')
  return st.text
}

// ---- 3. one module for each block ------------------------------------------------------------
mkdirSync(join(work, 'out'), { recursive: true })
const names = []
parsed.forEach((p) => {
  const { bi } = p
  const kind = new Map() // name -> where the meaning of the name comes from
  const pulled = [] // { k, si }
  const importLines = new Map()
  const bind = (n, key, line, why) => {
    if (kind.has(n) && kind.get(n) !== key) { fail(bi + 1, line, `the name \`${n}\` means two things in this block (${why})`); return false }
    kind.set(n, key)
    return kind.get(n) === key
  }
  for (const st of p.statements) for (const n of st.names) kind.set(n, 'own')
  for (const [n, d] of p.imports) { kind.set(n, 'own'); importLines.set(n, d) }
  // the request of a name by a statement at (k, si): the latest meaning of the name before the statement
  const resolve = (n, k0, si0, line) => {
    for (let k = k0; k >= 0; k--) {
      const sts = parsed[k].statements
      for (let si = (k === k0 ? si0 : sts.length) - 1; si >= 0; si--) {
        if (!sts[si].names.includes(n)) continue
        const key = `s${k}.${si}`
        if (!bind(n, key, line, `README line ${sts[si].line} and the block`)) return
        if (!pulled.some((q) => q.k === k && q.si === si)) { pulled.push({ k, si }); demand(sts[si], k, si) }
        return
      }
      if (parsed[k].imports.has(n)) {
        const key = `i${k}`
        if (!bind(n, key, line, `an import of block ${k + 1} and the block`)) return
        importLines.set(n, parsed[k].imports.get(n))
        return
      }
    }
  }
  const demand = (st, k, si) => {
    for (const n of st.used) {
      if (k === bi && kind.get(n) === 'own') continue
      resolve(n, k, si, st.line)
    }
  }
  p.statements.forEach((st, si) => demand(st, bi, si))
  pulled.sort((a, c) => a.k - c.k || a.si - c.si)
  const pieces = [{ text: "import { show } from './show.js'", line: p.line }]
  for (const d of new Set(importLines.values())) pieces.push({ text: d, line: p.line })
  for (const { k, si } of pulled) pieces.push({ text: parsed[k].statements[si].text, line: parsed[k].statements[si].pieceLine })
  for (const st of p.statements) pieces.push({ text: render(st, bi), line: st.pieceLine })
  const origin = []
  let out = ''
  for (const pc of pieces) { pc.text.split('\n').forEach((_, j) => origin.push(pc.line + j)); out += `${pc.text}\n` }
  out += 'export {}\n'
  const name = `b${String(bi + 1).padStart(2, '0')}`
  writeFileSync(join(work, `${name}.ts`), out)
  names.push({ name, bi, origin, run: !p.statements.some((s) => s.declare), comments: p.statements.filter((s) => s.expect).map((s) => s.expect.line) })
})

writeFileSync(join(work, 'out', 'show.js'), `import { appendFileSync } from 'node:fs'
import { inspect, isDeepStrictEqual } from 'node:util'
const record = (r) => appendFileSync(process.env.README_CHECK_SHOW, JSON.stringify(r) + '\\n')
const text = (v) => (v instanceof Error ? v.constructor.name + ': ' + v.message : inspect(v, { depth: 8, breakLength: Infinity }))
export function show(line, expect, actual) {
  let want
  try { want = new Function('return (' + expect + ')')() } catch { record({ line, status: 'unread', expect }); return actual }
  const same = isDeepStrictEqual(want, actual) || (typeof actual === 'object' && actual !== null && isDeepStrictEqual(want, JSON.parse(JSON.stringify(actual))))
  record(same ? { line, status: 'ok' } : { line, status: 'differs', want: text(want), got: text(actual) })
  return actual
}
`)
writeFileSync(join(work, 'show.d.ts'), 'export function show<T>(line: number, expect: string, actual: T): T\n')
writeFileSync(join(work, 'package.json'), '{ "type": "module" }\n')
writeFileSync(join(work, 'tsconfig.json'), JSON.stringify({
  compilerOptions: { module: 'nodenext', moduleResolution: 'nodenext', target: 'es2022', lib: ['es2022'], strict: true, noEmitOnError: false, outDir: 'out', skipLibCheck: false, types: [] },
  include: ['b*.ts', 'show.d.ts'],
}))

// ---- 4. compile ------------------------------------------------------------------------------
const tsc = spawnSync(process.execPath, [join(process.cwd(), 'node_modules/typescript/bin/tsc'), '-p', 'tsconfig.json', '--pretty', 'false'], { cwd: work, encoding: 'utf8' })
const compileFailed = new Set()
let last = null
for (const row of (tsc.stdout + tsc.stderr).split('\n')) {
  const m = /^(b\d+)\.ts\((\d+),\d+\): error (TS\d+): (.*)$/.exec(row)
  if (m) {
    const b = names.find((x) => x.name === m[1])
    const line = b.origin[Number(m[2]) - 1] ?? 0
    compileFailed.add(b.bi)
    last = { block: b.bi + 1, line, cause: `${m[3]} ${m[4]}` }
    failures.push(last)
  } else if (/^\s/.test(row) && last) { if (last.cause.length < 600) last.cause += ` ${row.trim()}` }
  else if (row.trim() && !m) { fail(0, 0, `the compiler printed: ${row.trim().slice(0, 300)}`); last = null }
}

// ---- 5. run ----------------------------------------------------------------------------------
writeFileSync(join(work, 'show.log'), '')
const status = [] // one line for each block
let checked = 0
for (const b of names) {
  const p = parsed[b.bi]
  const head = `block ${b.bi + 1} (${file}:${p.line})`
  const before = failures.length
  if (compileFailed.has(b.bi)) { status.push({ b, head, text: 'FAIL', from: before }); continue }
  if (!b.run) {
    status.push({ b, head, text: `SKIP  ${head}: compiled, not run, because it holds \`declare const\`${b.comments.length ? `. Not checked: \`// =>\` at ${file}:${b.comments.join(', ')}` : ''}` })
    continue
  }
  const log = join(work, `${b.name}.log`)
  writeFileSync(log, '')
  const r = spawnSync(process.execPath, [join(work, 'out', `${b.name}.js`)], { cwd: work, encoding: 'utf8', env: { ...process.env, README_CHECK_SHOW: log } })
  for (const row of readFileSync(log, 'utf8').split('\n').filter(Boolean)) {
    const v = JSON.parse(row)
    checked++
    if (v.status === 'unread') fail(b.bi + 1, v.line, `the \`// =>\` comment is no value that the check can read: ${v.expect}`)
    if (v.status === 'differs') fail(b.bi + 1, v.line, `the \`// =>\` comment differs from the value.\n  comment: ${v.want}\n  value:   ${v.got}`)
  }
  if (r.status !== 0) fail(b.bi + 1, p.line, `the block exits with ${r.status}: ${(r.stderr || '').split('\n').filter((x) => /^\w*Error\b/.test(x)).slice(0, 3).join(' | ').slice(0, 500)}`)
  status.push({ b, head })
}

// ---- 6. the report ---------------------------------------------------------------------------
for (const s of status) {
  if (s.text?.startsWith('SKIP')) { console.log(s.text); continue }
  const mine = failures.filter((f) => f.block === s.b.bi + 1)
  if (mine.length === 0) console.log(`PASS  ${s.head}`)
  else { console.log(`FAIL  ${s.head}`); for (const f of mine) console.log(`      | ${file}:${f.line}: ${f.cause.replaceAll('\n', '\n      | ')}`) }
}
const general = failures.filter((f) => f.block === 0 || !names.some((n) => n.bi + 1 === f.block))
for (const f of general) console.log(`FAIL  ${file}:${f.line}: ${f.cause}`)
const runCount = names.filter((b) => b.run && !compileFailed.has(b.bi)).length
console.log(`${failures.length === 0 ? 'PASS' : 'FAIL'}  ${blocks.length} ts blocks, ${runCount} run, ${checked} \`// =>\` comments compared, ${failures.length} failures`)
process.exit(failures.length === 0 ? 0 : 1)
