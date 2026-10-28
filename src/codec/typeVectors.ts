/**
 * Type vectors: the static types of `extract`, `exclude` and `at`, against the run time.
 *
 * The emitter in `lean.ts` puts each decision of the run time to the model. This module puts the
 * same decisions to the type checker. Each root of the pool prints as library calls in a generated
 * TypeScript file. Each check states one decision of the run time as one line. Where the run time
 * accepts, the line compiles. Where the run time refuses, the line sits under `@ts-expect-error`.
 * The checker in `formal/scripts/type_bridge.py` compiles the files, maps each error to its row,
 * and compares the set of disagreements with a list of known disagreements.
 *
 * ── the roots ─────────────────────────────────────────────────────────────────────────────────
 *
 * A slice root is a union of objects, with the `extract` and the `exclude` of each clause at each
 * name of an option. A path root is a codec, with each path into the codec under `at`. At a path
 * that the run time resolves, an `encoded` row states each member that the codec at the path writes
 * for a value that the codec generates: the type of `encode` admits the key. The roots
 * go in the order of the hash of their Lean print, so a reorder of the pool moves no line and no
 * row id.
 *
 * A meet root is a pair of the pool: the call of `meet` at two constants, and one value of the
 * result for each seed that the result codec writes. The bridge keeps the first {@link MEET_ROOTS}
 * pairs in the order of the hash. A slice root also takes each literal that its options hold, a union
 * pattern that covers or part-covers a name, and a union pattern at two names.
 *
 * ── the row id ────────────────────────────────────────────────────────────────────────────────
 *
 * A row id is the group, the verdict that the run time expects, a hash of the Lean print of the
 * root, and the text of the check. The Lean print is the identity that the pool deduplicates by,
 * so two roots with one hash are one root, and the second goes.
 *
 * **A declaration has the hash of its own content.** The roots share constants, and the root that
 * declares a shared constant depends on which object of two equal roots prints. The content is the
 * Lean print of the term that the declaration reads, with the kind of the declaration. Two
 * declarations of one content have one type, so one id names both.
 *
 * ── what cannot be emitted ────────────────────────────────────────────────────────────────────
 *
 * {@link TypeUnemittable} is thrown, never guessed around. A form that this module cannot print
 * as library calls would compare a codec that the library did not build.
 */
import { createHash } from 'node:crypto'
import { DynamoNumber, isNumeral, isStoredNumeral, memberOf } from './attribute'
import type { AnyCodec } from './codec'
import { boolean, meet, number, object, string, union } from './codec'
import { codecOfTerm } from './denote'
import type { PathStep, PathVectors, Slice } from './lean'
import { hostAt, LeanUnemittable, leanClosedOf, reachable } from './lean'
import { CodecError, failed } from './result'
import type { Literal, Term } from './term'
import { componentsOf, leafKinds, sameTerm, targetOf } from './term'
import { arbitraryOf, rngFrom } from './testing'

/** A term that this module cannot print as library calls. */
export class TypeUnemittable extends Error {
    /** The root and the form where the obstruction is. */
    readonly at: string
    /** Why the library calls cannot say it. */
    readonly reason: string
    constructor(at: string, reason: string) {
        super(`cannot emit TypeScript for ${at}: ${reason}`)
        this.name = 'TypeUnemittable'
        this.at = at
        this.reason = reason
    }
}

const refuse = (at: string, reason: string): never => {
    throw new TypeUnemittable(at, reason)
}

/** The verdict of the run time that a check states. */
export type Verdict = 'accept' | 'refuse'

/**
 * One check, at one line of one generated file.
 *
 * A row with `after` reads the result of the row that `after` names. Where that row disagrees, the
 * type of the result is not the type of the run time, and the checker reads no verdict here.
 */
export type TypeRow = {
    readonly id: string
    readonly file: string
    readonly line: number
    readonly expect: Verdict
    readonly after?: string
}

/* ── lexical ─────────────────────────────────────────────────────────────────────────────── */

/** A string literal. JSON escapes each line break, so one declaration stays on one line. */
const quoted = (s: string): string => JSON.stringify(s)

const keyText = (s: string): string =>
    /^[A-Za-z_$][\w$]*$/.test(s) ? s : quoted(s)

const numeralText = (v: DynamoNumber): string =>
    `orThrow(DynamoNumber.from(${quoted(String(v))}))`

const bytesText = (v: Uint8Array): string =>
    `new Uint8Array([${Array.from(v).join(', ')}])`

/** A fill, as a value expression. */
const valueText = (v: unknown, at: string): string => {
    if (v === undefined) return 'undefined'
    if (v === null) return 'null'
    if (typeof v === 'string') return quoted(v)
    if (typeof v === 'boolean') return String(v)
    if (typeof v === 'number')
        return Number.isFinite(v)
            ? String(v)
            : refuse(at, 'a fill that is no finite number')
    if (v instanceof DynamoNumber) return numeralText(v)
    if (v instanceof Uint8Array) return bytesText(v)
    // a const assertion keeps each literal member, as the type of a literal set reads it
    if (v instanceof Set) {
        const members: readonly unknown[] = [...v]
        return `new Set([${members.map((x) => valueText(x, at)).join(', ')}] as const)`
    }
    if (Array.isArray(v)) {
        const items: readonly unknown[] = v
        return `[${items.map((x) => valueText(x, at)).join(', ')}]`
    }
    if (typeof v === 'object')
        return `{ ${Object.entries(v)
            .map(([k, x]) => `${keyText(k)}: ${valueText(x, at)}`)
            .join(', ')} }`
    return refuse(at, `a fill of type ${typeof v}`)
}

/* ── the literals ────────────────────────────────────────────────────────────────────────── */

const isLiteral = (t: Term): t is Literal => t.kind === 'literal'

/** The argument that a literal constructor takes for one literal. */
const literalArgument = (l: Literal): string => {
    switch (l.base) {
        case 'string':
            return quoted(l.v)
        case 'number':
            return numeralText(l.v)
        case 'boolean':
            return String(l.v)
        case 'binary':
            return bytesText(l.v)
    }
}

/** The constructor that builds a literal at each base. */
const literalConstructor: { readonly [B in Literal['base']]: string } = {
    string: 'string',
    number: 'dynamoNumber',
    boolean: 'boolean',
    binary: 'binary',
}

/**
 * **A union of literals at one base prints as one call**, as `string('a', 'b')` builds it. Two
 * options at one value are two codecs, which a constructor of alternatives refuses, so such a
 * union prints as a `union`.
 */
const literalCall = (
    ts: readonly Term[],
): { readonly base: Literal['base']; readonly args: string } | undefined => {
    if (!ts.every(isLiteral)) return undefined
    const base = ts[0]?.base
    if (base === undefined || !ts.every((l) => l.base === base))
        return undefined
    const args = ts.map(literalArgument)
    if (new Set(args).size < args.length) return undefined
    return { base, args: args.join(', ') }
}

const literalText = (ts: readonly Term[]): string | undefined => {
    const call = literalCall(ts)
    return call && `${literalConstructor[call.base]}(${call.args})`
}

const optionsOf = (t: Term): readonly Term[] =>
    t.kind === 'union' ? t.options : [t]

/** The string literals of a term, or nothing where an option is no string literal. */
const stringLiterals = (t: Term): readonly string[] | undefined => {
    const out: string[] = []
    for (const one of optionsOf(t)) {
        if (one.kind !== 'literal' || one.base !== 'string') return undefined
        out.push(one.v)
    }
    return out
}

/** The numeric literals of a term, as JS numbers, or nothing where an option is no numeral. */
const numberLiterals = (t: Term): readonly number[] | undefined => {
    const out: number[] = []
    for (const one of optionsOf(t)) {
        if (one.kind !== 'literal' || one.base !== 'number') return undefined
        out.push(Number(String(one.v)))
    }
    return out
}

/** The float adapter of `number`, which the library ships and no `via` names. */
const numberAdapter = number.def.kind === 'held' ? number.def.f : undefined

/* ── the binders ─────────────────────────────────────────────────────────────────────────── */

type Ref = Extract<Term, { readonly kind: 'ref' }>

const binderCache = new Map<Term, boolean>()

/** A `ref` that closes a cycle: its target reaches the `ref` again. */
const isBinder = (t: Term): t is Ref => {
    if (t.kind !== 'ref') return false
    let hit = binderCache.get(t)
    if (hit === undefined) {
        const target = targetOf(t)
        hit = target !== undefined && reachable(target).has(t)
        binderCache.set(t, hit)
    }
    return hit
}

/* ── the printer ─────────────────────────────────────────────────────────────────────────── */

/**
 * One declaration: the kind, the content, and the line. The content is the Lean print of the term
 * that the declaration reads, so two declarations of one content have one type, and one row id.
 */
type Declaration = {
    readonly kind: string
    readonly content: string
    readonly line: string
}

/**
 * **The constants that the roots share.** A term object that two roots reach is one constant, and
 * the root that reaches the object first declares the constant. The type checker then reads the
 * type of the constant one time.
 */
type Shared = {
    readonly names: Map<Term, string>
    readonly state: Map<Term, 'progress' | 'done'>
    readonly adapters: Map<unknown, string>
    readonly predicates: Map<unknown, string>
    readonly sccs: ReadonlyMap<Term, Scc>
}

/**
 * **One strongly connected component of the pool**, printed as one `scope`. A term of the
 * component is an entry where a `ref` names the term, a term outside the component names the term,
 * a root names the term, or the term has more than one parent. Each other term has one parent in
 * the component, and prints in place inside that parent. So the print copies no term.
 */
type Scc = {
    readonly members: ReadonlySet<Term>
    readonly keys: ReadonlyMap<Term, string>
    name?: string
    state?: 'progress' | 'done'
}

/** **The cycles of the pool**: each term of a component, at the component. */
const sccsOf = (roots: readonly Term[]): ReadonlyMap<Term, Scc> => {
    const out = new Map<Term, Scc>()
    for (const { members, keys } of componentsOf(roots)) {
        const scc: Scc = { members, keys }
        for (const m of members) out.set(m, scc)
    }
    return out
}

const shared = (roots: readonly Term[]): Shared => ({
    names: new Map(),
    state: new Map(),
    adapters: new Map(),
    predicates: new Map(),
    sccs: sccsOf(roots),
})

/**
 * **The declarations of one root.** Each term object that the print can share declares one
 * constant, so a term that two places share stays one object in the print.
 *
 * **A cycle prints as one `scope`**: one entry for each term that the component names, and
 * `ref('key')` at each `ref` of the component. A term outside the component names an entry as a
 * member of the constant of the scope.
 */
const printerOf = (
    { names, state, adapters, predicates, sccs }: Shared,
    prefix: string,
    at: string,
) => {
    const declarations: Declaration[] = []
    let fresh = 0

    const full = (local: string): string => `${prefix}_${local}`
    const declare = (kind: string, content: string, line: string): void => {
        declarations.push({ kind, content, line })
    }
    /** The Lean print of a term: the content of a declaration, whichever root declares it. */
    const lean = (t: Term): string =>
        leanClosedOf(codecOfTerm(t), at, freshBound())
    const nameOf = (t: Term): string => {
        let n = names.get(t)
        if (n === undefined) {
            n = full(`h${fresh++}`)
            names.set(t, n)
        }
        return n
    }
    /** The constant of a term, declared once, as the print of the term as a root. */
    const ref = (t: Term): string => {
        if (leafKinds.has(t.kind)) return print(t, inline)
        const scc = sccs.get(t)
        if (scc !== undefined && t.kind !== 'ref') return entryOf(scc, t)
        const n = nameOf(t)
        const now = state.get(t)
        if (now === 'done') return n
        if (now === 'progress')
            return refuse(at, 'a constant that reads itself')
        state.set(t, 'progress')
        // a `ref` of a cycle names the entry that is its target: the scope is declared first
        const body = scc === undefined ? print(t, ref) : entryOf(scc, chase(t))
        declare('constant', lean(t), `export const ${n} = ${body}`)
        state.set(t, 'done')
        return n
    }

    /** The term that a chain of `ref`s reaches. */
    const chase = (t: Term): Term => {
        let u: Term | undefined = t
        for (let i = 0; u?.kind === 'ref' && i < 64; i++) u = targetOf(u)
        return u === undefined || u.kind === 'ref'
            ? refuse(at, 'a chain of thunks that returns no term')
            : u
    }

    /** An entry of a scope, as a member of the constant of the scope. */
    const entryOf = (scc: Scc, t: Term): string => {
        const key = scc.keys.get(t)
        if (key === undefined)
            return refuse(at, 'a term of a cycle that no entry names')
        return `${scopeOf(scc)}.${key}`
    }

    /** The constant of a scope, declared once, after each constant that its entries read. */
    const scopeOf = (scc: Scc): string => {
        if (scc.state === 'done' && scc.name !== undefined) return scc.name
        if (scc.state === 'progress')
            return refuse(at, 'a scope that reads itself')
        scc.state = 'progress'
        const entries = [...scc.keys].map(
            ([t, key]) => `${key}: ${member(scc, t)}`,
        )
        const name = full(`sc${fresh++}`)
        declare(
            'scope',
            [...scc.keys.keys()].map(lean).join(' | '),
            `export const ${name} = scope({ ${entries.join(', ')} })`,
        )
        scc.name = name
        scc.state = 'done'
        return name
    }

    /** A term of a scope: a `ref` of the scope prints as `ref`, and a term with one parent is in place. */
    const member = (scc: Scc, t: Term): string =>
        print(t, (c) => {
            if (leafKinds.has(c.kind)) return print(c, inline)
            if (sccs.get(c) !== scc) return ref(c)
            const target = chase(c)
            const key = scc.keys.get(target)
            if (key !== undefined && (c.kind === 'ref' || target === c))
                return `ref('${key}')`
            if (c.kind === 'ref')
                return refuse(
                    at,
                    'a thunk of a cycle whose target no entry names',
                )
            return member(scc, c)
        })

    /** The decoded type of a term, as a type expression. */
    const typeText = (t: Term): string => {
        const scc = sccs.get(t)
        if (scc === undefined) return `Decoded<typeof ${ref(t)}>`
        if (t.kind === 'ref') return typeText(chase(t))
        if (scc.keys.has(t)) return `Decoded<typeof ${entryOf(scc, t)}>`
        switch (t.kind) {
            case 'object': {
                const fields = Object.entries(t.body.fields).map(([k, f]) => {
                    const x = typeText(f.t)
                    if (f.mark === 'optional')
                        return `readonly ${keyText(k)}?: ${x}`
                    if (f.mark === 'undefinable')
                        return `readonly ${keyText(k)}: ${x} | undefined`
                    return `readonly ${keyText(k)}: ${x}`
                })
                const body = `{ ${fields.join('; ')} }`
                if (t.body.rest === undefined) return body
                // the index admits the declared fields too, as the decoded type of the library does
                const declared = Object.values(t.body.fields).map((f) =>
                    f.mark === 'optional'
                        ? `${typeText(f.t)} | undefined`
                        : typeText(f.t),
                )
                return `(${body} & { readonly [name: string]: ${[typeText(t.body.rest), ...declared].join(' | ')} })`
            }
            case 'list': {
                if (
                    t.spread !== undefined &&
                    t.pre.length === 0 &&
                    t.suf.length === 0
                )
                    return `readonly (${typeText(t.spread)})[]`
                const parts = [
                    ...t.pre.map(typeText),
                    ...(t.spread === undefined
                        ? []
                        : [`...(${typeText(t.spread)})[]`]),
                    ...t.suf.map(typeText),
                ]
                return `readonly [${parts.join(', ')}]`
            }
            case 'union':
                return t.options.map((o) => `(${typeText(o)})`).join(' | ')
            case 'held':
                return typeText(t.outer)
            case 'refine':
            case 'legacy':
                return typeText(t.inner)
            default:
                return refuse(at, `the type of a ${t.kind} over a binder`)
        }
    }

    const adapterOf = (t: Extract<Term, { readonly kind: 'held' }>) => {
        let name = adapters.get(t.f)
        if (name === undefined) {
            const local = `adapter${fresh++}`
            name = full(local)
            const inner = typeText(t.inner)
            const outer = typeText(t.outer)
            declare(
                'adapter',
                lean(t),
                `export const ${name} = { encode: (_v: ${outer}): Result<${inner}> => { throw new Error('stub') }, decode: (_t: ${inner}): Result<${outer}> => { throw new Error('stub') } }`,
            )
            adapters.set(t.f, name)
        }
        return name
    }

    /** A caller's predicate. One closure serves each refinement of the pool, so the stub is generic. */
    const predicateOf = (is: unknown) => {
        let name = predicates.get(is)
        if (name === undefined) {
            const local = `predicate${fresh++}`
            name = full(local)
            declare(
                'predicate',
                'predicate',
                `export const ${name} = <V,>(v: V): v is V => String(v) !== 'zz'`,
            )
            predicates.set(is, name)
        }
        return name
    }

    /**
     * A term as library calls. `sub` prints each child: {@link ref} declares the child, and
     * {@link inline} writes the child in place, as a clause needs.
     */
    const print = (t: Term, sub: (t: Term) => string): string => {
        switch (t.kind) {
            case 'string':
                return 'string'
            case 'number':
                return 'dynamoNumber'
            case 'boolean':
                return 'boolean'
            case 'binary':
                return 'binary'
            case 'null':
                return 'nullValue'
            case 'opaq':
                return 'opaque'
            case 'never':
                return 'never'
            case 'literal':
                return literalText([t]) ?? refuse(at, 'a literal')
            case 'set': {
                const e = t.elem
                if (e.kind === 'string') return 'string.set()'
                if (e.kind === 'number') return 'dynamoNumber.set()'
                if (e.kind === 'binary') return 'binary.set()'
                if (
                    e.kind === 'held' &&
                    e.via === 'decimalText' &&
                    e.inner.kind === 'number'
                )
                    return 'decimal.set()'
                const call = literalCall(optionsOf(e))
                if (call?.base === 'string') return `string.set(${call.args})`
                return refuse(at, `a set of ${e.kind}`)
            }
            case 'list': {
                if (
                    t.spread !== undefined &&
                    t.pre.length === 0 &&
                    t.suf.length === 0
                )
                    return `array(${sub(t.spread)})`
                return `list(${[
                    ...t.pre.map(sub),
                    ...(t.spread === undefined
                        ? []
                        : [`spread(${sub(t.spread)})`]),
                    ...t.suf.map(sub),
                ].join(', ')})`
            }
            case 'held': {
                if (t.via === 'decimalText') {
                    if (t.inner.kind === 'number') return 'decimal'
                    const ls = stringLiterals(t.outer)
                    return ls === undefined
                        ? refuse(at, 'a decimal over a non-literal')
                        : `decimal(${ls.map(quoted).join(', ')})`
                }
                if (t.via === 'opaqueLossy') return "opaque('lossy')"
                if (t.via === 'opaqueRefuse') return "opaque('refuse')"
                if (t.f === numberAdapter) {
                    if (t.inner.kind === 'number') return 'number'
                    const ns = numberLiterals(t.inner)
                    return ns === undefined
                        ? refuse(at, 'a number over a non-literal')
                        : `number(${ns.join(', ')})`
                }
                return `held(${sub(t.inner)}, ${sub(t.outer)}, ${adapterOf(t)})`
            }
            case 'refine': {
                const is = t.q.is
                // the shipped predicates return a boolean, and `refine` takes a type predicate
                if (is === isNumeral)
                    return `refine(${sub(t.inner)}, (s: string): s is string => isNumeral(s))`
                if (is === isStoredNumeral)
                    return `refine(${sub(t.inner)}, (s: string): s is string => isStoredNumeral(s))`
                return `refine(${sub(t.inner)}, ${predicateOf(is)})`
            }
            case 'legacy':
                return `withLegacyRead({ current: ${sub(t.inner)}, older: { decode: (): never => { throw new Error('older') } } })`
            // a `ref` that closes no cycle prints as a `ref` under its own scope, and not as its
            // target: the type level reads a key pinned through a `ref` as unpinned, so the print of the
            // target would hand the type a codec that the run time never reads. A clause prints the
            // target, because a clause is read as a pattern and holds no scope. A `ref` with no target
            // is a `ref` that no scope binds
            case 'ref': {
                const target = targetOf(t)
                if (target === undefined) return "ref('Undeclared')"
                if (sub === inline && isBinder(t))
                    return refuse(at, 'a binder in a clause')
                // the host refuses a declared `never` by the term it reads, and a `ref` hides the
                // term: the print keeps a `ref` where its target would be that `never`
                if (sub !== inline && target.kind === 'never')
                    return "scope({ At: ref('It'), It: never }).At"
                if (sub !== inline)
                    return `scope({ At: ref('It'), It: ${sub(target)} }).At`
                return sub(target)
            }
            case 'object': {
                const fields = Object.entries(t.body.fields).map(([k, f]) => {
                    const x = sub(f.t)
                    if (f.mark === 'optional')
                        return `${keyText(k)}: optional(${x})`
                    if (f.mark === 'undefinable')
                        return `${keyText(k)}: undefinable(${x})`
                    if (f.mark === 'fallback')
                        return `${keyText(k)}: withLegacyRead({ current: ${x}, whenMissing: ${valueText(f.v, at)} })`
                    return `${keyText(k)}: ${x}`
                })
                const spec = `{ ${fields.join(', ')} }`
                return t.body.rest === undefined
                    ? `object(${spec})`
                    : `object(${spec}, [string, optional(${sub(t.body.rest)})])`
            }
            case 'union':
                return (
                    literalText(t.options) ??
                    `union([${t.options.map(sub).join(', ')}])`
                )
        }
    }

    /** A clause codec, written in place. */
    const inline = (t: Term): string => print(t, inline)

    return {
        declarations,
        full,
        /** A constant of the root at a fixed name, of one kind. */
        constant: (local: string, kind: string, t: Term): void => {
            declare(kind, lean(t), `export const ${full(local)} = ${ref(t)}`)
        },
        /** A line of one kind, whose content is the term that the line reads. */
        line: (kind: string, t: Term, line: string): void =>
            declare(kind, lean(t), line),
        clause: (codec: AnyCodec): string => inline(codec.def),
    }
}

/* ── the checks ──────────────────────────────────────────────────────────────────────────── */

/** A check inside one root: the line inside the root's block, and the row without its place. */
type Check = Omit<TypeRow, 'file' | 'line'> & { readonly at: number }

/** The lines and the checks of one root, before the split places them in a file. */
type Block = { readonly lines: string[]; readonly checks: Check[] }

const block = (): Block => ({ lines: [], checks: [] })

/** A row with its check: a refusal sits under the directive on the line before. */
const assert = (b: Block, row: Omit<Check, 'at'>, text: string): void => {
    if (row.expect === 'refuse') b.lines.push('// @ts-expect-error')
    b.lines.push(text)
    b.checks.push({ ...row, at: b.lines.length })
}

const hash = (text: string): string =>
    createHash('sha256').update(text).digest('hex').slice(0, 10)

const rowId = (
    group: string,
    expect: Verdict,
    root: string,
    text: string,
): string => `${group}|${expect}|${root}|${text}`

/** The members that a slice keeps, as a term: a union, the bottom, or one member. */
const membersOf = (t: Term): readonly Term[] =>
    t.kind === 'union' ? t.options : t.kind === 'never' ? [] : [t]

/**
 * Which options a slice keeps, in the order of the union. A kept member is the option object
 * where the slice keeps the object, and the same term where the slice builds a new one.
 */
const keptOptions = (
    options: readonly Term[],
    kept: readonly Term[],
): readonly boolean[] => {
    const byObject = options.map((o) => kept.includes(o))
    return byObject.filter(Boolean).length === kept.length
        ? byObject
        : options.map((o) => kept.some((k) => sameTerm(k, o)))
}

/** The run-time slice, or nothing where the run time refuses the pattern. */
const sliced = (
    run: (pattern: AnyCodec) => AnyCodec,
    pattern: AnyCodec,
): readonly Term[] | undefined => {
    try {
        return membersOf(run(pattern).def)
    } catch (error) {
        if (!(error instanceof CodecError)) throw error
        return undefined
    }
}

const freshBound = () => ({
    closures: new Map<unknown, string>(),
    adapters: new Map<unknown, string>(),
    readers: new Map<unknown, string>(),
})

type Root = {
    readonly root: string
    readonly declarations: readonly Declaration[]
    readonly checks: Block
}

/**
 * The distinct string literals that a field term holds, through each union and each `ref`. A
 * `ref` reads its target, so a literal that a scope binds counts as a literal of the field.
 */
const literalsOf = (t: Term, depth = 0): readonly string[] => {
    if (depth > 8) return []
    switch (t.kind) {
        case 'literal':
            return t.base === 'string' ? [t.v] : []
        case 'union':
            return t.options.flatMap((o) => literalsOf(o, depth + 1))
        case 'ref': {
            const target = targetOf(t)
            return target === undefined ? [] : literalsOf(target, depth + 1)
        }
        default:
            return []
    }
}

/** Whether a field term is the base `boolean` through a union or a `ref`. */
const holdsBoolean = (t: Term, depth = 0): boolean => {
    if (depth > 8) return false
    switch (t.kind) {
        case 'boolean':
            return true
        case 'union':
            return t.options.some((o) => holdsBoolean(o, depth + 1))
        case 'ref': {
            const target = targetOf(t)
            return target !== undefined && holdsBoolean(target, depth + 1)
        }
        default:
            return false
    }
}

/** The literals of each name that the options of a union hold, at most four for each name. */
const namedLiterals = (
    options: readonly Term[],
): ReadonlyMap<string, readonly string[]> => {
    const out = new Map<string, string[]>()
    for (const o of options) {
        if (o.kind !== 'object') continue
        for (const [name, f] of Object.entries(o.body.fields)) {
            const seen = out.get(name) ?? []
            for (const l of literalsOf(f.t))
                if (!seen.includes(l) && seen.length < 4) seen.push(l)
            out.set(name, seen)
        }
    }
    return out
}

/**
 * A pattern: the argument of the call as the row id spells it, the same argument as source text,
 * and the codec that builds it.
 */
type Pattern = {
    readonly argument: string
    readonly source: string
    readonly codec: AnyCodec
}

// one cast each, where a constructor takes a tuple of literals and the root gives a list at run time
const stringOf = string as unknown as (...values: readonly string[]) => AnyCodec
const booleanOf = boolean as unknown as (value: boolean) => AnyCodec

/**
 * **The patterns that the options of a root suggest.** Each literal that an option holds at a name
 * is a clause of its own, and so is the set of them. A union pattern splits the literals of one
 * name into two members (a cover), keeps one literal and adds one that the root lacks (a partial
 * cover), and puts two names in one pattern. The base `boolean` is covered by `true` and `false`.
 * Each literal comes from the root, so the pattern meets the root.
 */
const patternsOf = (
    options: readonly Term[],
    clause: (codec: AnyCodec) => string,
): readonly Pattern[] => {
    const out: Pattern[] = []
    const member = (name: string, c: AnyCodec): AnyCodec =>
        object({ [name]: c })
    const objectPattern = (name: string, c: AnyCodec): Pattern => {
        const argument = `{ ${keyText(name)}: ${clause(c)} }`
        return {
            argument,
            source: `object(${argument})`,
            codec: member(name, c),
        }
    }
    const unionPattern = (members: readonly AnyCodec[]): Pattern => {
        const codec = union(members)
        const source = clause(codec)
        return { argument: source, source, codec }
    }
    const named = namedLiterals(options)
    const literal = [...named].filter(([, ls]) => ls.length > 0)
    for (const [name, ls] of literal) {
        for (const l of ls) out.push(objectPattern(name, stringOf(l)))
        const half = Math.ceil(ls.length / 2)
        if (ls.length >= 2) {
            out.push(objectPattern(name, stringOf(...ls)))
            out.push(
                unionPattern([
                    member(name, stringOf(...ls.slice(0, half))),
                    member(name, stringOf(...ls.slice(half))),
                ]),
            )
        }
        if (ls.length >= 3)
            out.push(unionPattern(ls.map((l) => member(name, stringOf(l)))))
        out.push(
            unionPattern([
                member(name, stringOf(...ls.slice(0, 1))),
                member(name, stringOf('zz')),
            ]),
        )
    }
    for (const name of named.keys()) {
        const field = (o: Term) =>
            o.kind === 'object' ? o.body.fields[name] : undefined
        if (
            !options.some((o) => holdsBoolean(field(o)?.t ?? { kind: 'never' }))
        )
            continue
        out.push(
            unionPattern([
                member(name, booleanOf(true)),
                member(name, booleanOf(false)),
            ]),
            unionPattern([member(name, booleanOf(true))]),
        )
    }
    literal.forEach(([a, firsts], i) => {
        const next = literal[i + 1]
        const x = firsts[0]
        const y = next?.[1][0]
        if (next === undefined || x === undefined || y === undefined) return
        out.push(
            unionPattern([
                member(a, stringOf(x)),
                member(next[0], stringOf(y)),
            ]),
        )
    })
    return out
}

/** One slice root: the union, its options, a sample of each option, and each clause. */
const sliceRoot = (
    slice: Slice,
    p: ReturnType<typeof printerOf>,
    root: string,
    vocabulary: readonly (() => AnyCodec)[],
): Root => {
    const def = slice.codec.def
    if (def.kind !== 'union')
        return refuse(slice.name, `a slice root that is a ${def.kind}`)
    const options = def.options
    const keys = slice.keys ?? []
    // a union names the drawn union itself, so a `ref` whose target is the union reaches this one
    if (keys.length === 0) p.constant('root', 'root', def)
    options.forEach((o, i) => {
        p.constant(`o${i}`, 'option', o)
    })
    const list = `[${options.map((_, i) => p.full(`o${i}`)).join(', ')}]`
    const [key] = keys
    if (key !== undefined)
        p.line(
            `dissection ${keys.join(',')}`,
            def,
            `export const ${p.full('root')} = ${keys.length === 1 ? `discriminatedUnion(${quoted(key)}, ${list})` : `mdunion([${keys.map(quoted).join(', ')}], ${list})`}`,
        )
    options.forEach((o, i) => {
        p.line(
            'sample',
            o,
            `export declare const ${p.full(`m${i}`)}: Decoded<typeof ${p.full(`o${i}`)}>`,
        )
    })
    const b = block()
    const names = new Set(
        options.flatMap((o) =>
            o.kind === 'object' ? Object.keys(o.body.fields) : [],
        ),
    )
    const patterns: Pattern[] = []
    for (const name of names)
        for (const make of vocabulary) {
            const argument = `{ ${keyText(name)}: ${p.clause(make())} }`
            patterns.push({
                argument,
                source: `object(${argument})`,
                codec: object({ [name]: make() }),
            })
        }
    const spelledAlready = new Set(patterns.map((q) => q.argument))
    for (const q of patternsOf(options, p.clause)) {
        if (spelledAlready.has(q.argument)) continue
        spelledAlready.add(q.argument)
        patterns.push(q)
    }
    for (const pattern of patterns)
        for (const op of ['extract', 'exclude'] as const) {
            const text = `${op}(${pattern.argument})`
            const kept = sliced(slice.codec[op], pattern.codec)
            const callRow = rowId(
                'call',
                kept === undefined ? 'refuse' : 'accept',
                root,
                text,
            )
            b.lines.push('{')
            assert(
                b,
                {
                    id: callRow,
                    expect: kept === undefined ? 'refuse' : 'accept',
                },
                `const r = ${op}(C.${p.full('root')}, ${pattern.source})`,
            )
            if (kept !== undefined)
                keptOptions(options, kept).forEach((keeps, i) => {
                    const expect = keeps ? 'accept' : 'refuse'
                    assert(
                        b,
                        {
                            id: rowId(op, expect, root, `${text} member ${i}`),
                            expect,
                            after: callRow,
                        },
                        `const m${i}: Decoded<typeof r> = C.${p.full(`m${i}`)}`,
                    )
                })
            b.lines.push('}')
        }
    return { root, declarations: p.declarations, checks: b }
}

/** One path root: the codec, the item that holds it at `r`, and each path. */
const pathRoot = (
    vectors: PathVectors,
    p: ReturnType<typeof printerOf>,
    root: string,
): Root => {
    p.constant('root', 'root', vectors.codec.def)
    p.line(
        'wrapper',
        vectors.codec.def,
        `export const ${p.full('w')} = item(object({ r: optional(${p.full('root')}) }))`,
    )
    /*
     * The call of a path is the steps themselves: each run of segments is one `at`, and each
     * clause is one `narrow`. A path that ends at a clause ends in `at(…, [])`, which checks that
     * one codec stands at the place.
     */
    const spelled = (path: readonly PathStep[]): string => {
        let call = `C.${p.full('w')}`
        let run: string[] = [quoted('r')]
        for (const s of path) {
            if (typeof s !== 'object') {
                run.push(typeof s === 'number' ? String(s) : quoted(s))
                continue
            }
            const clause = Object.entries(s.narrow.spec)
                .map(([k, c]) => `${keyText(k)}: ${p.clause(c)}`)
                .join(', ')
            call = `narrow(${run.length === 0 ? call : `at(${call}, [${run.join(', ')}])`}, object({ ${clause} }))`
            run = []
        }
        return `at(${call}, [${run.join(', ')}])`
    }
    const b = block()
    for (const path of vectors.paths) {
        const host = hostAt(vectors.codec, path)
        const expect = host.kind === 'resolved' ? 'accept' : 'refuse'
        const call = spelled(path)
        const text = call
        const id = rowId('path', expect, root, text)
        assert(b, { id, expect }, call)
        if (host.kind !== 'resolved') continue
        // the type of `encode` at the path admits the key of each attribute that the run time writes
        for (const key of writtenKeys(host.codec))
            assert(
                b,
                {
                    id: rowId('encoded', 'accept', root, `${text} ${key}`),
                    expect: 'accept',
                    after: id,
                },
                `encodes(${call}, ${quoted(key)})`,
            )
    }
    return { root, declarations: p.declarations, checks: b }
}

/** Two factors of a `meet`, as the pool pairs them. */
export type MeetPair = { readonly left: AnyCodec; readonly right: AnyCodec }

// one cast, where the run time takes erased factors and `meet` takes the tuple that it validates
const meetOfCodecs = meet as unknown as (
    ...factors: readonly AnyCodec[]
) => AnyCodec

/** The run-time meet, or nothing where the run time refuses the factors. */
const met = (pair: MeetPair): AnyCodec | undefined => {
    try {
        return meetOfCodecs(pair.left, pair.right)
    } catch (error) {
        if (!(error instanceof CodecError)) throw error
        return undefined
    }
}

/**
 * The values that the result of a meet generates, as value expressions: the seeds of
 * {@link rngFrom}. A value that the codec cannot generate, or that no expression states, adds
 * nothing.
 */
const meetSamples = (result: AnyCodec, at: string): readonly string[] => {
    const out = new Set<string>()
    for (const seed of SAMPLES) {
        try {
            const value = arbitraryOf(result, rngFrom(seed), 3)
            // a value that the run-time codec itself cannot write is no sample of the result
            if (!failed(result.encode(value as never)))
                out.add(valueText(value, at))
        } catch (error) {
            if (
                !(
                    error instanceof CodecError ||
                    error instanceof RangeError ||
                    error instanceof TypeUnemittable
                )
            )
                throw error
        }
    }
    return [...out]
}

/**
 * **One meet root**: the call of `meet` at two constants. The row expects `accept` where the run
 * time builds the meet, and `refuse` where the run time throws. Where the run time builds, each
 * value that the result generates must fit the decoded type of the call.
 */
const meetRoot = (
    pair: MeetPair,
    result: AnyCodec | undefined,
    p: ReturnType<typeof printerOf>,
    root: string,
    at: string,
): Root => {
    p.constant('l', 'left', pair.left.def)
    p.constant('r', 'right', pair.right.def)
    const text = `meet(${p.full('l')}, ${p.full('r')})`
    const callRow = rowId(
        'meet',
        result === undefined ? 'refuse' : 'accept',
        root,
        text,
    )
    const b = block()
    b.lines.push('{')
    assert(
        b,
        { id: callRow, expect: result === undefined ? 'refuse' : 'accept' },
        `const m = meet(C.${p.full('l')}, C.${p.full('r')})`,
    )
    if (result !== undefined)
        meetSamples(result, at).forEach((expression, i) => {
            assert(
                b,
                {
                    id: rowId(
                        'meetvalue',
                        'accept',
                        root,
                        `${text} ${expression}`,
                    ),
                    expect: 'accept',
                    after: callRow,
                },
                `const v${i}: Decoded<typeof m> = ${expression}`,
            )
        })
    b.lines.push('}')
    return { root, declarations: p.declarations, checks: b }
}

/** The samples of a codec at a path: the seeds of {@link rngFrom}. */
const SAMPLES = [1, 2, 3, 4, 5, 6] as const

/**
 * The members that a codec writes for the values it generates, in the order of the member name.
 * A value that the codec cannot generate or cannot write adds no member. The generator draws a
 * recursive union with no bound on its depth, and a draw that exhausts the stack adds no member.
 */
const writtenKeys = (codec: AnyCodec): readonly string[] => {
    const keys = new Set<string>()
    for (const seed of SAMPLES) {
        let value: unknown
        try {
            value = arbitraryOf(codec, rngFrom(seed), 3)
        } catch (error) {
            if (!(error instanceof CodecError || error instanceof RangeError))
                throw error
            continue
        }
        const written = codec.encode(value as never)
        if (failed(written)) continue
        const key = memberOf(written)
        if (key !== undefined) keys.add(key)
    }
    return [...keys].sort()
}

/* ── the files ───────────────────────────────────────────────────────────────────────────── */

/** The generated directory reaches the library two levels up. */
const library = '../../src/codec'

const codecsHeader = [
    `import type { AttributeCodec, Decoded } from '${library}/codec'`,
    `import { array, binary, boolean, decimal, discriminatedUnion, dynamoNumber, held, item, list, mdunion, never, nullValue, number, object, opaque, optional, ref, refine, scope, spread, string, undefinable, union, withLegacyRead } from '${library}/codec'`,
    `import { DynamoNumber, isNumeral, isStoredNumeral } from '${library}/attribute'`,
    `import { orThrow } from '${library}/result'`,
    `import type { Result } from '${library}/result'`,
]

const checksHeader = [
    `import type { Decoded } from '${library}/codec'`,
    `import { at, binary, boolean, decimal, dynamoNumber, exclude, extract, meet, narrow, number, object, string, union } from '${library}/codec'`,
    `import { DynamoNumber, type AttributeValue } from '${library}/attribute'`,
    `import { orThrow } from '${library}/result'`,
    "import * as C from './codecs'",
    // the keys that an attribute type admits, and a check that the type of `encode` admits one key
    'type Category<A> = A extends unknown ? keyof { [K in keyof A as A[K] extends undefined ? never : K]: 0 } : never',
    'const encodes = <A extends AttributeValue>(_at: { readonly unsafeEncode: (value: never) => A }, _key: Category<A>): void => {}',
]

/**
 * **The slice checks go to ten files**, cut at the boundary of a root. Ten files of the same
 * checks give the same errors as one file, in less time.
 */
const SLICE_FILES = [
    'slices0.ts',
    'slices1.ts',
    'slices2.ts',
    'slices3.ts',
    'slices4.ts',
    'slices5.ts',
    'slices6.ts',
    'slices7.ts',
    'slices8.ts',
    'slices9.ts',
] as const

/**
 * **The path checks go to three programs**, cut at the boundary of a root. The bridge compiles
 * the programs one after another, so its peak memory is the memory of one part. A narrowing at
 * a recursive union costs the checker more than any other check.
 */
const PATH_FILES = [
    ['paths0.ts', 'tsconfig.paths0.json'],
    ['paths1.ts', 'tsconfig.paths1.json'],
    ['paths2.ts', 'tsconfig.paths2.json'],
] as const

/**
 * **The meet checks go to their own programs**, cut at the boundary of a root. The bridge compiles
 * them beside the path programs, one after another, so the peak memory holds one program.
 */
const MEET_FILES = [['meets0.ts', 'tsconfig.meets0.json']] as const

/**
 * **The meets that the bridge puts to the checker**, the first ones in the order of the hash of the
 * pair. The type of a meet over a pair of the pool costs the checker more than a slice: all 3275
 * pairs ran a program for over an hour and past 8 GB.
 */
const MEET_ROOTS = 100

/** Each block in a file of its own lines, with its rows placed in that file. */
const placed = (
    file: string,
    header: readonly string[],
    blocks: readonly {
        readonly lines: readonly string[]
        readonly checks: readonly Check[]
    }[],
): { readonly text: string; readonly rows: readonly TypeRow[] } => {
    const lines = [...header]
    const rows: TypeRow[] = []
    for (const b of blocks) {
        const offset = lines.length
        lines.push(...b.lines)
        for (const { at, ...row } of b.checks)
            rows.push({ ...row, file, line: offset + at })
    }
    lines.push('')
    return { text: lines.join('\n'), rows }
}

/** The blocks cut into `parts` runs of about one size, in order. */
const split = <B extends { readonly lines: readonly string[] }>(
    blocks: readonly B[],
    parts: number,
): readonly (readonly B[])[] => {
    const total = blocks.reduce((n, b) => n + b.lines.length, 0)
    const out: B[][] = Array.from({ length: parts }, () => [])
    let seen = 0
    for (const b of blocks) {
        const part = Math.min(parts - 1, Math.floor((seen * parts) / total))
        out[part]?.push(b)
        seen += b.lines.length
    }
    return out
}

const tsconfig = (files: readonly string[]): string =>
    `${JSON.stringify(
        {
            extends: '../../tsconfig.json',
            compilerOptions: {
                rootDir: '../..',
                composite: false,
                declaration: false,
                declarationMap: false,
                noEmit: true,
                incremental: false,
                noUnusedLocals: false,
                noUnusedParameters: false,
            },
            files,
            include: [],
        },
        null,
        2,
    )}\n`

/** Each item once, by the hash of its identity, in the order of the hash. */
const byHash = <T>(
    items: readonly T[],
    identity: (item: T) => string,
): readonly (readonly [string, T])[] => {
    const out = new Map<string, T>()
    for (const item of items) {
        const root = hash(identity(item))
        if (!out.has(root)) out.set(root, item)
    }
    return [...out].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
}

/**
 * **The type vectors of the pool**: the codecs, the slice checks in ten files, the path checks in
 * three files, the rows, and one compiler configuration for the slice program and for each path
 * program.
 *
 * **The roots go in the order of their hash**, so the files depend on the set of roots and not
 * on the order of the pool. A root that the printer refuses throws: the roots share constants,
 * so a root that stops halfway leaves constants that no check reads.
 */
export const typeVectorFiles = ({
    slices,
    paths,
    meets,
    clauses,
}: {
    readonly slices: readonly Slice[]
    readonly paths: readonly PathVectors[]
    readonly meets: readonly MeetPair[]
    readonly clauses: readonly (() => AnyCodec)[]
}): readonly (readonly [string, string])[] => {
    /** The meets whose two factors print as library calls, each once by the identity of its pair. */
    const printable = byHash(
        meets.flatMap((pair) => {
            try {
                const scratch = shared([pair.left.def, pair.right.def])
                const p = printerOf(scratch, 'x', 'meet')
                p.constant('l', 'left', pair.left.def)
                p.constant('r', 'right', pair.right.def)
                return [pair]
            } catch (error) {
                if (
                    !(
                        error instanceof TypeUnemittable ||
                        error instanceof LeanUnemittable
                    )
                )
                    throw error
                return []
            }
        }),
        (pair) =>
            `meet|${leanClosedOf(pair.left, 'meet', freshBound())}|${leanClosedOf(pair.right, 'meet', freshBound())}`,
    )
    const constants = shared([
        ...slices.flatMap((s) => [
            s.codec.def,
            ...(s.codec.def.kind === 'union' ? s.codec.def.options : []),
        ]),
        ...paths.map((v) => v.codec.def),
        ...printable
            .slice(0, MEET_ROOTS)
            .flatMap(([, pair]) => [pair.left.def, pair.right.def]),
    ])
    const sliceRoots = byHash(
        slices,
        (s) =>
            `slice|${(s.keys ?? []).join(',')}|${leanClosedOf(s.codec, 'slice', freshBound())}`,
    ).map(([root, s], i) =>
        sliceRoot(s, printerOf(constants, `s${i}`, s.name), root, clauses),
    )
    const pathRoots = byHash(
        paths,
        // the term and not `leanPath`'s print, which holds the rows: a root keeps its id when the
        // pool draws another set of paths at it
        (v) => `path|${leanClosedOf(v.codec, 'path', freshBound())}`,
    ).map(([root, v], i) =>
        pathRoot(v, printerOf(constants, `p${i}`, v.name), root),
    )
    const meetRoots = printable
        .slice(0, MEET_ROOTS)
        .map(([root, pair], i) =>
            meetRoot(
                pair,
                met(pair),
                printerOf(constants, `m${i}`, 'meet'),
                root,
                'meet',
            ),
        )
    const codecs = placed(
        'codecs.ts',
        codecsHeader,
        [...sliceRoots, ...pathRoots, ...meetRoots].map(({ declarations }) => ({
            lines: declarations.map((d) => d.line),
            checks: declarations.map((d, i) => ({
                id: rowId('declaration', 'accept', hash(d.content), d.kind),
                expect: 'accept' as const,
                at: i + 1,
            })),
        })),
    )
    const parts = split(
        sliceRoots.map((r) => r.checks),
        SLICE_FILES.length,
    )
    const sliceFiles = SLICE_FILES.map((file, i) => ({
        file,
        ...placed(file, checksHeader, parts[i] ?? []),
    }))
    const pathParts = split(
        pathRoots.map((r) => r.checks),
        PATH_FILES.length,
    )
    const pathFiles = PATH_FILES.map(([file], i) => ({
        file,
        ...placed(file, checksHeader, pathParts[i] ?? []),
    }))
    const meetParts = split(
        meetRoots.map((r) => r.checks),
        MEET_FILES.length,
    )
    const meetFiles = MEET_FILES.map(([file], i) => ({
        file,
        ...placed(file, checksHeader, meetParts[i] ?? []),
    }))
    const rows = [
        ...codecs.rows,
        ...sliceFiles.flatMap((f) => f.rows),
        ...pathFiles.flatMap((f) => f.rows),
        ...meetFiles.flatMap((f) => f.rows),
    ]
    // two declarations of one content share one id; each check has an id of its own
    const checks = rows.filter((r) => !r.id.startsWith('declaration|'))
    if (new Set(checks.map((r) => r.id)).size !== checks.length)
        throw new Error(
            'two type rows share one id: a root prints one check twice',
        )
    return [
        ['codecs.ts', codecs.text],
        ...sliceFiles.map((f) => [f.file, f.text] as const),
        ...pathFiles.map((f) => [f.file, f.text] as const),
        ...meetFiles.map((f) => [f.file, f.text] as const),
        [
            'rows.json',
            `[\n${rows.map((r) => JSON.stringify(r)).join(',\n')}\n]\n`,
        ],
        [
            'tsconfig.slices0.json',
            tsconfig(['codecs.ts', ...SLICE_FILES.slice(0, 5)]),
        ],
        [
            'tsconfig.slices1.json',
            tsconfig(['codecs.ts', ...SLICE_FILES.slice(5)]),
        ],
        ...[...PATH_FILES, ...MEET_FILES].map(
            ([file, config]) =>
                [config, tsconfig(['codecs.ts', file])] as const,
        ),
    ]
}
