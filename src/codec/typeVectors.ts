/**
 * Type vectors: the static types of `extract`, `exclude` and `at`, against the run time.
 *
 * The emitter in `lean.ts` puts each decision of the run time to the model. This module puts the
 * same decisions to the type checker. Each root of the pool prints as library calls in a generated
 * TypeScript file. Each check states one decision of the run time as one line. Where the run time
 * accepts, the line compiles. Where the run time refuses, the line sits under `@ts-expect-error`.
 * A refused path row has no directive: the checker reads the error of its line, so the one compile
 * gives the verdict and the site. The checker in `formal/scripts/type_bridge.py` compiles the files, maps each error to its row,
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
 * A foreign root is a codec and a value of another kind, such as a number where the codec decodes
 * a string. The run time refuses the value, so the `decoded` row is a `refuse` row: the value
 * sits under `@ts-expect-error`, and a type that widened `Decoded` to `unknown` would accept it.
 * The pool rows are `accept` rows, and `unknown` admits each of them, so only a foreign root sees
 * the widening.
 *
 * A path row where the run time resolves has a `decoded` row. The row checks that a value which the
 * run-time codec at the path decodes is assignable to the decoded type of the call. The `encoded`
 * rows check only the names of the attributes that the codec writes. The value is one draw of the
 * codec, printed as a literal. A codec that draws no value gives no row: the path row stays, and the
 * pool spec pins the count of each. A value that has no literal throws {@link TypeUnemittable}.
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
import { isDeepStrictEqual } from 'node:util'
import { DynamoNumber, isNumeral, isStoredNumeral, memberOf } from './attribute'
import { codecOfTerm } from './capabilities'
import type { AnyCodec } from './codec'
import { boolean, legacy, meet, object, string, union } from './codec'
import type { PathStep, PathVectors, Slice } from './lean'
import { hostAt, LeanUnemittable, leanClosedOf, reachable } from './lean'
import { CodecError, failed } from './result'
import type { Literal, Term } from './term'
import {
    componentsOf,
    type Field,
    ground,
    leafKinds,
    resolvedTerm,
    sameTerm,
    targetOf,
    unionAlternatives,
} from './term'
import { arbitraryOf, rngFrom } from './testing'
import { own } from './value'

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
    readonly after?: string | readonly string[]
    /** A refusal with no directive on the line before: the error of the line is the verdict. */
    readonly bare?: boolean
    /** The 1-based column of the line where the first error of a bare row must start. */
    readonly hop?: number
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
    return call && `${ground[call.base].ctor}(${call.args})`
}

const optionsOf = (t: Term): readonly Term[] =>
    t.kind === 'union' ? t.options : [t]

/** The string literals of a term, or nothing where an option is no string literal. */
const stringLiterals = (t: Term): readonly string[] | undefined => {
    const alts = unionAlternatives(optionsOf(t))
    return alts?.base === 'string' ? alts.ls : undefined
}

/** The numeric literals of a term, as JS numbers, or nothing where an option is no numeral. */
const numberLiterals = (t: Term): readonly number[] | undefined => {
    const alts = unionAlternatives(optionsOf(t))
    return alts?.base === 'number'
        ? alts.ls.map((one) => Number(String(one)))
        : undefined
}

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
        const node = resolvedTerm(t)
        return node === undefined || node.kind === 'ref'
            ? refuse(at, 'a chain of thunks that returns no term')
            : node
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
            case 'number':
            case 'boolean':
            case 'binary':
            case 'null':
                return ground[t.kind].ctor
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
                if (t.via === 'native') return 'native'
                if (t.via === 'float') {
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
                return `legacy({ current: ${sub(t.inner)}, older: { decode: (): never => { throw new Error('older') } } })`
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
                    if (f.mark === 'fill')
                        return `${keyText(k)}: fill(${x}, ${valueText(f.v, at)})`
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
        /** A term, written in place. */
        term: inline,
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

/** A refusal that no directive hides: the checker reads the error of the line and where it starts. */
const assertBare = (b: Block, row: Omit<Check, 'at'>, text: string): void => {
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

/** The seeds of the values that a member draws. The same seeds give the same rows. */
const VALUE_SEEDS = 40

/** The distinct values that an option draws, with their literals: one draw of the option for all its rows. */
const drawsOfOption = new WeakMap<
    Term,
    readonly { readonly value: unknown; readonly text: string }[]
>()
const drawn = (option: Term, root: string) => {
    const known = drawsOfOption.get(option)
    if (known !== undefined) return known
    const codec = codecOfTerm(option)
    const seen = new Set<string>()
    const draws: { readonly value: unknown; readonly text: string }[] = []
    for (let seed = 1; seed <= VALUE_SEEDS; seed++) {
        try {
            const value = arbitraryOf(codec, rngFrom(seed), 2)
            const text = valueText(value, `${root} value`)
            if (seen.has(text)) continue
            seen.add(text)
            draws.push({ value, text })
        } catch (error) {
            // a codec that cannot draw (an adapter that refuses its inner values), or a recursive option that
            // has no finite draw (the draw overflows the stack), has no value to state
            if (
                error instanceof CodecError ||
                error instanceof TypeUnemittable ||
                error instanceof RangeError
            )
                continue
            throw error
        }
    }
    drawsOfOption.set(option, draws)
    return draws
}

/**
 * The values of an option that the slice keeps and that the slice refuses, each as a literal, for a
 * member whose drawn values lie on both sides of the narrowing. The member row states all values of
 * the option, and its verdict is right: a slice that keeps a narrowed copy of the option does not
 * keep the option. A type that is too narrow still refuses the values that the slice keeps, and the
 * member row cannot see it, so a value row states one value. A value is kept where the sliced codec
 * encodes it and the decode of the stored value gives the value back. A value is refused where
 * `encode` gives a `CodecError` value. A member whose drawn values all lie on one side has no value
 * row: the member row states that verdict.
 */
const valuesOf = (
    run: AnyCodec,
    option: Term,
    root: string,
): readonly { readonly keeps: boolean; readonly text: string }[] => {
    const values: { readonly keeps: boolean; readonly text: string }[] = []
    for (const { value, text } of drawn(option, root)) {
        const stored = run.encode(value as never)
        if (failed(stored)) {
            values.push({ keeps: false, text })
            continue
        }
        const back = run.decode(stored as never)
        if (!failed(back) && isDeepStrictEqual(back, value))
            values.push({ keeps: true, text })
    }
    return values.some((v) => v.keeps) && values.some((v) => !v.keeps)
        ? values
        : []
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
        // any other term pins no string literal
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
        // any other term is not the base `boolean`
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
    // an older reading around the object of one name: the opening reads through it, as it reads
    // through the plain pattern
    const [first] = literal
    const firstLiteral = first?.[1][0]
    if (first !== undefined && firstLiteral !== undefined) {
        const read = legacy({
            current: member(first[0], stringOf(firstLiteral)),
            older: {
                decode: (): never => {
                    throw new Error('older')
                },
            },
        })
        const source = clause(read)
        out.push({ argument: source, source, codec: read })
    }
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
            o.kind === 'object' ? own(o.body.fields, name) : undefined
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
    // the row of the dissection line: a row that reads a root that the type refuses has no verdict
    let dissection: string | undefined
    if (key !== undefined) {
        p.line(
            `dissection ${keys.join(',')}`,
            def,
            `export const ${p.full('root')} = ${keys.length === 1 ? `discriminatedUnion(${quoted(key)}, ${list})` : `mdunion([${keys.map(quoted).join(', ')}], ${list})`}`,
        )
        const line = p.declarations.at(-1)
        if (line !== undefined)
            dissection = rowId(
                'declaration',
                'accept',
                hash(line.content),
                line.kind,
            )
    }
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
    for (const shape of slice.shapes ?? []) {
        const codec = object(shape)
        const fields = codec.def.kind === 'object' ? codec.def.body.fields : {}
        const slot = (name: string, f: Field): string => {
            const text = p.term(f.t)
            switch (f.mark) {
                case 'req':
                    return text
                case 'optional':
                case 'undefinable':
                    return `${f.mark}(${text})`
                case 'fill':
                    return refuse(name, 'a fill slot in a pattern shape')
            }
        }
        const argument = `{ ${Object.entries(fields)
            .map(([name, f]) => `${keyText(name)}: ${slot(name, f)}`)
            .join(', ')} }`
        patterns.push({ argument, source: `object(${argument})`, codec })
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
                    ...(dissection === undefined ? {} : { after: dissection }),
                },
                `const r = ${op}(C.${p.full('root')}, ${pattern.source})`,
            )
            if (kept !== undefined) {
                const after =
                    dissection === undefined ? callRow : [callRow, dissection]
                const run = slice.codec[op](pattern.codec)
                keptOptions(options, kept).forEach((keeps, i) => {
                    const expect = keeps ? 'accept' : 'refuse'
                    assert(
                        b,
                        {
                            id: rowId(op, expect, root, `${text} member ${i}`),
                            expect,
                            after,
                        },
                        `const m${i}: Decoded<typeof r> = C.${p.full(`m${i}`)}`,
                    )
                    valuesOf(run, options[i] as Term, root).forEach(
                        (value, n) => {
                            const verdict = value.keeps ? 'accept' : 'refuse'
                            assert(
                                b,
                                {
                                    id: rowId(
                                        'value',
                                        verdict,
                                        root,
                                        `${text} member ${i} value ${n}`,
                                    ),
                                    expect: verdict,
                                    after,
                                },
                                `const v${i}_${n}: Decoded<typeof r> = ${value.text}`,
                            )
                        },
                    )
                })
            }
            b.lines.push('}')
        }
    return { root, declarations: p.declarations, checks: b }
}

/** One draw of the codec as a literal, or nothing where the codec draws no value. */
const decodedSample = (codec: AnyCodec, root: string): string | undefined => {
    try {
        return valueText(arbitraryOf(codec, rngFrom(1), 2), `${root} decoded`)
    } catch (error) {
        if (error instanceof CodecError) return undefined
        throw error
    }
}

/**
 * Whether the decoded type of the term is `unknown`: the term is `opaque`, or a union with an
 * `opaque` option, or a `legacy` over such a term, each read through a `ref` to its target. `unknown`
 * absorbs a union, so one option decides. The reading is of the term and not of what `encode` writes,
 * because a codec that writes much can still have a type that refuses a value, and such a codec owes
 * a row. A union that names itself through a `ref` is read once.
 */
const decodesUnknown = (term: Term, seen = new Set<Term>()): boolean => {
    const t = resolvedTerm(term)
    if (t === undefined || seen.has(t)) return false
    seen.add(t)
    return (
        t.kind === 'opaq' ||
        (t.kind === 'union' &&
            t.options.some((option) => decodesUnknown(option, seen))) ||
        (t.kind === 'legacy' && decodesUnknown(t.inner, seen))
    )
}

/**
 * A value that the codec at a path refuses and that its decoded type does not admit, or nothing. The
 * value is a number where the draw is no number and the numeral `'1'` where it is one, so the kind
 * differs from the kind that the codec decodes. The run time confirms the refusal, because a union
 * of the two kinds writes the value and is no row.
 *
 * **A codec that decodes `unknown` gives no row.** `opaque` refuses the JS number `1`, because it
 * holds a number exactly as a `DynamoNumber`, and it writes every other kind. That is a rule of
 * value over one kind. TypeScript has no type for "unknown except a number", so `Decoded` of
 * `opaque` is `unknown` by force of the compiler, and no type can refuse the number. A row there
 * would count a limit of the host language as a defect of the type of `at`.
 */
const foreignAt = (codec: AnyCodec): number | string | undefined => {
    if (decodesUnknown(codec.def)) return undefined
    let drawn: unknown
    try {
        drawn = arbitraryOf(codec, rngFrom(1), 2)
    } catch (error) {
        if (error instanceof CodecError) return undefined
        throw error
    }
    const foreign = typeof drawn === 'number' ? '1' : 1
    return failed(codec.encode(foreign as never)) ? foreign : undefined
}

/**
 * **The number of steps of the shortest prefix where the walk of `at` gives none**, or nothing.
 * The model's fold gives none where a segment has no answer: the host decision of the prefix is
 * `vacant` or `refused`. Such a prefix refuses at its last step, and each longer prefix refuses
 * too, so the first one is the hop that the path cannot take. A path of the kind `someVariants`
 * or `ambiguous` gives none at no prefix: the fold reaches a frontier, and the refusal is on use.
 * Another prefix may be in those kinds and a longer path leaves them, so those kinds find no hop.
 */
const noneAt = (
    codec: AnyCodec,
    path: readonly PathStep[],
): number | undefined => {
    for (let n = 1; n <= path.length; n++) {
        const at = hostAt(codec, path.slice(0, n)).kind
        if (at === 'vacant' || at === 'refused') return n
    }
    return undefined
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
     * one codec stands at the place. The text comes with the offset of each step, which is the
     * start of an element of a tuple or of the object of a clause, and with the offset of the last
     * tuple. A refusal on use starts at the last tuple.
     */
    const spelled = (path: readonly PathStep[]) => {
        let call = `C.${p.full('w')}`
        let offsets: number[] = []
        let run: { text: string; step: number }[] = [
            { text: quoted('r'), step: -1 },
        ]
        // the offsets of the elements of a run, from the start of the first element
        const placed = (from: number, into: number[]): void => {
            let at = from
            for (const { text, step } of run) {
                if (step >= 0) into[step] = at
                at += text.length + ', '.length
            }
        }
        path.forEach((s, step) => {
            if (typeof s !== 'object') {
                run.push({
                    text: typeof s === 'number' ? String(s) : quoted(s),
                    step,
                })
                return
            }
            const clause = Object.entries(s.narrow.spec)
                .map(([k, c]) => `${keyText(k)}: ${p.clause(c)}`)
                .join(', ')
            const head = run.length === 0 ? 'narrow(' : 'narrow(at('
            const tuple = run.map((r) => r.text).join(', ')
            const mid = run.length === 0 ? '' : `, [${tuple}])`
            const moved = offsets.map((o) => o + head.length)
            placed(head.length + call.length + ', ['.length, moved)
            moved[step] = head.length + call.length + mid.length + ', '.length
            call = `${head}${call}${mid}, object({ ${clause} }))`
            offsets = moved
            run = []
        })
        const head = 'at('
        const moved = offsets.map((o) => o + head.length)
        placed(head.length + call.length + ', ['.length, moved)
        return {
            call: `at(${call}, [${run.map((r) => r.text).join(', ')}])`,
            offsets: moved,
            tuple: head.length + call.length + ', '.length,
        }
    }
    const b = block()
    for (const path of vectors.paths) {
        const host = hostAt(vectors.codec, path)
        const expect = host.kind === 'resolved' ? 'accept' : 'refuse'
        const spelling = spelled(path)
        const call = spelling.call
        const text = call
        const id = rowId('path', expect, root, text)
        if (expect === 'accept') assert(b, { id, expect }, call)
        else {
            const none = noneAt(vectors.codec, path)
            const start =
                (none === undefined ? undefined : spelling.offsets[none - 1]) ??
                spelling.tuple
            assertBare(b, { id, expect, bare: true, hop: start + 1 }, call)
        }
        if (host.kind !== 'resolved') continue
        const sample = decodedSample(host.codec, root)
        if (sample !== undefined)
            assert(
                b,
                {
                    id: rowId(
                        'decoded',
                        'accept',
                        root,
                        `${text} ${hash(sample)}`,
                    ),
                    expect: 'accept',
                    after: id,
                },
                `{ const c = ${call}; const d: Decoded<typeof c> = ${sample}; void d }`,
            )
        // the decoded type of the codec at the path refuses a value of another kind, which `unknown` would admit
        const foreign = foreignAt(host.codec)
        if (foreign !== undefined)
            assert(
                b,
                {
                    id: rowId(
                        'decoded',
                        'refuse',
                        root,
                        `${text} foreign ${String(foreign)}`,
                    ),
                    expect: 'refuse',
                    after: id,
                },
                `{ const c = ${call}; const d: Decoded<typeof c> = ${valueText(foreign, `${root} foreign`)}; void d }`,
            )
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
export type MeetPair = {
    readonly left: AnyCodec
    readonly right: AnyCodec
    /** A pinned pair keeps a root beside the first {@link MEET_ROOTS}, whatever its hash. */
    readonly pinned?: boolean
}

/** A codec and a value of another kind, which no decoded type of the codec admits. */
export type ForeignSample = {
    readonly codec: AnyCodec
    /** A value that the codec refuses, and that the decoded type of the codec does not admit. */
    readonly sample: unknown
}

/**
 * One foreign sample: the codec as a constant, and the value as a `refuse` row of the `decoded`
 * group. The value must be one that the run time refuses, so the verdict is the answer of the run
 * time and not an assumption.
 */
const foreignRoot = (
    foreign: ForeignSample,
    p: ReturnType<typeof printerOf>,
    root: string,
): Root => {
    if (!failed(foreign.codec.encode(foreign.sample as never)))
        refuse(root, 'a foreign sample that the codec writes')
    p.constant('c', 'foreign', foreign.codec.def)
    const sample = valueText(foreign.sample, `${root} foreign`)
    const b = block()
    b.lines.push('{')
    assert(
        b,
        {
            id: rowId(
                'decoded',
                'refuse',
                root,
                `Decoded of the codec = ${sample}`,
            ),
            expect: 'refuse',
        },
        `const d: Decoded<typeof C.${p.full('c')}> = ${sample}`,
    )
    b.lines.push('}')
    return { root, declarations: p.declarations, checks: b }
}

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
    `import { array, binary, boolean, decimal, discriminatedUnion, fill, held, item, legacy, list, mdunion, never, nullValue, number, object, opaque, optional, ref, refine, scope, spread, string, undefinable, union } from '${library}/codec'`,
    `import { dynamoNumber } from '${library}/prisms'`,
    `import { DynamoNumber, isNumeral, isStoredNumeral } from '${library}/attribute'`,
    `import { native } from '${library}/native'`,
    `import { orThrow } from '${library}/result'`,
    `import type { Result } from '${library}/result'`,
]

const checksHeader = [
    `import type { Decoded } from '${library}/codec'`,
    `import { array, at, binary, boolean, decimal, exclude, extract, fill, legacy, list, meet, narrow, number, object, opaque, optional, spread, string, undefinable, union } from '${library}/codec'`,
    `import { dynamoNumber } from '${library}/prisms'`,
    `import { DynamoNumber, type AttributeValue } from '${library}/attribute'`,
    `import { native } from '${library}/native'`,
    `import { orThrow } from '${library}/result'`,
    "import * as C from './codecs'",
    // the keys that an attribute type admits, and a check that the type of `encode` admits one key
    'type Category<A> = A extends unknown ? keyof { [K in keyof A as A[K] extends undefined ? never : K]: 0 } : never',
    'const encodes = <A extends AttributeValue>(_at: { readonly unsafeEncode: (value: never) => A }, _key: Category<A>): void => {}',
]

/**
 * **The slice checks go to ten files**, cut at the boundary of a root. Ten files of the same
 * checks give the same errors as one file, in less time. Each file is one program, so the peak
 * memory holds one part: two programs of five files passed the heap of the checker.
 */
const SLICE_PROGRAMS = [
    ['slices0.ts', 'tsconfig.slices0.json'],
    ['slices1.ts', 'tsconfig.slices1.json'],
    ['slices2.ts', 'tsconfig.slices2.json'],
    ['slices3.ts', 'tsconfig.slices3.json'],
    ['slices4.ts', 'tsconfig.slices4.json'],
    ['slices5.ts', 'tsconfig.slices5.json'],
    ['slices6.ts', 'tsconfig.slices6.json'],
    ['slices7.ts', 'tsconfig.slices7.json'],
    ['slices8.ts', 'tsconfig.slices8.json'],
    ['slices9.ts', 'tsconfig.slices9.json'],
] as const
const SLICE_FILES = SLICE_PROGRAMS.map(([file]) => file)

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
    foreign,
    clauses,
}: {
    readonly slices: readonly Slice[]
    readonly paths: readonly PathVectors[]
    readonly meets: readonly MeetPair[]
    readonly foreign: readonly ForeignSample[]
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
    const meetRootsOf = [
        ...printable.filter(([, pair]) => pair.pinned),
        ...printable.filter(([, pair]) => !pair.pinned).slice(0, MEET_ROOTS),
    ]
    const constants = shared([
        ...slices.flatMap((s) => [
            s.codec.def,
            ...(s.codec.def.kind === 'union' ? s.codec.def.options : []),
        ]),
        ...paths.map((v) => v.codec.def),
        ...meetRootsOf.flatMap(([, pair]) => [pair.left.def, pair.right.def]),
        ...foreign.map((v) => v.codec.def),
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
    const meetRoots = meetRootsOf.map(([root, pair], i) =>
        meetRoot(
            pair,
            met(pair),
            printerOf(constants, `m${i}`, 'meet'),
            root,
            'meet',
        ),
    )
    const foreignRoots = byHash(
        foreign,
        (v) =>
            `foreign|${valueText(v.sample, 'foreign')}|${leanClosedOf(v.codec, 'foreign', freshBound())}`,
    ).map(([root, v], i) =>
        foreignRoot(v, printerOf(constants, `f${i}`, 'foreign'), root),
    )
    const codecs = placed(
        'codecs.ts',
        codecsHeader,
        [...sliceRoots, ...pathRoots, ...meetRoots, ...foreignRoots].map(
            ({ declarations }) => ({
                lines: declarations.map((d) => d.line),
                checks: declarations.map((d, i) => ({
                    id: rowId('declaration', 'accept', hash(d.content), d.kind),
                    expect: 'accept' as const,
                    at: i + 1,
                })),
            }),
        ),
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
        [...meetRoots, ...foreignRoots].map((r) => r.checks),
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
        ...[...SLICE_PROGRAMS, ...PATH_FILES, ...MEET_FILES].map(
            ([file, config]) =>
                [config, tsconfig(['codecs.ts', file])] as const,
        ),
    ]
}
