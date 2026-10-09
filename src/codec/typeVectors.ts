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
 * name of an option. A path root is a codec, with each path into the codec under `at`. The roots
 * go in the order of the hash of their Lean print, so a reorder of the pool moves no line and no
 * row id.
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
import { DynamoNumber, isNumeral, isStoredNumeral } from './attribute'
import type { AnyCodec } from './codec'
import { number } from './codec'
import { codecOfTerm } from './denote'
import type { PathStep, PathVectors, Slice } from './lean'
import { hostAt, leanTermOf, reachable } from './lean'
import { CodecError } from './result'
import type { Literal, Term } from './term'
import { force, sameTerm } from './term'

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
    if (v instanceof Set) {
        const members: readonly unknown[] = [...v]
        return `new Set([${members.map((x) => valueText(x, at)).join(', ')}])`
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

type Lazy = Extract<Term, { readonly kind: 'lazy' }>

const binderCache = new Map<Term, boolean>()

/** A thunk that closes a cycle: its target reaches the thunk again. */
const isBinder = (t: Term): t is Lazy => {
    if (t.kind !== 'lazy') return false
    let hit = binderCache.get(t)
    if (hit === undefined) {
        const target = force(t)
        hit = target !== undefined && reachable(target).has(t)
        binderCache.set(t, hit)
    }
    return hit
}

const containsBinder = (t: Term): boolean => [...reachable(t)].some(isBinder)

/** The terms that a term reaches without a thunk: the references that a declaration reads at once. */
const directly = (root: Term): Term[] => {
    const seen = new Set<Term>()
    const walk = (t: Term): void => {
        if (seen.has(t)) return
        seen.add(t)
        switch (t.kind) {
            case 'list':
                for (const one of [...t.pre, ...t.suf]) walk(one)
                if (t.spread !== undefined) walk(t.spread)
                return
            case 'object':
                for (const field of Object.values(t.body.fields)) walk(field.t)
                if (t.body.rest !== undefined) walk(t.body.rest)
                return
            case 'union':
                return t.options.forEach(walk)
            case 'set':
                return walk(t.elem)
            case 'held':
                walk(t.inner)
                return walk(t.outer)
            case 'refine':
            case 'legacy':
                return walk(t.inner)
            default:
                return
        }
    }
    walk(root)
    return [...seen]
}

/** A term that prints as a name of the library, and is declared by no constant. */
const leafKinds: ReadonlySet<Term['kind']> = new Set([
    'string',
    'number',
    'boolean',
    'binary',
    'null',
    'opaq',
    'never',
])

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
    readonly binders: Map<Term, string>
    readonly adapters: Map<unknown, string>
    readonly predicates: Map<unknown, string>
}

const shared = (): Shared => ({
    names: new Map(),
    state: new Map(),
    binders: new Map(),
    adapters: new Map(),
    predicates: new Map(),
})

/**
 * **The declarations of one root.** Each term object declares one constant, so a term that two
 * places share stays one object in the print. Every cycle passes a thunk, so the direct references
 * form no cycle. A thunk names its target and leaves the target pending, so the thunk is declared
 * before each term that refers to the thunk directly.
 */
const printerOf = (
    { names, state, binders, adapters, predicates }: Shared,
    prefix: string,
    at: string,
) => {
    const declarations: Declaration[] = []
    const pending: Term[] = []
    let fresh = 0

    const full = (local: string): string => `${prefix}_${local}`
    const declare = (kind: string, content: string, line: string): void => {
        declarations.push({ kind, content, line })
    }
    /** The Lean print of a term: the content of a declaration, whichever root declares it. */
    const lean = (t: Term): string =>
        leanTermOf(codecOfTerm(t), at, freshBound())
    const nameOf = (t: Term): string => {
        let n = names.get(t)
        if (n === undefined) {
            n = full(`h${fresh++}`)
            names.set(t, n)
        }
        return n
    }
    const ref = (t: Term): string => {
        if (leafKinds.has(t.kind)) return print(t, ref)
        const n = nameOf(t)
        if (state.has(t)) return n
        state.set(t, 'progress')
        const body = print(t, ref)
        declare('constant', lean(t), `export const ${n} = ${body}`)
        state.set(t, 'done')
        // a former forces a thunk at its declaration, so the target follows the thunk at once
        if (t.kind === 'lazy') {
            const target = force(t)
            if (target === undefined) return n
            if (directly(target).some((u) => state.get(u) === 'progress'))
                pending.push(target)
            else ref(target)
        }
        return n
    }

    const drain = (): void => {
        for (let t = pending.pop(); t !== undefined; t = pending.pop())
            if (!state.has(t)) ref(t)
    }

    /** The decoded type of a term, as a type expression. */
    const typeText = (t: Term): string => {
        if (!containsBinder(t)) return `Decoded<typeof ${ref(t)}>`
        switch (t.kind) {
            case 'lazy': {
                if (isBinder(t)) return binder(t)
                const target = force(t)
                return target === undefined
                    ? refuse(at, 'a thunk that throws, in a type')
                    : typeText(target)
            }
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
                return t.body.rest === undefined
                    ? body
                    : `(${body} & { readonly [name: string]: ${typeText(t.body.rest)} })`
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

    /** A thunk that closes a cycle: its decoded type, declared once, before its body is read. */
    const binder = (t: Lazy): string => {
        const seen = binders.get(t)
        if (seen !== undefined) return seen
        const local = `R${fresh++}`
        binders.set(t, full(local))
        const target = force(t)
        if (target === undefined)
            return refuse(at, 'a binder whose thunk throws')
        declare(
            'type',
            lean(t),
            `export type ${full(local)} = ${typeText(target)}`,
        )
        return full(local)
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
                if (t.q.kind !== 'closure')
                    return refuse(at, 'a refinement by members')
                const is = t.q.q.is
                // the shipped predicates return a boolean, and `refine` takes a type predicate
                if (is === isNumeral)
                    return `refine(${sub(t.inner)}, (s: string): s is string => isNumeral(s))`
                if (is === isStoredNumeral)
                    return `refine(${sub(t.inner)}, (s: string): s is string => isStoredNumeral(s))`
                return `refine(${sub(t.inner)}, ${predicateOf(is)})`
            }
            case 'legacy':
                return `withLegacyRead({ current: ${sub(t.inner)}, older: { decode: (): never => { throw new Error('older') } } })`
            case 'lazy': {
                const target = force(t)
                if (target === undefined)
                    return "lazy((): never => { throw new ReferenceError('undeclared') })"
                if (sub !== ref) {
                    if (isBinder(t)) return refuse(at, 'a binder in a clause')
                    return `lazy(() => ${sub(target)})`
                }
                const name = leafKinds.has(target.kind)
                    ? print(target, sub)
                    : nameOf(target)
                if (!leafKinds.has(target.kind)) pending.push(target)
                if (isBinder(t))
                    return `lazy((): AttributeCodec<${binder(t)}> => ${name})`
                return `lazy(() => ${name})`
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
            drain()
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

/** The run-time slice, or nothing where the run time refuses the clause. */
const sliced = (
    run: (clause: Readonly<Record<string, AnyCodec>>) => AnyCodec,
    clause: Readonly<Record<string, AnyCodec>>,
): readonly Term[] | undefined => {
    try {
        return membersOf(run(clause).def)
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
    // a union names the drawn union itself, so a thunk that returns the union returns this one
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
    for (const name of names)
        for (const make of vocabulary)
            for (const op of ['extract', 'exclude'] as const) {
                const clause = { [name]: make() }
                const text = `${op}({ ${keyText(name)}: ${p.clause(make())} })`
                const kept = sliced(slice.codec[op], clause)
                const call = rowId(
                    'call',
                    kept === undefined ? 'refuse' : 'accept',
                    root,
                    text,
                )
                b.lines.push('{')
                assert(
                    b,
                    {
                        id: call,
                        expect: kept === undefined ? 'refuse' : 'accept',
                    },
                    `const r = C.${p.full('root')}.${text}`,
                )
                if (kept !== undefined)
                    keptOptions(options, kept).forEach((keeps, i) => {
                        const expect = keeps ? 'accept' : 'refuse'
                        assert(
                            b,
                            {
                                id: rowId(
                                    op,
                                    expect,
                                    root,
                                    `${text} member ${i}`,
                                ),
                                expect,
                                after: call,
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
        `export const ${p.full('w')} = object({ r: optional(${p.full('root')}) }).item`,
    )
    const stepText = (s: PathStep): string =>
        typeof s === 'number'
            ? `.at(${s})`
            : typeof s === 'string'
              ? /^[A-Za-z_$][\w$]*$/.test(s)
                  ? `.${s}`
                  : `[${quoted(s)}]`
              : `.narrow({ ${Object.entries(s.narrow)
                    .map(([k, c]) => `${keyText(k)}: ${p.clause(c)}`)
                    .join(', ')} })`
    const b = block()
    for (const path of vectors.paths) {
        const expect =
            hostAt(vectors.codec, path).kind === 'resolved'
                ? 'accept'
                : 'refuse'
        const text = `r${path.map(stepText).join('')}`
        assert(
            b,
            { id: rowId('path', expect, root, text), expect },
            `C.${p.full('w')}.at((p) => p.${text})`,
        )
    }
    return { root, declarations: p.declarations, checks: b }
}

/* ── the files ───────────────────────────────────────────────────────────────────────────── */

/** The generated directory reaches the library two levels up. */
const library = '../../src/codec'

const codecsHeader = [
    `import type { AttributeCodec, Decoded } from '${library}/codec'`,
    `import { array, binary, boolean, decimal, discriminatedUnion, dynamoNumber, held, lazy, list, mdunion, never, nullValue, number, object, opaque, optional, refine, spread, string, undefinable, union, withLegacyRead } from '${library}/codec'`,
    `import { DynamoNumber, isNumeral, isStoredNumeral } from '${library}/attribute'`,
    `import { orThrow } from '${library}/result'`,
    `import type { Result } from '${library}/result'`,
]

const checksHeader = [
    `import type { Decoded } from '${library}/codec'`,
    `import { binary, boolean, decimal, dynamoNumber, number, string } from '${library}/codec'`,
    `import { DynamoNumber } from '${library}/attribute'`,
    `import { orThrow } from '${library}/result'`,
    "import * as C from './codecs'",
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
 * **The type vectors of the pool**: the codecs, the slice checks in ten files, the path checks,
 * the rows, and one compiler configuration for each of the two programs.
 *
 * **The roots go in the order of their hash**, so the files depend on the set of roots and not
 * on the order of the pool. A root that the printer refuses throws: the roots share constants,
 * so a root that stops halfway leaves constants that no check reads.
 */
export const typeVectorFiles = ({
    slices,
    paths,
    clauses,
}: {
    readonly slices: readonly Slice[]
    readonly paths: readonly PathVectors[]
    readonly clauses: readonly (() => AnyCodec)[]
}): readonly (readonly [string, string])[] => {
    const constants = shared()
    const sliceRoots = byHash(
        slices,
        (s) =>
            `slice|${(s.keys ?? []).join(',')}|${leanTermOf(s.codec, 'slice', freshBound())}`,
    ).map(([root, s], i) =>
        sliceRoot(s, printerOf(constants, `s${i}`, s.name), root, clauses),
    )
    const pathRoots = byHash(
        paths,
        // the term and not `leanPath`'s print, which holds the rows: a root keeps its id when the
        // pool draws another set of paths at it
        (v) => `path|${leanTermOf(v.codec, 'path', freshBound())}`,
    ).map(([root, v], i) =>
        pathRoot(v, printerOf(constants, `p${i}`, v.name), root),
    )
    const codecs = placed(
        'codecs.ts',
        codecsHeader,
        [...sliceRoots, ...pathRoots].map(({ declarations }) => ({
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
    const pathFile = placed(
        'paths.ts',
        checksHeader,
        pathRoots.map((r) => r.checks),
    )
    const rows = [
        ...codecs.rows,
        ...sliceFiles.flatMap((f) => f.rows),
        ...pathFile.rows,
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
        ['paths.ts', pathFile.text],
        [
            'rows.json',
            `[\n${rows.map((r) => JSON.stringify(r)).join(',\n')}\n]\n`,
        ],
        ['tsconfig.slices.json', tsconfig(['codecs.ts', ...SLICE_FILES])],
        ['tsconfig.paths.json', tsconfig(['codecs.ts', 'paths.ts'])],
    ]
}
