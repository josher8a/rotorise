/**
 * **The decisions over the graph of a closed codec**: disjointness and compatibility, the model's
 * `Scoped.disjoint` and `Scoped.compat`.
 *
 * Each decision reads the graph that the emitter prints for a closed codec ({@link graphOf}): an
 * entry for each entry of each cycle, and the root. Below a guard a walk assumes a pair of entries
 * while it compares the two bodies. At an unguarded position a walk unfolds an entry. A fuel bounds
 * each walk as the model's fuel does, so the host and the model compute one function.
 *
 * **The host has one disjointness decision**, the walk of this file. {@link agrees}, path narrowing
 * and the disjointness rows each read the walk, and each Lean twin reads `Scoped.disjoint`.
 */
import type { Body, Field, Term } from './term'
import {
    childrenOf,
    componentsOf,
    dominates,
    entryOrder,
    isPrim,
    otherShape,
    primsApart,
    sameAdapter,
    targetOf,
} from './term'

/** The term, or one of its two views. */
type Mode = 'raw' | 'caller' | 'stored'

/**
 * **The graph of a term, as the emitter prints the closed codec**: the entries of each cycle in the
 * order of {@link entryOrder}, scope by scope in the order of {@link componentsOf}, then the root
 * where no cycle holds it. `undefined` is a term with no scoped form.
 */
const graphOf = (
    root: Term,
): { readonly bodies: readonly Term[]; readonly root: number } | undefined => {
    const scopes: Term[][] = []
    for (const component of componentsOf([root])) {
        const order = entryOrder(component)
        if (order.kind === 'refused') return undefined
        scopes.push([...order.entries])
    }
    if (!scopes.some((entries) => entries.includes(root))) scopes.push([root])
    const bodies = scopes.flat()
    return { bodies, root: bodies.indexOf(root) }
}

/**
 * **A position of the graph**: an entry, a term in place, a refinement over a position, or a `ref`
 * with no target.
 */
type At =
    | { readonly kind: 'entry'; readonly j: number }
    | { readonly kind: 'term'; readonly t: Term; readonly side: Side }
    | { readonly kind: 'refine'; readonly inner: At }
    | { readonly kind: 'free' }

/** One operand: its entries, its view, and the entries that reach an adapter. */
type Side = {
    readonly bodies: readonly Term[]
    readonly index: ReadonlyMap<Term, number>
    readonly root: number
    readonly mode: Mode
    /** The entries that reach an adapter in the operand that the test reads. */
    readonly adapts: readonly boolean[]
    readonly stable: boolean
}

/** The pairs of entries assumed apart, or assumed to agree. */
type Table = readonly (readonly [number, number])[]

type Ctx = {
    readonly left: Side
    readonly right: Side
    readonly prev: (table: Table, l: At, r: At) => boolean
}

const sideOf = (t: Term, mode: Mode): Side | undefined => {
    const graph = graphOf(t)
    if (graph === undefined) return undefined
    const index = new Map(graph.bodies.map((one, j) => [one, j]))
    const base = {
        bodies: graph.bodies,
        index,
        root: graph.root,
        mode: 'raw' as Mode,
        adapts: [],
        stable: true,
    }
    const [raw, rawStable] = adaptersOf(base)
    const rawSide: Side = { ...base, adapts: raw, stable: rawStable }
    if (mode === 'raw') return rawSide
    const viewed: Side = { ...rawSide, mode }
    const [adapts, stable] = adaptersOf(viewed)
    return { ...viewed, adapts, stable }
}

/**
 * **The entries that reach an adapter**, the model's `adOf`: the table after one round per entry,
 * and whether the table is a fixed point (`adStable`).
 */
const adaptersOf = (side: Side): readonly [readonly boolean[], boolean] => {
    let table: boolean[] = side.bodies.map(() => false)
    for (let round = 0; round < side.bodies.length; round++) {
        const known = table
        table = side.bodies.map((_, j) => reachesAdapter(known, body(side, j)))
    }
    const final = table
    const stable = side.bodies.every(
        (_, j) => reachesAdapter(final, body(side, j)) === final[j],
    )
    return [final, stable]
}

/** Whether a position reaches an adapter, where `table` answers at each entry. */
const reachesAdapter = (table: readonly boolean[], at: At): boolean => {
    switch (at.kind) {
        case 'entry':
            return table[at.j] ?? true
        case 'free':
            return true
        case 'refine':
            return reachesAdapter(table, at.inner)
        case 'term': {
            const t = at.t
            if (t.kind === 'held' || t.kind === 'legacy') return true
            if (
                t.kind === 'object' &&
                Object.values(t.body.fields).some(
                    (field) => markOf(field, at.side.mode) === 'fill',
                )
            )
                return true
            return childrenAt(at.side, t).some((one) =>
                reachesAdapter(table, one),
            )
        }
    }
}

/** **A position below the top**, the model's `belowTop`: the position reaches no adapter. */
const belowTopAt = (side: Side, at: At): boolean =>
    side.stable && !reachesAdapter(side.adapts, at)

/** The body of an entry, in the operand that the test reads. */
const body = (side: Side, j: number): At => {
    const t = side.bodies[j] as Term
    if (t.kind !== 'ref') return viewAt(side, t)
    const target = targetOf(t)
    return target === undefined ? { kind: 'free' } : place(side, target)
}

/**
 * **A term in place**: a `ref` reads its target, an entry prints as its entry, and
 * any other term prints in place.
 */
const place = (side: Side, t: Term): At => {
    const j = side.index.get(t)
    if (j !== undefined) return { kind: 'entry', j }
    if (t.kind !== 'ref') return viewAt(side, t)
    const target = targetOf(t)
    return target === undefined ? { kind: 'free' } : place(side, target)
}

/**
 * **The view of a term in place**, the model's `viewG`. A `held` reads its caller side, and a
 * `withLegacyRead` reads its inner term where it writes and `opaque` where it reads. A refinement
 * is a position over its inner term.
 */
const viewAt = (side: Side, t: Term): At => {
    switch (t.kind) {
        case 'refine':
            return { kind: 'refine', inner: place(side, t.inner) }
        case 'held':
            if (side.mode === 'raw') break
            return place(side, side.mode === 'caller' ? t.outer : t.inner)
        case 'legacy':
            if (side.mode === 'raw') break
            return side.mode === 'caller'
                ? place(side, t.inner)
                : { kind: 'term', t: opaque, side }
    }
    return { kind: 'term', t, side }
}

/** **The presence of a field in the view**: a `fallback` holds the name where it writes. */
const markOf = (field: Field, mode: Mode): 'req' | 'opt' | 'fill' => {
    switch (field.mark) {
        case 'req':
            return 'req'
        case 'fallback':
            return mode === 'raw' ? 'fill' : mode === 'caller' ? 'req' : 'opt'
        default:
            return 'opt'
    }
}

/** The positions of a term in place. */
const childrenAt = (side: Side, t: Term): readonly At[] =>
    childrenOf(t).map((one) => place(side, one))

/**
 * **One row per operation of the left operand**, the model's `rowG`, with `prev` as the walk at
 * the next fuel.
 */
const row = (c: Ctx, table: Table, l: At, r: At): boolean => {
    const restart = (r1: At) => c.prev(table, l, r1)
    switch (l.kind) {
        case 'entry':
            return c.prev(table, body(c.left, l.j), r)
        case 'free':
            return rightRows(c, restart, () => false, r)
        case 'refine':
            return row(c, table, l.inner, r)
        case 'term':
            break
    }
    const t = l.t
    const pair = (a: At) => (b: At) => pairAt(c, table, a, b)
    switch (t.kind) {
        case 'never':
            return true
        case 'held':
        case 'legacy':
        case 'opaq':
        case 'ref':
            return rightRows(c, restart, () => false, r)
        case 'refine':
            return row(c, table, viewAt(c.left, t), r)
        case 'union':
            return t.options.every((option) =>
                row(c, table, place(c.left, option), r),
            )
        case 'set': {
            const elem = place(c.left, t.elem)
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u) =>
                        u.kind === 'set'
                            ? c.prev([], elem, place(c.right, u.elem))
                            : otherShape(u, ['prim', 'list', 'object']),
                    ),
                r,
            )
        }
        case 'list': {
            const parts = (u: Extract<Term, { kind: 'list' }>, side: Side) => ({
                pre: u.pre.map((one) => place(side, one)),
                spread:
                    u.spread === undefined ? undefined : place(side, u.spread),
                suf: u.suf.map((one) => place(side, one)),
            })
            const mine = parts(t, c.left)
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u) => {
                        if (u.kind !== 'list')
                            return otherShape(u, ['prim', 'set', 'object'])
                        const theirs = parts(u, c.right)
                        return listRows(
                            mine.pre.map(pair),
                            mine.spread === undefined
                                ? undefined
                                : pair(mine.spread),
                            mine.suf.map(pair),
                            theirs.pre,
                            theirs.spread,
                            theirs.suf,
                        )
                    }),
                r,
            )
        }
        case 'object': {
            const body = t.body
            const block =
                body.rest === undefined
                    ? () => true
                    : pair(place(c.left, body.rest))
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u) =>
                        u.kind === 'object'
                            ? Object.entries(body.fields).some(
                                  ([name, field]) => {
                                      const slot = slotAt(c.right, u.body, name)
                                      return (
                                          (markOf(field, c.left.mode) ===
                                              'req' ||
                                              slot.mark === 'req') &&
                                          pair(place(c.left, field.t))(slot.at)
                                      )
                                  },
                              ) ||
                              Object.entries(u.body.fields).some(
                                  ([name, field]) =>
                                      !(name in body.fields) &&
                                      markOf(field, c.right.mode) === 'req' &&
                                      block(place(c.right, field.t)),
                              )
                            : otherShape(u, ['prim', 'set', 'list']),
                    ),
                r,
            )
        }
        default:
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u) =>
                        isPrim(u)
                            ? primsApart(t, u)
                            : otherShape(u, ['set', 'list', 'object']),
                    ),
                r,
            )
    }
}

/** A family over a term in place; every other position answers `false`. */
const termOf = (at: At, fam: (t: Term) => boolean): boolean =>
    at.kind === 'term' && fam(at.t)

/**
 * **A pair of positions below a guard**, the model's `pairAt`: a pair of entries already assumed
 * is apart, and a new pair is assumed while the walk compares the two bodies.
 */
const pairAt = (c: Ctx, table: Table, a: At, b: At): boolean => {
    if (a.kind === 'entry' && b.kind === 'entry')
        return (
            table.some(([i, j]) => i === a.j && j === b.j) ||
            c.prev(
                [[a.j, b.j], ...table],
                body(c.left, a.j),
                body(c.right, b.j),
            )
        )
    return c.prev(table, a, b)
}

/**
 * **The slot that an object gives one name**: the declared field, or `optional` of the open block,
 * which is the bottom where the object has no block.
 */
const slotAt = (
    side: Side,
    b: Body,
    name: string,
): { readonly mark: 'req' | 'opt' | 'fill'; readonly at: At } => {
    const field = b.fields[name]
    if (field !== undefined)
        return { mark: markOf(field, side.mode), at: place(side, field.t) }
    return {
        mark: 'opt',
        at:
            b.rest === undefined
                ? { kind: 'term', t: never, side }
                : place(side, b.rest),
    }
}

/**
 * **Every row that reads the right operand alone**, the model's `rightC` at a family that answers no
 * entry, refinement or union. The bottom admits
 * nothing. A union is disjoint where each option is. A refinement is bounded by its inner term.
 * An entry unfolds through `restart`. `fam` answers every other position.
 */
const rightRows = (
    c: Ctx,
    restart: (r: At) => boolean,
    fam: (r: At) => boolean,
    r: At,
): boolean => {
    switch (r.kind) {
        case 'entry':
            return restart(body(c.right, r.j))
        case 'refine':
            return rightRows(c, restart, fam, r.inner)
        case 'free':
            return fam(r)
        case 'term':
            switch (r.t.kind) {
                case 'never':
                    return true
                case 'refine':
                    return rightRows(c, restart, fam, viewAt(c.right, r.t))
                case 'union':
                    return r.t.options.every((option) =>
                        rightRows(c, restart, fam, place(c.right, option)),
                    )
            }
            return fam(r)
    }
}

/**
 * **Two list shapes apart**, the model's `listRowG`. Two values of different lengths differ, so
 * the shapes are disjoint where one position of each common length is. **Either side without a
 * spread** fixes the one length, and a length the other side refuses is disjoint outright. **Both
 * spreading**: where one side dominates, one disjoint position of the row at
 * `max p1 p2 + max s1 s2` decides. Where no side dominates, the test answers `false`.
 */
const listRows = (
    fpre: readonly ((r: At) => boolean)[],
    fsp: ((r: At) => boolean) | undefined,
    fsuf: readonly ((r: At) => boolean)[],
    pre: readonly At[],
    sp: At | undefined,
    suf: readonly At[],
): boolean => {
    const anyZip = (fs: readonly ((r: At) => boolean)[], us: readonly At[]) =>
        fs.some((f, at) => at < us.length && f(us[at] as At))
    if (fsp !== undefined && sp !== undefined) {
        if (!dominates(fpre.length, fsuf.length, pre.length, suf.length))
            return false
        const n =
            Math.max(fpre.length, pre.length) +
            Math.max(fsuf.length, suf.length)
        const fs = rowAt(fpre, fsp, fsuf, n)
        const us = rowAt(pre, sp, suf, n)
        return fs !== undefined && us !== undefined && anyZip(fs, us)
    }
    if (fsp === undefined) {
        const us = rowAt(pre, sp, suf, fpre.length + fsuf.length)
        return us === undefined || anyZip([...fpre, ...fsuf], us)
    }
    const fs = rowAt(fpre, fsp, fsuf, pre.length + suf.length)
    return fs === undefined || anyZip(fs, [...pre, ...suf])
}

/**
 * **The row a list shape assigns to `n` positions**, the model's `rowOfG`: the prefix, the spread
 * as often as the middle needs, then the suffix. `undefined` is a length the shape refuses.
 */
const rowAt = <T>(
    pre: readonly T[],
    spread: T | undefined,
    suf: readonly T[],
    n: number,
): readonly T[] | undefined => {
    const declared = pre.length + suf.length
    if (spread === undefined)
        return n === declared ? [...pre, ...suf] : undefined
    if (n < declared) return undefined
    return [
        ...pre,
        ...Array.from({ length: n - declared }, () => spread),
        ...suf,
    ]
}

/**
 * **The fuel of a walk between two operands**, the model's: one unit for each pair of entries below
 * a guard, and for each unguarded unfolding between two guards.
 */
const fuelOf = (left: Side, right: Side): number =>
    (left.bodies.length * right.bodies.length + 1) *
    (left.bodies.length + right.bodies.length + 2)

/**
 * **Whether two positions share no datum**, the model's walk `decG` with no assumed pair, at the
 * fuel of the two operands. `true` says that no datum is accepted by both positions at either
 * orientation. `false` states nothing: the test is sound, not complete.
 *
 * **A `held`, a `withLegacyRead` and `opaque` are disjoint only from the bottom.** The admission
 * of the first two is a function that no reader can read without running it, and `opaque` admits
 * every value. The views read a `held` ({@link viewOf}).
 *
 * **A `ref` with no target is a free variable.** The model has none, because the emitter prints no
 * codec that holds one. A free variable is disjoint from the bottom alone.
 */
const apartAt = (left: Side, right: Side, l: At, r: At): boolean => {
    const walk = (n: number, table: Table, l1: At, r1: At): boolean =>
        n === 0
            ? false
            : row(
                  {
                      left,
                      right,
                      prev: (t, l2, r2) => walk(n - 1, t, l2, r2),
                  },
                  table,
                  l1,
                  r1,
              )
    return walk(fuelOf(left, right), [], l, r)
}

/**
 * **The view of a position**, the model's `viewG` on a graph term: an entry stays an entry, and a
 * term reads its view at the operand of the view.
 */
const viewOf = (side: Side, at: At): At => {
    switch (at.kind) {
        case 'entry':
        case 'free':
            return at
        case 'refine':
            return { kind: 'refine', inner: viewOf(side, at.inner) }
        case 'term':
            return viewAt(side, at.t)
    }
}

/**
 * **Whether two terms share no datum in one mode**: the walk of {@link apartAt} with no assumed
 * pair, each term rooted as its own graph at its root entry, at the fuel of the two graphs. A view
 * keeps an entry an entry, so the root of a view is the root entry. `false` states nothing, and so
 * does a term with no graph.
 */
const apartIn = (mode: Mode, x: Term, y: Term): boolean => {
    const left = sideOf(x, mode)
    const right = sideOf(y, mode)
    if (left === undefined || right === undefined) return false
    return apartAt(
        left,
        right,
        { kind: 'entry', j: left.root },
        { kind: 'entry', j: right.root },
    )
}

/**
 * **Whether two terms share no value and no attribute**, the model's `Closed.disjoint`: the walk of
 * {@link apartAt} over the raw graphs. `true` says that no datum is accepted by both terms at either
 * orientation (`Closed.disjoint_sound`). `false` states nothing, and so does a term with no graph.
 */
export const disjoint = (x: Term, y: Term): boolean => apartIn('raw', x, y)

/**
 * **Whether the two pairs of views are disjoint**, the model's `Closed.viewsDisjoint`: the caller
 * views share no value, and the stored views share no attribute. Two options whose views are
 * disjoint are orthogonal: no value has two writers, and no attribute has two readers
 * (`Closed.viewsDisjoint_sound`). `false` states nothing, and so does a term with no graph.
 */
export const viewsDisjoint = (x: Term, y: Term): boolean =>
    apartIn('caller', x, y) && apartIn('stored', x, y)

/**
 * **Whether the stored views of two terms share no attribute**, the model's `narrowC` at one
 * option: {@link apartIn} at the stored view of each term.
 */
export const storedApart = (x: Term, y: Term): boolean =>
    apartIn('stored', x, y)

/* ── compatibility ────────────────────────────────────────────────────────────────────── */

/**
 * One half of agreement: on the write half two writers of one value write one attribute, and on
 * the read half two readers of one attribute read one value. The write half is the model's
 * orientation `.host`, and the read half is `.dual`.
 */
type Half = 'write' | 'read'

/** **Where the decision is**: the half, the two operands, and the two operands of the view. */
type Agreement = Ctx & {
    readonly half: Half
    readonly viewL: Side
    readonly viewR: Side
}

/**
 * **Whether two options agree on both halves**, the model's `Scoped.compatPair`. A union is the
 * join of its options, and the join of two lawful options exists exactly when the two are
 * compatible (Lawson: `s ∨ t` exists iff `s ∼ t`). Compatibility of two partial bijections is two
 * halves of agreement. `true` gives agreement on both halves of the two meanings
 * (`Closed.compatPair_sound`). A term with no graph agrees with nothing.
 */
export const agrees = (x: Term, y: Term): boolean =>
    agreesAt('write', x, y) && agreesAt('read', x, y)

/** **One half of agreement**, the model's `Scoped.compat` at the orientation of the half. */
const agreesAt = (half: Half, x: Term, y: Term): boolean => {
    const left = sideOf(x, 'raw')
    const right = sideOf(y, 'raw')
    const mode: Mode = half === 'write' ? 'caller' : 'stored'
    const viewL = sideOf(x, mode)
    const viewR = sideOf(y, mode)
    if (
        left === undefined ||
        right === undefined ||
        viewL === undefined ||
        viewR === undefined
    )
        return false
    const walk = (n: number, table: Table, l: At, r: At): boolean =>
        n === 0
            ? false
            : agreeRow(
                  {
                      half,
                      left,
                      right,
                      viewL,
                      viewR,
                      prev: (t, l1, r1) => walk(n - 1, t, l1, r1),
                  },
                  table,
                  l,
                  r,
              )
    return walk(
        fuelOf(left, right),
        [],
        { kind: 'entry', j: left.root },
        { kind: 'entry', j: right.root },
    )
}

/** The bottom, as a position. */
const isNeverAt = (at: At): boolean =>
    at.kind === 'term' && at.t.kind === 'never'

/**
 * **The position inside which a `held` acts on one half**, the model's `heldIn`: a `held` writes
 * inside its outer term and reads inside its inner term. Where that term is a `held` too, the half
 * acts inside its term in turn. An entry stops the walk.
 */
const heldIn = (half: Half, side: Side, at: At): At =>
    at.kind === 'term' && at.t.kind === 'held'
        ? heldIn(
              half,
              side,
              place(side, half === 'write' ? at.t.outer : at.t.inner),
          )
        : at

/**
 * **The rows that read no structure**, the model's `cbaseG`. The bottom agrees with every
 * position. Two positions below the top are bounded by the top. Two positions that share no datum
 * agree, and so do the two positions inside which their `held`s act, and the two views of the half.
 */
const agreeBase = (k: Agreement, l: At, r: At): boolean =>
    isNeverAt(l) ||
    isNeverAt(r) ||
    (belowTopAt(k.left, l) && belowTopAt(k.right, r)) ||
    apartAt(k.left, k.right, l, r) ||
    apartAt(
        k.left,
        k.right,
        heldIn(k.half, k.left, l),
        heldIn(k.half, k.right, r),
    ) ||
    apartAt(k.viewL, k.viewR, viewOf(k.viewL, l), viewOf(k.viewR, r))

/**
 * **The rows of the right operand**, the model's `rightC`. `fam` answers each position first. The
 * bottom agrees with every position. A union agrees where each option does, and a refinement
 * where its inner position does. An entry unfolds through `restart`.
 */
const agreeRight = (
    k: Agreement,
    restart: (r: At) => boolean,
    fam: (r: At) => boolean,
    r: At,
): boolean => {
    switch (r.kind) {
        case 'entry':
            return fam(r) || restart(body(k.right, r.j))
        case 'refine':
            return fam(r) || agreeRight(k, restart, fam, r.inner)
        case 'free':
            return fam(r)
        case 'term':
            switch (r.t.kind) {
                case 'never':
                    return true
                case 'refine':
                    return agreeRight(k, restart, fam, viewAt(k.right, r.t))
                case 'union':
                    return (
                        fam(r) ||
                        r.t.options.every((option) =>
                            agreeRight(k, restart, fam, place(k.right, option)),
                        )
                    )
            }
            return fam(r)
    }
}

/**
 * **One row per operation of the left operand**, the model's `rowC`, with `prev` as the walk at
 * the next fuel. A set and a `held` compare their positions with no assumed pair. A list and an
 * object compare their positions below the guard ({@link pairAt}).
 */
const agreeRow = (k: Agreement, table: Table, l: At, r: At): boolean => {
    const restart = (r1: At) => k.prev(table, l, r1)
    const base = (r1: At) => agreeBase(k, l, r1)
    switch (l.kind) {
        case 'entry':
            return base(r) || k.prev(table, body(k.left, l.j), r)
        case 'refine':
            return base(r) || agreeRow(k, table, l.inner, r)
        case 'free':
            return agreeRight(k, restart, base, r)
        case 'term':
            break
    }
    const t = l.t
    switch (t.kind) {
        case 'never':
            return true
        case 'refine':
            return agreeRow(k, table, viewAt(k.left, t), r)
        case 'union':
            return (
                base(r) ||
                t.options.every((option) =>
                    agreeRow(k, table, place(k.left, option), r),
                )
            )
        // two `held`s of one adapter agree where their inner terms agree
        case 'held':
            return agreeRight(
                k,
                restart,
                (r1) =>
                    base(r1) ||
                    termOf(
                        r1,
                        (u) =>
                            u.kind === 'held' &&
                            sameAdapter(t, u) &&
                            agreeRow(
                                k,
                                [],
                                place(k.left, t.inner),
                                place(k.right, u.inner),
                            ),
                    ),
                r,
            )
        case 'set':
            return agreeRight(
                k,
                restart,
                (r1) =>
                    base(r1) ||
                    termOf(
                        r1,
                        (u) =>
                            u.kind === 'set' &&
                            agreeRow(
                                k,
                                [],
                                place(k.left, t.elem),
                                place(k.right, u.elem),
                            ),
                    ),
                r,
            )
        case 'list':
            return agreeRight(
                k,
                restart,
                (r1) =>
                    base(r1) ||
                    termOf(
                        r1,
                        (u) =>
                            u.kind === 'list' &&
                            positionsOf(t).every((one) =>
                                positionsOf(u).every((other) =>
                                    pairAt(
                                        k,
                                        table,
                                        place(k.left, one),
                                        place(k.right, other),
                                    ),
                                ),
                            ),
                    ),
                r,
            )
        case 'object':
            return agreeRight(
                k,
                restart,
                (r1) =>
                    base(r1) ||
                    termOf(
                        r1,
                        (u) =>
                            u.kind === 'object' &&
                            bodiesAgree(k, table, t.body, u.body),
                    ),
                r,
            )
        default:
            return agreeRight(k, restart, base, r)
    }
}

/** Every position of a list shape: the prefix, the spread, and the suffix. */
const positionsOf = (t: Extract<Term, { kind: 'list' }>): readonly Term[] => [
    ...t.pre,
    ...(t.spread === undefined ? [] : [t.spread]),
    ...t.suf,
]

/**
 * **Two bodies agree**, the model's `objC`: at each name that a body declares, the two slots agree
 * and answer alike at absence, and the two open blocks agree. An undeclared name holds `optional`
 * of the open block, which is the bottom where the body has no block.
 */
const bodiesAgree = (k: Agreement, table: Table, a: Body, b: Body): boolean => {
    const fieldOf = (body: Body, name: string): Field =>
        body.fields[name] ?? { mark: 'optional', t: body.rest ?? never }
    const absent = (name: string) =>
        k.half === 'write' || standInsAgree(fieldOf(a, name), fieldOf(b, name))
    return (
        Object.entries(a.fields).every(
            ([name, field]) =>
                absent(name) &&
                pairAt(
                    k,
                    table,
                    place(k.left, field.t),
                    slotAt(k.right, b, name).at,
                ),
        ) &&
        Object.entries(b.fields).every(
            ([name, field]) =>
                absent(name) &&
                pairAt(
                    k,
                    table,
                    slotAt(k.left, a, name).at,
                    place(k.right, field.t),
                ),
        ) &&
        (a.rest === undefined ||
            pairAt(
                k,
                table,
                place(k.left, a.rest),
                b.rest === undefined
                    ? { kind: 'term', t: never, side: k.right }
                    : place(k.right, b.rest),
            ))
    )
}

/**
 * **Two fields read a map without the name to one value**, or one of the two reads no such map. A
 * field with a fallback reads such a map to its stand-in. **The host admits two fallbacks with one
 * stand-in, and the model refuses every two fills**, because the model's constants have no
 * decidable equality. So a pair with a fill at one name on each side states no compatibility row.
 */
const standInsAgree = (a: Field, b: Field): boolean =>
    a.mark === 'fallback'
        ? b.mark === 'req' || (b.mark === 'fallback' && Object.is(a.v, b.v))
        : b.mark !== 'fallback' || a.mark === 'req'

const never: Term = { kind: 'never' }
const opaque: Term = { kind: 'opaq' }
