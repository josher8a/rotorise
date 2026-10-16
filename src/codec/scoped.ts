/**
 * **The decisions over the graph of a closed codec**: disjointness and compatibility, the model's
 * `Scoped.disjoint` and `Scoped.compat`.
 *
 * Each decision reads the flat scope that the emitter prints for a closed codec ({@link flatOf}): an
 * entry for each entry of each cycle, the root, and each child of a container. Below a guard a walk
 * assumes a pair of entries while it compares the two bodies. At an unguarded position a walk
 * unfolds an entry. A fuel bounds each walk as the model's fuel does, so the host and the model
 * compute one function.
 *
 * **The host has one disjointness decision**, the walk of this file. {@link agrees}, path narrowing
 * and the disjointness rows each read the walk, and each Lean twin reads `Scoped.disjoint`.
 */
import type { Body, Field, Term } from './term'
import {
    childrenOf,
    componentsOf,
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
 * **The flat scope of a term, as the emitter prints the closed codec**: the entries of each cycle in
 * the order of {@link entryOrder}, scope by scope in the order of {@link componentsOf}, then the root
 * where no cycle holds it, then each child of a container as an entry of its own.
 *
 * A position above every guard names an entry of a cycle only, so `cycles` holds the entries that
 * such a position names. **Each child of a container is an entry**, so `index` holds an entry for
 * each term at such a child. A child that a cycle holds is the entry of the cycle, and every other
 * child is an entry after the root, in the order that the walk of the bodies meets it. A wall closes
 * the names below it, so the children below a wall stay in place. A cycle passes no wall, so no
 * cycle passes a term in place, and the walk below a wall needs no table.
 */
export type FlatScope = {
    readonly bodies: readonly Term[]
    readonly cycles: ReadonlyMap<Term, number>
    readonly index: ReadonlyMap<Term, number>
    readonly root: number
}

/** **The flat scope of a term**, or the reason that the term has no scoped form. */
export const flatOf = (
    root: Term,
):
    | ({ readonly kind: 'flat' } & FlatScope)
    | { readonly kind: 'refused'; readonly reason: string } => {
    const bodies: Term[] = []
    for (const component of componentsOf([root])) {
        const order = entryOrder(component)
        if (order.kind === 'refused')
            return { kind: 'refused', reason: order.reason }
        bodies.push(...order.entries)
    }
    if (!bodies.includes(root)) bodies.push(root)
    const cycles = new Map(bodies.map((one, j) => [one, j]))
    const index = new Map(cycles)
    // a child of a container is an entry: an entry of a cycle, or a new entry after the others
    const hoist = (t: Term): void => {
        if (index.has(t)) return
        if (t.kind === 'ref') {
            const target = targetOf(t)
            if (target !== undefined) hoist(target)
            return
        }
        index.set(t, bodies.length)
        bodies.push(t)
    }
    // the children of a term in place: a container hoists each child, and a wall keeps them
    const visit = (t: Term): void => {
        switch (t.kind) {
            case 'list':
            case 'set':
            case 'object':
                for (const one of childrenOf(t)) hoist(one)
                return
            case 'held':
            case 'legacy':
                return
        }
        for (const one of childrenOf(t)) keep(one)
    }
    // a term in place above every guard: an entry of a cycle is visited as an entry
    const keep = (t: Term): void => {
        if (cycles.has(t)) return
        if (t.kind !== 'ref') return visit(t)
        const target = targetOf(t)
        if (target !== undefined) keep(target)
    }
    for (let j = 0; j < bodies.length; j++) visit(bodies[j] as Term)
    return { kind: 'flat', bodies, cycles, index, root: bodies.indexOf(root) }
}

/**
 * **A position of the graph**: an entry, a term in place, a refinement over a position, or a `ref`
 * with no target. A term below a wall is `closed`: its children stay in place.
 */
type At =
    | Entry
    | {
          readonly kind: 'term'
          readonly t: Term
          readonly side: Side
          readonly closed: boolean
      }
    | { readonly kind: 'refine'; readonly inner: At }
    | Free

/** An entry of the flat scope. */
type Entry = { readonly kind: 'entry'; readonly j: number }

/** A `ref` with no target. */
type Free = { readonly kind: 'free' }

/** One operand: its entries, its view, and the entries that reach an adapter. */
type Side = {
    readonly bodies: readonly Term[]
    readonly cycles: ReadonlyMap<Term, number>
    readonly index: ReadonlyMap<Term, number>
    readonly root: number
    readonly mode: Mode
    /** The entries that reach an adapter in the operand that the test reads. */
    readonly adapts: readonly boolean[]
    readonly stable: boolean
}

/** The pairs of entries assumed apart, or assumed to agree. */
type Table = readonly (readonly [number, number])[]

/**
 * **The context of a walk**: the two operands, the walk at the next fuel (`prev`), and the row at
 * the same fuel (`same`). One walk serves each relation, and only the row differs.
 */
type Ctx = {
    readonly left: Side
    readonly right: Side
    readonly prev: (table: Table, l: At, r: At) => boolean
    readonly same: (table: Table, l: At, r: At) => boolean
}

const sideOf = (t: Term, mode: Mode): Side | undefined => {
    const flat = flatOf(t)
    if (flat.kind === 'refused') return undefined
    const base = {
        bodies: flat.bodies,
        cycles: flat.cycles,
        index: flat.index,
        root: flat.root,
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
            return childrenAt(at.side, t, at.closed).some((one) =>
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
    if (t.kind !== 'ref') return viewAt(side, t, false)
    const target = targetOf(t)
    return target === undefined ? { kind: 'free' } : place(side, target)
}

/**
 * **A term in place above every guard**: a `ref` reads its target, an entry of a cycle prints as its
 * entry, and any other term prints in place.
 */
const place = (side: Side, t: Term): At => {
    const j = side.cycles.get(t)
    if (j !== undefined) return { kind: 'entry', j }
    if (t.kind !== 'ref') return viewAt(side, t, false)
    const target = targetOf(t)
    return target === undefined ? { kind: 'free' } : place(side, target)
}

/** **A term in place below a wall**: a `ref` reads its target, and the term names no entry. */
const closedAt = (side: Side, t: Term): At => {
    if (t.kind !== 'ref') return viewAt(side, t, true)
    const target = targetOf(t)
    return target === undefined ? { kind: 'free' } : closedAt(side, target)
}

/** A term in place, below a wall or above every guard. */
const inPlace = (side: Side, t: Term, closed: boolean): At =>
    closed ? closedAt(side, t) : place(side, t)

/**
 * **A child of a container above every wall is an entry.** {@link flatOf} holds an entry for each
 * such child, so a child with no entry is a broken invariant of the flat scope, and throws.
 */
const entryAt = (side: Side, t: Term): Entry | Free => {
    const j = side.index.get(t)
    if (j !== undefined) return { kind: 'entry', j }
    if (t.kind !== 'ref')
        throw new Error(
            'the flat scope holds no entry for a child of a container: flatOf missed the child',
        )
    const target = targetOf(t)
    return target === undefined ? { kind: 'free' } : entryAt(side, target)
}

/** **A child of a container**: an entry, or a term in place below a wall. */
const childAt = (side: Side, t: Term, closed: boolean): At =>
    closed ? closedAt(side, t) : entryAt(side, t)

/**
 * **The view of a term in place**, the model's `viewG`. A `held` reads its caller side, and a
 * `withLegacyRead` reads its inner term where it writes and `opaque` where it reads. A refinement
 * is a position over its inner term.
 */
const viewAt = (side: Side, t: Term, closed: boolean): At => {
    switch (t.kind) {
        case 'refine':
            return { kind: 'refine', inner: inPlace(side, t.inner, closed) }
        case 'held':
            if (side.mode === 'raw') break
            return closedAt(side, side.mode === 'caller' ? t.outer : t.inner)
        case 'legacy':
            if (side.mode === 'raw') break
            return side.mode === 'caller'
                ? closedAt(side, t.inner)
                : { kind: 'term', t: opaque, side, closed: true }
    }
    return { kind: 'term', t, side, closed }
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

/** The positions of a term in place: a container names an entry at each child, and a wall closes. */
const childrenAt = (side: Side, t: Term, closed: boolean): readonly At[] => {
    const down = t.kind === 'list' || t.kind === 'set' || t.kind === 'object'
    const walled = closed || t.kind === 'held' || t.kind === 'legacy'
    return childrenOf(t).map((one) =>
        down ? childAt(side, one, closed) : inPlace(side, one, walled),
    )
}

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
    const pair = (a: At) => (b: At) => pairX(c, table, a, b)
    switch (t.kind) {
        case 'never':
            return true
        case 'held':
        case 'legacy':
        case 'opaq':
        case 'ref':
            return rightRows(c, restart, () => false, r)
        case 'refine':
            return row(c, table, viewAt(c.left, t, l.closed), r)
        case 'union':
            return t.options.every((option) =>
                row(c, table, inPlace(c.left, option, l.closed), r),
            )
        case 'set': {
            const elem = childAt(c.left, t.elem, l.closed)
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u, closed) =>
                        u.kind === 'set'
                            ? pair(elem)(childAt(c.right, u.elem, closed))
                            : otherShape(u, ['prim', 'list', 'object']),
                    ),
                r,
            )
        }
        case 'list': {
            const parts = (
                u: Extract<Term, { kind: 'list' }>,
                side: Side,
                closed: boolean,
            ) => ({
                pre: u.pre.map((one) => childAt(side, one, closed)),
                spread:
                    u.spread === undefined
                        ? undefined
                        : childAt(side, u.spread, closed),
                suf: u.suf.map((one) => childAt(side, one, closed)),
            })
            const mine = parts(t, c.left, l.closed)
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u, closed) => {
                        if (u.kind !== 'list')
                            return otherShape(u, ['prim', 'set', 'object'])
                        const theirs = parts(u, c.right, closed)
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
                    : pair(childAt(c.left, body.rest, l.closed))
            return rightRows(
                c,
                restart,
                (r1) =>
                    termOf(r1, (u, closed) =>
                        u.kind === 'object'
                            ? Object.entries(body.fields).some(
                                  ([name, field]) => {
                                      const slot = slotAt(
                                          c.right,
                                          u.body,
                                          name,
                                          closed,
                                      )
                                      return (
                                          (markOf(field, c.left.mode) ===
                                              'req' ||
                                              slot.mark === 'req') &&
                                          pair(
                                              childAt(
                                                  c.left,
                                                  field.t,
                                                  l.closed,
                                              ),
                                          )(slot.at)
                                      )
                                  },
                              ) ||
                              Object.entries(u.body.fields).some(
                                  ([name, field]) =>
                                      !(name in body.fields) &&
                                      markOf(field, c.right.mode) === 'req' &&
                                      block(childAt(c.right, field.t, closed)),
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
const termOf = (at: At, fam: (t: Term, closed: boolean) => boolean): boolean =>
    at.kind === 'term' && fam(at.t, at.closed)

/**
 * **A pair of positions below a guard**, the model's `pairX`, for both relations. A pair of entries
 * already assumed holds, and a new pair is assumed while the walk compares the two bodies. Each
 * child of a container is an entry, so any other pair has a term in place below a wall: a closed
 * term names no entry, so no cycle passes through the pair. That pair runs the row at the same
 * fuel.
 */
const pairX = (c: Ctx, table: Table, a: At, b: At): boolean =>
    a.kind === 'entry' && b.kind === 'entry'
        ? table.some(([i, j]) => i === a.j && j === b.j) ||
          c.prev([[a.j, b.j], ...table], body(c.left, a.j), body(c.right, b.j))
        : c.same(table, a, b)

/**
 * **The walk of one relation**, the model's `walk`: the fuel and the table live here, and the row
 * of the relation is the argument. `make` gives the context of the relation from the context of
 * the walk. An empty fuel answers `false`.
 */
const walkOf = <K extends Ctx>(
    row: (k: K, table: Table, l: At, r: At) => boolean,
    make: (c: Ctx) => K,
    left: Side,
    right: Side,
): ((n: number, table: Table, l: At, r: At) => boolean) => {
    const walk = (n: number, table: Table, l: At, r: At): boolean => {
        if (n === 0) return false
        const k: K = make({
            left,
            right,
            prev: (t, l1, r1) => walk(n - 1, t, l1, r1),
            same: (t, l1, r1) => row(k, t, l1, r1),
        })
        return row(k, table, l, r)
    }
    return walk
}

/**
 * **The slot that an object gives one name**: the declared field, or `optional` of the open block,
 * which is the bottom where the object has no block.
 */
const slotAt = (
    side: Side,
    b: Body,
    name: string,
    closed: boolean,
): { readonly mark: 'req' | 'opt' | 'fill'; readonly at: At } => {
    const field = b.fields[name]
    if (field !== undefined)
        return {
            mark: markOf(field, side.mode),
            at: childAt(side, field.t, closed),
        }
    return {
        mark: 'opt',
        at:
            b.rest === undefined
                ? { kind: 'term', t: never, side, closed: true }
                : childAt(side, b.rest, closed),
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
                    return rightRows(
                        c,
                        restart,
                        fam,
                        viewAt(c.right, r.t, r.closed),
                    )
                case 'union':
                    return r.t.options.every((option) =>
                        rightRows(
                            c,
                            restart,
                            fam,
                            inPlace(c.right, option, r.closed),
                        ),
                    )
            }
            return fam(r)
    }
}

/**
 * **The aligned rows of two list shapes**, the model's `alignedRows`: one pair of rows at each
 * common length. **Either side without a spread** fixes the one length, and the pair is absent
 * where the other side refuses that length. **Both spreading**: the shapes share the lengths from
 * `max (p1 + s1) (p2 + s2)` up. The middle positions pair the two spreads from `hi + 1` up, where
 * `hi` is `max p1 p2 + max s1 s2`, and each longer row re-spreads the row at `hi + 1`. So the
 * lengths from the first bound to `hi + 1` reach every pair of positions.
 */
const alignedRows = <L, R>(
    lpre: readonly L[],
    lsp: L | undefined,
    lsuf: readonly L[],
    rpre: readonly R[],
    rsp: R | undefined,
    rsuf: readonly R[],
): readonly (readonly [readonly L[], readonly R[]])[] => {
    if (lsp !== undefined && rsp !== undefined) {
        const lo = Math.max(
            lpre.length + lsuf.length,
            rpre.length + rsuf.length,
        )
        const hi =
            Math.max(lpre.length, rpre.length) +
            Math.max(lsuf.length, rsuf.length)
        return Array.from({ length: hi + 2 - lo }, (_, k) => lo + k).flatMap(
            (n) => {
                const ls = rowAt(lpre, lsp, lsuf, n)
                const rs = rowAt(rpre, rsp, rsuf, n)
                return ls === undefined || rs === undefined
                    ? []
                    : [[ls, rs] as const]
            },
        )
    }
    if (lsp === undefined) {
        const rs = rowAt(rpre, rsp, rsuf, lpre.length + lsuf.length)
        return rs === undefined ? [] : [[[...lpre, ...lsuf], rs] as const]
    }
    const ls = rowAt(lpre, lsp, lsuf, rpre.length + rsuf.length)
    return ls === undefined ? [] : [[ls, [...rpre, ...rsuf]] as const]
}

/**
 * **Two list shapes apart**, the model's `listRowG`. Two values of different lengths differ, so
 * the shapes are disjoint where the aligned rows at each common length hold one disjoint position.
 */
const listRows = (
    fpre: readonly ((r: At) => boolean)[],
    fsp: ((r: At) => boolean) | undefined,
    fsuf: readonly ((r: At) => boolean)[],
    pre: readonly At[],
    sp: At | undefined,
    suf: readonly At[],
): boolean =>
    alignedRows(fpre, fsp, fsuf, pre, sp, suf).every(([fs, us]) =>
        fs.some((f, at) => at < us.length && f(us[at] as At)),
    )

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
const apartAt = (left: Side, right: Side, l: At, r: At): boolean =>
    walkOf(row, (c) => c, left, right)(fuelOf(left, right), [], l, r)

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
            return viewAt(side, at.t, at.closed)
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
    return walkOf(
        agreeRow,
        (c): Agreement => ({ ...c, half, viewL, viewR }),
        left,
        right,
    )(
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
              closedAt(side, half === 'write' ? at.t.outer : at.t.inner),
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
                    return agreeRight(
                        k,
                        restart,
                        fam,
                        viewAt(k.right, r.t, r.closed),
                    )
                case 'union':
                    return (
                        fam(r) ||
                        r.t.options.every((option) =>
                            agreeRight(
                                k,
                                restart,
                                fam,
                                inPlace(k.right, option, r.closed),
                            ),
                        )
                    )
            }
            return fam(r)
    }
}

/**
 * **One row per operation of the left operand**, the model's `rowSpecC`, with `prev` as the walk at
 * the next fuel. A set and an object compare their positions below the guard ({@link pairX}). A
 * list compares the aligned rows at each common length ({@link alignedRows}). A `held` compares its inner terms, which are closed, through the same test.
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
            return agreeRow(k, table, viewAt(k.left, t, l.closed), r)
        case 'union':
            return (
                base(r) ||
                t.options.every((option) =>
                    agreeRow(k, table, inPlace(k.left, option, l.closed), r),
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
                            pairX(
                                k,
                                table,
                                closedAt(k.left, t.inner),
                                closedAt(k.right, u.inner),
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
                        (u, closed) =>
                            u.kind === 'set' &&
                            pairX(
                                k,
                                table,
                                childAt(k.left, t.elem, l.closed),
                                childAt(k.right, u.elem, closed),
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
                        (u, closed) =>
                            u.kind === 'list' &&
                            alignedRows(
                                t.pre,
                                t.spread,
                                t.suf,
                                u.pre,
                                u.spread,
                                u.suf,
                            ).every(([ones, others]) =>
                                ones.every((one, at) => {
                                    const other = others[at]
                                    return (
                                        other === undefined ||
                                        pairX(
                                            k,
                                            table,
                                            childAt(k.left, one, l.closed),
                                            childAt(k.right, other, closed),
                                        )
                                    )
                                }),
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
                        (u, closed) =>
                            u.kind === 'object' &&
                            bodiesAgree(k, table, t.body, u.body, {
                                left: l.closed,
                                right: closed,
                            }),
                    ),
                r,
            )
        default:
            return agreeRight(k, restart, base, r)
    }
}

/**
 * **Two bodies agree**, the model's `objK`: at each name that a body declares, the two slots agree
 * and answer alike at absence, and the two open blocks agree. An undeclared name holds `optional`
 * of the open block, which is the bottom where the body has no block.
 */
const bodiesAgree = (
    k: Agreement,
    table: Table,
    a: Body,
    b: Body,
    closed: { readonly left: boolean; readonly right: boolean },
): boolean => {
    const fieldOf = (body: Body, name: string): Field =>
        body.fields[name] ?? { mark: 'optional', t: body.rest ?? never }
    const absent = (name: string) =>
        k.half === 'write' || standInsAgree(fieldOf(a, name), fieldOf(b, name))
    return (
        Object.entries(a.fields).every(
            ([name, field]) =>
                absent(name) &&
                pairX(
                    k,
                    table,
                    childAt(k.left, field.t, closed.left),
                    slotAt(k.right, b, name, closed.right).at,
                ),
        ) &&
        Object.entries(b.fields).every(
            ([name, field]) =>
                absent(name) &&
                pairX(
                    k,
                    table,
                    slotAt(k.left, a, name, closed.left).at,
                    childAt(k.right, field.t, closed.right),
                ),
        ) &&
        (a.rest === undefined ||
            pairX(
                k,
                table,
                childAt(k.left, a.rest, closed.left),
                b.rest === undefined
                    ? { kind: 'term', t: never, side: k.right, closed: true }
                    : childAt(k.right, b.rest, closed.right),
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
