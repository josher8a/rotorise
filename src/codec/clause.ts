import type { AnyCodec } from './build'
import { termOf } from './denote'
import { CodecError, setOwn } from './result'
import type { Field, Term } from './term'
import { mapChildren, throughRefs } from './term'

/**
 * **The clause of `narrow`**, the `φ` of the model's `narrowC`: an object term whose keys are each
 * required at the term of a codec, and whose open block is `opaque` at every depth.
 */
export type Clause = Extract<Term, { readonly kind: 'object' }>

/** **The pattern of `narrow`**: an object codec, each key at a codec that writes the key. */
export type ClausePattern = {
    readonly def: Term
    readonly spec: Readonly<Record<string, AnyCodec>>
}

/**
 * **The opening of a pattern**: the term of the pattern, open at every object, so every undeclared
 * name of the pattern holds `opaque`. A pattern of `extract`, `exclude` and `narrow` names the keys
 * that it constrains and no other key, so each of the three reads the pattern through this opening.
 * The opening reads through each `ref`, and a cycle of the term is a cycle of the opening.
 */
export const opened = throughRefs((t, opened) => {
    switch (t.kind) {
        case 'object': {
            const fields: Record<string, Field> = {}
            for (const [name, field] of Object.entries(t.body.fields))
                setOwn(fields, name, { ...field, t: opened(field.t) })
            const { rest } = t.body
            return {
                kind: 'object',
                body: {
                    fields,
                    rest: rest === undefined ? { kind: 'opaq' } : opened(rest),
                },
            }
        }
        // the opening stops at these two, which stay as the pattern wrote them
        case 'set':
        case 'refine':
            return t
        default:
            return mapChildren(t, opened, 'wire')
    }
})

/** The term of a clause, built one time when the path records the clause. */
export const clauseOf = (pattern: ClausePattern): Clause => {
    const t = opened(termOf(pattern as unknown as AnyCodec))
    // the type admits an object codec only, so the term of the pattern is an object
    if (t.kind !== 'object')
        throw new CodecError('a pattern of `narrow` is an object codec')
    return t
}
