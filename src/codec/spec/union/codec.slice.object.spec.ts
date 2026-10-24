/**
 * An object is a union of one option, so the slice of an object is the slice of that union.
 *
 * `extract(object(spec), pattern)` and `extract(union([object(spec)]), pattern)` must agree on the
 * decoded type, on the option count, on the values that decode, and on the refusal. A caller who
 * wraps an object in a union only to slice the object gets nothing from the wrapper.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AnyCodec, Decoded } from '../../codec'
import {
    array,
    exclude,
    extract,
    list,
    object,
    optional,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'
import type { Term } from '../../term'
import { arbitraryOf, rngFrom } from '../../testing'

const optionsOf = (codec: { readonly def: Term }): readonly Term[] =>
    codec.def.kind === 'union'
        ? codec.def.options
        : codec.def.kind === 'never'
          ? []
          : [codec.def]

const owner = union([
    object({ type: string('PERSON'), name: string }),
    object({ type: string('SHELTER'), id: string }),
])
const adoption = object({
    kind: string('ADOPT', 'RETURN'),
    owner,
    note: string,
})
const wrapped = union([adoption])

/** Each answer of `a` on a pool of 1000 values of the object, against the answer of `b`. */
const samePool = (a: AnyCodec, b: AnyCodec) => {
    let decoded = 0
    for (let seed = 1; seed <= 1000; seed++) {
        const row = adoption.encode(
            arbitraryOf(adoption, rngFrom(seed), 3) as never,
        )
        const x = a.decode(row as never)
        const y = b.decode(row as never)
        expect([failed(x), seed]).toEqual([failed(y), seed])
        if (!failed(x)) {
            decoded++
            expect(x).toEqual(y)
        }
    }
    return decoded
}

const refusal = (slice: () => unknown): string => {
    try {
        slice()
    } catch (e) {
        return (e as Error).message
    }
    return ''
}

describe('the slice of an object keeps what the slice of its one-option union keeps', () => {
    const pattern = object({ kind: string('ADOPT', 'RETURN') })
    const byObject = extract(adoption, pattern)
    const byUnion = extract(wrapped, pattern)

    it('has the decoded type of the union slice', () => {
        expectTypeOf<Decoded<typeof byObject>>().toEqualTypeOf<
            Decoded<typeof byUnion>
        >()
    })
    it('has the option count of the union slice', () => {
        expect(optionsOf(byObject)).toHaveLength(1)
        expect(optionsOf(byObject)).toEqual(optionsOf(byUnion))
    })
    it('decodes a pool of the object as the union slice does', () => {
        expect(samePool(byObject, byUnion)).toBeGreaterThan(0)
    })
})

describe('a pattern that splits a field of the object gives the options of the union slice', () => {
    const pattern = object({ owner: object({ type: string('PERSON') }) })

    for (const [name, byObject, byUnion] of [
        ['extract', extract(adoption, pattern), extract(wrapped, pattern)],
        ['exclude', exclude(adoption, pattern), exclude(wrapped, pattern)],
    ] as const) {
        it(`${name}: has the option count and the pool of the union slice`, () => {
            expect(optionsOf(byObject)).toHaveLength(optionsOf(byUnion).length)
            expect(samePool(byObject, byUnion)).toBeGreaterThan(0)
        })
    }
    it('has the decoded type of the union slice', () => {
        const a = exclude(adoption, pattern)
        const b = exclude(wrapped, pattern)
        expectTypeOf<Decoded<typeof a>>().toEqualTypeOf<Decoded<typeof b>>()
        const c = extract(adoption, pattern)
        const d = extract(wrapped, pattern)
        expectTypeOf<Decoded<typeof c>>().toEqualTypeOf<Decoded<typeof d>>()
    })
})

describe('the exclusion of a pattern that fits the whole object is never', () => {
    const pattern = object({ kind: string('ADOPT', 'RETURN') })
    it('keeps no option, as the union slice keeps none', () => {
        expect(optionsOf(exclude(adoption, pattern))).toEqual([])
        expect(optionsOf(exclude(wrapped, pattern))).toEqual([])
    })
})

describe('a pattern that no member fits extracts never on an object, as on its one-option union', () => {
    it('extracts never and excludes all for a key that no member declares', () => {
        const stray = object({ missing: string('X') })
        const kept = extract(adoption, stray)
        const rest = exclude(adoption, stray)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof adoption>
        >()
        expect(kept.def.kind).toBe('never')
        expect(extract(wrapped, stray).def.kind).toBe('never')
        expect(rest.def).toEqual(exclude(wrapped, stray).def)
        samePool(rest, adoption)
    })

    it('extracts never for a fixed position of an array, which declares no position', () => {
        const route = object({ route: array(owner) })
        const fixed = object({
            route: list(object({ type: string('PERSON') })),
        })
        const kept = extract(route, fixed)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<never>()
        expect(kept.def.kind).toBe('never')
        expect(extract(union([route]), fixed).def.kind).toBe('never')
    })

    it('refuses a split of an open key entry, with the message of the union', () => {
        const tagged = object({
            kind: string('LISTED'),
            tags: union([
                object({ id: string('tag-1') }, [string, optional(string)]),
                object({ id: string('tag-2') }, [string, optional(string)]),
            ]),
        })
        const pattern = object({ tags: object({ id: string('tag-1') }) })
        const onObject = refusal(() => extract(tagged, pattern))
        expect(onObject).toMatch(/open key entry/)
        expect(onObject).toBe(refusal(() => extract(union([tagged]), pattern)))
    })
})
