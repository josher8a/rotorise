/**
 * An option that holds no value fits every pattern, so the exclusion drops it.
 *
 * A `held` whose inner term holds no value holds none, and the term names the inner term by a
 * `ref` to an entry of a scope. The fit reads the name in the scope that binds it, as the run time
 * reads the closed copy.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { Decoded } from '../../codec'
import {
    CodecError,
    exclude,
    held,
    never,
    object,
    ref,
    scope,
    string,
    union,
} from '../../codec'

describe('an option that is an entry whose held term names an empty entry', () => {
    const { Held } = scope({
        Gone: never,
        Held: held(ref('Gone'), string, {
            encode: (name: string) => new CodecError(`'${name}' is gone`),
            decode: (_gone: unknown) => '',
        }),
    })
    const pets = union([Held, object({ name: string })])

    it('is dropped by the exclusion of a pattern that every option fits, as the run time drops it', () => {
        const rest = exclude(pets, object({ name: string }))
        expect(rest.def.kind).toBe('never')
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<never>()
    })
})

/**
 * The defect that remains: a `held` that is an option of the union of an entry. The head of the
 * slice carries no scope, so the type cannot read the name, and the type keeps the option. The type
 * is wider than the value, and each value that the run time gives fits the type.
 */
describe('an option of the union of an entry whose held term names an empty entry', () => {
    const { Pets } = scope({
        Gone: never,
        Pets: union([
            held(ref('Gone'), string, {
                encode: (name: string) => new CodecError(`'${name}' is gone`),
                decode: (_gone: unknown) => '',
            }),
            object({ name: string }),
        ]),
    })

    it('is dropped by the exclusion at run time, and the type keeps the option', () => {
        const rest = exclude(Pets, object({ name: string }))
        expect(rest.def.kind).toBe('never')
        expectTypeOf<Decoded<typeof rest>>().not.toEqualTypeOf<never>()
    })
})
