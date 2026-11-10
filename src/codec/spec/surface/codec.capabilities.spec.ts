/**
 * A codec that a term denotes holds the capabilities that the term decides.
 *
 * A codec that a slice, a meet or a scope builds is built from a term, and a caller writes the
 * same term with a constructor. The two must give one codec: the literal call of a base, the
 * `.set()` of a base and of a refinement, and the `.spec` of an object each come from the term,
 * so a slot of a built object holds the codec that the caller wrote.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec } from '../../codec'
import {
    binary,
    boolean,
    codecOfTerm,
    decimal,
    extract,
    item,
    meet,
    number,
    object,
    opaque,
    refine,
    string,
    union,
} from '../../codec'
import { dynamoNumber } from '../../prisms'
import type { Term } from '../../term'
import { sameTerm } from '../../term'

/**
 * What a codec that a term denotes holds at run time. The type of `codecOfTerm` promises the pair
 * and no more, so the one cast of this file reads the capabilities that the term decides.
 */
type Denoted = AnyCodec & {
    (...allowed: never[]): AnyCodec
    readonly set: (...allowed: never[]) => AnyCodec
    readonly spec: Record<string, Denoted | undefined>
}
const denoted = (term: Term): Denoted => codecOfTerm(term) as unknown as Denoted

describe('a constant is the codec that its own term denotes', () => {
    it('gives the constant for the term of the constant, for each base', () => {
        expect(codecOfTerm(string.def)).toBe(string)
        expect(codecOfTerm(number.def)).toBe(number)
        expect(codecOfTerm(decimal.def)).toBe(decimal)
        expect(codecOfTerm(boolean.def)).toBe(boolean)
        expect(codecOfTerm(binary.def)).toBe(binary)
        expect(codecOfTerm(dynamoNumber.def)).toBe(dynamoNumber)
    })
})

describe('a term that is equal to the term of a base denotes a codec with the capabilities of the base', () => {
    it('takes the literal call at each base, as the constant does', () => {
        // the codecs write the same attribute: two `decimal` calls build two converters, so the
        // terms are compared by what they write
        const writes = (made: AnyCodec, written: AnyCodec, value: unknown) =>
            expect(made.unsafeEncode(value as never)).toEqual(
                written.unsafeEncode(value as never),
            )
        writes(
            denoted({ kind: 'string' })('REX' as never),
            string('REX'),
            'REX',
        )
        writes(denoted({ kind: 'boolean' })(true as never), boolean(true), true)
        writes(
            denoted({ ...decimal.def })('1.5' as never),
            decimal('1.5'),
            '1.5',
        )
        writes(denoted({ ...number.def })(5 as never), number(5), 5)
    })

    it('takes the set of the base and the set of a literal at the base, and boolean has none', () => {
        const text = denoted({ kind: 'string' })
        expect(sameTerm(text.set().def, string.set().def)).toBe(true)
        expect(
            sameTerm(
                text.set('REX' as never, 'FLUFFY' as never).def,
                string.set('REX', 'FLUFFY').def,
            ),
        ).toBe(true)
        expect('set' in denoted({ kind: 'boolean' })).toBe(false)
    })

    it('takes the set of a refinement over any term', () => {
        const named = refine(
            string,
            (value): value is string => value.length > 0,
        )
        const built = denoted({ ...named.def })
        expect(built).not.toBe(named)
        expect(sameTerm(built.set().def, named.set().def)).toBe(true)
    })
})

describe('the slots of an object that a term denotes are the codecs that the caller wrote', () => {
    it('holds the constant at a member that the term names as a base', () => {
        const pet = denoted({ ...object({ name: string }).def })
        expect(pet.spec.name).toBe(string)
        expect(pet.spec.name?.set).toBeTypeOf('function')
    })

    it('holds that codec in the spec of a meet', () => {
        const both = meet(object({ name: string }), object({ chip: string }))
        expect(both.spec.name).toBe(string)
        expect(item(both).spec.chip.set).toBeTypeOf('function')
    })

    it('holds that codec in the spec of each option of the item of a union', () => {
        const pets = union([
            object({ name: string, kind: string('DOG') }),
            object({ owner: string, kind: string('CAT') }),
        ])
        expect(item(pets).spec[0]?.name).toBe(string)
        expect(item(pets).spec[1]?.owner).toBe(string)
    })

    it('holds that codec in the spec of the item of an extraction', () => {
        const pets = union([
            object({ name: string, kind: string('DOG') }),
            object({ owner: string, kind: string('CAT') }),
        ])
        const dogs = extract(pets, object({ kind: string('DOG') }))
        expect(item(dogs).spec[0]?.name).toBe(string)
    })
})

describe('what the term does not decide', () => {
    /**
     * `opaque(policy)` chooses one of three codecs by the policy, and the canonical term holds no
     * policy: the terms of the two numeric policies are other terms (a `held` with its own `via`).
     * A call on the canonical term would read a fact that the term lacks, so the term denotes a
     * codec with no call, and only the constant `opaque` has one.
     */
    it('gives no call to the canonical opaque term, and the constant has one', () => {
        expect(typeof opaque).toBe('function')
        expect(typeof codecOfTerm({ kind: 'opaq' })).toBe('object')
    })
})
