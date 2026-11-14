/**
 * `key` returns each refusal of the attributes as a value, and `unsafeKey` throws it.
 *
 * A full key that prints no segment, a component that the attributes lack, a part that holds the
 * separator, a discriminator that selects no arm, and a value that no key can print are failures of
 * the attributes, so a caller that holds attributes of the declared type reads a `CodecError` and never
 * a throw. The error has the `RotoriseError` of the builder as its `cause`. A key name that the schema
 * does not declare, and a depth that is no non-negative integer, are refused by the type, so the call is
 * broken and throws a `RotoriseError`. The twin throws the value that `key` returns. This pass changes
 * the channel only: a partial key keeps the outcome that it had.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'

type Pet = { petId: string; nick: string }

const Pets = tableEntry<Pet>()({ PK: ['petId'], SK: 'nick' })
const rex: Pet = { petId: 'p1', nick: 'rex' }

type Animal = { petId: string; kind: 'DOG' | 'CAT' }
const Animals = tableEntry<Animal>()({
    PK: ['petId'],
    SK: { discriminator: 'kind', spec: { DOG: ['petId'], CAT: null } },
})

describe('key returns the refusal of the attributes as a value', () => {
    it('returns the refusal of an empty full key, and names the attribute', () => {
        const refused = Pets.key('SK', { ...rex, nick: '' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError) {
            expect(refused.kind).toBe('refused')
            expect(refused.cause).toBeInstanceOf(RotoriseError)
            expect(refused.message).toContain("the attribute 'nick' is empty")
        }
    })

    it('returns the refusal of a full key that lacks a component', () => {
        const refused = Pets.key('PK', {} as never)
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toContain('Attribute petId not found')
    })

    it('returns the refusal of a separator in a key part with the kind separator', () => {
        const refused = Pets.key('PK', { ...rex, petId: 'a#b' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.kind).toBe('separator')
    })

    it('returns the refusal of a discriminator that the attributes lack', () => {
        const refused = Animals.key('SK', { petId: 'p1' } as never)
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toContain('Discriminator kind not found')
    })

    it('returns the refusal of a value that is an object, where the entry has no codec', () => {
        const refused = Pets.key('PK', { petId: { x: 1 } } as never)
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toContain('is an object')
    })

    it('gives the key where the attributes build it, and none where the arm is null', () => {
        expect(Pets.key('PK', rex)).toBe('PETID#p1')
        expect(Animals.key('SK', { petId: 'p1', kind: 'CAT' })).toBeUndefined()
    })

    it('keeps the outcome of a partial key, which this pass does not change', () => {
        expect(Pets.key('PK', {} as never, { allowPartial: true })).toBe('')
        expect(Pets.key('PK', rex, { depth: 0 })).toBe('')
    })
})

describe('key never throws for attributes of the declared type', () => {
    it('returns a value for each item of a list', () => {
        const given: Pet[] = [
            rex,
            { ...rex, nick: '' },
            { ...rex, petId: '' },
            { petId: '#', nick: '#' },
        ]
        for (const attributes of given) {
            expect(() => Pets.key('PK', attributes)).not.toThrow()
            expect(() => Pets.key('SK', attributes)).not.toThrow()
        }
    })
})

describe('a call that the type refuses is broken, and throws', () => {
    it('throws for a key name that the schema does not declare', () => {
        expect(() => Pets.key('NOPE' as never, rex as never)).toThrow(
            RotoriseError,
        )
    })

    it('throws for a depth that is no non-negative integer', () => {
        expect(() => Pets.key('PK', rex, { depth: -1 } as never)).toThrow(
            RotoriseError,
        )
        expect(() => Pets.key('PK', rex, { depth: 1.5 } as never)).toThrow(
            RotoriseError,
        )
    })
})

describe('unsafeKey throws what key returns', () => {
    const thrownBy = (run: () => unknown): unknown => {
        try {
            run()
        } catch (thrown) {
            return thrown
        }
        return undefined
    }

    it('throws a CodecError with the kind and the reason of the value', () => {
        for (const given of [
            { ...rex, nick: '' },
            { ...rex, petId: 'a#b' },
            { nick: 'rex' } as never,
        ]) {
            const returned = Pets.key('PK', given)
            const thrown = thrownBy(() => Pets.unsafeKey('PK', given))
            const second = Pets.key('SK', given)
            expect(
                returned instanceof CodecError || second instanceof CodecError,
            ).toBe(true)
            if (returned instanceof CodecError) {
                expect(thrown).toBeInstanceOf(CodecError)
                if (thrown instanceof CodecError) {
                    expect(thrown.kind).toBe(returned.kind)
                    expect(thrown.reason).toBe(returned.reason)
                    expect(thrown.cause).toBeInstanceOf(RotoriseError)
                }
            }
        }
        const empty = Pets.key('SK', { ...rex, nick: '' })
        const emptyThrown = thrownBy(() =>
            Pets.unsafeKey('SK', { ...rex, nick: '' }),
        )
        expect(empty).toBeInstanceOf(CodecError)
        expect(emptyThrown).toBeInstanceOf(CodecError)
        if (empty instanceof CodecError && emptyThrown instanceof CodecError) {
            expect(emptyThrown.kind).toBe(empty.kind)
            expect(emptyThrown.reason).toBe(empty.reason)
        }
    })

    it('gives the key where key gives the key', () => {
        expect(Pets.unsafeKey('PK', rex)).toBe(Pets.key('PK', rex))
    })

    it('has the type that key had, and key has that type or the error', () => {
        const key = Pets.unsafeKey('PK', rex)
        expectTypeOf(key).toEqualTypeOf<`PETID#${string}`>()
        expectTypeOf(Pets.key('PK', rex)).toEqualTypeOf<
            typeof key | CodecError
        >()
    })
})
