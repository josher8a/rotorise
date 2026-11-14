/**
 * `keys` and `keyCondition` return each refusal of the attributes as a value, and the twins throw it.
 *
 * A key that cannot print, a key that the attributes give no value for, and a part that prints after
 * an absent part are failures of the argument, so a caller that holds attributes of the declared type
 * reads a `CodecError` and never a throw. The error has the `RotoriseError` of the builder as its
 * `cause`. A name that the schema does not declare, and an index that the options do not declare, are
 * refused by the type, so the call is broken and throws. The twin throws the value that the method
 * returns, so it throws a `CodecError`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'
import { string } from '../../codec'

type Pet = { petId: string; shelterId: string; nick: string }

const Pets = tableEntry<Pet>()(
    {
        PK: ['petId'],
        SK: ['nick', 'petId'],
        GSI1PK: ['shelterId'],
        GSI1SK: ['nick', 'petId'],
    },
    {
        key: { partition: 'PK', sort: 'SK' },
        indexes: { G1: { partition: 'GSI1PK', sort: 'GSI1SK' } },
        codec: { petId: string, shelterId: string, nick: string },
    },
)
const rex: Pet = { petId: 'p1', shelterId: 's1', nick: 'rex' }

describe('keys returns the refusal of the attributes as a value', () => {
    it('returns the refusal of a key that lacks a component, in both forms', () => {
        const named = Pets.keys(['PK'], { shelterId: 's1' })
        const table = Pets.keys({ shelterId: 's1' })
        for (const refused of [named, table]) {
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError) {
                expect(refused.kind).toBe('refused')
                expect(refused.cause).toBeInstanceOf(RotoriseError)
                expect(refused.message).toContain('Attribute petId not found')
            }
        }
    })

    it('returns the refusal of a separator in a key part with the kind separator', () => {
        const refused = Pets.keys({ ...rex, petId: 'a#b' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.kind).toBe('separator')
    })

    it('returns the refusal of a call that names no key', () => {
        const refused = Pets.keys([], rex)
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toContain('names no key')
    })

    it('gives the keys where the attributes build each key', () => {
        expect(Pets.keys(rex)).toEqual({
            PK: { S: 'PETID#p1' },
            SK: { S: 'NICK#rex#PETID#p1' },
        })
    })
})

describe('keyCondition returns the refusal of the attributes as a value', () => {
    it('returns the refusal of a table condition that lacks a partition component', () => {
        const refused = Pets.keyCondition({ nick: 'rex' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toContain('Attribute petId not found')
    })

    it('returns the refusal of a part that prints after an absent part, for an index', () => {
        const refused = Pets.keyCondition('G1', {
            shelterId: 's1',
            petId: 'p1',
        })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError) {
            expect(refused.cause).toBeInstanceOf(RotoriseError)
            expect(refused.message).toContain(
                "'GSI1SK' gives no key and no prefix for these attributes",
            )
        }
    })

    it('returns the refusal of a separator in a sort part with the kind separator', () => {
        const refused = Pets.keyCondition('G1', {
            shelterId: 's1',
            nick: 'a#b',
        })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.kind).toBe('separator')
    })

    it('gives the condition where the attributes build it', () => {
        expect(Pets.keyCondition({ petId: 'p1', nick: 'rex' })).toEqual({
            partition: { name: 'PK', value: { S: 'PETID#p1' } },
            sort: { name: 'SK', equals: { S: 'NICK#rex#PETID#p1' } },
        })
    })
})

describe('keys and keyCondition never throw for attributes of the declared type', () => {
    it('returns a value for each partial entity of the pool', () => {
        const given: Partial<Pet>[] = [
            {},
            { petId: 'p1' },
            { nick: 'rex' },
            { petId: '', nick: '' },
            { petId: '#', shelterId: '#', nick: '#' },
            rex,
        ]
        for (const attributes of given) {
            expect(() => Pets.keys(attributes)).not.toThrow()
            expect(() => Pets.keys(['SK', 'PK'], attributes)).not.toThrow()
            expect(() => Pets.keyCondition(attributes)).not.toThrow()
            expect(() => Pets.keyCondition('G1', attributes)).not.toThrow()
        }
    })
})

describe('a call that the type refuses is broken, and throws', () => {
    it('throws for an index that the options do not declare', () => {
        expect(() => Pets.keyCondition('NOPE' as never, rex)).toThrow(
            RotoriseError,
        )
    })

    it('throws for a key name that the schema does not declare', () => {
        expect(() => Pets.keys(['NOPE'] as never, rex)).toThrow(RotoriseError)
    })

    it('throws for the table form of an entry that declares no key option', () => {
        const Plain = tableEntry<Pet>()({ PK: ['petId'] }) as unknown as {
            keys: (given: object) => unknown
        }
        expect(() => Plain.keys(rex)).toThrow(RotoriseError)
    })
})

describe('the twins throw what the methods return', () => {
    const thrownBy = (run: () => unknown): unknown => {
        try {
            run()
        } catch (thrown) {
            return thrown
        }
        return undefined
    }

    it('throws a CodecError with the kind and the reason of the value, for keys', () => {
        for (const given of [{ shelterId: 's1' }, { ...rex, petId: 'a#b' }]) {
            const returned = Pets.keys(given)
            const thrown = thrownBy(() => Pets.unsafeKeys(given))
            expect(returned).toBeInstanceOf(CodecError)
            expect(thrown).toBeInstanceOf(CodecError)
            if (
                returned instanceof CodecError &&
                thrown instanceof CodecError
            ) {
                expect(thrown.kind).toBe(returned.kind)
                expect(thrown.reason).toBe(returned.reason)
            }
        }
    })

    it('throws a CodecError with the kind and the reason of the value, for keyCondition', () => {
        for (const given of [
            { shelterId: 's1', petId: 'p1' },
            { shelterId: 's1', nick: 'a#b' },
        ]) {
            const returned = Pets.keyCondition('G1', given)
            const thrown = thrownBy(() => Pets.unsafeKeyCondition('G1', given))
            expect(returned).toBeInstanceOf(CodecError)
            expect(thrown).toBeInstanceOf(CodecError)
            if (
                returned instanceof CodecError &&
                thrown instanceof CodecError
            ) {
                expect(thrown.kind).toBe(returned.kind)
                expect(thrown.reason).toBe(returned.reason)
            }
        }
        expect(
            thrownBy(() => Pets.unsafeKeyCondition({ nick: 'rex' })),
        ).toBeInstanceOf(CodecError)
    })

    it('gives the value where the method gives the value', () => {
        expect(Pets.unsafeKeys(rex)).toEqual(Pets.keys(rex))
        expect(Pets.unsafeKeyCondition({ petId: 'p1', nick: 'rex' })).toEqual(
            Pets.keyCondition({ petId: 'p1', nick: 'rex' }),
        )
    })

    it('has the type that the method had, and the method has that type or the error', () => {
        const names = Pets.unsafeKeys(['PK'], rex)
        const table = Pets.unsafeKeys(rex)
        const condition = Pets.unsafeKeyCondition({ petId: 'p1', nick: 'rex' })
        const indexed = Pets.unsafeKeyCondition('G1', { shelterId: 's1' })
        expectTypeOf(Pets.keys(['PK'], rex)).toEqualTypeOf<
            typeof names | CodecError
        >()
        expectTypeOf(Pets.keys(rex)).toEqualTypeOf<typeof table | CodecError>()
        expectTypeOf(
            Pets.keyCondition({ petId: 'p1', nick: 'rex' }),
        ).toEqualTypeOf<typeof condition | CodecError>()
        expectTypeOf(
            Pets.keyCondition('G1', { shelterId: 's1' }),
        ).toEqualTypeOf<typeof indexed | CodecError>()
        expectTypeOf(indexed.index).toEqualTypeOf<'G1'>()
    })
})
