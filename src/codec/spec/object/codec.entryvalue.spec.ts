/**
 * `toEntry` returns each refusal of an item as a value, and `unsafeToEntry` throws it.
 *
 * A key that cannot print, a name of a key that the entity holds, and a numeral that the marshaller
 * cannot write are failures of the argument, so a caller that holds an item of the declared type
 * reads a `CodecError` and never a throw. The error has the `RotoriseError` of the builder as its
 * `cause`. The twin throws the value that `toEntry` returns, so it throws a `CodecError`. The type of
 * the twin is the entry, and the type of `toEntry` is the entry or the error.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'
import { decimal, string } from '../../codec'

type Pet = { petId: string; nick: string }

const Pets = tableEntry<Pet>()({ PK: ['petId'], SK: 'nick' })
const Coded = tableEntry<Pet>()(
    { PK: ['petId'], SK: 'nick' },
    { codec: { petId: string, nick: string } },
)
const Weights = tableEntry<{ id: string; weight: string }>()(
    { PK: ['id'], SK: 'weight' },
    { codec: { id: string, weight: decimal } },
)
const rex: Pet = { petId: 'p1', nick: 'rex' }

describe('toEntry returns the refusal of an item as a value', () => {
    it('returns the refusal of an empty key, with and without a codec, and names the attribute', () => {
        const check = (refused: unknown) => {
            expect(refused).toBeInstanceOf(CodecError)
            expect((refused as CodecError).kind).toBe('refused')
            expect((refused as CodecError).cause).toBeInstanceOf(RotoriseError)
            expect((refused as CodecError).message).toContain(
                "the attribute 'nick' is empty",
            )
        }
        check(Pets.toEntry({ ...rex, nick: '' }))
        check(Coded.toEntry({ ...rex, nick: '' }))
    })

    it('returns the refusal of a separator in a key part with the kind separator', () => {
        const refused = Pets.toEntry({ ...rex, petId: 'a#b' })
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).kind).toBe('separator')
    })

    it('returns the refusal of an entity that holds the name of a key', () => {
        const refused = Pets.toEntry({ ...rex, PK: 'stale' } as never)
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).message).toMatch(
            /^'PK' is a key of the schema, and the entity holds an attribute of that name/,
        )
    })

    it('returns the refusal of a numeral that the marshaller cannot write, and points to toItem', () => {
        const refused = Weights.toEntry({
            id: 'w1',
            weight: '12345678901234567890.123',
        })
        expect(refused).toBeInstanceOf(CodecError)
        expect((refused as CodecError).message).toContain(
            'Read the key from toItem',
        )
    })

    it('never throws for an item of the declared type', () => {
        for (const given of [
            rex,
            { ...rex, nick: '' },
            { ...rex, petId: '' },
            { ...rex, petId: '#', nick: '#' },
        ])
            expect(() => Pets.toEntry(given)).not.toThrow()
    })

    it('gives the entry where the item has no refusal', () => {
        expect(Pets.toEntry(rex)).toEqual({
            petId: 'p1',
            nick: 'rex',
            PK: 'PETID#p1',
            SK: 'rex',
        })
    })
})

describe('unsafeToEntry throws what toEntry returns', () => {
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
            { ...rex, PK: 'stale' } as never,
        ]) {
            const returned = Pets.toEntry(given) as CodecError
            const thrown = thrownBy(() => Pets.unsafeToEntry(given))
            expect(thrown).toBeInstanceOf(CodecError)
            expect((thrown as CodecError).kind).toBe(returned.kind)
            expect((thrown as CodecError).reason).toBe(returned.reason)
            expect((thrown as CodecError).cause).toBeInstanceOf(RotoriseError)
        }
    })

    it('gives the entry where toEntry gives the entry', () => {
        expect(Pets.unsafeToEntry(rex)).toEqual(Pets.toEntry(rex))
    })

    it('has the type of the entry, and toEntry has the entry or the error', () => {
        const entry = Pets.unsafeToEntry(rex)
        expectTypeOf(entry.PK).toEqualTypeOf<`PETID#${string}`>()
        expectTypeOf(entry.SK).toEqualTypeOf<string>()
        expectTypeOf(Pets.toEntry(rex)).toEqualTypeOf<
            typeof entry | CodecError
        >()
    })
})
