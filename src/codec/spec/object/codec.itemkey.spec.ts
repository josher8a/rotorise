/**
 * `toItem` has one channel: each refusal is a value.
 *
 * The codec refuses a value that it cannot write, and a key refuses a component that it cannot print.
 * Both come back as a `CodecError`, so a caller that holds an item of the declared type never reads a
 * throw. The error of a key has the `RotoriseError` of the builder as its cause, and the error of the
 * codec has none, so a reader tells the two apart. `unsafeToItem` throws the value that `toItem`
 * returns.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'
import { item, object, optional, string } from '../../codec'

type Pet = { petId: string; nick: string }

const Pets = tableEntry<Pet>()(
    { PK: ['petId'], SK: 'nick' },
    {
        key: { partition: 'PK', sort: 'SK' },
        codec: { petId: string, nick: string },
    },
)

const rex: Pet = { petId: 'p1', nick: 'rex' }

describe('toItem returns the refusal of a key as a value', () => {
    it('returns the refusal of an empty key, and names the attribute', () => {
        const refused = Pets.toItem({ ...rex, nick: '' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError) expect(refused.kind).toBe('refused')
        if (refused instanceof CodecError)
            expect(refused.message).toContain("the attribute 'nick' is empty")
    })

    it('returns the refusal of a separator in a key part with the kind separator', () => {
        const refused = Pets.toItem({ ...rex, petId: 'a#b' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.kind).toBe('separator')
        if (refused instanceof CodecError)
            expect(refused.message).toContain(
                'the print of petId holds the separator',
            )
    })

    it('returns the refusal of a write that holds the name of a key, where the codec is open', () => {
        const Open = tableEntry<{ petId: string }>()(
            { PK: ['petId'] },
            {
                codec: item(
                    object({ petId: string }, [
                        string,
                        optional(string),
                    ]) as never,
                ) as never,
            },
        ) as unknown as {
            toItem: (row: object) => unknown
        }
        const refused = Open.toItem({ petId: 'p1', PK: 'stale' })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toMatch(
                /^'PK' is a key of the schema, and the write of the codec holds an attribute of that name/,
            )
    })

    it('never throws for an item of the declared type', () => {
        for (const given of [
            rex,
            { ...rex, nick: '' },
            { ...rex, petId: '' },
            { ...rex, petId: '#', nick: '#' },
        ])
            expect(() => Pets.toItem(given)).not.toThrow()
    })

    it('tells a refusal of a key from a refusal of the codec by the cause', () => {
        const ofKey = Pets.toItem({ ...rex, nick: '' })
        // a caller without the type passes a number where the codec writes a string
        const ofCodec = Pets.toItem({ ...rex, nick: 5 as never })
        expect(ofKey).toBeInstanceOf(CodecError)
        expect(ofCodec).toBeInstanceOf(CodecError)
        if (ofKey instanceof CodecError)
            expect(ofKey.cause).toBeInstanceOf(RotoriseError)
        if (ofCodec instanceof CodecError) expect(ofCodec.cause).toBeUndefined()
    })
})

describe('unsafeToItem throws what toItem returns', () => {
    const thrownBy = (run: () => unknown): unknown => {
        try {
            run()
        } catch (thrown) {
            return thrown
        }
        return undefined
    }

    it('throws the error of a key with the kind and the reason of the value', () => {
        for (const given of [
            { ...rex, nick: '' },
            { ...rex, petId: 'a#b' },
            { ...rex, nick: 5 as never },
        ]) {
            const returned = Pets.toItem(given)
            const thrown = thrownBy(() => Pets.unsafeToItem(given))
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

    it('gives the item where toItem gives the item', () => {
        expect(Pets.unsafeToItem(rex)).toEqual(Pets.toItem(rex))
    })
})
