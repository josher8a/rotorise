/**
 * `toEntry` of an entry with a codec refuses an item that the codec refuses.
 *
 * `toEntry` prints the keys from the attributes of the item, and returns the item with the keys.
 * `toItem` of the same entry refuses an item that the codec refuses, so `toEntry` asks the codec too,
 * after the keys: a refusal of a key keeps its own kind and text. The type refuses a name in excess
 * at each depth. An entry with no codec holds no codec to ask, so it checks no value.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    CodecError,
    discriminatedUnion,
    item,
    number,
    object,
    string,
} from '../../codec'

type Pet = {
    petId: string
    note: string
    owner: { name: string; nick: string }
}
const spec = {
    petId: string,
    note: string,
    owner: object({ name: string, nick: string }),
}
const Coded = tableEntry<Pet>()(
    { PK: ['petId'], GSI1PK: ['owner.name'] },
    { codec: spec },
)
const Plain = tableEntry<Pet>()({ PK: ['petId'], GSI1PK: ['owner.name'] })
const pet: Pet = { petId: 'p', note: 'n', owner: { name: 'b', nick: 'k' } }
/** The item with a name in excess below the owner. */
const ghosted = { ...pet, owner: { name: 'b', nick: 'k', ghost: 'g' } }

type Dog = { kind: 'dog'; petId: string; bark: string }
type Cat = { kind: 'cat'; petId: string; lives: number }
const Animals = tableEntry<Dog | Cat>()(
    { PK: ['petId'] },
    {
        codec: item(
            discriminatedUnion('kind', [
                object({ kind: string('dog'), petId: string, bark: string }),
                object({ kind: string('cat'), petId: string, lives: number }),
            ]),
        ),
    },
)

/** An item that the type refuses, as a caller with no type check writes it. */
const through = (given: Record<string, unknown>) => given as never

const refusalOf = (given: unknown): CodecError => {
    expect(given).toBeInstanceOf(CodecError)
    return given as CodecError
}

describe('toEntry of an entry with a codec refuses an item that the codec refuses', () => {
    it('refuses an object with a name that the codec does not declare', () => {
        const refusal = refusalOf(Coded.toEntry(through(ghosted)))
        expect(refusal.kind).toBe('refused')
        expect(refusal.reason).toBe(
            "'ghost' is not an attribute this codec declares",
        )
    })

    it('refuses an object that lacks a required name', () => {
        const refusal = refusalOf(
            Coded.toEntry(through({ ...pet, owner: { name: 'b' } })),
        )
        expect(refusal.reason).toBe("'nick' is required and was not given")
    })

    it('refuses a name in excess at the top level', () => {
        refusalOf(Coded.toEntry(through({ ...pet, ghost: 1 })))
    })

    it('refuses a value of another type at a name that no key reads', () => {
        refusalOf(Coded.toEntry(through({ ...pet, note: 5 })))
    })

    it('keeps the kind and the text of a refusal of a key, where the codec refuses the item too', () => {
        const refusal = refusalOf(
            Coded.toEntry(through({ ...pet, petId: '', note: 5 })),
        )
        expect(refusal.kind).toBe('key')
    })

    it('throws the same refusal from the twin that throws', () => {
        expect(() => Coded.unsafeToEntry(through(ghosted))).toThrow(
            "'ghost' is not an attribute this codec declares",
        )
    })

    it('builds the entry of an item that the codec admits, with the keys', () => {
        expect(Coded.unsafeToEntry(pet)).toEqual({
            ...pet,
            PK: 'PETID#p',
            GSI1PK: 'NAME#b',
        })
    })
})

describe('toEntry of an entry with a tagged codec reads the variant that the item chooses', () => {
    it('refuses an item that the chosen variant refuses', () => {
        refusalOf(
            Animals.toEntry(through({ kind: 'cat', petId: 'p', bark: 'x' })),
        )
    })

    it('builds the entry of an item that the chosen variant admits', () => {
        expect(
            Animals.unsafeToEntry({ kind: 'dog', petId: 'p', bark: 'x' }),
        ).toEqual({ kind: 'dog', petId: 'p', bark: 'x', PK: 'PETID#p' })
    })
})

describe('toEntry of an entry with no codec checks no value of the item', () => {
    it('builds the entry of an item that no codec reads, because there is no codec to ask', () => {
        expect(Plain.unsafeToEntry(through(ghosted))).toMatchObject({
            PK: 'PETID#p',
            GSI1PK: 'NAME#b',
        })
    })
})

describe('the type of the item of toEntry refuses a name in excess at each depth', () => {
    it('refuses a name in excess below an object, in a fresh literal and in a variable, and at the top level', () => {
        const extra = {
            petId: 'p',
            note: 'n',
            owner: { name: 'b', nick: 'k', ghost: 'g' },
        }
        const refused = () => {
            Coded.toEntry({
                ...pet,
                // @ts-expect-error the owner holds no name ghost
                owner: { name: 'b', nick: 'k', ghost: 'g' },
            })
            // @ts-expect-error the same name, read from a variable
            Coded.toEntry(extra)
            // @ts-expect-error the item holds no name ghost
            Coded.toEntry({ ...pet, ghost: 1 })
            // @ts-expect-error the twin that throws reads the same type
            Coded.unsafeToEntry(extra)
        }
        expect(refused).toBeTypeOf('function')
    })
})
