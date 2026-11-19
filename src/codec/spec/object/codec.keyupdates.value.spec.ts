/**
 * `keyUpdates` refuses a change at a value that the codec refuses.
 *
 * A change at a name writes the value at the name, so the codec of the name must admit the value. The
 * run time asks the codec at each changed name, and the type refuses a name in excess at each depth.
 * A write of `undefined` is a removal, as the model states `changed: name → none`, so the codec
 * checks no value for it.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    array,
    CodecError,
    discriminatedUnion,
    item,
    number,
    object,
    opaque,
    optional,
    string,
} from '../../codec'

type Pet = {
    petId: string
    note: string
    nick?: string
    owner: { name: string; alias?: string }
    address: { street: string; zip: string }
    legs: { id: number }[]
}
const Coded = tableEntry<Pet>()(
    { PK: ['petId'], GSI1PK: ['owner.name'] },
    {
        codec: {
            petId: string,
            note: string,
            nick: optional(string),
            owner: object({ name: string, alias: optional(string) }),
            address: object({ street: string, zip: string }),
            legs: array(object({ id: number })),
        } as never,
    },
)
const Plain = tableEntry<Pet>()({ PK: ['petId'], GSI1PK: ['owner.name'] })

type Dog = { kind: 'dog'; petId: string; bark: string }
type Cat = { kind: 'cat'; petId: string; bark: number }
const Animals = tableEntry<Dog | Cat>()(
    { PK: ['petId'] },
    {
        codec: item(
            discriminatedUnion('kind', [
                object({ kind: string('dog'), petId: string, bark: string }),
                object({ kind: string('cat'), petId: string, bark: number }),
            ]),
        ),
    },
)

type MetaKeys = { TAG: 'META'; id: string }
type Meta = MetaKeys & { [key: string]: unknown }
const Open = tableEntry<Meta, never, MetaKeys>()(
    { PK: ['id'] },
    {
        codec: item(
            object({ TAG: string('META'), id: string }, [
                string,
                optional(opaque('lossy')),
            ]),
        ),
    },
)

/** A change that the type refuses, as a caller with no type check writes it. */
const through = (change: Record<string, unknown>) => change as never

const refusalOf = (given: unknown): CodecError => {
    expect(given).toBeInstanceOf(CodecError)
    return given as CodecError
}

describe('keyUpdates refuses an object that the codec refuses', () => {
    it('refuses an object with a name that the codec does not declare', () => {
        const refusal = refusalOf(
            Coded.keyUpdates(
                through({ owner: { name: 'b', alias: 'k', ghost: 'n' } }),
            ),
        )
        expect(refusal.kind).toBe('refused')
        expect(refusal.reason).toBe(
            "'ghost' is not an attribute this codec declares",
        )
    })

    it('refuses an object that lacks a required name, at an attribute that no key reads', () => {
        const refusal = refusalOf(
            Coded.keyUpdates(through({ address: { street: 's' } })),
        )
        expect(refusal.reason).toBe("'zip' is required and was not given")
    })

    it('refuses an object with a name that the codec does not declare, at an attribute that no key reads', () => {
        const refusal = refusalOf(
            Coded.keyUpdates(
                through({ address: { street: 's', zip: 'z', ghost: 'n' } }),
            ),
        )
        expect(refusal.reason).toBe(
            "'ghost' is not an attribute this codec declares",
        )
    })

    it('refuses a value of another type at a path that a key reads, with the refusal of the key', () => {
        refusalOf(Coded.keyUpdates(through({ 'owner.name': 5 })))
    })

    it('refuses a value of another type at a top-level name that no key reads', () => {
        refusalOf(Coded.keyUpdates(through({ note: 5 })))
    })

    it('names the path of the change in the refusal, as toItem names the attribute', () => {
        const nested = { owner: { name: 'b', alias: 'k', ghost: 'n' } }
        expect(refusalOf(Coded.keyUpdates(through(nested))).path).toEqual([
            'owner',
        ])
        expect(
            refusalOf(
                Coded.keyUpdates(through({ legs: [{ id: 1, ghost: 1 }] })),
            ).path,
        ).toEqual(['legs', 0])
        expect(
            refusalOf(Coded.keyUpdates(through({ 'address.zip': 5 }))).path,
        ).toEqual(['address', 'zip'])
    })

    it('throws the same refusal from the twin that throws', () => {
        expect(() =>
            Coded.unsafeKeyUpdates(
                through({ owner: { name: 'b', ghost: 'n' } }),
            ),
        ).toThrow("'ghost' is not an attribute this codec declares")
    })

    it('accepts an object that the codec admits, and rebuilds the key', () => {
        expect(
            Coded.unsafeKeyUpdates({ owner: { name: 'b', alias: 'k' } }),
        ).toEqual({ set: { GSI1PK: { S: 'NAME#b' } }, remove: [] })
    })
})

describe('keyUpdates reads a write of undefined as a removal, which is no value for the codec', () => {
    it('gives the removal at a required name, as the model states changed: name → none', () => {
        expect(Coded.unsafeKeyUpdates(through({ note: undefined }))).toEqual({
            set: {},
            remove: [],
        })
    })

    it('gives the removal at an optional name', () => {
        expect(Coded.unsafeKeyUpdates(through({ nick: undefined }))).toEqual({
            set: {},
            remove: [],
        })
    })

    it('gives the removal at a name below an object that no key reads', () => {
        expect(
            Coded.unsafeKeyUpdates(through({ 'owner.alias': undefined })),
        ).toEqual({ set: {}, remove: [] })
    })
})

describe('keyUpdates of a tagged codec refuses a value that no variant at the name admits', () => {
    it('accepts a value that one variant admits, where the change holds no discriminator', () => {
        expect(Animals.unsafeKeyUpdates(through({ bark: 'x' }))).toEqual({
            set: {},
            remove: [],
        })
        expect(Animals.unsafeKeyUpdates(through({ bark: 3 }))).toEqual({
            set: {},
            remove: [],
        })
    })

    it('refuses a value that no variant admits', () => {
        refusalOf(Animals.keyUpdates(through({ bark: true })))
    })

    it('reads only the chosen variant where the change holds the discriminator', () => {
        refusalOf(Animals.keyUpdates(through({ kind: 'dog', bark: 3 })))
        expect(Animals.unsafeKeyUpdates({ kind: 'cat', bark: 3 })).toEqual({
            set: {},
            remove: [],
        })
    })
})

describe('keyUpdates of an entry with a rest asks the codec of the rest', () => {
    it('accepts a value that the codec of the rest admits', () => {
        expect(Open.unsafeKeyUpdates({ extra: 'x' })).toEqual({
            set: {},
            remove: [],
        })
    })
})

describe('keyUpdates of an entry with no codec checks no value', () => {
    it('gives the patch for an object that no codec reads, because the run time holds no fact about the value', () => {
        expect(
            Plain.keyUpdates(
                through({ owner: { name: 'b', alias: 'k', ghost: 'n' } }),
            ),
        ).toEqual({ set: { GSI1PK: { S: 'NAME#b' } }, remove: [] })
    })
})

describe('the type of a change refuses a name in excess at each depth', () => {
    const owner = { name: 'b', ghost: 'n' }
    const deep = { name: 'b', alias: 'k' }

    it('refuses a name in excess below an object, in a fresh literal and in a variable', () => {
        const refused = () => {
            // @ts-expect-error the owner holds no name ghost
            Coded.keyUpdates({ owner: { name: 'b', ghost: 'n' } })
            // @ts-expect-error the same name, read from a variable
            Coded.keyUpdates({ owner })
        }
        expect(refused).toBeTypeOf('function')
    })

    it('accepts a name that the object holds, a list of objects and a record', () => {
        const accepted = () => {
            Coded.keyUpdates({ owner: deep })
            Coded.keyUpdates({ legs: [{ id: 1 }] })
        }
        expect(accepted).toBeTypeOf('function')
    })
})
