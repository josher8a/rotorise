/**
 * `keyUpdates` refuses a change at a name that the entry cannot write.
 *
 * The type refuses a name that the entity does not hold, and a call through a cast reaches the run
 * time. With a codec, the codec states the names, so the run time returns the refusal of the codec.
 * With no codec, the run time holds no fact that tells `note` from `ghost`, so the entry refuses only
 * a name that is no path.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import {
    CodecError,
    discriminatedUnion,
    item,
    number,
    object,
    opaque,
    optional,
    string,
} from '../../codec'

type Owned = { petId: string; note: string; owner: { name: string } }
const Plain = tableEntry<Owned>()({ PK: ['petId'], GSI1PK: ['owner.name'] })
const Coded = tableEntry<Owned>()(
    { PK: ['petId'], GSI1PK: ['owner.name'] },
    {
        codec: item(
            object({
                petId: string,
                note: string,
                owner: object({ name: string }),
            }),
        ),
    },
)

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

describe('keyUpdates of an entry with a codec refuses a name that the codec does not write', () => {
    it('refuses a change at a name that the codec does not declare, with the kind of the codec', () => {
        const refusal = refusalOf(Coded.keyUpdates(through({ ghost: 1 })))
        expect(refusal.kind).toBe('vacant')
        expect(refusal.reason).toBe("no attribute is declared at 'ghost'")
    })

    it('refuses a dotted name below a declared object that the object does not declare, as a path', () => {
        const refusal = refusalOf(
            Coded.keyUpdates(through({ 'owner.nick': 'bob' })),
        )
        expect(refusal.kind).toBe('vacant')
        expect(refusal.reason).toBe("no attribute is declared at 'owner.nick'")
    })

    it('refuses the empty name, because a name has a character', () => {
        expect(
            refusalOf(Coded.keyUpdates(through({ '': 1 }))).reason,
        ).toContain('a name has a character')
    })

    it('throws the same refusal from the twin that throws', () => {
        expect(() => Coded.unsafeKeyUpdates(through({ ghost: 1 }))).toThrow(
            "no attribute is declared at 'ghost'",
        )
    })

    it('accepts a declared name that no key reads, and gives the empty patch', () => {
        expect(Coded.unsafeKeyUpdates({ note: 'n' })).toEqual({
            set: {},
            remove: [],
        })
    })

    it('accepts a dotted name that the codec enters, and rebuilds the key', () => {
        expect(Coded.unsafeKeyUpdates({ 'owner.name': 'bob' })).toEqual({
            set: { GSI1PK: { S: 'NAME#bob' } },
            remove: [],
        })
    })
})

describe('keyUpdates of an entry with a rest holds each name that the spec lacks', () => {
    it('accepts a name that the rest holds', () => {
        expect(Open.unsafeKeyUpdates({ extra: 'x' })).toEqual({
            set: {},
            remove: [],
        })
    })

    it('gives the refusal of the codec for a path below an attribute of the rest', () => {
        const refusal = refusalOf(Open.keyUpdates({ 'extra.x': 'x' }))
        expect(refusal.kind).toBe('refused')
        expect(refusal.reason).toContain('a path cannot go into an adapter')
    })
})

describe('keyUpdates of an entry with a tagged codec refuses a name that every variant refuses', () => {
    it('refuses a name that no variant declares', () => {
        const refusal = refusalOf(Animals.keyUpdates(through({ ghost: 1 })))
        expect(refusal.kind).toBe('vacant')
    })

    it('accepts a name that one variant declares, where the change holds no discriminator', () => {
        expect(Animals.unsafeKeyUpdates({ bark: 'x' })).toEqual({
            set: {},
            remove: [],
        })
    })

    it('refuses a name of another variant where the discriminator chooses the variant', () => {
        const refusal = refusalOf(
            Animals.keyUpdates(through({ kind: 'dog', lives: 1 })),
        )
        expect(refusal.kind).toBe('vacant')
        expect(refusal.reason).toBe("no attribute is declared at 'lives'")
    })

    it('accepts a name of the chosen variant, and rebuilds the key from a name that both variants hold', () => {
        expect(Animals.unsafeKeyUpdates({ kind: 'dog', bark: 'x' })).toEqual({
            set: {},
            remove: [],
        })
        expect(Animals.unsafeKeyUpdates({ kind: 'cat', petId: 'p' })).toEqual({
            set: { PK: { S: 'PETID#p' } },
            remove: [],
        })
    })
})

describe('keyUpdates of an entry with no codec refuses only a name that is no key path', () => {
    it('gives the empty patch for a well formed name that no key reads, because the run time holds no fact about the name', () => {
        expect(Plain.unsafeKeyUpdates({ note: 'n' })).toEqual({
            set: {},
            remove: [],
        })
        expect(Plain.keyUpdates(through({ ghost: 1 }))).toEqual({
            set: {},
            remove: [],
        })
    })

    it('refuses a name with an empty segment, with the kind of the parser', () => {
        const refusal = refusalOf(Plain.keyUpdates(through({ 'a..b': 1 })))
        expect(refusal.kind).toBe('refused')
    })

    it('refuses a name that holds a position, because a key does not read into a list', () => {
        const refusal = refusalOf(Plain.keyUpdates(through({ 'a[0]': 1 })))
        expect(refusal.kind).toBe('key')
    })

    it('refuses the empty name', () => {
        refusalOf(Plain.keyUpdates(through({ '': 1 })))
    })

    it('throws the refusal from the twin that throws', () => {
        expect(() => Plain.unsafeKeyUpdates(through({ 'a..b': 1 }))).toThrow(
            "'a..b' is no document path",
        )
    })
})

describe('the type of a change reads a name with a dot as a path', () => {
    type Dotted = { id: string; 'a.b': string }
    const Flat = tableEntry<Dotted>()({ PK: ['id'] })

    it('refuses a flat name with a dot that no key reads as a path, as the run time reads the name as a path', () => {
        const refused = () =>
            // @ts-expect-error 'a.b' is a path, and no key reads it
            Flat.keyUpdates({ 'a.b': 'x' })
        expect(refused).toBeTypeOf('function')
    })
})
