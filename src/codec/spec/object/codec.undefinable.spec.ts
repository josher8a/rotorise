/**
 * `undefinable` — a key that is always there, holding `undefined` when the row has no attribute.
 *
 * Two claims carry the mark and both are checked here: it stores what `optional` stores, byte for
 * byte, and it is the stricter of the pair — `optional` reads `{ k: undefined }` back as `{}`,
 * while here the round trip is an equality.
 */
import { describe, expect, it } from 'vitest'
import type { Encoded } from '../../codec'
import {
    boolean,
    CodecError,
    item,
    object,
    optional,
    string,
    undefinable,
} from '../../codec'
import { leanVector } from '../../lean'
import { checkRoundTrip, checkStable } from '../../testing'

type Pet = {
    id: string
    // the spelling this mark exists for: the key is always there, the value may not be
    nickname: string | undefined
    chipped: boolean | undefined
}

const Pet = item(
    object({
        id: string,
        nickname: undefinable(string),
        chipped: undefinable(boolean),
    }),
)

/** The same entity with the other mark, for the comparisons below. */
const Loose = item(
    object({
        id: string,
        nickname: optional(string),
    }),
)

describe('what it stores', () => {
    it('writes no attribute at all when the value is undefined', () => {
        const row = Pet.unsafeEncode({
            id: 'p1',
            nickname: undefined,
            chipped: undefined,
        })
        expect(row).toEqual({ id: { S: 'p1' } })
        expect('nickname' in row).toBe(false)
        expect('chipped' in row).toBe(false)
    })

    /** `null` is a value DynamoDB holds; `undefined` is the absence of one. */
    it('never writes NULL for an undefined value', () => {
        const row = Pet.unsafeEncode({
            id: 'p1',
            nickname: undefined,
            chipped: undefined,
        })
        expect(JSON.stringify(row)).not.toContain('NULL')
    })

    it('writes the attribute normally when there is a value', () => {
        expect(
            Pet.unsafeEncode({
                id: 'p1',
                nickname: 'Rex',
                chipped: true,
            }),
        ).toEqual({
            id: { S: 'p1' },
            nickname: { S: 'Rex' },
            chipped: { BOOL: true },
        })
    })

    it('stores what optional stores', () => {
        expect(
            Pet.unsafeEncode({
                id: 'p1',
                nickname: undefined,
                chipped: undefined,
            }),
        ).toEqual(Loose.unsafeEncode({ id: 'p1' }))
        expect(
            Pet.unsafeEncode({ id: 'p1', nickname: 'Rex', chipped: undefined }),
        ).toEqual(Loose.unsafeEncode({ id: 'p1', nickname: 'Rex' }))
    })
})

describe('what it reads back', () => {
    it('gives the key back holding undefined when the attribute is absent', () => {
        const pet = Pet.unsafeDecode({ id: { S: 'p1' } })
        expect(pet.nickname).toBeUndefined()
        // the assertion that matters: the key is *there*, so the value agrees with its own type
        expect(Object.keys(pet).sort()).toEqual(['chipped', 'id', 'nickname'])
        expect('nickname' in pet).toBe(true)
    })

    it('and optional does not, which is the whole difference', () => {
        expect(Object.keys(Loose.unsafeDecode({ id: { S: 'p1' } }))).toEqual([
            'id',
        ])
    })

    it('still refuses a required attribute the row does not carry', () => {
        expect(() => Pet.unsafeDecode({ nickname: { S: 'Rex' } })).toThrow(
            CodecError,
        )
    })

    it('still refuses an attribute of the wrong member', () => {
        expect(() =>
            Pet.unsafeDecode({ id: { S: 'p1' }, nickname: { N: '1' } }),
        ).toThrow(CodecError)
    })
})

describe('the laws', () => {
    it('round-trips every entity it can generate', () => {
        expect(() => checkRoundTrip(Pet, { count: 500 })).not.toThrow()
    })

    /** The absent case is the one the mark changes: the key it invents must not become bytes. */
    it('is stable on a row whether or not the attribute is there', () => {
        expect(() =>
            checkStable(Pet, [
                { id: { S: 'p1' } },
                { id: { S: 'p1' }, nickname: { S: 'Rex' } },
                { id: { S: 'p1' }, chipped: { BOOL: false } },
            ]),
        ).not.toThrow()
    })

    it('re-encodes an absent attribute as absent, not as NULL', () => {
        const row = { id: { S: 'p1' } }
        expect(Pet.unsafeEncode(Pet.unsafeDecode(row))).toEqual(row)
    })

    /** `{ k: undefined }` is a legal value of `{ k?: T }`, and `optional` loses the key on it. */
    it('round-trips the value optional cannot', () => {
        const entity = { id: 'p1', nickname: undefined, chipped: undefined }
        const back = Pet.unsafeDecode(Pet.unsafeEncode(entity))
        expect(back).toEqual(entity)
        expect(Object.keys(back).sort()).toEqual(Object.keys(entity).sort())

        // the same value through `optional`, for contrast: the key does not survive
        const loose = { id: 'p1', nickname: undefined }
        const looseBack = Loose.unsafeDecode(Loose.unsafeEncode(loose))
        expect(Object.keys(looseBack)).toEqual(['id'])
        expect(Object.keys(looseBack)).not.toEqual(Object.keys(loose))
    })
})

describe('the types', () => {
    it('keeps the key required and admits undefined', () => {
        // `Pet` the type and `Pet` the codec agree, which is the pin the mark exists to make hold
        const entity: Pet = Pet.unsafeDecode({ id: { S: 'p1' } })
        expect(entity.id).toBe('p1')

        // @ts-expect-error the key is required: leaving it out is not a Pet
        const _missing: Pet = { id: 'p1', chipped: undefined }
        expect(_missing).toBeDefined()
    })

    it('writes an optional attribute, as the row does', () => {
        type Row = Encoded<{
            id: typeof string
            nickname: ReturnType<typeof undefinable<typeof string>>
        }>
        const bare: Row = { id: { S: 'p1' } }
        const full: Row = { id: { S: 'p1' }, nickname: { S: 'Rex' } }
        expect([bare, full]).toHaveLength(2)
    })
})

/**
 * The mark needs no Lean of its own: `Value` has no `undefined` and `Value.map` is a key set with a
 * total function on it, so `{ k: undefined }` and `{}` are one `Value`. An undefinable
 * `ObjectSlot` could only be defined as `optional`'s denotation. That the emitter's
 * `ObjectSlot.optional` is therefore exact, rather than an approximation, is checkable — both
 * marks emit the same theorem.
 */
describe('what the model is asked to check', () => {
    it('emits the theorem optional emits, character for character', () => {
        const asUndefinable = object({ id: string, nick: undefinable(string) })
        const asOptional = object({ id: string, nick: optional(string) })

        const one = leanVector({
            name: 'x',
            codec: asUndefinable as never,
            value: { id: 'p1', nick: undefined } as never,
        })
        const other = leanVector({
            name: 'x',
            codec: asOptional as never,
            value: { id: 'p1' } as never,
        })

        expect(one).toBe(other)
        expect(one).toContain('ObjectSlot.optional')
        // the key is not in the emitted `Value`: there is no `Value` for `undefined` to be
        expect(one).toContain('Value.map {"id"}')
    })
})
