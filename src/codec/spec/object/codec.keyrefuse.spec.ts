/**
 * A key of one attribute has one member, and the type refuses the key that has none.
 *
 * A key attribute of DynamoDB is `S`, `N` or `B`, and this library writes `S` and `N`. A GSI
 * attribute has one type, so the arms of one key give one member. A key of a top-level attribute of an
 * entry with a codec takes the member that the codec writes for that field, so a decimal that the
 * codec writes as `N` is an `N` key. The refusal lands on the attribute that is wrong, at
 * construction, because a refusal at the first write would leave the schema accepted. A key of a
 * path below the top level has no field of the codec and takes the member that `native` writes.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import type { Attribute } from '../../attribute'
import { boolean, decimal, string } from '../../codec'

/** What a consumer writes: the narrowing of a result. */
const isError = (value: unknown): value is Error => value instanceof Error

describe('a key of one attribute is refused at construction where the attribute is no key', () => {
    it('refuses a boolean attribute key, on the attribute', () => {
        tableEntry<{ petId: string; vaccinated: boolean }>()({
            PK: ['petId'],
            // @ts-expect-error DynamoDB stores a key as S, N or B, and a boolean is none of them
            GSI1PK: 'vaccinated',
        })
    })

    it('refuses an attribute that is a string or a number', () => {
        tableEntry<{ petId: string; tag: string | number }>()({
            PK: ['petId'],
            // @ts-expect-error a key attribute has one type
            GSI1PK: 'tag',
        })
    })

    it('refuses the arms of a match that give S in one arm and N in another', () => {
        type Pet =
            | { petId: string; status: 'ADOPTED'; owner: string }
            | { petId: string; status: 'AVAILABLE'; age: number }
        tableEntry<Pet>()({
            PK: ['petId'],
            GSI1PK: {
                discriminator: 'status',
                spec: {
                    // @ts-expect-error this arm gives S and the other arm gives N
                    ADOPTED: 'owner',
                    // @ts-expect-error this arm gives N and the other arm gives S
                    AVAILABLE: 'age',
                },
            },
        })
    })

    it('accepts the arms of a match that give one member, and a null arm', () => {
        type Pet =
            | { petId: string; status: 'ADOPTED'; owner: string }
            | { petId: string; status: 'AVAILABLE'; shelter: string }
            | { petId: string; status: 'LOST' }
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            GSI1PK: {
                discriminator: 'status',
                spec: { ADOPTED: 'owner', AVAILABLE: 'shelter', LOST: null },
            },
        })
        expect(
            Pets.keys(['GSI1PK'], { status: 'ADOPTED', owner: 'ann' }),
        ).toEqual({ GSI1PK: { S: 'ann' } })
    })
})

describe('the codec decides the member of a key of one top-level attribute', () => {
    type Litter = { litterId: string; weight: string }

    const Litters = tableEntry<Litter>()(
        { PK: ['litterId'], GSI1SK: 'weight' },
        { codec: { litterId: string, weight: decimal } },
    )

    it('writes N in toItem, where the codec writes a decimal as N', () => {
        const written = Litters.toItem({ litterId: 'l1', weight: '1.5' })
        if (isError(written)) return expect.unreachable()
        expect(written.GSI1SK).toEqual({ N: '1.5' })
        expectTypeOf(written.GSI1SK).toEqualTypeOf<Attribute<'N'>>()
    })

    it('writes N in keys, and in keyUpdates, as toItem does', () => {
        expect(Litters.keys(['GSI1SK'], { weight: '1.5' })).toEqual({
            GSI1SK: { N: '1.5' },
        })
        expect(Litters.keyUpdates({ weight: '2.25' }).set).toEqual({
            GSI1SK: { N: '2.25' },
        })
    })

    it('refuses a field that the codec writes as a member that is no key', () => {
        tableEntry<{ litterId: string; weaned: boolean }>()(
            {
                PK: ['litterId'],
                // @ts-expect-error the codec writes BOOL at this field, and a boolean is no key
                GSI1SK: 'weaned',
            },
            { codec: { litterId: string, weaned: boolean } },
        )
    })

    it('keeps the native rule for a path below the top level', () => {
        type Weighed = {
            litterId: string
            body: { kind: 'DOG'; grams: number }
        }
        const Weighed = tableEntry<Weighed>()({
            PK: ['litterId'],
            GSI1SK: {
                discriminator: 'body.kind',
                spec: { DOG: 'body.grams' },
            },
        })
        expect(
            Weighed.keys(['GSI1SK'], { body: { kind: 'DOG', grams: 90 } }),
        ).toEqual({ GSI1SK: { N: '90' } })
    })
})

describe('the type of key() at an attribute arm', () => {
    type Pet =
        | { petId: string; status: 'ADOPTED'; owner: string | null }
        | { petId: string; status: 'LOST' }
    const Pets = tableEntry<Pet>()({
        PK: ['petId'],
        GSI2PK: {
            discriminator: 'status',
            spec: { ADOPTED: 'owner', LOST: null },
        },
    })

    it('admits undefined and not the discriminator literal at a null attribute', () => {
        const key = Pets.key('GSI2PK', { status: 'ADOPTED', owner: null })
        expectTypeOf(key).toEqualTypeOf<undefined>()
    })

    it('is the value of the attribute that the spec names', () => {
        const key = Pets.key('GSI2PK', { status: 'ADOPTED', owner: 'ann' })
        expectTypeOf(key).toEqualTypeOf<'ann'>()
    })
})
