/**
 * A codec at a path.
 *
 * Writing one attribute deep inside an item needs two things about the same place: the document
 * path to write at, and how to encode what goes there. Taking the first from `path()` and the
 * second from a generic marshaller drops out of the schema for that subtree and lets the two
 * disagree. `at` derives both from one expression, so they cannot.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    discriminatedUnion,
    number,
    object,
    optional,
    string,
    tuple,
} from './codec'

const Delivery = object({
    id: string,
    scan_status: number,
    courier: optional(object({ staffId: string, handle: optional(string) })),
})

const Leg = object({
    legType: string,
    pickupRequest: optional(
        object({ id: string, expiresAt: optional(string) }),
    ),
    deliveredAt: optional(Delivery),
    pickupRequest_failedAttempts: optional(number),
})

type Fulfilment =
    | { type: 'SINGLE_LEG'; legs: readonly [Leg] }
    | { type: 'MULTI_LEG'; legs: readonly [Leg, Leg] }
type Leg = typeof Leg extends { unsafeDecode: (...a: never[]) => infer T }
    ? T
    : never

const Fulfilment = discriminatedUnion('type', [
    object({
        type: string('SINGLE_LEG'),
        legs: tuple(Leg),
    }),
    object({
        type: string('MULTI_LEG'),
        legs: tuple(Leg, Leg),
    }),
])

type Adoption = {
    adoptionId: string
    currentLegIndex: number
    tags: readonly string[]
    fulfilment: Fulfilment
}

const Adoption = object({
    adoptionId: string,
    currentLegIndex: number,
    tags: array(string),
    fulfilment: Fulfilment,
}).item

describe('a codec at a path', () => {
    const stepIndex: number = 1

    it('gives the path and the codec from one expression', () => {
        const deliveredAt = Adoption.at(
            (p) => p.fulfilment.legs.at(stepIndex).deliveredAt,
        )

        expect(deliveredAt.path()).toBe('fulfilment.legs[1].deliveredAt')
        expect(deliveredAt.unsafeEncode({ id: 'o1', scan_status: 3 })).toEqual({
            M: { id: { S: 'o1' }, scan_status: { N: '3' } },
        })
    })

    it('encodes through the declared codec, not a generic marshaller', () => {
        // `scan_status` is `number` in the spec, so it must reach `N` — a generic marshaller
        // would have to guess, and this is the guess that has been wrong all session
        const txStatus = Adoption.at(
            (p) => p.fulfilment.legs.at(0).deliveredAt.scan_status,
        )
        expect(txStatus.path()).toBe(
            'fulfilment.legs[0].deliveredAt.scan_status',
        )
        expect(txStatus.unsafeEncode(7)).toEqual({ N: '7' })
    })

    it('round-trips what it encodes', () => {
        const courier = Adoption.at(
            (p) => p.fulfilment.legs.at(stepIndex).deliveredAt.courier,
        )
        const value = { staffId: 'u1', handle: 'ana' }
        expect(courier.unsafeDecode(courier.unsafeEncode(value))).toEqual(value)
    })

    it('reaches a top-level attribute', () => {
        expect(Adoption.at((p) => p.adoptionId).path()).toBe('adoptionId')
        expect(Adoption.at((p) => p.adoptionId).unsafeEncode('q1')).toEqual({
            S: 'q1',
        })
    })

    it('reaches into a plain list', () => {
        const tag = Adoption.at((p) => p.tags.at(2))
        expect(tag.path()).toBe('tags[2]')
        expect(tag.unsafeEncode('x')).toEqual({ S: 'x' })
    })

    it('is safe when the selector names an intermediate node', () => {
        // a shared, accumulating recorder would record both reads as one path
        const located = Adoption.at((p) => {
            const leg = p.fulfilment.legs.at(stepIndex)
            leg.legType // read, and not the one selected
            return leg.deliveredAt
        })
        expect(located.path()).toBe('fulfilment.legs[1].deliveredAt')
    })

    it('reuses one instance for many independent paths', () => {
        // `path()` has always worked this way — every hop returns a new proxy, nothing mutates
        const p = Adoption.path()
        expect(p.adoptionId.toString()).toBe('adoptionId')
        expect(p.currentLegIndex.toString()).toBe('currentLegIndex')
        expect(p.adoptionId.toString()).toBe('adoptionId')
        const leg = p.fulfilment.legs.at(0)
        expect(leg.legType.toString()).toBe('fulfilment.legs[0].legType')
        expect(leg.deliveredAt.id.toString()).toBe(
            'fulfilment.legs[0].deliveredAt.id',
        )
    })

    it('refuses a path the schema does not declare', () => {
        expect(() =>
            // @ts-expect-error there is no such attribute
            Adoption.at((p) => p.fulfilment.legs.at(0).nonsense),
        ).toThrow(/no attribute is declared at 'fulfilment.legs\[0\].nonsense'/)
    })

    it('types the codec by what lives at the path', () => {
        const located = Adoption.at(
            (p) => p.fulfilment.legs.at(stepIndex).deliveredAt,
        )
        // thunks, so the assertion is about the types and nothing is actually encoded
        // @ts-expect-error a string is not a delivery
        const _wrongShape = () => located.unsafeEncode('not a delivery')

        const index = Adoption.at((p) => p.currentLegIndex)
        // @ts-expect-error currentLegIndex is a number
        const _wrongScalar = () => index.unsafeEncode('1')

        expect(located.path()).toBe('fulfilment.legs[1].deliveredAt')
    })
})
