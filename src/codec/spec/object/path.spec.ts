/**
 * Attribute paths.
 *
 * Typing `path()` as the entity forces a `!` at every optional hop, and files that build many
 * expressions end up silencing the lint rule wholesale. Those assertions claim a *value* is present
 * while building a *string*, which is a claim nobody needed to make: a path to `deliveredAt` is
 * well formed whether or not anything has been delivered — writing the path is how you ask.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import { number, object, optional, string } from '../../codec'

type Leg = {
    readonly legType: string
    readonly pickupRequest?: {
        id: string
        requestType: 'WITH_PETS' | 'WITHOUT_PETS' | undefined
        expiresAt: string | undefined
    }
    readonly pickupRequest_failedAttempts?: number
    readonly deliveredAt_failedAttempts?: number
    readonly deliveredAt?: {
        id: string
        scan_status: number
        courier: { userId: string; username: string | undefined } | undefined
    }
}

type Adoption = {
    readonly TAG: 'ADOPTION'
    readonly adoptionId: string
    readonly userId: string
    readonly status: 'DRAFT' | 'PACKING'
    readonly updatedAt: string
    readonly currentLegIndex: number
    readonly fulfilment:
        | { type: 'SINGLE_LEG'; legs: readonly [Leg] }
        | { type: 'MULTI_LEG'; legs: readonly [Leg, Leg] }
}

const AdoptionEntry = () =>
    tableEntry<Adoption>()({
        PK: ['adoptionId'],
        SK: ['adoptionId'],
        GSI1PK: ['userId'],
        GSI1SK: ['status', 'updatedAt'],
    })

describe('paths need no non-null assertions', () => {
    const path = AdoptionEntry().path()
    // the runtime index the repo actually uses
    const stepIndex: number = 1

    it('reaches an optional attribute without asserting a value is there', () => {
        expect(path.fulfilment.legs.at(stepIndex).deliveredAt.toString()).toBe(
            'fulfilment.legs[1].deliveredAt',
        )
        expect(
            path.fulfilment.legs.at(stepIndex).pickupRequest.id.toString(),
        ).toBe('fulfilment.legs[1].pickupRequest.id')
    })

    it('reaches through two optional hops, which is where the ! used to pile up', () => {
        expect(
            path.fulfilment.legs
                .at(stepIndex)
                .deliveredAt.scan_status.toString(),
        ).toBe('fulfilment.legs[1].deliveredAt.scan_status')
        expect(
            path.fulfilment.legs
                .at(stepIndex)
                .deliveredAt.courier.username.toString(),
        ).toBe('fulfilment.legs[1].deliveredAt.courier.username')
    })

    it('reaches the failed-attempt counters the repo increments', () => {
        expect(
            path.fulfilment.legs
                .at(stepIndex)
                .pickupRequest_failedAttempts.toString(),
        ).toBe('fulfilment.legs[1].pickupRequest_failedAttempts')
        expect(
            path.fulfilment.legs
                .at(stepIndex)
                .deliveredAt_failedAttempts.toString(),
        ).toBe('fulfilment.legs[1].deliveredAt_failedAttempts')
    })

    it('indexes a literal position the same way', () => {
        // brackets also work, but carry `| undefined` under noUncheckedIndexedAccess,
        // which is the assertion this type exists to remove — so `at` is the form
        expect(path.fulfilment.legs.at(0).deliveredAt.id.toString()).toBe(
            'fulfilment.legs[0].deliveredAt.id',
        )
    })

    it('reaches a top-level attribute and a computed key', () => {
        expect(path.currentLegIndex.toString()).toBe('currentLegIndex')
        expect(path.GSI1SK.toString()).toBe('GSI1SK')
    })

    it('refuses a path that is not an attribute path', () => {
        // `PK` is a string; `.length` is a property of the value, not a document path
        // @ts-expect-error there is no such attribute path
        path.PK.length
    })
})

describe('both entry points build the same paths', () => {
    /**
     * `tableEntry(...).path()` and `object(...).path()` are one implementation.
     *
     * They have to agree: `at` resolves a codec by walking the segments the builder records, so a
     * second implementation that drifted would resolve a codec for one path and hand back another.
     */
    const Codec = object({
        TAG: string('ADOPTION'),
        adoptionId: string,
        userId: string,
        status: string('DRAFT', 'PACKING'),
        updatedAt: string,
        currentLegIndex: number,
        fulfilment: optional(string) as never,
    }).item

    const fromEntry = AdoptionEntry().path()
    const fromCodec = Codec.path()

    for (const [name, a, b] of [
        ['a scalar', fromEntry.adoptionId, fromCodec.adoptionId],
        [
            'another scalar',
            fromEntry.currentLegIndex,
            fromCodec.currentLegIndex,
        ],
        ['a literal union', fromEntry.status, fromCodec.status],
    ] as const) {
        it(`agrees on ${name}`, () => {
            expect(a.toString()).toBe(b.toString())
        })
    }

    it('agrees that a fresh builder and a reused one are the same', () => {
        expect(AdoptionEntry().path().adoptionId.toString()).toBe(
            fromEntry.adoptionId.toString(),
        )
    })
})

/**
 * Maps whose keys are only known at runtime.
 *
 * A caller writes
 * `AdopterEntry.path().checks?.[check.checkId]?.toString() as string`. Both halves of that are the
 * path type getting in the way: the `?.` because `checks` is an optional attribute, and the
 * `as string` because indexing a record with a runtime key yields `| undefined`. Neither says
 * anything about the path, which is a string either way.
 */
describe('a map whose keys are not known ahead of time', () => {
    type Adopter = {
        userId: string
        shelter: string
        checks?: Record<string, { checkId: string; status: string }>
    }
    type Check = {
        userId: string
        checkId: string
        vaccinationIds?: string[]
    }

    const AdopterEntry = tableEntry<Adopter>()({ PK: ['userId'] })
    const CheckEntry = tableEntry<Check>()({ PK: ['userId'] })

    // the id is only known at runtime, which is the whole point
    const checkId: string = 'c1'

    it('indexes by a runtime key without an assertion', () => {
        expect(AdopterEntry.path().checks.at(checkId).toString()).toBe(
            'checks.c1',
        )
    })

    it('keeps walking past the runtime key', () => {
        expect(AdopterEntry.path().checks.at(checkId).status.toString()).toBe(
            'checks.c1.status',
        )
    })

    it('reaches an optional attribute with no `?.` and no `as string`', () => {
        const path: string = CheckEntry.path().vaccinationIds.toString()
        expect(path).toBe('vaccinationIds')
    })

    it('listings `at` only where the keys are actually unknown', () => {
        // a plain object has named keys, and `.userId` is how you reach one
        // @ts-expect-error there is no `at` on an object with known keys
        const _noAt = () => AdopterEntry.path().at('userId')
        expect(typeof _noAt).toBe('function')
    })
})

/**
 * A path is a value, not a promise and not a function.
 *
 * The recorder is a `Proxy` that answers *every* property with another recorder, so whatever its
 * target is leaks into what a path appears to be. A callable target made `typeof path` be
 * `'function'` and `path.then` callable — which is the definition of a thenable, so `await path`,
 * `Promise.resolve(path)` and returning a path from an `async` function all hung forever with no
 * error. The segments live in a side table for this reason.
 */
describe('what a path is, to the runtime', () => {
    const Pet = object({
        id: string,
        then: string,
    }).item

    it('is an object, not a function', () => {
        expect(typeof Pet.path().id).toBe('object')
    })

    it('is not a thenable, so awaiting one does not hang', async () => {
        const path = Pet.path().id
        const settled = await Promise.race([
            Promise.resolve(path).then(() => 'resolved'),
            new Promise((stop) => setTimeout(() => stop('hung'), 250)),
        ])
        expect(settled).toBe('resolved')
    })

    /** And `then` stays an attribute name a schema may use, rather than a hole in the namespace. */
    it('records an attribute called `then` like any other', () => {
        expect(Pet.path().then.toString()).toBe('then')
    })
})
