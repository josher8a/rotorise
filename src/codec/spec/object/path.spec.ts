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
import {
    at,
    CodecError,
    item,
    number,
    object,
    optional,
    pathBuilder,
    path as pathOf,
    string,
} from '../../codec'

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
     * `tableEntry(...).path()` and the path of a codec that `at` located render one path in one
     * syntax. They have to agree: an expression that mixes the two must name one attribute.
     */
    const Codec = item(
        object({
            TAG: string('ADOPTION'),
            adoptionId: string,
            userId: string,
            status: string('DRAFT', 'PACKING'),
            updatedAt: string,
            currentLegIndex: number,
            fulfilment: optional(string) as never,
        }),
    )

    const fromEntry = AdoptionEntry().path()
    for (const [name, a, b] of [
        ['a scalar', fromEntry.adoptionId, pathOf(at(Codec, ['adoptionId']))],
        [
            'another scalar',
            fromEntry.currentLegIndex,
            pathOf(at(Codec, ['currentLegIndex'])),
        ],
        ['a literal union', fromEntry.status, pathOf(at(Codec, ['status']))],
    ] as const) {
        it(`agrees on ${name}`, () => {
            expect(a.toString()).toBe(b)
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
    const Pet = pathBuilder<{ id: string; then: string }>()

    it('is an object, not a function', () => {
        expect(typeof Pet.id).toBe('object')
    })

    it('is not a thenable, so awaiting one does not hang', async () => {
        const path = Pet.id
        const settled = await Promise.race([
            Promise.resolve(path).then(() => 'resolved'),
            new Promise((stop) => setTimeout(() => stop('hung'), 250)),
        ])
        expect(settled).toBe('resolved')
    })

    /** And `then` stays an attribute name a schema may use, rather than a hole in the namespace. */
    it('records an attribute called `then` like any other', () => {
        expect(Pet.then.toString()).toBe('then')
    })
})

/**
 * DynamoDB admits `at`, `narrow` and `toString` as attribute names, and the path type
 * offers each as a hop. The path reads such a name as the attribute, and calls it as the method.
 */
describe('an attribute that shares the name of a method of the path', () => {
    const Pet = pathBuilder<{
        at: { entry: string }
        narrow: string
        toString: string
        tags: string[]
    }>()

    it('is the attribute where the path reads it', () => {
        expect(Pet.at.entry.toString()).toBe('at.entry')
        expect(Pet.narrow.toString()).toBe('narrow')
        expect(Pet.toString.toString()).toBe('toString')
    })

    it('is the method where the path calls it', () => {
        expect(Pet.tags.at(0).toString()).toBe('tags[0]')
        expect(Pet.at.toString()).toBe('at')
    })

    it('is a plain hop where the path has no method of that name', () => {
        expect(typeof Reflect.get(Pet.at, 'entry')).toBe('object')
    })

    it('is not a thenable, so awaiting one does not hang', async () => {
        const settled = await Promise.race([
            Promise.resolve(Pet.at).then(() => 'resolved'),
            new Promise((stop) => setTimeout(() => stop('hung'), 250)),
        ])
        expect(settled).toBe('resolved')
    })
})

/**
 * **A path string addresses the place that the segments address, or no string exists.** A key that
 * is data can hold a `.`, a `-` or a leading digit. An expression does not read such a key as one
 * name, so the builder refuses the string, and a plain key prints as the segments say.
 */
describe('the string of a path that a key makes', () => {
    type Adopter = {
        userId: string
        checks?: Record<string, { checkId: string; status: string }>
        pets?: string[]
    }
    const Adopters = tableEntry<Adopter>()({ PK: ['userId'] })

    it('prints a plain key', () => {
        const key: string = 'rabies2024'
        expect(Adopters.path().checks.at(key).status.toString()).toBe(
            'checks.rabies2024.status',
        )
    })

    it.each([
        'rabies.2024',
        'a[0]',
        'a[',
        'a]',
        'a,b',
        ' a',
        'rabies-2024',
        '2024',
        '_a',
        '',
    ])(
        'refuses the string of the key %j, because an expression does not read the key as one name',
        (key) => {
            const placed = Adopters.path().checks.at(key).status
            expect(() => placed.toString()).toThrow(CodecError)
            expect(() => placed.toString()).toThrow(/ExpressionAttributeNames/)
        },
    )

    it.each([-1, 0.5, 2 ** 53])(
        'refuses the string of the position %j, because an expression takes a position that is a non-negative integer',
        (position) => {
            const placed = Adopters.path().pets.at(position)
            expect(() => placed.toString()).toThrow(CodecError)
            expect(() => placed.toString()).toThrow(/position/)
        },
    )

    it('prints the largest position that a number holds exactly, because a larger position names no list element', () => {
        const last: number = Number.MAX_SAFE_INTEGER
        expect(Adopters.path().pets.at(last).toString()).toBe(
            'pets[9007199254740991]',
        )
    })
})

/**
 * **A hop in digits is a position, and only a list offers a position.** The builder holds no codec,
 * so the run time reads the property `'2024'` as the position 2024, and an expression prints
 * `[2024]`. DynamoDB reads that as a list element, and the place is a key of a map. The type of the
 * entity owns the fact that a place is a list. So a map offers `at(key)` and no bracket hop, and
 * `at(key)` refuses a key that an expression cannot print.
 */
describe('a hop in digits on a place that is no list', () => {
    type Visit = { vet: string; weight: number }
    type Clinic = {
        clinicId: string
        visits: Record<string, Visit>
        optionalVisits?: Record<string, Visit>
        weights: Record<number, number>
        doses?: { 2024: string; 2025: string }
        namedDoses: { '2024': string }
        tags: { [tag: string]: string; kind: string }
        history: Record<string, Visit>[]
        records: Visit[] | Record<string, Visit>
        pets: string[]
        pair: [Visit, Visit]
        byBigint: Record<`${bigint}`, Visit>
        byPrefixed: Record<`y${number}`, Visit>
        byNumberThenText: Record<`${number}${string}`, Visit>
        patterned: { kind: string; [k: `y${number}`]: string }
    }
    const Clinics = tableEntry<Clinic>()({ PK: ['clinicId'] })
    const year: string = '2024'
    const position: number = 7
    const bigintYear: `${bigint}` = '2024'
    const prefixed: `y${number}` = 'y2024'
    const numberThenText: `${number}${string}` = '2024'

    it('offers no bracket hop on a required map, which a key in digits would print as a position', () => {
        // @ts-expect-error a map offers `at(key)` and no bracket hop
        const _byKey = () => Clinics.path().visits[year]
        // @ts-expect-error a literal in digits is a position too
        const _byLiteral = () => Clinics.path().visits[2024]
        expect(typeof _byKey).toBe('function')
        expect(typeof _byLiteral).toBe('function')
    })

    it('offers no bracket hop on an optional map', () => {
        // @ts-expect-error a map offers `at(key)` and no bracket hop
        const _byKey = () => Clinics.path().optionalVisits[year]
        expect(typeof _byKey).toBe('function')
    })

    it('offers no hop on a map that a number indexes, because the stored key of the map is text', () => {
        // @ts-expect-error a number index signature is a map, and the key is text
        const _byPosition = () => Clinics.path().weights[position]
        // @ts-expect-error a number index signature offers no `at`
        const _byAt = () => Clinics.path().weights.at(year)
        expect(typeof _byPosition).toBe('function')
        expect(typeof _byAt).toBe('function')
    })

    it('offers no hop for a declared name in digits, because no expression prints the name', () => {
        // @ts-expect-error a name that reads as a number is a key, and a key has no bracket hop
        const _byNumber = () => Clinics.path().doses[2024]
        // @ts-expect-error the same name as text
        const _byText = () => Clinics.path().namedDoses['2024']
        expect(typeof _byNumber).toBe('function')
        expect(typeof _byText).toBe('function')
    })

    it('keeps the declared name of an open map as a hop, and carries any other key through `at`', () => {
        // @ts-expect-error the index signature of an open map offers no bracket hop
        const _byKey = () => Clinics.path().tags[year]
        expect(typeof _byKey).toBe('function')
        expect(Clinics.path().tags.kind.toString()).toBe('tags.kind')
        expect(Clinics.path().tags.at('colour').toString()).toBe('tags.colour')
    })

    it('offers no bracket hop on a map inside a list, and keeps the position of the list', () => {
        // @ts-expect-error the map inside the list offers no bracket hop
        const _byKey = () => Clinics.path().history.at(0)[year]
        expect(typeof _byKey).toBe('function')
        expect(Clinics.path().history.at(0).at('rabies').vet.toString()).toBe(
            'history[0].rabies.vet',
        )
    })

    it('offers no bracket hop on a place that is a list or a map, because the position is not certain', () => {
        // @ts-expect-error a place that may be a map offers no position
        const _byPosition = () => Clinics.path().records[position]
        // @ts-expect-error a place that may be a map offers no bracket hop for a key
        const _byKey = () => Clinics.path().records[year]
        expect(typeof _byPosition).toBe('function')
        expect(typeof _byKey).toBe('function')
    })

    it('keeps the position hop on a list and on a tuple', () => {
        expect(Clinics.path().pets[0]?.toString()).toBe('pets[0]')
        expect(Clinics.path().pets.at(position).toString()).toBe('pets[7]')
        expect(Clinics.path().pair[1]?.vet.toString()).toBe('pair[1].vet')
    })

    it('offers no bracket hop on a map whose key is digits by pattern, because the key can be 2024', () => {
        // @ts-expect-error a key of the form `${bigint}` is digits
        const _bigint = () => Clinics.path().byBigint[bigintYear]
        // @ts-expect-error the key admits a text in digits
        const _text = () => Clinics.path().byNumberThenText[numberThenText]
        expect(typeof _bigint).toBe('function')
        expect(typeof _text).toBe('function')
    })

    it('offers no bracket hop on a map whose key is another pattern, and carries a key of the pattern through `at`', () => {
        // @ts-expect-error each index signature is a map, and a map offers no bracket hop
        const _byKey = () => Clinics.path().byPrefixed[prefixed]
        // @ts-expect-error `rabies` is no key of the pattern
        const _outside = () => Clinics.path().byPrefixed.at('rabies')
        expect(typeof _byKey).toBe('function')
        expect(typeof _outside).toBe('function')
        expect(Clinics.path().byPrefixed.at(prefixed).vet.toString()).toBe(
            'byPrefixed.y2024.vet',
        )
    })

    it('refuses the string of a key in digits that a pattern map carries through `at`', () => {
        const placed = Clinics.path().byBigint.at(bigintYear).vet
        expect(() => placed.toString()).toThrow(CodecError)
    })

    it('keeps the declared name beside an index signature of a pattern', () => {
        expect(Clinics.path().patterned.kind.toString()).toBe('patterned.kind')
        expect(Clinics.path().patterned.at(prefixed).toString()).toBe(
            'patterned.y2024',
        )
    })

    it('offers no `at` on a map that a number indexes', () => {
        // @ts-expect-error a number key has no expression string
        const _at = () => Clinics.path().weights.at('2024')
        expect(typeof _at).toBe('function')
    })

    it('refuses the string of the key 2024 through `at`, so the path never prints the position 2024', () => {
        const placed = Clinics.path().visits.at(year).vet
        expect(() => placed.toString()).toThrow(CodecError)
        expect(() => placed.toString()).toThrow(/ExpressionAttributeNames/)
    })
})

describe('a hop in digits on a union of entities', () => {
    type Visit = { vet: string }
    type Cat = {
        petId: string
        kind: 'CAT'
        checks: Record<string, Visit>
        toys: string[]
    }
    type Dog = {
        petId: string
        kind: 'DOG'
        checks: Visit[]
        tags: Record<string, string>
    }
    const Pets = tableEntry<Cat | Dog>()({ PK: ['petId'] })
    const year: string = '2024'
    const position: number = 7

    it('offers no bracket hop on a name that is a map in one option and a list in the other', () => {
        // @ts-expect-error the place may be a map
        const _byPosition = () => Pets.path().checks[position]
        // @ts-expect-error the place may be a map
        const _byKey = () => Pets.path().checks[year]
        expect(typeof _byPosition).toBe('function')
        expect(typeof _byKey).toBe('function')
    })

    it('keeps the position of a list that one option holds, and refuses the bracket hop of a map that one option holds', () => {
        expect(Pets.path().toys[0]?.toString()).toBe('toys[0]')
        expect(Pets.path().tags.at('colour').toString()).toBe('tags.colour')
        // @ts-expect-error a map offers no bracket hop
        const _byKey = () => Pets.path().tags[year]
        expect(typeof _byKey).toBe('function')
    })
})
