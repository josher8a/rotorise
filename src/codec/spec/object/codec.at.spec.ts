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
    type AttributeCodec,
    array,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    lazy,
    list,
    never,
    number,
    object,
    opaque,
    optional,
    refine,
    string,
    union,
    withLegacyRead,
} from '../../codec'

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
        legs: list(Leg),
    }),
    object({
        type: string('MULTI_LEG'),
        legs: list(Leg, Leg),
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

/**
 * **A path stops at a refinement and at an older reading.** A predicate reads the whole value, and
 * a write at a path writes one part of the value, so the write cannot keep the predicate. An older
 * encoding has another shape, which a path inside the attribute does not address.
 */
describe('a path that crosses a whole-value adapter', () => {
    it('a path that crosses a refinement is refused, because a path write cannot keep the predicate', () => {
        const Account = object({
            a: refine(
                object({ x: dynamoNumber }),
                (v): v is { x: typeof v.x } => !v.x.digits.startsWith('-'),
                { describe: 'a balance that is not negative' },
            ),
        }).item
        expect(() => Account.at((p) => p.a.x)).toThrow(CodecError)
        expect(() => Account.at((p) => p.a.x)).toThrow(
            /a path cannot go into `refine` at 'x'/,
        )
        // the refined attribute itself is a path, and its codec keeps the predicate
        expect(Account.at((p) => p.a).path()).toBe('a')
    })

    it('a path that crosses an older reading is refused, because a path addresses the current shape only', () => {
        const Migrated = object({
            a: withLegacyRead({
                current: object({ x: decimal }),
                older: { decode: () => ({ x: '0' }) },
            }),
        }).item
        expect(() => Migrated.at((p) => p.a.x)).toThrow(
            /a path cannot go into `withLegacyRead` at 'x'/,
        )
    })
})

/**
 * **A path passes an option whose stored member is not the container of the segment.** The store
 * refuses the segment on every attribute of that option, so the option has no codec at the path.
 * A thunk that closes no cycle is the codec that the thunk returns, so a thunk changes nothing.
 */
describe('an option that the store keeps apart from the segment', () => {
    it('a path passes a refined number behind a thunk, because the store holds no map at a number', () => {
        const Reading = union([
            object({ x: string }),
            refine(
                lazy(() => dynamoNumber),
                (v): v is typeof v => !v.digits.startsWith('-'),
                { describe: 'a reading that is not negative' },
            ),
        ])
        const Meter = object({ reading: Reading }).item
        const x = Meter.at((p) => p.reading.x)
        expect(x.path()).toBe('reading.x')
        expect(x.unsafeEncode('high')).toEqual({ S: 'high' })
    })

    it('a path does not pass a refinement of a recursive list, because the member of a recursion is not read off the term', () => {
        type Nest = readonly Nest[]
        const Nest: AttributeCodec<Nest> = array(lazy(() => Nest))
        const Shape = union([
            object({ x: string }),
            refine(Nest, (v): v is Nest => v.length > 0, {
                describe: 'a nest that is not empty',
            }),
        ])
        const Drawing = object({ shape: Shape }).item
        expect(() => Drawing.at((p) => p.shape.x)).toThrow(
            /a path cannot go into `refine` at 'x'/,
        )
    })
})

/**
 * **A path under `opaque` stands at `opaque`.** `opaque` admits every value, so the attribute at
 * each segment below it admits every value too. The type of the path stops at `opaque`, and the
 * runtime answers the path that the type refuses.
 */
describe('a path under opaque', () => {
    it('a path under opaque writes any value, because opaque admits every value at every depth', () => {
        const Envelope = object({ payload: opaque }).item
        // @ts-expect-error the type of a path offers no segment below `opaque`
        const deep = Envelope.at((p) => p.payload.a.b.at(2).c)
        expect(deep.path()).toBe('payload.a.b[2].c')
        expect(deep.unsafeEncode({ k: 'v' })).toEqual({
            M: { k: { S: 'v' } },
        })
        // no `narrow` narrows the path, so a write needs no precondition
        expect(deep.preconditions).toEqual([])
    })
})

describe('a path to a codec that admits no value', () => {
    const vacant = /no attribute is declared at /

    it('a path to a declared `never` is vacant, because the model reads it as a frame of `never`', () => {
        const item = object({ a: string, b: optional(never) }).item
        expect(() => item.at((p) => p.b)).toThrow(vacant)
    })

    it('a path past a list of `never` is vacant in either option order, because the verdict reads the term and not the order', () => {
        const declares = object({ k: string('a'), x: array(never) })
        const lacks = object({ k: string('b') })
        for (const options of [
            [declares, lacks],
            [lacks, declares],
        ] as const) {
            const item = object({ r: union(options) }).item
            // @ts-expect-error a list that holds no value offers no position, at the type as at run time
            expect(() => item.at((p) => p.r.x.at(0))).toThrow(vacant)
        }
    })

    it('a `never` beside a codec is a path that some variants declare only, because a write there leaves the other variant unreadable', () => {
        const empty = object({ k: string('a'), x: optional(never) })
        const full = object({ k: string('b'), x: string })
        for (const options of [
            [empty, full],
            [full, empty],
        ] as const) {
            const at = object({ r: union(options) }).item.at((p) => p.r.x)
            expect(at.decode({ S: 'v' })).toMatchObject({
                message: expect.stringMatching(
                    /declared by some variants only/,
                ),
            })
        }
    })
})
