/**
 * A codec at a path.
 *
 * Writing one attribute deep inside an item needs two things about the same place: the document
 * path to write at, and how to encode what goes there. Taking the first from `path()` and the
 * second from a generic marshaller drops out of the schema for that subtree and lets the two
 * disagree. `at` derives both from one expression, so they cannot.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { type Attribute, type AttributeValue, memberOf } from '../../attribute'
import {
    array,
    at as atOf,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    item as itemOf,
    list,
    never,
    number,
    object,
    opaque,
    optional,
    path,
    preconditions,
    ref,
    refine,
    scope,
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

const Adoption = itemOf(
    object({
        adoptionId: string,
        currentLegIndex: number,
        tags: array(string),
        fulfilment: Fulfilment,
    }),
)

describe('a codec at a path', () => {
    const stepIndex: number = 1

    it('gives the path and the codec from one expression', () => {
        const deliveredAt = atOf(Adoption, [
            'fulfilment',
            'legs',
            stepIndex,
            'deliveredAt',
        ])

        expect(path(deliveredAt)).toBe('fulfilment.legs[1].deliveredAt')
        expect(deliveredAt.unsafeEncode({ id: 'o1', scan_status: 3 })).toEqual({
            M: { id: { S: 'o1' }, scan_status: { N: '3' } },
        })
    })

    it('encodes through the declared codec, not a generic marshaller', () => {
        // `scan_status` is `number` in the spec, so it must reach `N` — a generic marshaller
        // would have to guess, and this is the guess that has been wrong all session
        const txStatus = atOf(Adoption, [
            'fulfilment',
            'legs',
            0,
            'deliveredAt',
            'scan_status',
        ])
        expect(path(txStatus)).toBe(
            'fulfilment.legs[0].deliveredAt.scan_status',
        )
        expect(txStatus.unsafeEncode(7)).toEqual({ N: '7' })
    })

    it('round-trips what it encodes', () => {
        const courier = atOf(Adoption, [
            'fulfilment',
            'legs',
            stepIndex,
            'deliveredAt',
            'courier',
        ])
        const value = { staffId: 'u1', handle: 'ana' }
        expect(courier.unsafeDecode(courier.unsafeEncode(value))).toEqual(value)
    })

    it('reaches a top-level attribute', () => {
        expect(path(atOf(Adoption, ['adoptionId']))).toBe('adoptionId')
        expect(atOf(Adoption, ['adoptionId']).unsafeEncode('q1')).toEqual({
            S: 'q1',
        })
    })

    it('reaches into a plain list', () => {
        const tag = atOf(Adoption, ['tags', 2])
        expect(path(tag)).toBe('tags[2]')
        expect(tag.unsafeEncode('x')).toEqual({ S: 'x' })
    })

    it('refuses a path the schema does not declare', () => {
        expect(() =>
            // @ts-expect-error there is no such attribute
            atOf(Adoption, ['fulfilment', 'legs', 0, 'nonsense']),
        ).toThrow(/no attribute is declared at 'fulfilment.legs\[0\].nonsense'/)
    })

    it('types the codec by what lives at the path', () => {
        const located = atOf(Adoption, [
            'fulfilment',
            'legs',
            stepIndex,
            'deliveredAt',
        ])
        // thunks, so the assertion is about the types and nothing is actually encoded
        // @ts-expect-error a string is not a delivery
        const _wrongShape = () => located.unsafeEncode('not a delivery')

        const index = atOf(Adoption, ['currentLegIndex'])
        // @ts-expect-error currentLegIndex is a number
        const _wrongScalar = () => index.unsafeEncode('1')

        expect(path(located)).toBe('fulfilment.legs[1].deliveredAt')
    })
})

/**
 * **A path stops at a refinement and at an older reading.** A predicate reads the whole value, and
 * a write at a path writes one part of the value, so the write cannot keep the predicate. An older
 * encoding has another shape, which a path inside the attribute does not address.
 */
describe('a path that crosses a whole-value adapter', () => {
    it('a path that crosses a refinement is refused, because a path write cannot keep the predicate', () => {
        const Account = itemOf(
            object({
                a: refine(
                    object({ x: dynamoNumber }),
                    (v): v is { x: typeof v.x } => !v.x.digits.startsWith('-'),
                    { describe: 'a balance that is not negative' },
                ),
            }),
        )
        // @ts-expect-error a path cannot go into `refine`, at the type as at run time
        expect(() => atOf(Account, ['a', 'x'])).toThrow(CodecError)
        // @ts-expect-error a path cannot go into `refine`, at the type as at run time
        expect(() => atOf(Account, ['a', 'x'])).toThrow(
            /a path cannot go into `refine` at 'x'/,
        )
        // the refined attribute itself is a path, and its codec keeps the predicate
        expect(path(atOf(Account, ['a']))).toBe('a')
    })

    it('a path that crosses an older reading is refused, because a path addresses the current shape only', () => {
        const Migrated = itemOf(
            object({
                a: withLegacyRead({
                    current: object({ x: decimal }),
                    older: { decode: () => ({ x: '0' }) },
                }),
            }),
        )
        // @ts-expect-error a path cannot go into `withLegacyRead`, at the type as at run time
        expect(() => atOf(Migrated, ['a', 'x'])).toThrow(
            /a path cannot go into `withLegacyRead` at 'x'/,
        )
    })
})

/**
 * **A path passes an option whose stored member is not the container of the segment.** The store
 * refuses the segment on every attribute of that option, so the option has no codec at the path.
 */
describe('an option that the store keeps apart from the segment', () => {
    it('a path passes a refined number behind a scope entry, because the store holds no map at a number', () => {
        const Reading = union([
            object({ x: string }),
            refine(
                scope({ At: ref('N'), N: dynamoNumber }).At,
                (v): v is typeof v => !v.digits.startsWith('-'),
                { describe: 'a reading that is not negative' },
            ),
        ])
        const Meter = itemOf(object({ reading: Reading }))
        const x = atOf(Meter, ['reading', 'x'])
        expect(path(x)).toBe('reading.x')
        expect(x.unsafeEncode('high')).toEqual({ S: 'high' })
    })

    it('a path does not pass a refinement of a recursive list, because the member of a recursion is not read off the term', () => {
        type Nest = readonly Nest[]
        const { Nest } = scope({ Nest: array(ref('Nest')) })
        const Shape = union([
            object({ x: string }),
            refine(Nest, (v): v is Nest => v.length > 0, {
                describe: 'a nest that is not empty',
            }),
        ])
        const Drawing = itemOf(object({ shape: Shape }))
        // @ts-expect-error a path cannot go into `refine`, at the type as at run time
        expect(() => atOf(Drawing, ['shape', 'x'])).toThrow(
            /a path cannot go into `refine` at 'x'/,
        )
    })
})

/**
 * **A path under `opaque` stands at `opaque`.** `opaque` admits every value, so the attribute at
 * each segment below it admits every value too. The type of the path continues below `opaque`, as
 * the run time and the model's walk do.
 */
describe('a path under opaque', () => {
    it('a path under opaque writes any value, because opaque admits every value at every depth', () => {
        const Envelope = itemOf(object({ payload: opaque }))
        const deep = atOf(Envelope, ['payload', 'a', 'b', 2, 'c'])
        expect(path(deep)).toBe('payload.a.b[2].c')
        expect(deep.unsafeEncode({ k: 'v' })).toEqual({
            M: { k: { S: 'v' } },
        })
        // no `narrow` narrows the path, so a write needs no precondition
        expect(preconditions(deep)).toEqual([])
    })
})

describe('a path to a codec that admits no value', () => {
    const vacant = /no attribute is declared at /

    it('a path to a declared `never` is vacant, because the model reads it as a frame of `never`', () => {
        const item = itemOf(object({ a: string, b: optional(never) }))
        // @ts-expect-error a path to a declared `never` is vacant, at the type as at run time
        expect(() => atOf(item, ['b'])).toThrow(vacant)
    })

    it('a path past a list of `never` is vacant in either option order, because the verdict reads the term and not the order', () => {
        const declares = object({ k: string('a'), x: array(never) })
        const lacks = object({ k: string('b') })
        for (const options of [
            [declares, lacks],
            [lacks, declares],
        ] as const) {
            const item = itemOf(object({ r: union(options) }))
            // @ts-expect-error a list that holds no value offers no position, at the type as at run time
            expect(() => atOf(item, ['r', 'x', 0])).toThrow(vacant)
        }
    })

    it('a `never` beside a codec is a path that some variants declare only, because a write there leaves the other variant unreadable', () => {
        const empty = object({ k: string('a'), x: optional(never) })
        const full = object({ k: string('b'), x: string })
        for (const options of [
            [empty, full],
            [full, empty],
        ] as const) {
            // @ts-expect-error a variant does not declare `x`, so the path refuses at the type as on use
            const at = atOf(itemOf(object({ r: union(options) })), ['r', 'x'])
            expect(at.decode({ S: 'v' })).toMatchObject({
                message: expect.stringMatching(
                    /declared by some variants only/,
                ),
            })
        }
    })
})

/**
 * **The codec at a path keeps the attribute it writes.** An expression library reads the category
 * of a value from its key: an `ADD` or a `DELETE` ties the path and the value to one category. So
 * the type of `encode` at a path is the attribute of the member that the model reads at the frame,
 * and a frame where the model reads no one member gives the attributes of its options.
 */
describe('the attribute that the codec at a path writes', () => {
    /** The keys that an attribute type admits: the category that an expression library reads. */
    type Category<A> = A extends unknown
        ? keyof { [K in keyof A as A[K] extends undefined ? never : K]: 0 }
        : never
    const Tree = scope({
        Node: object({ v: string, next: optional(ref('Node')) }),
    })
    const Shelf = itemOf(
        object({
            name: string,
            count: number,
            tags: string.set(),
            notes: array(string),
            address: object({ city: string }),
            either: union([string, number]),
            payload: opaque,
            tree: Tree.Node,
        }),
    )

    it('a string field writes an S, because the category of the value is the member of its term', () => {
        const written = atOf(Shelf, ['name']).unsafeEncode('a')
        expect(memberOf(written)).toBe('S')
        expectTypeOf<Category<typeof written>>().toEqualTypeOf<'S'>()
    })

    it('a number field writes an N, because the float adapter writes the member of its stored term', () => {
        const written = atOf(Shelf, ['count']).unsafeEncode(1.5)
        expect(memberOf(written)).toBe('N')
        expectTypeOf<Category<typeof written>>().toEqualTypeOf<'N'>()
    })

    it('a string set writes an SS, because the member of a set follows the member of its element', () => {
        const written = atOf(Shelf, ['tags']).unsafeEncode(new Set(['a']))
        expect(memberOf(written)).toBe('SS')
        expectTypeOf<Category<typeof written>>().toEqualTypeOf<'SS'>()
    })

    it('an array writes an L, and an object writes an M, because a container has one member', () => {
        const list = atOf(Shelf, ['notes']).unsafeEncode(['a'])
        const map = atOf(Shelf, ['address']).unsafeEncode({ city: 'c' })
        expect([memberOf(list), memberOf(map)]).toEqual(['L', 'M'])
        expectTypeOf<Category<typeof list>>().toEqualTypeOf<'L'>()
        expectTypeOf<Category<typeof map>>().toEqualTypeOf<'M'>()
    })

    it('a union of a string and a number writes an S or an N, because each option writes its own member', () => {
        const either = atOf(Shelf, ['either'])
        const written = [either.unsafeEncode('a'), either.unsafeEncode(1)]
        expect(written.map(memberOf)).toEqual(['S', 'N'])
        expectTypeOf<Category<(typeof written)[number]>>().toEqualTypeOf<
            'S' | 'N'
        >()
    })

    it('opaque writes any member, because opaque admits every value', () => {
        const payload = atOf(Shelf, ['payload'])
        const written = [payload.unsafeEncode('a'), payload.unsafeEncode(true)]
        expect(written.map(memberOf)).toEqual(['S', 'BOOL'])
        expectTypeOf<Category<(typeof written)[number]>>().toEqualTypeOf<
            Category<AttributeValue>
        >()
    })

    it('a path through a scope ref writes the member of the entry that the ref names', () => {
        const value = atOf(Shelf, ['tree', 'next', 'v']).unsafeEncode('a')
        const node = atOf(Shelf, ['tree', 'next']).unsafeEncode({ v: 'a' })
        expect([memberOf(value), memberOf(node)]).toEqual(['S', 'M'])
        expectTypeOf<Category<typeof value>>().toEqualTypeOf<'S'>()
        expectTypeOf<Category<typeof node>>().toEqualTypeOf<'M'>()
    })

    it('an attribute of another category does not type-check, because the key states the category', () => {
        const count = atOf(Shelf, ['count'])
        // @ts-expect-error a number field writes an N, never an S
        const wrong: Attribute<'S'> = count.unsafeEncode(1)
        expect(memberOf(wrong)).toBe('N')
    })

    it('the root of an item writes a row and no attribute, so the root keeps the wide type', () => {
        const root = atOf(itemOf(object({ name: string })), [])
        expect(root.unsafeEncode({ name: 'a' })).toEqual({ name: { S: 'a' } })
        expectTypeOf(root.unsafeEncode).returns.toEqualTypeOf<AttributeValue>()
    })
})
