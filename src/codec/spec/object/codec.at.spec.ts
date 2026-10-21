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
    list,
    never,
    number,
    object,
    opaque,
    optional,
    path,
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

const Adoption = object({
    adoptionId: string,
    currentLegIndex: number,
    tags: array(string),
    fulfilment: Fulfilment,
}).item

describe('a codec at a path', () => {
    const stepIndex: number = 1

    it('gives the path and the codec from one expression', () => {
        const deliveredAt = atOf(
            Adoption,
            (p) => p.fulfilment.legs.at(stepIndex).deliveredAt,
        )

        expect(path(deliveredAt)).toBe('fulfilment.legs[1].deliveredAt')
        expect(deliveredAt.unsafeEncode({ id: 'o1', scan_status: 3 })).toEqual({
            M: { id: { S: 'o1' }, scan_status: { N: '3' } },
        })
    })

    it('encodes through the declared codec, not a generic marshaller', () => {
        // `scan_status` is `number` in the spec, so it must reach `N` — a generic marshaller
        // would have to guess, and this is the guess that has been wrong all session
        const txStatus = atOf(
            Adoption,
            (p) => p.fulfilment.legs.at(0).deliveredAt.scan_status,
        )
        expect(path(txStatus)).toBe(
            'fulfilment.legs[0].deliveredAt.scan_status',
        )
        expect(txStatus.unsafeEncode(7)).toEqual({ N: '7' })
    })

    it('round-trips what it encodes', () => {
        const courier = atOf(
            Adoption,
            (p) => p.fulfilment.legs.at(stepIndex).deliveredAt.courier,
        )
        const value = { staffId: 'u1', handle: 'ana' }
        expect(courier.unsafeDecode(courier.unsafeEncode(value))).toEqual(value)
    })

    it('reaches a top-level attribute', () => {
        expect(path(atOf(Adoption, (p) => p.adoptionId))).toBe('adoptionId')
        expect(atOf(Adoption, (p) => p.adoptionId).unsafeEncode('q1')).toEqual({
            S: 'q1',
        })
    })

    it('reaches into a plain list', () => {
        const tag = atOf(Adoption, (p) => p.tags.at(2))
        expect(path(tag)).toBe('tags[2]')
        expect(tag.unsafeEncode('x')).toEqual({ S: 'x' })
    })

    it('is safe when the selector names an intermediate node', () => {
        // a shared, accumulating recorder would record both reads as one path
        const located = atOf(Adoption, (p) => {
            const leg = p.fulfilment.legs.at(stepIndex)
            leg.legType // read, and not the one selected
            return leg.deliveredAt
        })
        expect(path(located)).toBe('fulfilment.legs[1].deliveredAt')
    })

    it('reuses one instance for many independent paths', () => {
        // `path()` has always worked this way — every hop returns a new proxy, nothing mutates
        const p = path(Adoption)
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
            atOf(Adoption, (p) => p.fulfilment.legs.at(0).nonsense),
        ).toThrow(/no attribute is declared at 'fulfilment.legs\[0\].nonsense'/)
    })

    it('types the codec by what lives at the path', () => {
        const located = atOf(
            Adoption,
            (p) => p.fulfilment.legs.at(stepIndex).deliveredAt,
        )
        // thunks, so the assertion is about the types and nothing is actually encoded
        // @ts-expect-error a string is not a delivery
        const _wrongShape = () => located.unsafeEncode('not a delivery')

        const index = atOf(Adoption, (p) => p.currentLegIndex)
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
        const Account = object({
            a: refine(
                object({ x: dynamoNumber }),
                (v): v is { x: typeof v.x } => !v.x.digits.startsWith('-'),
                { describe: 'a balance that is not negative' },
            ),
        }).item
        // @ts-expect-error a path cannot go into `refine`, at the type as at run time
        expect(() => atOf(Account, (p) => p.a.x)).toThrow(CodecError)
        // @ts-expect-error a path cannot go into `refine`, at the type as at run time
        expect(() => atOf(Account, (p) => p.a.x)).toThrow(
            /a path cannot go into `refine` at 'x'/,
        )
        // the refined attribute itself is a path, and its codec keeps the predicate
        expect(path(atOf(Account, (p) => p.a))).toBe('a')
    })

    it('a path that crosses an older reading is refused, because a path addresses the current shape only', () => {
        const Migrated = object({
            a: withLegacyRead({
                current: object({ x: decimal }),
                older: { decode: () => ({ x: '0' }) },
            }),
        }).item
        // @ts-expect-error a path cannot go into `withLegacyRead`, at the type as at run time
        expect(() => atOf(Migrated, (p) => p.a.x)).toThrow(
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
        const Meter = object({ reading: Reading }).item
        const x = atOf(Meter, (p) => p.reading.x)
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
        const Drawing = object({ shape: Shape }).item
        // @ts-expect-error a path cannot go into `refine`, at the type as at run time
        expect(() => atOf(Drawing, (p) => p.shape.x)).toThrow(
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
        const deep = atOf(Envelope, (p) => p.payload.a.b.at(2).c)
        expect(path(deep)).toBe('payload.a.b[2].c')
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
        // @ts-expect-error a path to a declared `never` is vacant, at the type as at run time
        expect(() => atOf(item, (p) => p.b)).toThrow(vacant)
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
            expect(() => atOf(item, (p) => p.r.x.at(0))).toThrow(vacant)
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
            const at = atOf(object({ r: union(options) }).item, (p) => p.r.x)
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
    const Shelf = object({
        name: string,
        count: number,
        tags: string.set(),
        notes: array(string),
        address: object({ city: string }),
        either: union([string, number]),
        payload: opaque,
        tree: Tree.Node,
    }).item

    it('a string field writes an S, because the category of the value is the member of its term', () => {
        const written = atOf(Shelf, (p) => p.name).unsafeEncode('a')
        expect(memberOf(written)).toBe('S')
        expectTypeOf<Category<typeof written>>().toEqualTypeOf<'S'>()
    })

    it('a number field writes an N, because the float adapter writes the member of its stored term', () => {
        const written = atOf(Shelf, (p) => p.count).unsafeEncode(1.5)
        expect(memberOf(written)).toBe('N')
        expectTypeOf<Category<typeof written>>().toEqualTypeOf<'N'>()
    })

    it('a string set writes an SS, because the member of a set follows the member of its element', () => {
        const written = atOf(Shelf, (p) => p.tags).unsafeEncode(new Set(['a']))
        expect(memberOf(written)).toBe('SS')
        expectTypeOf<Category<typeof written>>().toEqualTypeOf<'SS'>()
    })

    it('an array writes an L, and an object writes an M, because a container has one member', () => {
        const list = atOf(Shelf, (p) => p.notes).unsafeEncode(['a'])
        const map = atOf(Shelf, (p) => p.address).unsafeEncode({ city: 'c' })
        expect([memberOf(list), memberOf(map)]).toEqual(['L', 'M'])
        expectTypeOf<Category<typeof list>>().toEqualTypeOf<'L'>()
        expectTypeOf<Category<typeof map>>().toEqualTypeOf<'M'>()
    })

    it('a union of a string and a number writes an S or an N, because each option writes its own member', () => {
        const either = atOf(Shelf, (p) => p.either)
        const written = [either.unsafeEncode('a'), either.unsafeEncode(1)]
        expect(written.map(memberOf)).toEqual(['S', 'N'])
        expectTypeOf<Category<(typeof written)[number]>>().toEqualTypeOf<
            'S' | 'N'
        >()
    })

    it('opaque writes any member, because opaque admits every value', () => {
        const payload = atOf(Shelf, (p) => p.payload)
        const written = [payload.unsafeEncode('a'), payload.unsafeEncode(true)]
        expect(written.map(memberOf)).toEqual(['S', 'BOOL'])
        expectTypeOf<Category<(typeof written)[number]>>().toEqualTypeOf<
            Category<AttributeValue>
        >()
    })

    it('a path through a scope ref writes the member of the entry that the ref names', () => {
        const value = atOf(Shelf, (p) => p.tree.next.v).unsafeEncode('a')
        const node = atOf(Shelf, (p) => p.tree.next).unsafeEncode({ v: 'a' })
        expect([memberOf(value), memberOf(node)]).toEqual(['S', 'M'])
        expectTypeOf<Category<typeof value>>().toEqualTypeOf<'S'>()
        expectTypeOf<Category<typeof node>>().toEqualTypeOf<'M'>()
    })

    it('an attribute of another category does not type-check, because the key states the category', () => {
        const count = atOf(Shelf, (p) => p.count)
        // @ts-expect-error a number field writes an N, never an S
        const wrong: Attribute<'S'> = count.unsafeEncode(1)
        expect(memberOf(wrong)).toBe('N')
    })

    it('the root of an item writes a row and no attribute, so the root keeps the wide type', () => {
        const root = atOf(object({ name: string }).item, (p) => p)
        expect(root.unsafeEncode({ name: 'a' })).toEqual({ name: { S: 'a' } })
        expectTypeOf(root.unsafeEncode).returns.toEqualTypeOf<AttributeValue>()
    })
})
