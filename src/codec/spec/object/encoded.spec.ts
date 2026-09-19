/**
 * The stored shape, written by hand and derived from the codec, pinned against each other.
 *
 * A team migrating off a hand-written marshaller needs to know one thing before they start: does
 * the codec put the same bytes in the table? `Encoded<Spec>` answers it at the type level, and
 * `satisfies Writes<Shape>` refuses to compile when the answer is no.
 *
 * `satisfies` is the whole mechanism, and it needs help for this one: the stored shape appears only
 * in `encode`'s return, so it is covariant, and a codec writing a *subset* of the pinned shape would
 * be accepted. {@link Writes} names it in a parameter and a return position both, which makes the
 * comparison mutual — and mutual is what "the same shape" means.
 *
 * The shape is also worth having on its own. Written out and checked in, it is what the table holds
 * — diffable in review, readable without adopting a codec, and the thing to compare against when
 * somebody changes an attribute.
 */
import { describe, expect, it } from 'vitest'
import { table, tableEntry } from '../../../Rotorise'
import type {
    AttributeMap,
    B,
    BOOL,
    L,
    M,
    N,
    NULL,
    S,
    SS,
} from '../../attribute'
import type { Encoded, ItemCodec, Writes } from '../../codec'
import {
    array,
    binary,
    boolean,
    decimal,
    discriminatedUnion,
    list,
    nullable,
    number,
    object,
    opaque,
    optional,
    record,
    string,
    union,
} from '../../codec'

type Pet = {
    TAG: 'PET'
    id: string
    /** money: a string in the entity, a number in the table — the case a marshaller gets wrong */
    price: string
    weight: number
    adopted: boolean
    photo: Uint8Array
    tags: ReadonlySet<string>
    breed: { species: string; coat?: string }
    visits: readonly { at: string }[]
    note?: string
    retiredAt: string | null
}

/** What the table holds. Written by hand, on purpose. */
type PetItem = {
    TAG: S
    id: S
    price: N
    weight: N
    adopted: BOOL
    photo: B
    tags: SS
    breed: M<{ species: S; coat?: S }>
    visits: L<M<{ at: S }>>
    note?: S
    retiredAt: S | NULL
}

const spec = {
    TAG: string('PET'),
    id: string,
    price: decimal,
    weight: number,
    adopted: boolean,
    photo: binary,
    tags: string.set(),
    breed: object({ species: string, coat: optional(string) }),
    visits: array(object({ at: string })),
    note: optional(string),
    retiredAt: nullable(string),
}

/**
 * The pin. This does not compile if the codec stops writing `PetItem`.
 *
 * Two questions, asked separately and chained: `ItemCodec<Pet>` is the entity the codec reads and
 * writes, `Writes<PetItem>` is the row it puts in the table. Neither needs a type argument on the
 * constructor — the spec is what `item` is given, and everything else is checked against it.
 */
const Pet = object(spec).item satisfies ItemCodec<Pet> satisfies Writes<PetItem>

const pet: Pet = {
    TAG: 'PET',
    id: 'p1',
    price: '10.5',
    weight: 4,
    adopted: true,
    photo: Uint8Array.from([1]),
    tags: new Set(['a', 'b']),
    breed: { species: 'dog' },
    visits: [{ at: 'now' }],
    retiredAt: null,
}

describe('the shape a codec writes', () => {
    it('is the shape written by hand', () => {
        // the compiler has already checked this; the assignment is the assertion
        const derived: PetItem = {} as Encoded<typeof spec>
        const declared: Encoded<typeof spec> = {} as PetItem
        expect([derived, declared]).toHaveLength(2)
    })

    it('and the runtime agrees, member for member', () => {
        const written = Pet.unsafeEncode({
            TAG: 'PET',
            id: 'p1',
            price: '10.5',
            weight: 4,
            adopted: true,
            photo: Uint8Array.from([1]),
            tags: new Set(['calm', 'small']),
            breed: { species: 'dog' },
            visits: [{ at: '2026-01-01' }],
            retiredAt: null,
        })

        expect(written.price).toEqual({ N: '10.5' })
        expect(written.tags).toEqual({ SS: ['calm', 'small'] })
        expect(written.breed).toEqual({ M: { species: { S: 'dog' } } })
        expect(written.visits).toEqual({
            L: [{ M: { at: { S: '2026-01-01' } } }],
        })
        expect(written.retiredAt).toEqual({ NULL: true })
        expect(written).not.toHaveProperty('note')
    })
})

/**
 * The message lands where the codec is *used*, not where it is built: a parameter whose type
 * depends on the spec being inferred stops the spec being inferred, so the check is on the
 * result. Reading anything off it is what surfaces it.
 */
describe('the pin refuses a codec that writes something else', () => {
    /**
     * `price` as a string is the migration this exists to catch.
     * @anchored
     */
    /**
     * Reported on the declaration, which is why none of these reach for the codec afterwards.
     *
     * The check is intersected with the spec parameter, so a mismatch is an error on the argument.
     * Were it on the *result* instead, the declaration would typecheck and the message would wait
     * for the first `.encode` — so a test that touched one would pass either way and say nothing
     * about where the error appears.
     */
    it('when an attribute reaches a different member', () => {
        const drifted = { ...spec, price: string }
        const _wrong = () =>
            // @ts-expect-error `string` writes S where the shape pins N
            object(drifted) satisfies Writes<PetItem>
        expect(typeof _wrong).toBe('function')
    })

    /** A list and a set are the distinction a marshaller that guesses cannot make. */
    it('when a set becomes a list', () => {
        const drifted = { ...spec, tags: array(string) }
        const _wrong = () =>
            // @ts-expect-error `array(string)` writes L where the shape pins SS
            object(drifted) satisfies Writes<PetItem>
        expect(typeof _wrong).toBe('function')
    })

    it('when a nested map writes a different member', () => {
        const drifted = {
            ...spec,
            breed: object({ species: string, coat: optional(decimal) }),
        }
        const _wrong = () =>
            // @ts-expect-error `coat` writes N inside the map where the shape pins S
            object(drifted) satisfies Writes<PetItem>
        expect(typeof _wrong).toBe('function')
    })

    it('when a required attribute becomes optional', () => {
        const drifted = { ...spec, id: optional(string) }
        const _wrong = () =>
            // @ts-expect-error the shape pins `id` as present, not optional
            object(drifted) satisfies Writes<PetItem>
        expect(typeof _wrong).toBe('function')
    })

    /**
     * The reason the pin is a function pair and not a property.
     *
     * A property carrying the shape is covariant, so a codec that writes a *subset* of it would be
     * accepted — and "writes N where the row may hold N or S" is exactly the drift worth catching.
     */
    it('when the codec writes a subset of the pinned shape', () => {
        type Wider = Omit<PetItem, 'price'> & { price: N | S }
        const _wrong = () =>
            // @ts-expect-error the row admits S here and the codec never writes it
            object(spec) satisfies Writes<Wider>
        expect(typeof _wrong).toBe('function')
    })

    it('is off unless a shape is given, so nothing existing has to change', () => {
        const unpinned = object(spec).item
        expect(typeof unpinned.encode).toBe('function')
    })
})

/**
 * What a codec writes, read off the codec rather than written beside it.
 *
 * `Encoded<Spec>` had to be spelled out to be seen, while `encode` returned "some attribute map" —
 * even though `object(...)` is built from an item codec and did keep the shape. So the fixed point a
 * team wants to diff in review is now the codec's own return type, with no second declaration to
 * drift from it.
 */
describe('an item codec types what it writes', () => {
    it('names each attribute, not `AttributeValue`', () => {
        const written = Pet.unsafeEncode(pet)

        // the member each attribute carries is known, so reading the right one needs no cast
        const price: string = written.price.N
        const tags: readonly string[] = written.tags.SS
        expect([price, tags]).toEqual(['10.5', ['a', 'b']])

        // ...and the wrong one is `never`, which is what makes `N` and `S` distinguishable
        // @ts-expect-error `price` is stored as N, so it never carries S
        const wrong: string = written.price.S
        expect(wrong).toBeUndefined()

        // under the default policy nothing else is written, so there is no attribute to reach for
        // @ts-expect-error the spec declares no such attribute
        written.notDeclared
    })

    it('distinguishes a set from a list, which a marshaller that guesses cannot', () => {
        const written = Pet.unsafeEncode(pet)
        // @ts-expect-error `tags` is a set, so it is carried as SS and never as L
        const asList: readonly unknown[] = written.tags.L
        expect(asList).toBeUndefined()
    })

    it('agrees with the shape written by hand', () => {
        type FromCodec = ReturnType<typeof Pet.unsafeEncode>
        // mutual assignability, which is what "the same shape" means — see `Same`
        const there: FromCodec = {} as PetItem
        const back: PetItem = {} as FromCodec
        expect([there, back]).toHaveLength(2)
    })

    it('still satisfies the wide map a request holds', () => {
        const request: AttributeMap = Pet.unsafeEncode(pet)
        expect(Object.keys(request).length).toBeGreaterThan(0)
    })

    /**
     * A rest policy writes attributes the spec never named, so the type says so.
     *
     * Claiming `Encoded<Spec>` exactly would refuse to read an attribute the codec really wrote —
     * which is what made the first attempt at this wrong.
     */
    it('admits the attributes a rest policy adds', () => {
        const Open = object(
            {
                id: string,
            },
            [string, optional(opaque('lossy'))],
        ).item
        const written = Open.unsafeEncode({ id: 'p', extra: 'x' })
        expect(written.id.S).toBe('p')
        expect(written.extra).toEqual({ S: 'x' })
    })
})

/**
 * A patch types what *it* writes, not what the entity could hold.
 *
 * `Partial<Encoded<Spec>>` was the weaker answer: every attribute optional, so an `UpdateItem` built
 * from one was checked against the whole entity rather than against the attributes being set.
 */
describe('a patch types the attributes it names', () => {
    it('names them, and only them', () => {
        const written = Pet.unsafeEncodePartial({ price: '1', note: 'hi' })

        // the two named attributes are present and known — no optional chaining
        const price: string = written.price.N
        const note: string = written.note.S
        expect([price, note]).toEqual(['1', 'hi'])

        // @ts-expect-error the patch does not name `weight`, so it writes no such attribute
        written.weight
    })

    it('keeps a patched attribute optional only where the patch admits undefined', () => {
        const maybe: string | undefined = undefined
        const written = Pet.unsafeEncodePartial({ note: maybe })
        // `note` may or may not be written, because the value given may be absent
        expect(written.note?.S).toBeUndefined()
    })
})

/**
 * A whole row: the codec's attributes and the schema's computed keys, in one type.
 *
 * This is the function a team calls to write a row, so it is the shape worth diffing in review.
 */
describe('an entry types the row it writes', () => {
    const Entry = tableEntry<Pet>()(
        { PK: table(['id']), GSI1PK: ['TAG'] },
        { codec: spec },
    )

    it('carries the declared attributes and the computed keys', () => {
        const row = Entry.unsafeToItem(pet)
        const pk: string = row.PK.S
        const gsi: string = row.GSI1PK.S
        const price: string = row.price.N
        expect([pk, gsi, price]).toEqual(['ID#p1', 'TAG#PET', '10.5'])
    })

    it('is still the wide map a request holds', () => {
        const request: AttributeMap = Entry.unsafeToItem(pet)
        expect(Object.keys(request)).toContain('PK')
    })

    it('refuses an attribute neither the codec nor the schema writes', () => {
        const row = Entry.unsafeToItem(pet)
        // @ts-expect-error no such attribute is written
        row.notAThing
    })
})

/**
 * `record` and `tuple` name what they hold, so a shape containing either can be pinned.
 *
 * Both used to write `Attribute<'M'>` and `Attribute<'L'>` — "some map", "some list" — which meant a
 * shape containing one could not be pinned at all, and the pin is the whole point.
 */
describe('a record and a tuple keep their shape', () => {
    type Crate = {
        prices: Readonly<Record<string, string>>
        span: readonly [string, number]
        nested: Readonly<Record<string, { at: string }>>
    }

    type CrateItem = {
        prices: M<{ readonly [key: string]: N }>
        span: L<readonly [S, N]>
        nested: M<{ readonly [key: string]: M<{ at: S }> }>
    }

    const crateSpec = {
        prices: record(decimal),
        span: list(string, number),
        nested: record(object({ at: string })),
    }

    /** The pin. This does not compile if either constructor starts flattening again. */
    const Crate = object(crateSpec)
        .item satisfies ItemCodec<Crate> satisfies Writes<CrateItem>

    it('writes the shape written by hand', () => {
        const written = Crate.unsafeEncode({
            prices: { dog: '1.5' },
            span: ['a', 2],
            nested: { x: { at: 'now' } },
        })
        // a tuple keeps its positions, so each is the member that position writes
        const first: string = written.span.L[0].S
        const second: string = written.span.L[1].N
        expect([first, second]).toEqual(['a', '2'])
        expect(written.prices.M.dog).toEqual({ N: '1.5' })
        expect(written.nested.M.x?.M.at).toEqual({ S: 'now' })
    })

    it('is refused when a record holds a different member', () => {
        const drifted = { ...crateSpec, prices: record(string) }
        const _wrong = () =>
            // @ts-expect-error `prices` holds strings, and the shape pins N
            object(drifted) satisfies Writes<CrateItem>
        expect(typeof _wrong).toBe('function')
    })

    it('is refused when a tuple position changes', () => {
        const drifted = {
            ...crateSpec,
            span: list(decimal, number) as never,
        }
        const _wrong = () =>
            // @ts-expect-error `span` is readonly [S, N], and this writes [N, N]
            object(drifted) satisfies Writes<CrateItem>
        expect(typeof _wrong).toBe('function')
    })
})

/**
 * The pin, on the three declarations that were not covered.
 *
 * `item` had it; a union and a whole row did not — and a union is where it matters most, because a
 * variant that drifts writes a different attribute at a *key component*, so the mis-description
 * lands in an index rather than in a field.
 */
describe('a union pins the shape it writes', () => {
    /** One variant or the other, never the merge — a row is exactly one of them. */
    type VisitItem =
        | { TAG: S; kind: S; petId: S; vetId: S }
        | { TAG: S; kind: S; petId: S; dose: N }

    const checkup = object({
        TAG: string('VISIT'),
        kind: string('CHECKUP'),
        petId: string,
        vetId: string,
    })
    const shot = object({
        TAG: string('VISIT'),
        kind: string('SHOT'),
        petId: string,
        dose: decimal,
    })

    it('accepts a tagged codec that writes it', () => {
        const Visit = discriminatedUnion('kind', [checkup, shot])
            .item satisfies Writes<VisitItem>
        expect(
            Visit.unsafeEncode({
                TAG: 'VISIT',
                kind: 'SHOT',
                petId: 'p',
                dose: '1.5',
            }).dose,
        ).toEqual({ N: '1.5' })
    })

    it('refuses one where a single variant has drifted', () => {
        const drifted = [
            checkup,
            object({ ...shot.item.spec, dose: string }),
        ] as const
        const _wrong = () =>
            // @ts-expect-error `dose` writes S in the SHOT variant, where the shape pins N
            discriminatedUnion('kind', drifted) satisfies Writes<VisitItem>
        expect(typeof _wrong).toBe('function')
    })

    it('pins an untagged union by position', () => {
        type LineItem = { petId: S; price: N } | { petIds: L<S> }

        const ok = union([
            object({ petId: string, price: decimal }),
            object({ petIds: array(string) }),
        ]).item satisfies Writes<LineItem>
        expect(ok.unsafeEncode({ petId: 'p', price: '1' }).price).toEqual({
            N: '1',
        })

        const drifted = [
            { petId: string, price: string },
            { petIds: array(string) },
        ] as const
        const _wrong = () =>
            // @ts-expect-error `price` writes S here, where the shape pins N
            union(drifted) satisfies Writes<LineItem>
        expect(typeof _wrong).toBe('function')
    })
})

/**
 * And the whole row, which is the shape a team actually diffs.
 *
 * Pinned against the attributes *and* the computed keys together, so a key that changes name or a
 * key that stops being computed is caught — neither of which a shape of only the attributes sees.
 */
describe('an entry pins the row it writes', () => {
    type Row = { TAG: 'PET'; id: string; price: string }
    type RowItem = { TAG: S; id: S; price: N; PK: S; GSI1PK: S }

    const rowSpec = { TAG: string('PET'), id: string, price: decimal }
    const row: Row = { TAG: 'PET', id: 'p', price: '1.5' }

    // the schema is written inline at each call: hoisted, `['TAG']` widens to `string[]` and stops
    // being a key spec at all, because `const` inference only reaches a literal argument

    it('accepts an entry that writes it', () => {
        const Entry = tableEntry<Row, RowItem>()(
            { PK: table(['id']), GSI1PK: ['TAG'] },
            { codec: rowSpec },
        )
        const written = Entry.unsafeToItem(row)
        expect(written.PK).toEqual({ S: 'ID#p' })
        expect(written.GSI1PK).toEqual({ S: 'TAG#PET' })
        expect(written.price).toEqual({ N: '1.5' })
    })

    it('refuses one whose attribute has drifted', () => {
        const _wrong = () =>
            tableEntry<Row, RowItem>()(
                { PK: table(['id']), GSI1PK: ['TAG'] },
                // @ts-expect-error `price` writes S here, where the row pins N
                { codec: { ...rowSpec, price: string } },
            )
        expect(typeof _wrong).toBe('function')
    })

    /** The case a shape of only the attributes cannot see. */
    it('refuses one that stopped computing a key', () => {
        const _wrong = () =>
            tableEntry<Row, RowItem>()(
                { PK: table(['id']) },
                // @ts-expect-error the row pins `GSI1PK`, and this schema does not compute it
                { codec: rowSpec },
            )
        expect(typeof _wrong).toBe('function')
    })
})
