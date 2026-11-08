/**
 * A key attribute is `S`, `N` or `B`, and the key of one attribute takes the member of that attribute.
 *
 * A key attribute of DynamoDB is `S`, `N` or `B`. A composite key joins its parts, so it is `S`. A
 * key of one attribute copies the attribute: the value, or the stored payload where the field is
 * under the adapter of a caller. So a number is `N`, a `Uint8Array` is
 * `B`, and an `N` sort key
 * orders by number where an `S` key orders `10` before `9`. Every path that writes a row writes the
 * same member: `toItem`, `keys` and `keyUpdates`. `null` gives no key, as `undefined` does, in every
 * path. A key value that the store refuses is refused, and the refusal names the key and never the
 * value.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import type { Attribute } from '../../attribute'
import {
    binary,
    CodecError,
    decimal,
    discriminatedUnion,
    held,
    item,
    nullable,
    number,
    object,
    opaque,
    optional,
    ref,
    scope,
    string,
    union,
} from '../../codec'
import { native } from '../../native'
import type { StandardSchemaV1 } from '../../standard'
import { arbitraryOf, rngFrom, structuralEquals } from '../../testing'

/** What a consumer writes: the narrowing of a result. */
const isError = (value: unknown): value is Error => value instanceof Error

type Pet =
    | { petId: string; status: 'ADOPTED'; owner: string | null; age: number }
    | { petId: string; status: 'AVAILABLE'; shelter: string; age: number }

const Pets = tableEntry<Pet>()({
    PK: ['petId'],
    GSI1SK: 'age',
    GSI2PK: {
        discriminator: 'status',
        spec: { ADOPTED: 'owner', AVAILABLE: ['shelter'] },
    },
})

type Litter = { litterId: string; born: number; name: string }

const Litters = tableEntry<Litter>()(
    { PK: ['litterId'], GSI1SK: 'born' },
    { codec: { litterId: string, born: number, name: string } },
)

describe('a key of one number attribute is N in every path that writes a row', () => {
    it('toItem writes N, and the composite key stays S', () => {
        const written = Litters.toItem({ litterId: 'l1', born: 9, name: 'a' })
        if (isError(written)) return expect.unreachable()
        expect(written.GSI1SK).toEqual({ N: '9' })
        expect(written.PK).toEqual({ S: 'LITTERID#l1' })
        expectTypeOf(written.GSI1SK).toEqualTypeOf<Attribute<'N'>>()
        expectTypeOf(written.PK).toEqualTypeOf<Attribute<'S'>>()
    })

    it('keyUpdates sets N, the member that toItem writes', () => {
        expect(Litters.keyUpdates({ born: 10 }).set).toEqual({
            GSI1SK: { N: '10' },
        })
    })

    it('keys writes N', () => {
        expect(Pets.keys(['GSI1SK'], { age: 3 })).toEqual({
            GSI1SK: { N: '3' },
        })
    })

    it('toEntry writes the number, which a marshaller writes as N', () => {
        expect(
            Pets.toEntry({
                petId: 'p1',
                status: 'AVAILABLE',
                shelter: 's1',
                age: 3,
            }).GSI1SK,
        ).toBe(3)
    })
})

describe('null gives no key in every path, as undefined does', () => {
    const adopted = {
        petId: 'p1',
        status: 'ADOPTED',
        owner: null,
        age: 3,
    } as const

    it('key gives no key for a null attribute arm', () => {
        expect(Pets.key('GSI2PK', adopted)).toBeUndefined()
    })

    it('toEntry omits the key of a null attribute arm', () => {
        expect(Pets.toEntry(adopted)).not.toHaveProperty('GSI2PK')
    })

    it('keyUpdates removes the key of a null attribute arm', () => {
        expect(Pets.keyUpdates({ status: 'ADOPTED', owner: null })).toEqual({
            set: {},
            remove: ['GSI2PK'],
        })
    })

    it('toItem omits the key of a null attribute arm', () => {
        type Owned = { petId: string; owner: string | null }
        const Owned = tableEntry<Owned>()(
            { PK: ['petId'], GSI1PK: 'owner' },
            { codec: { petId: string, owner: nullable(string) } },
        )
        const written = Owned.toItem({ petId: 'p1', owner: null })
        if (isError(written)) return expect.unreachable()
        expect(written).not.toHaveProperty('GSI1PK')
    })
})

describe('keys refuses a key that the attributes do not build', () => {
    it('refuses a key of a null attribute, and names the key', () => {
        expect(() => Pets.keys(['GSI2PK'], { status: 'ADOPTED' })).toThrow(
            "'GSI2PK' gives no key for these attributes",
        )
    })
})

describe('a key value that the store refuses is refused', () => {
    it('refuses a number that DynamoDB cannot store, and names the key and not the value', () => {
        const refusal = (() => {
            try {
                Pets.keys(['GSI1SK'], { age: Number.NaN })
            } catch (error) {
                return error
            }
        })()
        expect(refusal).toBeInstanceOf(RotoriseError)
        expect(String(refusal)).toContain("'GSI1SK'")
        expect(String(refusal)).not.toContain('NaN')
    })
})

type Tag = { tagId: Uint8Array; petId: string; nick: string }

const Tags = tableEntry<Tag>()(
    { PK: 'tagId', SK: 'nick' },
    { codec: { tagId: binary, petId: string, nick: string } },
)

describe('a key of one Uint8Array attribute is B in every path that writes a row', () => {
    const tagId = new Uint8Array([1, 2, 3])

    it('toItem writes B', () => {
        const written = Tags.toItem({ tagId, petId: 'p1', nick: 'Rex' })
        if (isError(written)) return expect.unreachable()
        expect(written.PK).toEqual({ B: tagId })
        expectTypeOf(written.PK).toEqualTypeOf<Attribute<'B'>>()
    })

    it('keys writes B', () => {
        expect(Tags.keys(['PK', 'SK'], { tagId, nick: 'Rex' })).toEqual({
            PK: { B: tagId },
            SK: { S: 'Rex' },
        })
    })

    it('a key with no codec writes B for a Uint8Array', () => {
        const Chips = tableEntry<{ chip: Uint8Array }>()({ GSI1PK: 'chip' })
        expect(Chips.keys(['GSI1PK'], { chip: tagId })).toEqual({
            GSI1PK: { B: tagId },
        })
    })
})

describe('DynamoDB refuses an empty key value, so the run time refuses it', () => {
    it('refuses an empty string key, and names the key and not the value', () => {
        expect(() => Tags.keys(['SK'], { nick: '' })).toThrow(
            "'SK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('refuses an empty Uint8Array key', () => {
        expect(() => Tags.keys(['PK'], { tagId: new Uint8Array() })).toThrow(
            "'PK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('keyUpdates refuses an empty key, where the update writes a key that DynamoDB refuses', () => {
        expect(() => Tags.keyUpdates({ nick: '' })).toThrow(
            "'SK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('toEntry refuses an empty key, which a marshaller writes as a key that DynamoDB refuses', () => {
        expect(() =>
            Tags.toEntry({ tagId: new Uint8Array([1]), petId: 'p1', nick: '' }),
        ).toThrow(
            "'SK' is built from a value that DynamoDB cannot store as a key",
        )
        expect(() =>
            Tags.toEntry({ tagId: new Uint8Array(), petId: 'p1', nick: 'Rex' }),
        ).toThrow(
            "'PK' is built from a value that DynamoDB cannot store as a key",
        )
    })

    it('toItem refuses an empty key, where the item has no key that DynamoDB stores', () => {
        expect(() =>
            Tags.toItem({ tagId: new Uint8Array([1]), petId: 'p1', nick: '' }),
        ).toThrow(RotoriseError)
    })
})

describe('a key has the one member that construction decided', () => {
    /**
     * `opaque` states no member in its term, so a union of `string` and `opaque` decides `S` at
     * construction. A `Uint8Array` that reaches the write past the type is a value that `opaque`
     * writes as `B`. A key of another member than the decided member would give a table one key
     * attribute of two types, so the write refuses it and names the key.
     */
    it('refuses a write at another member than the decided member, and names the key', () => {
        const Mixed = tableEntry<{ id: string; name: string }>()(
            { PK: 'id' },
            { codec: { id: union([string, opaque]) as never, name: string } },
        )
        const past = new Uint8Array([1]) as never
        expect(() => Mixed.toItem({ id: past, name: 'x' })).toThrow(
            "'PK' is built from a value that DynamoDB cannot store as a key",
        )
    })
})

describe('a key follows its attribute in every path that writes a row', () => {
    const dateSchema: StandardSchemaV1<Date> = {
        '~standard': {
            version: 1,
            vendor: 'handwritten',
            validate: (value) =>
                value instanceof Date
                    ? { value }
                    : { issues: [{ message: 'not a Date' }] },
        },
    }
    const bornAt = held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
    })
    const Born = tableEntry<{ petId: string; bornAt: Date }>()(
        { PK: ['petId'], SK: 'bornAt' },
        { codec: { petId: string, bornAt } },
    )
    const day = new Date('2020-01-01T00:00:00.000Z')

    it('toItem writes the key that the codec writes for a held Date, as keys does', () => {
        const written = Born.unsafeToItem({ petId: 'p1', bornAt: day })
        expect(written.SK).toEqual({ S: '2020-01-01T00:00:00.000Z' })
        expect(Born.keys(['SK'], { bornAt: day })).toEqual({
            SK: { S: '2020-01-01T00:00:00.000Z' },
        })
    })

    it('toEntry holds the key that toItem writes for a held Date, and refuses nothing that toItem writes', () => {
        expect(Born.toEntry({ petId: 'p1', bornAt: day }).SK).toBe(
            '2020-01-01T00:00:00.000Z',
        )
        const past = 2 ** 60
        expect(
            Litters.unsafeToItem({ litterId: 'l1', born: past, name: 'a' })
                .GSI1SK,
        ).toEqual({ N: String(past) })
        expect(
            Litters.toEntry({ litterId: 'l1', born: past, name: 'a' }).GSI1SK,
        ).toBe(past)
    })
})

/**
 * **Every route gives one answer for each key name**, over generated entities. A key has five
 * routes: the builder `keys`, the update of `keyUpdates`, the entry of `toEntry`, the write of the
 * item, and the written item that holds the attribute. For each draw and each key name, `keys` is
 * called with that name alone, and exactly one of three rows holds.
 *
 * - **some**: `keys`, `toItem` and `keyUpdates.set` give one attribute, equal by member and text,
 *   and the marshalled `toEntry` is that attribute. Where the key is one attribute of the codec, the
 *   attribute is the one that the written item holds at the field or at the path.
 * - **none**: `keys` refuses with "gives no key", `toItem` and `toEntry` lack the name, and
 *   `keyUpdates.remove` holds it.
 * - **refused**: every route refuses with one reason.
 *
 * A draw that is refused is counted and pinned, not skipped: a string that holds the separator cannot
 * be a part of a composite key. A name that one route answers as another route does not is a failure.
 * Two counted rows state a gap that the owner has not ruled on: `toEntry` holds a string where the
 * row holds `N`, and a number past the safe range, which `native` refuses.
 */
describe('keys and toItem write one key for each key name, over generated entities', () => {
    const dateSchema: StandardSchemaV1<Date> = {
        '~standard': {
            version: 1,
            vendor: 'handwritten',
            validate: (value) =>
                value instanceof Date
                    ? { value }
                    : { issues: [{ message: 'not a Date' }] },
        },
    }
    // a drawn string is rarely a date, so the held side draws one
    const bornOn = held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
        arbitrary: (rng) => new Date(Math.floor(rng() * 4e12)),
    })
    type Route = {
        readonly codec: unknown
        readonly keys: (
            names: readonly string[],
            attributes: never,
        ) => Record<string, unknown>
        readonly keyUpdates: (changed: never) => {
            readonly set: Record<string, unknown>
            readonly remove: readonly string[]
        }
        readonly toEntry: (item: never) => Record<string, unknown>
        readonly toItem: (item: never) => unknown
    }
    type Priced =
        | { kind: 'DOG'; petId: string; price: string }
        | { kind: 'CAT'; petId: string; price: string }
    const pricedVariants = () =>
        item(
            discriminatedUnion('kind', [
                object({ kind: string('DOG'), petId: string }, [
                    string,
                    optional(decimal),
                ]),
                object({ kind: string('CAT'), petId: string }, [
                    string,
                    optional(decimal),
                ]),
            ]),
        )
    const drawPriced = (rng: () => number) => ({
        kind: rng() < 0.5 ? 'DOG' : 'CAT',
        petId: `p${Math.floor(rng() * 9)}`,
        price: `${1 + Math.floor(rng() * 90)}.5`,
    })
    const isoAt = held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
        arbitrary: (rng) => new Date(Math.floor(rng() * 4e12)),
    })
    const epochAt = held(string, dateSchema, {
        encode: (day: Date) => String(day.getTime()),
        decode: (text: string) => new Date(Number(text)),
        arbitrary: (rng) => new Date(Math.floor(rng() * 4e12)),
    })
    type Visit =
        | { kind: 'DOG'; petId: string; at: Date }
        | { kind: 'CAT'; petId: string; at: Date }
    const numberSchema: StandardSchemaV1<number> = {
        '~standard': {
            version: 1,
            vendor: 'handwritten',
            validate: (value) =>
                typeof value === 'number'
                    ? { value }
                    : { issues: [{ message: 'not a number' }] },
        },
    }
    const hexed = held(string, numberSchema, {
        encode: (n: number) => n.toString(16),
        decode: (text: string) => Number.parseInt(text, 16),
        arbitrary: (rng) => Math.floor(rng() * 1e6),
    })
    // a tag that the caller writes as another literal: 'dog' is stored as 'D'
    const Dog = held(string('D'), string('dog'), {
        encode: (_: 'dog') => 'D' as const,
        decode: (_: 'D') => 'dog' as const,
    })
    const unionOf = (dog: unknown) =>
        item(
            discriminatedUnion('kind', [
                object({
                    kind: dog as never,
                    petId: string,
                    chip: hexed,
                    at: isoAt,
                }),
                object({
                    kind: string('cat'),
                    petId: string,
                    chip: hexed,
                    at: isoAt,
                }),
            ] as never),
        )
    const { Pets: refUnion } = scope({
        Pets: discriminatedUnion('kind', [
            object({
                kind: ref('DogTag'),
                petId: string,
                chip: hexed,
                at: isoAt,
            }),
            object({
                kind: string('cat'),
                petId: string,
                chip: hexed,
                at: isoAt,
            }),
        ] as never),
        DogTag: Dog,
    } as never) as { Pets: never }
    /** An entry that the type need not admit, as the entities under a caller tag are. */
    const route = (schema: unknown, codec?: unknown): Route =>
        tableEntry<Record<string, unknown>>()(
            schema as never,
            (codec === undefined ? undefined : { codec }) as never,
        ) as unknown as Route
    const entries: Record<
        string,
        {
            entry: () => Route
            names: readonly string[]
            draw?: (rng: () => number) => unknown
            /** The field or the path that a key of one attribute is, by key name. */
            attribute?: Record<string, string>
        }
    > = {
        Tagged: {
            entry: () =>
                tableEntry<Visit>()(
                    { PK: ['petId'], GSI1SK: 'at' },
                    {
                        codec: item(
                            discriminatedUnion('kind', [
                                object({
                                    kind: string('DOG'),
                                    petId: string,
                                    at: isoAt,
                                }),
                                object({
                                    kind: string('CAT'),
                                    petId: string,
                                    at: isoAt,
                                }),
                            ]),
                        ),
                    },
                ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            attribute: { GSI1SK: 'at' },
        },
        TaggedComposite: {
            entry: () =>
                tableEntry<Visit>()(
                    { PK: ['petId'], GSI1SK: ['at'] },
                    {
                        codec: item(
                            discriminatedUnion('kind', [
                                object({
                                    kind: string('DOG'),
                                    petId: string,
                                    at: isoAt,
                                }),
                                object({
                                    kind: string('CAT'),
                                    petId: string,
                                    at: isoAt,
                                }),
                            ]),
                        ),
                    },
                ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
        },
        TaggedRest: {
            entry: () =>
                tableEntry<Priced>()(
                    { PK: ['petId'], GSI1SK: 'price' },
                    { codec: pricedVariants() as never },
                ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            attribute: { GSI1SK: 'price' },
            draw: drawPriced,
        },
        TaggedRestComposite: {
            entry: () =>
                tableEntry<Priced>()(
                    { PK: ['petId'], GSI1SK: ['kind', 'price'] },
                    { codec: pricedVariants() as never },
                ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            draw: drawPriced,
        },
        Rest: {
            entry: () =>
                tableEntry<{ petId: string; price: string }>()(
                    { PK: ['petId'], GSI1SK: 'price' },
                    {
                        codec: item(
                            object({ petId: string }, [
                                string,
                                optional(decimal),
                            ]),
                        ) as never,
                    },
                ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            attribute: { GSI1SK: 'price' },
            draw: (rng) => ({
                petId: `p${Math.floor(rng() * 9)}`,
                price: `${1 + Math.floor(rng() * 90)}.5`,
            }),
        },
        HeldTag: {
            entry: () =>
                route(
                    {
                        PK: ['petId'],
                        GSI1SK: 'at',
                        SK: ['kind', 'chip'],
                    },
                    unionOf(Dog),
                ),
            names: ['PK', 'GSI1SK', 'SK'],
            attribute: { GSI1SK: 'at' },
        },
        HeldRef: {
            entry: () =>
                route(
                    {
                        PK: ['petId'],
                        GSI1SK: 'at',
                        SK: ['kind', 'chip'],
                    },
                    item(refUnion),
                ),
            names: ['PK', 'GSI1SK', 'SK'],
            attribute: { GSI1SK: 'at' },
        },
        Discriminator: {
            entry: () =>
                route(
                    { PK: ['petId'], GSI1PK: 'kind' },
                    unionOf(string('DOG')),
                ),
            names: ['PK', 'GSI1PK'],
            attribute: { GSI1PK: 'kind' },
        },
        PathNumber: {
            entry: () =>
                route(
                    { PK: ['litterId'], GSI1SK: 'body.grams' },
                    { litterId: string, body: object({ grams: number }) },
                ),
            names: ['PK', 'GSI1SK'],
            attribute: { GSI1SK: 'body.grams' },
        },
        PathBinary: {
            entry: () =>
                route(
                    { PK: ['litterId'], GSI1SK: 'body.chip' },
                    { litterId: string, body: object({ chip: binary }) },
                ),
            names: ['PK', 'GSI1SK'],
            attribute: { GSI1SK: 'body.chip' },
        },
        Sparse: {
            entry: () =>
                route(
                    {
                        PK: ['petId'],
                        GSI1SK: {
                            discriminator: 'kind',
                            spec: { dog: 'at', cat: null },
                        },
                    },
                    unionOf(Dog),
                ),
            names: ['PK', 'GSI1SK'],
        },
        HeldComposite: {
            entry: () =>
                tableEntry<{ petId: string; at: Date }>()(
                    { PK: ['petId'], SK: ['at'] },
                    { codec: { petId: string, at: isoAt } },
                ) as unknown as Route,
            names: ['PK', 'SK'],
        },
        Born: {
            entry: () =>
                tableEntry<{ petId: string; bornAt: Date }>()(
                    { PK: ['petId'], SK: 'bornAt' },
                    { codec: { petId: string, bornAt: bornOn } },
                ) as unknown as Route,
            names: ['PK', 'SK'],
            attribute: { SK: 'bornAt' },
        },
        Litters: {
            entry: () => Litters as unknown as Route,
            names: ['PK', 'GSI1SK'],
            attribute: { GSI1SK: 'born' },
        },
        Prices: {
            entry: () =>
                tableEntry<{ id: string; price: string }>()(
                    { PK: ['id', 'price'] },
                    { codec: { id: string, price: decimal } },
                ) as unknown as Route,
            names: ['PK'],
        },
    }
    type Counts = {
        some: number
        none: number
        refused: number
        toEntryString: number
        toEntryUnsafe: number
    }
    const pinned: Record<string, Counts> = {
        Tagged: {
            some: 150,
            none: 0,
            refused: 25,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        TaggedComposite: {
            some: 150,
            none: 0,
            refused: 25,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        TaggedRest: {
            some: 100,
            none: 0,
            refused: 0,
            toEntryString: 100,
            toEntryUnsafe: 0,
        },
        TaggedRestComposite: {
            some: 200,
            none: 0,
            refused: 0,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        Rest: {
            some: 100,
            none: 0,
            refused: 0,
            toEntryString: 100,
            toEntryUnsafe: 0,
        },
        HeldTag: {
            some: 228,
            none: 0,
            refused: 24,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        HeldRef: {
            some: 228,
            none: 0,
            refused: 24,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        Discriminator: {
            some: 152,
            none: 0,
            refused: 24,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        PathNumber: {
            some: 149,
            none: 0,
            refused: 23,
            toEntryString: 0,
            toEntryUnsafe: 5,
        },
        PathBinary: {
            some: 134,
            none: 0,
            refused: 33,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        Sparse: {
            some: 119,
            none: 33,
            refused: 24,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        HeldComposite: {
            some: 156,
            none: 0,
            refused: 22,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        Born: {
            some: 156,
            none: 0,
            refused: 22,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
        Litters: {
            some: 152,
            none: 0,
            refused: 19,
            toEntryString: 0,
            toEntryUnsafe: 10,
        },
        Prices: {
            some: 78,
            none: 0,
            refused: 22,
            toEntryString: 0,
            toEntryUnsafe: 0,
        },
    }

    /** The attribute that a written item holds at a field or at a path. */
    const heldAt = (written: Record<string, unknown>, path: string) => {
        let at: unknown = written
        for (const [index, segment] of path.split('.').entries()) {
            const map = (index === 0 ? at : (at as { M?: unknown })?.M) as
                | Record<string, unknown>
                | undefined
            at = map?.[segment]
        }
        return at
    }
    /**
     * The reason of a refusal of `keyUpdates`, without the key that the step names first. The step
     * puts `'KEY' cannot be rebuilt from this change: ` before the reason of the builder or of the
     * carrier, so the reason is the one that every route gives. The answer is `undefined` where the
     * message does not start with the prefix of the key that refused, so a step that names no key,
     * or another key, fails the comparison.
     */
    const afterKey = (said: string | undefined, key: string) => {
        const prefix = `'${key}' cannot be rebuilt from this change: `
        return said?.startsWith(prefix) ? said.slice(prefix.length) : undefined
    }
    const said = (run: () => unknown): { value?: unknown; said?: string } => {
        try {
            return { value: run() }
        } catch (error) {
            return { said: (error as Error).message }
        }
    }

    for (const [
        label,
        { entry: build, names, draw, attribute },
    ] of Object.entries(entries)) {
        it(`holds for ${label}`, () => {
            const entry = build()
            const rng = rngFrom(20261107)
            const count: Counts = {
                some: 0,
                none: 0,
                refused: 0,
                toEntryString: 0,
                toEntryUnsafe: 0,
            }
            const failures: string[] = []
            for (let at = 0; at < 100; at++) {
                const entity = (
                    draw ? draw(rng) : arbitraryOf(entry.codec as never, rng, 3)
                ) as never
                const where = `${label} ${at}`
                const keyed = Object.fromEntries(
                    names.map((name) => [
                        name,
                        said(() => entry.keys([name], entity)[name]),
                    ]),
                )
                const written = said(() => {
                    const result = entry.toItem(entity)
                    if (result instanceof Error) throw result
                    return result as Record<string, unknown>
                })
                const entered = said(() => entry.toEntry(entity))
                const updated = said(() => entry.keyUpdates(entity))
                const refusedBy = names.find(
                    (name) =>
                        keyed[name]?.said !== undefined &&
                        !/gives no key for these attributes/.test(
                            keyed[name]?.said ?? '',
                        ),
                )
                if (refusedBy !== undefined) {
                    // refused: every route refuses with the one reason, and the step of `keyUpdates` names the key
                    const reason = keyed[refusedBy]?.said
                    for (const [route, run] of [
                        ['toItem', written],
                        ['toEntry', entered],
                        ['keyUpdates', updated],
                    ] as const)
                        if (
                            (route === 'keyUpdates'
                                ? afterKey(run.said, refusedBy)
                                : run.said) !== reason
                        )
                            failures.push(
                                `${where}: keys says ${reason}, ${route} says ${run.said ?? 'a result'}`,
                            )
                    count.refused++
                    continue
                }
                const row = written.value as Record<string, unknown> | undefined
                const entry2 = entered.value as
                    | Record<string, unknown>
                    | undefined
                const update = updated.value as
                    | { set: Record<string, unknown>; remove: string[] }
                    | undefined
                if (!row || !entry2 || !update) {
                    failures.push(
                        `${where}: no key is refused, and a route refuses: ${written.said ?? entered.said ?? updated.said}`,
                    )
                    continue
                }
                for (const name of names) {
                    const key = keyed[name]?.value
                    if (keyed[name]?.said !== undefined) {
                        // none: the key of this name is absent on every route
                        if (
                            row[name] === undefined &&
                            entry2[name] === undefined &&
                            update.remove.includes(name) &&
                            update.set[name] === undefined
                        )
                            count.none++
                        else
                            failures.push(`${where} ${name}: none on keys only`)
                        continue
                    }
                    const oracle = attribute?.[name]
                        ? heldAt(row, attribute[name])
                        : row[name]
                    if (
                        !structuralEquals(key, row[name]) ||
                        !structuralEquals(update.set[name], row[name]) ||
                        !structuralEquals(oracle, row[name])
                    ) {
                        failures.push(`${where} ${name}: two keys`)
                        continue
                    }
                    const marshalled = native.encode(entry2[name] as never)
                    if (structuralEquals(marshalled, row[name])) count.some++
                    else if (
                        typeof entry2[name] === 'string' &&
                        (row[name] as { N?: string }).N === entry2[name]
                    )
                        count.toEntryString++
                    else if (
                        typeof entry2[name] === 'number' &&
                        marshalled instanceof CodecError &&
                        Number((row[name] as { N?: string }).N) === entry2[name]
                    )
                        count.toEntryUnsafe++
                    else
                        failures.push(
                            `${where} ${name}: toEntry is another key`,
                        )
                }
            }
            expect(failures).toEqual([])
            expect(count).toEqual(pinned[label])
        })
    }

    it('refuses at construction a key that two variants write with two codecs', () => {
        expect(() =>
            tableEntry<Visit>()(
                { PK: ['petId'], GSI1SK: 'at' },
                {
                    codec: item(
                        discriminatedUnion('kind', [
                            object({
                                kind: string('DOG'),
                                petId: string,
                                at: isoAt,
                            }),
                            object({
                                kind: string('CAT'),
                                petId: string,
                                at: epochAt,
                            }),
                        ]),
                    ),
                },
            ),
        ).toThrow(/which two variants write with two codecs/)
    })
})

/**
 * **A variant that does not declare a key attribute has no codec for it.** The type refuses a key
 * that names an attribute which a variant lacks, so the check at run time reads the entity that
 * the type forbids. A value at that attribute is read with no codec, and the codec of another
 * variant never reads it, so `keys` refuses it. The closed body of the variant refuses the same
 * entity in `toItem` before any key is built, and that refusal is a rule of the codec.
 */
describe('a key attribute that the variant of the entity lacks is read with no codec of another variant', () => {
    const dateSchema: StandardSchemaV1<Date> = {
        '~standard': {
            version: 1,
            vendor: 'handwritten',
            validate: (value) =>
                value instanceof Date
                    ? { value }
                    : { issues: [{ message: 'not a Date' }] },
        },
    }
    const isoAt = held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
    })
    const Absent = tableEntry<
        | { kind: 'DOG'; petId: string; at: Date }
        | { kind: 'CAT'; petId: string }
    >()(
        // @ts-expect-error the type refuses a key that names an attribute which a variant lacks
        { PK: ['petId'], GSI1SK: 'at' },
        {
            codec: item(
                discriminatedUnion('kind', [
                    object({
                        kind: string('DOG'),
                        petId: string,
                        at: isoAt,
                    }),
                    object({ kind: string('CAT'), petId: string }),
                ]),
            ),
        },
    )
    const stray = { kind: 'CAT', petId: 'p1', at: new Date(0) } as never

    it('refuses the key of a CAT that carries a Date, where DOG would write the text of the Date', () => {
        expect(
            Absent.keys(['GSI1SK'], { kind: 'DOG', at: new Date(0) } as never),
        ).toEqual({
            GSI1SK: { S: '1970-01-01T00:00:00.000Z' },
        })
        expect(() => Absent.keys(['GSI1SK'], stray)).toThrow(
            /built from a value that DynamoDB cannot store as a key/,
        )
    })
})

/**
 * **A key component is the stored text of its attribute**, over generated entities. A composite key
 * prints each component. The component of an attribute with a codec is the `S` text or the `N`
 * digits that `toItem` writes for the field. `keys` and `toItem` can agree and both print the
 * `toString` of a held `Date`, so the law compares the key with the stored attribute, not with the
 * other route. A draw that `toItem` refuses is counted and pinned.
 */
describe('a key component is the stored text of its attribute, over generated entities', () => {
    const dateSchema: StandardSchemaV1<Date> = {
        '~standard': {
            version: 1,
            vendor: 'handwritten',
            validate: (value) =>
                value instanceof Date
                    ? { value }
                    : { issues: [{ message: 'not a Date' }] },
        },
    }
    const isoAt = held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
        arbitrary: (rng) => new Date(Math.floor(rng() * 4e12)),
    })
    type Route = {
        readonly codec: unknown
        readonly toItem: (item: never) => unknown
        readonly keys: (
            names: readonly string[],
            attributes: never,
        ) => Record<string, { S?: string }>
    }
    const entries: Record<
        string,
        { entry: Route; key: string; fields: readonly string[] }
    > = {
        HeldComposite: {
            entry: tableEntry<{ petId: string; at: Date }>()(
                { PK: ['petId'], SK: ['at'] },
                { codec: { petId: string, at: isoAt } },
            ) as unknown as Route,
            key: 'SK',
            fields: ['at'],
        },
        Prices: {
            entry: tableEntry<{ id: string; price: string }>()(
                { PK: ['id', 'price'] },
                { codec: { id: string, price: decimal } },
            ) as unknown as Route,
            key: 'PK',
            fields: ['id', 'price'],
        },
    }
    const pinned: Record<string, { agree: number; refused: number }> = {
        HeldComposite: { agree: 78, refused: 22 },
        Prices: { agree: 78, refused: 22 },
    }

    for (const [label, { entry, key, fields }] of Object.entries(entries)) {
        it(`holds for ${label}`, () => {
            const rng = rngFrom(20261107)
            const count = { agree: 0, refused: 0 }
            const failures: string[] = []
            for (let at = 0; at < 100; at++) {
                const entity = arbitraryOf(entry.codec as never, rng, 3)
                let written: Record<string, { S?: string; N?: string }>
                try {
                    const row = entry.toItem(entity as never)
                    if (row instanceof Error) {
                        count.refused++
                        continue
                    }
                    written = row as typeof written
                } catch (error) {
                    // a refusal is a value, so a throw other than a refusal is a defect that the law reports
                    if (
                        !(
                            error instanceof RotoriseError ||
                            error instanceof CodecError
                        )
                    )
                        throw error
                    count.refused++
                    continue
                }
                const text = (field: string) => {
                    const stored = written[field]
                    return stored?.S ?? stored?.N
                }
                const expected = fields
                    .flatMap((field) => [field.toUpperCase(), text(field)])
                    .join('#')
                const printed = entry.keys([key], entity as never)[key]?.S
                if (printed === expected) count.agree++
                else
                    failures.push(
                        `${label} ${at}: ${printed} is not ${expected}`,
                    )
            }
            expect(failures).toEqual([])
            expect(count).toEqual(pinned[label])
        })
    }
})
