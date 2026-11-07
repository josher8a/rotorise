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
    decimal,
    discriminatedUnion,
    held,
    item,
    nullable,
    number,
    object,
    opaque,
    optional,
    string,
    union,
} from '../../codec'
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
 * **Every route writes one key for each key name**, over generated entities. A key has four routes,
 * the key builder of `keys`, the update of `keyUpdates`, the entry of `toEntry` and the write of the
 * item, and each must give the key that the codec gives for the attribute. The entities are drawn from the codec of each entry. A draw that
 * both routes refuse is counted and pinned, not skipped: a string that holds the separator cannot be
 * a part of a composite key, and `keys` and `toItem` say so alike. A draw that one route writes and
 * the other refuses is a failure, as is a draw that the two write as two keys.
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
    type Visit =
        | { kind: 'DOG'; petId: string; at: Date }
        | { kind: 'CAT'; petId: string; at: Date }
    const entries: Record<
        string,
        {
            entry: Route
            names: readonly string[]
            draw?: (rng: () => number) => unknown
        }
    > = {
        Tagged: {
            entry: tableEntry<Visit>()(
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
        },
        TaggedComposite: {
            entry: tableEntry<Visit>()(
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
            entry: tableEntry<Priced>()(
                { PK: ['petId'], GSI1SK: 'price' },
                { codec: pricedVariants() as never },
            ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            draw: drawPriced,
        },
        TaggedRestComposite: {
            entry: tableEntry<Priced>()(
                { PK: ['petId'], GSI1SK: ['kind', 'price'] },
                { codec: pricedVariants() as never },
            ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            draw: drawPriced,
        },
        Rest: {
            entry: tableEntry<{ petId: string; price: string }>()(
                { PK: ['petId'], GSI1SK: 'price' },
                {
                    codec: item(
                        object({ petId: string }, [string, optional(decimal)]),
                    ) as never,
                },
            ) as unknown as Route,
            names: ['PK', 'GSI1SK'],
            draw: (rng) => ({
                petId: `p${Math.floor(rng() * 9)}`,
                price: `${1 + Math.floor(rng() * 90)}.5`,
            }),
        },
        HeldComposite: {
            entry: tableEntry<{ petId: string; at: Date }>()(
                { PK: ['petId'], SK: ['at'] },
                { codec: { petId: string, at: isoAt } },
            ) as unknown as Route,
            names: ['PK', 'SK'],
        },
        Born: {
            entry: tableEntry<{ petId: string; bornAt: Date }>()(
                { PK: ['petId'], SK: 'bornAt' },
                { codec: { petId: string, bornAt: bornOn } },
            ) as unknown as Route,
            names: ['PK', 'SK'],
        },
        Litters: {
            entry: Litters as unknown as Route,
            names: ['PK', 'GSI1SK'],
        },
        Prices: {
            entry: tableEntry<{ id: string; price: string }>()(
                { PK: ['id', 'price'] },
                { codec: { id: string, price: decimal } },
            ) as unknown as Route,
            names: ['PK'],
        },
    }
    const pinned: Record<string, { agree: number; bothRefuse: number }> = {
        Born: { agree: 78, bothRefuse: 22 },
        Litters: { agree: 81, bothRefuse: 19 },
        Prices: { agree: 78, bothRefuse: 22 },
        Tagged: { agree: 75, bothRefuse: 25 },
        TaggedComposite: { agree: 75, bothRefuse: 25 },
        TaggedRest: { agree: 100, bothRefuse: 0 },
        TaggedRestComposite: { agree: 100, bothRefuse: 0 },
        Rest: { agree: 100, bothRefuse: 0 },
        HeldComposite: { agree: 78, bothRefuse: 22 },
    }

    for (const [label, { entry, names, draw }] of Object.entries(entries)) {
        it(`holds for ${label}`, () => {
            const rng = rngFrom(20261107)
            const count = { agree: 0, bothRefuse: 0 }
            const failures: string[] = []
            for (let at = 0; at < 100; at++) {
                const entity = draw
                    ? draw(rng)
                    : arbitraryOf(entry.codec as never, rng, 3)
                let keyed: Record<string, unknown> | undefined
                let keysSaid: string | undefined
                try {
                    keyed = entry.keys(names, entity as never)
                } catch (error) {
                    keysSaid = (error as Error).message
                }
                let item: Record<string, unknown> | undefined
                let itemSaid: string | undefined
                try {
                    const written = entry.toItem(entity as never)
                    if (written instanceof Error) itemSaid = written.message
                    else item = written as Record<string, unknown>
                } catch (error) {
                    itemSaid = (error as Error).message
                }
                if (keyed === undefined && item === undefined) {
                    count.bothRefuse++
                } else if (keyed === undefined || item === undefined) {
                    failures.push(
                        `${label} ${at}: keys ${keysSaid ?? 'writes'}, toItem ${itemSaid ?? 'writes'}`,
                    )
                } else if (
                    names.every((name) =>
                        structuralEquals(keyed[name], item[name]),
                    )
                ) {
                    // the other two routes write the key that the item holds
                    let updated: Record<string, unknown> | undefined
                    let entered: Record<string, unknown> | undefined
                    try {
                        updated = entry.keyUpdates(entity as never).set
                        entered = entry.toEntry(entity as never)
                    } catch (error) {
                        failures.push(
                            `${label} ${at}: ${(error as Error).message}`,
                        )
                        continue
                    }
                    const held = (name: string) => {
                        const stored = item[name] as {
                            S?: string
                            N?: string
                        }
                        return stored.S ?? stored.N
                    }
                    if (
                        names.every(
                            (name) =>
                                structuralEquals(updated?.[name], item[name]) &&
                                (typeof entered?.[name] === 'number'
                                    ? entered[name] === Number(held(name))
                                    : entered?.[name] === held(name)),
                        )
                    )
                        count.agree++
                    else failures.push(`${label} ${at}: two keys`)
                } else {
                    failures.push(`${label} ${at}: two keys`)
                }
            }
            expect(failures).toEqual([])
            expect(count.agree).toBeGreaterThan(50)
            expect(count).toEqual(pinned[label])
        })
    }
})

describe('two variants that write a key attribute with two codecs are refused, at a name and at a component', () => {
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
    const iso = held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
    })
    const epoch = held(string, dateSchema, {
        encode: (day: Date) => String(day.getTime()),
        decode: (text: string) => new Date(Number(text)),
    })
    type Visit =
        | { kind: 'DOG'; petId: string; at: Date }
        | { kind: 'CAT'; petId: string; at: Date }
    const build = (spec: never, first: unknown, second: unknown) =>
        tableEntry<Visit>()(spec, {
            codec: item(
                discriminatedUnion('kind', [
                    object({
                        kind: string('DOG'),
                        petId: string,
                        at: first as never,
                    }),
                    object({
                        kind: string('CAT'),
                        petId: string,
                        at: second as never,
                    }),
                ]),
            ),
        } as never)

    it('refuses the key of one attribute, and each plain component of a list', () => {
        for (const spec of [
            { PK: ['petId'], GSI1SK: 'at' },
            { PK: ['petId'], GSI1SK: ['at'] },
            { PK: ['petId'], GSI1SK: ['petId', 'at'] },
        ])
            expect(() => build(spec as never, iso, epoch)).toThrow(
                /'GSI1SK' is built from 'at', which two variants write with two codecs/,
            )
    })

    it('accepts one codec that both variants share', () => {
        expect(() =>
            build({ PK: ['petId'], GSI1SK: ['at'] } as never, iso, iso),
        ).not.toThrow()
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
                } catch {
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
            expect(count.agree).toBeGreaterThan(50)
            expect(count).toEqual(pinned[label])
        })
    }
})
