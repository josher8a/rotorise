/**
 * The round-trip law against DynamoDB itself, rather than against a belief about it.
 *
 * Every other spec asserts `decode(encode(x)) = x` in memory. That is a claim about the codec, not
 * about storage — and storage is where the interesting losses happen. `codec.listing.spec.ts` fakes
 * the storage leg by hand-writing `{ N: '1.5' }` for an item encoded as `{ N: '1.50' }`, which
 * encodes *my belief* about normalisation into the fixture. This tier removes the belief:
 *
 * ```
 * decode(getItem(putItem(encode(x)))) = x
 * ```
 *
 * Opt-in, because it needs a running DynamoDB:
 *
 * ```sh
 * DYNAMODB_ENDPOINT=http://localhost:4566 npx vitest run src/codec/spec/surface/codec.dynamodb.spec.ts
 * ```
 *
 * Spoken to over plain HTTP rather than through the AWS SDK, so this package keeps its zero
 * dependencies. Local DynamoDB and LocalStack do not verify the signature; a real endpoint would
 * need SigV4 and is not what this tier is for.
 *
 * The wire format is JSON, in which `B` is base64 — a detail the SDK normally hides, and one that
 * has to be handled here or `binary` could never be tested through storage at all.
 */
import { afterAll, beforeAll, describe, expect, it } from 'vitest'
import type { AttributeMap } from '../../attribute'
import type { ItemCodec } from '../../codec'
import {
    array,
    binary,
    decimal,
    failed,
    item,
    number,
    object,
    opaque,
    optional,
    string,
} from '../../codec'
import {
    arbitraryOf,
    type Checkable,
    rngFrom,
    structuralEquals,
} from '../../testing'

const endpoint = process.env.DYNAMODB_ENDPOINT
const suite = endpoint ? describe : describe.skip

/** `B` and `BS` travel as base64 on the wire; a `Uint8Array` does not survive `JSON.stringify`. */
const toWire = (value: unknown): unknown => {
    if (value instanceof Uint8Array)
        return Buffer.from(value).toString('base64')
    if (Array.isArray(value)) return value.map(toWire)
    if (value && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value).map(([k, v]) => [k, toWire(v)]),
        )
    }
    return value
}

const fromWire = (value: unknown, key?: string): unknown => {
    if (typeof value === 'string' && (key === 'B' || key === 'BS')) {
        return Uint8Array.from(Buffer.from(value, 'base64'))
    }
    if (Array.isArray(value)) return value.map((x) => fromWire(x, key))
    if (value && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value).map(([k, v]) => [k, fromWire(v, k)]),
        )
    }
    return value
}

const call = async (
    target: string,
    body: unknown,
): Promise<Record<string, unknown>> => {
    const response = await fetch(endpoint as string, {
        method: 'POST',
        headers: {
            'Content-Type': 'application/x-amz-json-1.0',
            'X-Amz-Target': `DynamoDB_20120810.${target}`,
            Authorization:
                'AWS4-HMAC-SHA256 Credential=test/20260101/us-east-1/dynamodb/aws4_request, SignedHeaders=host;x-amz-target, Signature=unverified',
        },
        body: JSON.stringify(toWire(body)),
    })
    const text = await response.text()
    if (!response.ok) throw new Error(`${target}: ${response.status} ${text}`)
    return text ? (fromWire(JSON.parse(text)) as Record<string, unknown>) : {}
}

type Row = {
    pk: string
    /** money: the reason `decimal` exists */
    amount: string
    /** a counter, where losing precision is fine */
    count: number
    kind: 'A' | 'B'
    /** a native set, which comes back in an order nobody chose */
    tags: ReadonlySet<string>
    /** an ordered list, which must keep its order */
    steps: readonly string[]
    /** binary, which the wire carries as base64 */
    blob: Uint8Array
    /**
     * the escape hatch, whose `N` handling depends on what the service does to the digits.
     *
     * Optional, and it has to be: `unknown` includes `undefined`, so nothing about a required
     * `unknown` distinguishes it from an absent one. Declaring the entity first hid that — an
     * optional codec satisfied a required `unknown` attribute without comment.
     */
    extra?: unknown
    note?: string
}

const Row = item(
    object({
        pk: string,
        amount: decimal,
        count: number,
        kind: string('A', 'B'),
        tags: string.set(),
        steps: array(string),
        blob: binary,
        // `unknown` includes `undefined`, so the spec requires the optional form.
        // Numbers are opted into here, because this row stores them through the escape hatch.
        extra: optional(opaque('lossy')),
        note: optional(string),
    }),
) satisfies ItemCodec<Row>

const TABLE = `rotorise_roundtrip_${Date.now()}`

/** Encode, store, read back, decode — the law with the real system in the middle. */
const throughDynamo = async (value: Row): Promise<Row> => {
    await call('PutItem', { TableName: TABLE, Item: Row.unsafeEncode(value) })
    const { Item } = (await call('GetItem', {
        TableName: TABLE,
        Key: { pk: { S: value.pk } },
        ConsistentRead: true,
    })) as { Item?: AttributeMap }
    if (!Item) throw new Error(`no item came back for '${value.pk}'`)
    return Row.unsafeDecode(Item)
}

suite('the law, against DynamoDB', () => {
    beforeAll(async () => {
        await call('CreateTable', {
            TableName: TABLE,
            BillingMode: 'PAY_PER_REQUEST',
            AttributeDefinitions: [{ AttributeName: 'pk', AttributeType: 'S' }],
            KeySchema: [{ AttributeName: 'pk', KeyType: 'HASH' }],
        })
        for (let i = 0; i < 60; i++) {
            const { Table } = (await call('DescribeTable', {
                TableName: TABLE,
            })) as { Table: { TableStatus: string } }
            if (Table.TableStatus === 'ACTIVE') return
            await new Promise((r) => setTimeout(r, 200))
        }
        throw new Error('table never became ACTIVE')
    }, 60_000)

    afterAll(async () => {
        if (endpoint) await call('DeleteTable', { TableName: TABLE })
    })

    it('holds for generated rows that have been through storage', async () => {
        const rng = rngFrom(20260826)
        const subject: Checkable<Row> = Row
        for (let i = 0; i < 40; i++) {
            const value = {
                ...(arbitraryOf(subject as never, rng, 3) as Row),
                pk: `case-${i}`,
            }
            const returned = await throughDynamo(value)
            if (!structuralEquals(returned, value)) {
                throw new Error(
                    `decode(getItem(putItem(encode(x)))) !== x at case ${i}\n  x        = ${JSON.stringify(value)}\n  returned = ${JSON.stringify(returned)}`,
                )
            }
        }
    }, 120_000)

    /**
     * The measurement `decimal`'s held set is read off, and it has to bypass the codec now: a
     * denormalised numeral is exactly what `decimal` refuses to write, so the only way to put one
     * in the table is by hand. What comes back is the normal form, which is why the refusal exists.
     */
    it('normalises every N it accepts, which is why `decimal` refuses the rest', async () => {
        const written = [
            ['1.500', '1.5'],
            ['007', '7'],
            ['+1', '1'],
            ['1e5', '100000'],
            ['-0', '0'],
            ['0.0', '0'],
            ['1.0', '1'],
            ['.5', '0.5'],
            ['1.', '1'],
            ['01', '1'],
        ] as const

        for (const [put, expected] of written) {
            const pk = `normalisation-${put}`
            await call('PutItem', {
                TableName: TABLE,
                Item: { pk: { S: pk }, n: { N: put } },
            })
            const { Item } = (await call('GetItem', {
                TableName: TABLE,
                Key: { pk: { S: pk } },
                ConsistentRead: true,
            })) as { Item?: AttributeMap }
            expect([put, (Item?.n as { N: string }).N]).toEqual([put, expected])
            // and every one of them is a form `decimal` declines to produce
            expect(failed(decimal.encode(put))).toBe(true)
        }
    }, 60_000)

    /** The other half: what it does hand back, `decimal` writes and reads. */
    it('hands back exactly what `decimal` wrote, for the forms it accepts', async () => {
        for (const amount of ['0', '1.5', '10', '100', '-1.5', '0.0000001']) {
            const returned = await throughDynamo({
                pk: `normal-${amount}`,
                amount,
                count: 1,
                kind: 'A',
                tags: new Set(['x']),
                steps: [],
                blob: Uint8Array.from([1, 2, 3]),
                extra: null,
            })
            expect(returned.amount).toBe(amount)
        }
    }, 60_000)

    /** Precision and magnitude are hard errors from the service, not silent truncation. */
    it('rejects what `decimal` and `number` reject, rather than rounding it', async () => {
        const refused = [
            '123456789012345678901234567890123456789',
            '1E+126',
            '1E-131',
            'NaN',
        ] as const
        for (const n of refused) {
            expect(failed(decimal.encode(n))).toBe(true)
            await expect(
                call('PutItem', {
                    TableName: TABLE,
                    Item: { pk: { S: `refused-${n}` }, n: { N: n } },
                }),
            ).rejects.toThrow()
        }
    }, 60_000)

    it('confirms a set loses the order it was written in', async () => {
        const returned = await throughDynamo({
            pk: 'set-order',
            amount: '0',
            count: 0,
            kind: 'B',
            tags: new Set(['b', 'a']),
            steps: ['b', 'a'],
            blob: new Uint8Array(0),
            extra: null,
        })
        expect(returned.tags).toEqual(new Set(['a', 'b']))
        // ...while a list keeps it, which is why the two are different codecs
        expect(returned.steps).toEqual(['b', 'a'])
    }, 30_000)

    it('round-trips a number through the escape hatch, despite N normalisation', async () => {
        // the codec writes `String(n)` and reads a number back only when the stored digits are
        // exactly that form — so this is the case where the service must not have rewritten them
        for (const n of [0, 1, -7, 1.5, 0.1, 1e20, 0.1 + 0.2]) {
            const returned = await throughDynamo({
                pk: `unknown-number-${n}`,
                amount: '0',
                count: 0,
                kind: 'A',
                tags: new Set(['x']),
                steps: [],
                blob: new Uint8Array(0),
                extra: n,
            })
            expect(returned.extra).toBe(n)
        }
    }, 60_000)

    it('rounds a foreign N under lossy, and keeps it an N', async () => {
        const wide = '123456789012345678901234567890'
        await call('PutItem', {
            TableName: TABLE,
            Item: {
                ...Row.unsafeEncode({
                    pk: 'foreign-n',
                    amount: '0',
                    count: 0,
                    kind: 'A',
                    tags: new Set(['x']),
                    steps: [],
                    blob: new Uint8Array(0),
                    extra: null,
                }),
                // written by another service, with more precision than a float holds
                extra: { N: wide },
            },
        })
        const read = async () => {
            const { Item } = (await call('GetItem', {
                TableName: TABLE,
                Key: { pk: { S: 'foreign-n' } },
                ConsistentRead: true,
            })) as { Item: AttributeMap }
            return Item
        }

        const stored = await read()
        // opting into `lossy` means exactly this: the digits do not survive
        expect(Row.unsafeDecode(stored).extra).toBe(Number(wide))
        expect(String(Row.unsafeDecode(stored).extra)).not.toBe(wide)

        // but the member does, which is the property that keeps queries working
        await call('PutItem', {
            TableName: TABLE,
            Item: Row.unsafeEncode(Row.unsafeDecode(stored)),
        })
        expect(Object.keys((await read()).extra as object)).toEqual(['N'])
    }, 30_000)

    it('carries binary through base64 without altering a byte', async () => {
        const blob = Uint8Array.from([0, 1, 127, 128, 255])
        const returned = await throughDynamo({
            pk: 'binary',
            amount: '0',
            count: 0,
            kind: 'A',
            tags: new Set(['x']),
            steps: [],
            blob,
            extra: null,
        })
        expect(returned.blob).toBeInstanceOf(Uint8Array)
        expect([...returned.blob]).toEqual([...blob])
    }, 30_000)

    it('carries a decimal no JS number could hold', async () => {
        const amount = '123456789012345678901234567890.12345678'
        const returned = await throughDynamo({
            pk: 'wide',
            amount,
            count: 0,
            kind: 'A',
            tags: new Set(['x']),
            steps: [],
            blob: Uint8Array.from([1, 2, 3]),
            extra: null,
        })
        expect(returned.amount).toBe(amount)
        expect(Number(amount).toString()).not.toBe(amount)
    }, 30_000)
})
