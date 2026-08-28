/**
 * `patch` against the key-schema shapes a real table reaches for.
 *
 * The simple case — a key built from a plain list of components — is covered elsewhere. These are
 * the rest: a discriminated key with a `null` variant, so an index is sparse; a discriminated key
 * whose variants carry transform tuples; a transform with a default; and the `TAG` discriminant
 * that tends to appear in every key of a single-table design.
 */
import { describe, expect, it } from 'vitest'
import {
    CodecError,
    discriminatedUnion,
    literal,
    number,
    object,
    optional,
    string,
} from './codec'
import { RotoriseError, tableEntry } from './Rotorise'

describe('shipments', () => {
    type Shipment = {
        TAG: 'SHIPMENT'
        userId: string
        shipmentId: string
        status: 'PENDING' | 'SETTLED'
        createdAt: string
        provider: string
        vendorShipmentId: string
        amount: string
    }
    const Shipments = tableEntry<Shipment>()(
        {
            PK: ['userId'],
            SK: ['TAG', 'shipmentId'],
            GSI1PK: ['TAG', 'status'],
            GSI1SK: ['createdAt'],
            GSI2PK: ['provider'],
            GSI2SK: ['TAG', 'vendorShipmentId'],
        },
        {
            codec: {
                TAG: literal('SHIPMENT'),
                userId: string,
                shipmentId: string,
                status: literal('PENDING', 'SETTLED'),
                createdAt: string,
                provider: string,
                vendorShipmentId: string,
                amount: string,
            },
        },
    )

    it('rebuilds only the key a status change invalidates, TAG unasked', () => {
        // `TAG: literal('SHIPMENT')` admits one value, so the codec supplies it and the signature
        // does not ask. This call carried `{ TAG: 'SHIPMENT' }` as context before the codec was read.
        const keys = Shipments.keyUpdates({ status: 'SETTLED' })
        expect(Object.keys(keys)).toEqual(['GSI1PK'])
        expect(keys.GSI1PK).toEqual({ S: 'TAG#SHIPMENT#STATUS#SETTLED' })
    })

    it("rejects TAG as context, because it is not the caller's to decide", () => {
        const _overridesTag = () =>
            // @ts-expect-error the codec decides TAG; there is no context left to pass
            Shipments.keyUpdates({ status: 'SETTLED' }, { TAG: 'SHIPMENT' })
        expect(typeof _overridesTag).toBe('function')
    })

    it('supplies TAG to every key built from it, not only the first', () => {
        const keys = Shipments.keyUpdates({ vendorShipmentId: 'p2' })
        expect(Object.keys(keys)).toEqual(['GSI2SK'])
    })

    it('touches no key when only a non-key attribute changes', () => {
        expect(Shipments.keyUpdates({ amount: '10' })).toEqual({})
    })
})

describe('invoices, with a null variant', () => {
    type Invoice =
        | {
              TAG: 'INVOICE'
              type: 'CARD'
              orgId: string
              invoiceId: string
              status: 'NEW' | 'DONE'
              vendorInvoiceId: string
          }
        | {
              TAG: 'INVOICE'
              type: 'PICKUP'
              orgId: string
              invoiceId: string
              status: 'NEW' | 'DONE'
          }

    const Invoices = tableEntry<Invoice>()({
        PK: ['TAG', 'orgId'],
        SK: ['invoiceId'],
        // PICKUP invoices are absent from GSI1 entirely — a sparse index
        GSI1PK: {
            discriminator: 'type',
            spec: { CARD: ['vendorInvoiceId'], PICKUP: null },
        },
        GSI1SK: {
            discriminator: 'type',
            spec: { CARD: ['TAG', 'orgId'], PICKUP: null },
        },
        GSI2PK: ['status'],
        GSI2SK: ['TAG', 'orgId', 'invoiceId'],
    })

    it('reads components through a discriminated spec, and past the null variant', () => {
        // GSI2PK is built from status alone, so a status change rebuilds it
        const keys = Invoices.keyUpdates({ status: 'DONE' })
        expect(keys.GSI2PK).toEqual({ S: 'STATUS#DONE' })
        // keyUpdates returns keys only — the attribute itself is the caller's to encode
        expect(Object.keys(keys)).toEqual(['GSI2PK'])
    })

    it('treats the discriminator itself as a component', () => {
        // changing `type` moves the invoice in and out of the sparse index, so the
        // components of both GSI1 keys are needed before it can be rebuilt
        // @ts-expect-error vendorInvoiceId, TAG and orgId are all still needed
        const _movesIndex = () => Invoices.keyUpdates({ type: 'CARD' })
        expect(typeof _movesIndex).toBe('function')
    })

    it('rebuilds the sparse key when every component is given', () => {
        const patch = Invoices.keyUpdates(
            { type: 'CARD', vendorInvoiceId: 'p1' },
            { TAG: 'INVOICE', orgId: 'o1' },
        )
        expect(patch.GSI1PK).toEqual({ S: 'VENDORINVOICEID#p1' })
        expect(patch.GSI1SK).toEqual({ S: 'TAG#INVOICE#ORGID#o1' })
    })
})

describe('a transform with a default', () => {
    type Account = {
        TAG: 'KENNEL'
        orgId: string
        id: string
        provider: string
        externalId?: string
    }
    const Accounts = tableEntry<Account>()({
        PK: ['TAG', 'orgId'],
        SK: ['TAG', 'id'],
        GSI1PK: ['provider'],
        GSI1SK: ['TAG', ['externalId', (x: string) => x, '']],
    })

    it('sees the attribute named inside a transform tuple', () => {
        // @ts-expect-error GSI1SK is built from TAG and the externalId inside the tuple
        const _needsTag = () => Accounts.keyUpdates({ externalId: 'e1' })
        expect(typeof _needsTag).toBe('function')
    })

    it('rebuilds it with the transform applied', () => {
        const patch = Accounts.keyUpdates(
            { externalId: 'e1' },
            { TAG: 'KENNEL' },
        )
        expect(patch.GSI1SK).toEqual({ S: 'TAG#KENNEL#EXTERNALID#e1' })
    })
})

describe('identity, discriminated with transforms', () => {
    type Identity =
        | { TAG: 'EMAIL'; userId: string; email: string }
        | { TAG: 'PHONE'; userId: string; phone: string }

    const Identities = tableEntry<Identity>()({
        PK: {
            discriminator: 'TAG',
            spec: {
                EMAIL: ['TAG', ['email', (x: string) => x.toLowerCase()]],
                PHONE: ['TAG', ['phone', (x: string) => x.toLowerCase()]],
            },
        },
        SK: ['TAG'],
        GSI1PK: ['userId'],
    })

    it('collects components from every variant of a discriminated key', () => {
        // @ts-expect-error TAG and phone are not in the change
        const _needsBoth = () => Identities.keyUpdates({ email: 'A@B.COM' })
        expect(typeof _needsBoth).toBe('function')
    })

    it('applies the variant transform when rebuilding', () => {
        /**
         * Only `TAG` is asked for, not `phone`.
         *
         * `PK` names `email` or `phone` depending on the discriminant, so its components across all
         * variants are `TAG | email | phone` — but the context is typed `Pick<Identity, …>`, and
         * `keyof` a union is the keys its members share, which leaves `TAG`. That lands on the right
         * answer for the right reason here: a change carrying `email` is an EMAIL identity, whose
         * `PK` needs `TAG` and `email` and nothing else. It would under-ask for a change that named
         * neither, which the runtime guard still catches.
         */
        const keys = Identities.keyUpdates(
            { email: 'A@B.COM' },
            { TAG: 'EMAIL' },
        )
        expect(keys.PK).toEqual({ S: 'TAG#EMAIL#EMAIL#a@b.com' })
    })
})

describe('a single-key table', () => {
    type Otp = { otpIdentifier: string; code: string; attempts: number }
    const Otps = tableEntry<Otp>()(
        { PK: ['otpIdentifier'], SK: ['otpIdentifier'] },
        {
            codec: { otpIdentifier: string, code: string, attempts: number },
        },
    )

    it('leaves the keys alone when the identity is not changing', () => {
        expect(Otps.keyUpdates({ attempts: 3, code: 'x' })).toEqual({})
    })

    it('warns rather than silently emitting a table key', () => {
        // patching the identity rebuilds PK/SK, which DynamoDB refuses to update —
        // recorded here because the schema cannot yet say which keys are the table's
        const keys = Otps.keyUpdates({ otpIdentifier: 'new' })
        expect(keys).toHaveProperty('PK')
        expect(keys).toHaveProperty('SK')
    })
})

describe('a literal decides a component only when it admits one value', () => {
    type Row = { TAG: 'ROW'; kind: 'A' | 'B'; id: string; label: string }
    const Rows = tableEntry<Row>()(
        {
            PK: ['id'],
            GSI1PK: ['TAG', 'label'],
            GSI2PK: ['kind', 'label'],
        },
        {
            codec: {
                TAG: literal('ROW'),
                kind: literal('A', 'B'),
                id: string,
                label: string,
            },
        },
    )

    it('still asks for a many-valued literal', () => {
        const _needsKind = () =>
            // @ts-expect-error GSI2PK is built from `kind`, and literal('A', 'B') decides nothing
            Rows.keyUpdates({ label: 'x' })
        expect(typeof _needsKind).toBe('function')
    })

    it('asks for that one only, the single-valued one being settled', () => {
        const keys = Rows.keyUpdates({ label: 'x' }, { kind: 'A' })
        expect(Object.keys(keys).sort()).toEqual(['GSI1PK', 'GSI2PK'])
    })
})

type ItemWriter = {
    unsafeToItem: (row: unknown) => Record<string, { S: string }>
    keyUpdates: (changed: unknown) => Record<string, { S: string }>
}

describe('a constant is only ever as good as the codec that claims it', () => {
    type Row =
        | { TAG: 'A'; id: string; label: string }
        | { TAG: 'B'; id: string; label: string }

    /**
     * The declaration is the mistake, so that is where it is reported.
     *
     * One map of attributes describes one variant. `TAG` is typed as the whole union at the
     * boundary, so a `'B'` row reaches a codec admitting only `'A'` — and `TAG` is a component of
     * `GSI1PK`, which is how a mis-description becomes a wrong index entry rather than a wrong
     * field. Refused at `tableEntry`, for the reason `item` refuses the same thing.
     */
    it('refuses a single map of attributes for a union entity', () => {
        const _single = () =>
            tableEntry<Row>()(
                { PK: ['id'], GSI1PK: ['TAG', 'label'] },
                {
                    // @ts-expect-error one map describes one variant and mis-describes the rest
                    codec: { TAG: literal('A'), id: string, label: string },
                },
            )
        expect(typeof _single).toBe('function')
    })

    /**
     * The net beneath it, for a caller who cast past the signature.
     *
     * Before `literal` checked on the way out, this wrote `TAG#B#...` from the row and
     * `TAG#A#...` from the constant, silently, into the same index. The constant was not wrong;
     * the codec making the claim was not keeping it.
     */
    it('refuses a value the claiming codec does not admit, either way', () => {
        const Rows = tableEntry<Row>()(
            { PK: ['id'], GSI1PK: ['TAG', 'label'] },
            {
                codec: {
                    TAG: literal('A'),
                    id: string,
                    label: string,
                } as never,
            },
        )
        const b: Row = { TAG: 'B', id: 'i', label: 'l' }

        expect(() => (Rows as never as ItemWriter).unsafeToItem(b)).toThrow(
            CodecError,
        )
        expect(() => literal('A').unsafeEncode('B' as 'A')).toThrow(
            "'B' is not one of 'A'",
        )
        // and for a row it does admit, the codec and the constant agree
        const admitted = (Rows as never as ItemWriter).unsafeToItem({
            TAG: 'A',
            id: 'i',
            label: 'l',
        })
        expect(admitted.GSI1PK).toEqual(
            (Rows as never as ItemWriter).keyUpdates({ label: 'l' }).GSI1PK,
        )
    })

    /**
     * A union *is* describable — by a discriminated codec, which can say which variant an item is.
     * What is refused is a codec that cannot: read as a plain attribute, the same union is one `M`
     * value with no variants to ask.
     */
    it('refuses a codec that cannot name a variant', () => {
        // read as one `M` value rather than through `.item`, which is the whole difference:
        // an attribute codec has no variants to ask
        const asUnion = discriminatedUnion('TAG', [
            object({ TAG: literal('A'), id: string, label: string }),
            object({ TAG: literal('B'), id: string, label: string }),
        ])

        expect(() =>
            tableEntry<Row>()(
                { PK: ['id'], GSI1PK: ['TAG', 'label'] },
                {
                    codec: asUnion as never,
                },
            ),
        ).toThrow(RotoriseError)
        expect(() =>
            tableEntry<Row>()(
                { PK: ['id'], GSI1PK: ['TAG', 'label'] },
                {
                    codec: asUnion as never,
                },
            ),
        ).toThrow(/neither an item codec nor a tagged one/)
    })
})

describe('a union entity, described by a tagged codec', () => {
    type Invoice =
        | {
              TAG: 'INVOICE'
              type: 'CARD'
              orgId: string
              invoiceId: string
              status: 'NEW' | 'DONE'
              vendorInvoiceId: string
          }
        | {
              TAG: 'INVOICE'
              type: 'PICKUP'
              orgId: string
              invoiceId: string
              status: 'NEW' | 'DONE'
          }

    const Invoices = tableEntry<Invoice>()(
        {
            PK: ['TAG', 'orgId'],
            SK: ['invoiceId'],
            GSI2PK: ['status'],
            GSI2SK: ['TAG', 'orgId', 'invoiceId'],
            GSI3PK: ['type', 'orgId'],
        },
        {
            codec: discriminatedUnion('type', [
                object({
                    TAG: literal('INVOICE'),
                    type: literal('CARD'),
                    orgId: string,
                    invoiceId: string,
                    status: literal('NEW', 'DONE'),
                    vendorInvoiceId: string,
                }),
                object({
                    TAG: literal('INVOICE'),
                    type: literal('PICKUP'),
                    orgId: string,
                    invoiceId: string,
                    status: literal('NEW', 'DONE'),
                }),
            ]).item,
        },
    )

    const bank: Invoice = {
        TAG: 'INVOICE',
        type: 'CARD',
        orgId: 'o1',
        invoiceId: 'p1',
        status: 'NEW',
        vendorInvoiceId: 'x1',
    }

    it('round-trips each variant through the keys and back', () => {
        const item = Invoices.unsafeToItem(bank)
        expect(item.PK).toEqual({ S: 'TAG#INVOICE#ORGID#o1' })
        expect(Invoices.unsafeFromItem(item)).toEqual(bank)

        const onchain: Invoice = {
            TAG: 'INVOICE',
            type: 'PICKUP',
            orgId: 'o1',
            invoiceId: 'p2',
            status: 'DONE',
        }
        expect(Invoices.unsafeFromItem(Invoices.unsafeToItem(onchain))).toEqual(
            onchain,
        )
    })

    /** Every variant writes `TAG: literal('INVOICE')`, so the variants together decide it. */
    it('reads a constant the variants agree on', () => {
        // GSI2SK is built from TAG, orgId and invoiceId; only orgId has to be supplied
        const keys = Invoices.keyUpdates({ invoiceId: 'p9' }, { orgId: 'o1' })
        expect(keys.GSI2SK).toEqual({
            S: 'TAG#INVOICE#ORGID#o1#INVOICEID#p9',
        })
    })

    it('rejects the agreed constant as context, having decided it', () => {
        const _overrides = () =>
            Invoices.keyUpdates(
                { invoiceId: 'p9' },
                // @ts-expect-error TAG is decided by the variants; only orgId is left to pass
                { orgId: 'o1', TAG: 'INVOICE' },
            )
        expect(typeof _overrides).toBe('function')
    })

    it('agrees with what the codec would have written', () => {
        const moved: Invoice = { ...bank, status: 'DONE' }
        expect(Invoices.keyUpdates({ status: 'DONE' }).GSI2PK).toEqual(
            Invoices.unsafeToItem(moved).GSI2PK,
        )
    })

    /**
     * `type` is `literal('CARD')` in one variant and `literal('PICKUP')` in the other, so it is
     * exactly what the variants do not agree on — deciding it is their whole disagreement. `TAG`
     * is a component of `PK` in the same change and is not asked for, which is the contrast.
     */
    it('does not read a constant the variants disagree on', () => {
        const _needsType = () =>
            // @ts-expect-error GSI3PK is built from `type`, and GSI2SK from invoiceId
            Invoices.keyUpdates({ orgId: 'o2' })
        expect(typeof _needsType).toBe('function')

        // with invoiceId supplied, GSI2SK is satisfied and GSI3PK is what is left short
        const untyped = Invoices.keyUpdates as (
            c: object,
            ctx?: object,
        ) => unknown
        expect(() => untyped({ orgId: 'o2' }, { invoiceId: 'p1' })).toThrow(
            /'GSI3PK' is built from 'type', 'orgId'.*'type' is not given/s,
        )

        // and with both supplied, PK still rebuilds without TAG being mentioned anywhere
        const keys = Invoices.keyUpdates(
            { orgId: 'o2' },
            { type: 'PICKUP', invoiceId: 'p1' },
        )
        expect(keys.PK).toEqual({ S: 'TAG#INVOICE#ORGID#o2' })
        expect(keys.GSI3PK).toEqual({ S: 'TYPE#PICKUP#ORGID#o2' })
    })
})
