/**
 * Checking a codec against the marshaller a table was already written with.
 *
 * The question adoption turns on. A team has a hand-written marshaller and a table full of rows it
 * wrote; before swapping in a codec they need to know whether the bytes change and whether the
 * existing rows still read back the same. Asked over generated entities, not the three anyone
 * thinks to try by hand.
 */
import { attest } from '@ark/attest'
import * as sdk from '@aws-sdk/util-dynamodb'
import { describe, expect, it } from 'vitest'
import type { AttributeMap, AttributeValue } from './attribute'
import type { Encoded } from './codec'
import { array, CodecError, decimal, number, object, string } from './codec'
import type { native } from './native'
import type { Reference } from './testing'
import { checkAgainst, firstDifference } from './testing'

type Pet = { TAG: 'PET'; id: string; price: string; tags: ReadonlySet<string> }

const Pet = object({
    TAG: string('PET'),
    id: string,
    price: decimal,
    tags: string.set(),
}).item

/** A marshaller that agrees: money as `N`, tags as a set. */
const agreeing: Reference<Pet> = {
    marshall: (pet) => ({
        TAG: { S: pet.TAG },
        id: { S: pet.id },
        price: { N: pet.price },
        tags: { SS: [...pet.tags].sort() },
    }),
    unmarshall: (item) => ({
        TAG: (item.TAG as { S: string }).S,
        id: (item.id as { S: string }).S,
        price: (item.price as { N: string }).N,
        tags: new Set([...((item.tags as { SS: string[] }).SS ?? [])].sort()),
    }),
}

describe('a codec that matches the marshaller it replaces', () => {
    it('agrees on every generated entity, both ways', () => {
        expect(() =>
            checkAgainst(Pet, agreeing, { count: 200, seed: 20260827 }),
        ).not.toThrow()
    })
})

describe('a codec that does not', () => {
    /** The divergence this session started from: money stored as `S` by one, `N` by the other. */
    it('reports the attribute where the bytes differ', () => {
        const asString: Reference<Pet> = {
            marshall: (pet) => ({
                ...agreeing.marshall(pet),
                price: { S: pet.price },
            }),
        }

        try {
            checkAgainst(Pet, asString, { count: 50, seed: 1 })
            expect.unreachable()
        } catch (thrown) {
            const error = thrown as CodecError
            expect(error).toBeInstanceOf(CodecError)
            expect(error.message).toContain('write parity')
            expect(error.message).toContain('at price')
        }
    })

    /** A list and a set hold the same strings and are not the same attribute. */
    it('reports a set stored as a list', () => {
        const asList: Reference<Pet> = {
            marshall: (pet) => ({
                ...agreeing.marshall(pet),
                tags: { L: [...pet.tags].map((tag) => ({ S: tag })) },
            }),
        }
        expect(() => checkAgainst(Pet, asList, { count: 50, seed: 1 })).toThrow(
            /write parity.*at tags/s,
        )
    })

    /**
     * The half that matters more: a codec can be right about every future write and still be
     * unable to read the rows that are already there.
     */
    it('reports where an existing row reads back differently', () => {
        const readsDifferently: Reference<Pet> = {
            ...agreeing,
            unmarshall: (item) => ({
                ...(agreeing.unmarshall as (i: AttributeMap) => object)(item),
                // this marshaller hands money back as a number, the codec as a string
                price: Number((item.price as { N: string }).N),
            }),
        }
        expect(() =>
            checkAgainst(Pet, readsDifferently, { count: 50, seed: 1 }),
        ).toThrow(/read parity.*at price/s)
    })
})

describe('the difference is reported as a path', () => {
    const at = (ours: unknown, theirs: unknown) =>
        firstDifference(ours, theirs)?.path

    it('names the attribute, not the whole item', () => {
        expect(
            at(
                { a: { S: 'x' }, b: { S: 'y' } },
                { a: { S: 'x' }, b: { S: 'z' } },
            ),
        ).toEqual(['b', 'S'])
    })

    it('descends into a nested map', () => {
        const ours: AttributeValue = { M: { inner: { M: { n: { S: 'a' } } } } }
        const theirs: AttributeValue = {
            M: { inner: { M: { n: { S: 'b' } } } },
        }
        expect(at(ours, theirs)).toEqual(['M', 'inner', 'M', 'n', 'S'])
    })

    it('names the index inside a list', () => {
        const ours: AttributeValue = { L: [{ S: 'a' }, { S: 'b' }] }
        const theirs: AttributeValue = { L: [{ S: 'a' }, { S: 'c' }] }
        expect(at(ours, theirs)).toEqual(['L', 1, 'S'])
    })

    it('says nothing when they agree', () => {
        expect(
            firstDifference({ a: { S: 'x' } }, { a: { S: 'x' } }),
        ).toBeUndefined()
    })

    it('reports an attribute one side does not have at all', () => {
        expect(at({ a: { S: 'x' } }, { a: { S: 'x' }, b: { S: 'y' } })).toEqual(
            ['b'],
        )
    })
})

/**
 * The same question of the types, which is the half a generated run cannot reach.
 *
 * A run over 200 entities says the bytes agreed on those 200. It cannot say the two implementations
 * agree on the *shape* of a row, because a shape is not a value — and shape is what a team needs
 * before a migration: whether the attributes their marshaller writes are the attributes the codec
 * writes, and whether reading their rows back yields the entity they have.
 *
 * `attest<[A], [B]>()` is exact in both directions, so a difference is a named failure with both
 * types printed rather than something to spot by eye. Tuples because `attest` cannot take `never`
 * as an explicit second argument — it cannot tell one from its own default.
 */
describe('the two implementations agree on the shape of a row', () => {
    /** What the SDK's marshaller takes: money as a number, because that is all `N` offers it. */
    type SaleTheirs = {
        id: string
        price: number
        qty: number
        tags: ReadonlySet<string>
        fee: { price: number }
        history: readonly number[]
    }

    /** What ours takes: money as the digits, so a price does not become a float. */
    type SaleOurs = {
        id: string
        price: string
        qty: number
        tags: ReadonlySet<string>
        fee: { price: string }
        history: readonly string[]
    }

    const saleSpec = {
        id: string,
        price: decimal,
        qty: number,
        tags: string.set(),
        fee: object({ price: decimal }),
        history: array(decimal),
    }

    /**
     * The bytes are the same, attribute for attribute, nested and inside collections.
     *
     * This is the migration answer: a team's existing rows are exactly the rows the codec writes,
     * so adopting it changes nothing on disk. The two disagree about the *entity*, not the table.
     */
    it('writes what their marshaller writes', () => {
        attest<[Encoded<typeof saleSpec>], [native.ItemEncode<SaleTheirs>]>()
    })

    /**
     * Reading those same bytes back through their marshaller does *not* give our entity, and this
     * is where the three differences are.
     *
     * Written out rather than compared to `SaleOurs`, because the differences are the deliverable:
     * a team can read this and know what changes when they swap implementations, which is the whole
     * reason to have the shape as a type.
     */
    it('reads back as an entity that differs from ours, and says how', () => {
        attest<
            [native.ItemDecode<Encoded<typeof saleSpec>, string>],
            [
                {
                    id: string
                    /**
                     * The digits, as asked — but `qty` too, and `qty` is a count.
                     *
                     * The deviation belongs to the *marshaller*, not to an attribute: telling it to
                     * keep digits keeps them for every `N` in the table. Ours reaches the same
                     * result per attribute, `decimal` where it matters and `number` where it does
                     * not, which is the difference that does not show up in the bytes.
                     */
                    price: string
                    qty: string
                    /** A native set, as a `Set` — which is what `.set()` reads too. */
                    tags: Set<string>
                    /** Nested maps come back readonly, where the top level does not. */
                    fee: { readonly price: string }
                    /** And a list comes back mutable. */
                    history: string[]
                },
            ]
        >()
    })

    /** Our entity, for contrast — the same rows, read the way the codec reads them. */
    it('is not what the codec decodes', () => {
        attest<
            [Pick<SaleOurs, 'qty' | 'tags'>],
            [{ qty: number; tags: ReadonlySet<string> }]
        >()
    })

    /**
     * Left alone, their marshaller reads `N` as a `number`, widening past the safe range.
     *
     * Which is the reason `price` is a `string` on our side, and the fourth difference: a price
     * that becomes a float stops being the price.
     */
    it('differs again on how a number is read, when not told otherwise', () => {
        attest<
            [native.ItemDecode<Encoded<typeof saleSpec>>],
            [
                {
                    id: string
                    price: number | bigint
                    qty: number | bigint
                    tags: Set<string>
                    fee: { readonly price: number | bigint }
                    history: (number | bigint)[]
                },
            ]
        >()
    })
})

/**
 * The link the chain was missing: a codec against the *real* SDK, not a stand-in.
 *
 * Until now two things were established separately — the port agrees with `@aws-sdk/util-dynamodb`
 * (`native.spec.ts`, over generated values), and a codec agrees with a hand-written reference
 * (above). Neither says a codec agrees with the SDK, which is what a team migrating off
 * `marshall`/`unmarshall` is actually asking.
 *
 * With this, `native.ItemEncode<T>` stops resting on a shape somebody wrote down. The chain closes:
 * `Encoded<Spec>` equals `native.ItemEncode<T>` as types (asserted above), a codec's runtime output *is*
 * `Encoded<Spec>`, and that runtime agrees with `sdk.marshall` here. So the type describes what the
 * SDK writes, and no step in that is a hand-written expectation.
 */
describe('a codec against the SDK itself', () => {
    type Row = {
        TAG: 'ROW'
        id: string
        note: string
        tags: ReadonlySet<string>
    }

    const Row = object({
        TAG: string('ROW'),
        id: string,
        note: string,
        tags: string.set(),
    }).item

    const row: Row = {
        TAG: 'ROW',
        id: 'r1',
        note: 'n',
        tags: new Set(['b', 'a']),
    }

    /**
     * Both reach `SS` from the same value, which they did not always.
     *
     * A set used to be held as a `readonly string[]`, and handed an array the SDK writes a **list** —
     * so the two disagreed about the attribute type itself, and a team whose entity modelled a set as
     * an array had been storing lists. Holding it as a `Set` removes the disagreement rather than
     * adapting around it: only a `Set` reaches `SS`, in either marshaller.
     */
    it('reaches SS from the same value the SDK does', () => {
        const ours = Row.unsafeEncode(row)
        const theirs = sdk.marshall(row) as AttributeMap
        expect(ours.tags).toEqual({ SS: ['a', 'b'] })
        expect(theirs.tags).toEqual({ SS: ['b', 'a'] })
    })

    /**
     * The one difference that is left: order.
     *
     * `SS` is a set, so the order it is written in carries no information — and DynamoDB does not
     * promise to give it back. a set codec sorts, so what is stored is a function of the value alone;
     * the SDK writes the order the `Set` happened to be built in.
     */
    it('sorts a set where the SDK keeps the order it was given', () => {
        expect(sdk.marshall({ tags: new Set(['b', 'a']) })).toEqual({
            tags: { SS: ['b', 'a'] },
        })
        expect(Row.unsafeEncode(row).tags).toEqual({ SS: ['a', 'b'] })
        expect(
            firstDifference(
                Row.unsafeEncode(row),
                sdk.marshall(row) as AttributeMap,
            )?.path,
        ).toEqual(['tags', 'SS', 0])
    })

    /**
     * With both adaptations named, a codec and the real SDK agree over generated rows.
     *
     * This is the link that was missing. `native.spec.ts` establishes port ≡ SDK and the checks
     * above establish codec ≡ a hand-written reference; neither says codec ≡ SDK, which is what a
     * team leaving `marshall`/`unmarshall` is actually asking. With this, `native.ItemEncode<T>` no
     * longer rests on a shape somebody wrote down: `Encoded<Spec>` equals `native.ItemEncode<T>` as
     * types, a codec's runtime output *is* `Encoded<Spec>`, and that runtime agrees with
     * `sdk.marshall` here.
     */
    it('agrees over generated rows once the ordering is adapted', () => {
        // one adaptation now, not two: the order a set is written in. The `Set`-versus-array
        // disagreement it used to also need is gone
        const theSdk: Reference<Row> = {
            marshall: ({ tags, ...rest }) =>
                sdk.marshall({
                    ...rest,
                    tags: new Set([...tags].sort()),
                }) as AttributeMap,
            unmarshall: (stored) => sdk.unmarshall(stored as never) as Row,
        }
        expect(() =>
            checkAgainst(Row, theSdk, { count: 200, seed: 20260827 }),
        ).not.toThrow()
    })

    /**
     * The third difference is a hard limit rather than an adaptation.
     *
     * `N` carries 38 digits; `sdk.marshall` refuses anything past `MAX_SAFE_INTEGER` because it
     * routes numbers through `number`. `decimal` never makes one, which is the entire reason it
     * exists — so this is a shape a team cannot express with the SDK at all, and a reason to move
     * rather than a risk in moving.
     */
    it('keeps digits the SDK refuses to store', () => {
        const Priced = object({
            id: string,
            price: decimal,
        }).item
        const wide = '12345678901234567890'

        expect(Priced.unsafeEncode({ id: 'p', price: wide })).toEqual({
            id: { S: 'p' },
            price: { N: wide },
        })
        expect(() => sdk.marshall({ price: Number(wide) })).toThrow(
            /greater than Number.MAX_SAFE_INTEGER/,
        )
    })
})
