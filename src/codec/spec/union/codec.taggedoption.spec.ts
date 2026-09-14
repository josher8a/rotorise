/**
 * A {@link union} whose options are themselves tagged, which is the shape a 2x2 product takes when
 * its two axes are different kinds of axis.
 *
 * One axis separates by **names** — an order naming one pet against an order naming a list — and
 * the other by a **literal**, the status the order is at. `union` resolves by names and cannot see
 * the literal; `discriminatedUnion` resolves by tag and takes one option per tag. Neither spans
 * both axes alone, so the two nest: the outer union picks the group, the inner tag picks the
 * variant.
 *
 * This declared at runtime and was refused by the type, because {@link ObjectSpecsOf} read a
 * tagged option's `item.spec` as a record of attributes. It is the **tag map**, so two tagged
 * options both looked to require `placed` and `delivered` and `Collides` called them the same. A
 * tagged option is not judged by names at all: `identifies` certifies it, and the runtime selects
 * it by attempting.
 */
import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { ErrorMessage } from '../../../utils'
import type { AttributeCodec, ValidateOptions } from '../../codec'
import {
    discriminatedUnion,
    object,
    optional,
    string,
    union,
} from '../../codec'

/** That it refuses, rather than the words it refuses with. */
type Refuses<T> = [T] extends [ErrorMessage<string>] ? true : false

type Order =
    | {
          readonly status: 'placed'
          readonly petId: string
          readonly shipDate?: string
      }
    | { readonly status: 'delivered'; readonly petId: string }
    | { readonly status: 'placed'; readonly petIds: string }
    | { readonly status: 'delivered'; readonly petIds: string }

const byPetId = discriminatedUnion('status', [
    object({
        status: string('placed'),
        petId: string,
        shipDate: optional(string),
    }),
    object({ status: string('delivered'), petId: string }),
])

const byPetIds = discriminatedUnion('status', [
    object({ status: string('placed'), petIds: string }),
    object({ status: string('delivered'), petIds: string }),
])

describe('a union whose options are tagged', () => {
    const order = union([byPetId, byPetIds]) satisfies AttributeCodec<Order>

    it('declares, where the tag map read as attributes refused it', () => {
        attest<
            false,
            Refuses<ValidateOptions<[typeof byPetId, typeof byPetIds]>>
        >()
    })

    it('picks the group by name and the variant by tag, in both directions', () => {
        for (const value of [
            { status: 'placed', petId: 'a', shipDate: 'd' },
            { status: 'delivered', petId: 'a' },
            { status: 'placed', petIds: 'a' },
            { status: 'delivered', petIds: 'a' },
        ] as const satisfies readonly Order[]) {
            expect(order.unsafeDecode(order.unsafeEncode(value))).toEqual(value)
        }
    })

    it('reads back the variant the value was written as', () => {
        attest<Order, ReturnType<typeof order.unsafeDecode>>()
    })

    /**
     * The whole-item reading, which is what a repository stores a row through.
     *
     * A union of tagged options is still a union of objects, so it has one. `AllObjects` asks
     * whether every option is an `AnyObjectCodec`, and a tagged option's `spec` is its tag map
     * rather than a record of attributes — so the type degraded `.item` to an `ErrorMessage` and
     * the runtime had no `declares` to match names against.
     */
    it('reads and writes a whole item', () => {
        const row = order.item.unsafeEncode({
            status: 'placed',
            petId: 'a',
            shipDate: 'd',
        })
        expect(row).toEqual({
            status: { S: 'placed' },
            petId: { S: 'a' },
            shipDate: { S: 'd' },
        })
        expect(order.item.unsafeDecode(row)).toEqual({
            status: 'placed',
            petId: 'a',
            shipDate: 'd',
        })

        const other = order.item.unsafeEncode({
            status: 'delivered',
            petIds: 'b',
        })
        expect(order.item.unsafeDecode(other)).toEqual({
            status: 'delivered',
            petIds: 'b',
        })
    })

    /**
     * The refusal the dropped check does not lose.
     *
     * `same` admits every value `byPetId` admits, `shipDate` being optional, so no value selects
     * it. That is {@link Restricting} — a question about the entities, which a tagged option
     * answers as readily as an object one.
     *
     * The type refuses it and the runtime does not, which is where an object option already
     * stands: {@link separable} exempts one on its first row and defers the name question to the
     * declaration. A tagged option reaches the same answer one row later, by {@link identifies}.
     */
    it('still refuses a tagged option whose entity sits inside another', () => {
        const same = discriminatedUnion('status', [
            object({ status: string('placed'), petId: string }),
            object({ status: string('delivered'), petId: string }),
        ])
        attest<true, Refuses<ValidateOptions<[typeof byPetId, typeof same]>>>()
    })
})
