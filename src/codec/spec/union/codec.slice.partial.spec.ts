/**
 * A summand that fits a member of a union pattern only in part.
 *
 * The slice of an option goes into the field that holds a union and keeps the members that fit, in
 * place. A summand of that field can fit a member of the pattern in part: some of its values fit and
 * the others do not. The run time then splits the option and keeps the parts that fit. The type
 * must say the same, or the decoded type of the extraction excludes values that the run time keeps.
 *
 * Each case lists, for every class of value in a pool, whether the run time keeps the class and
 * whether the decoded type admits it. The two tables are one table, so a type that drops a kept
 * class, or a run time that keeps a class that the type drops, fails here.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AttributeValue } from '../../attribute'
import type { Decoded } from '../../codec'
import {
    discriminatedUnion,
    exclude,
    extract,
    object,
    string,
    union,
} from '../../codec'
import { failed } from '../../result'

const owner = union([
    object({ type: string('PERSON'), name: string }),
    object({ type: string('SHELTER'), id: string }),
])
const pets = union([
    object({ category: string('DOG'), owner }),
    object({ category: string('CAT'), owner }),
])
const order = union([
    object({ kind: string('ADOPT'), pet: pets }),
    object({ kind: string('RETURN'), pet: pets, note: string }),
])

type Kind = 'ADOPT' | 'RETURN'
type Category = 'DOG' | 'CAT'
type Owner = 'PERSON' | 'SHELTER'
type OwnerOf<O extends Owner> = O extends 'PERSON'
    ? { readonly type: 'PERSON'; readonly name: string }
    : { readonly type: 'SHELTER'; readonly id: string }
type Value<
    K extends Kind,
    C extends Category,
    O extends Owner,
> = K extends 'RETURN'
    ? {
          readonly kind: K
          readonly pet: { readonly category: C; readonly owner: OwnerOf<O> }
          readonly note: string
      }
    : {
          readonly kind: K
          readonly pet: { readonly category: C; readonly owner: OwnerOf<O> }
      }
type Classes = {
    readonly ADOPT_DOG_PERSON: Value<'ADOPT', 'DOG', 'PERSON'>
    readonly ADOPT_DOG_SHELTER: Value<'ADOPT', 'DOG', 'SHELTER'>
    readonly ADOPT_CAT_PERSON: Value<'ADOPT', 'CAT', 'PERSON'>
    readonly ADOPT_CAT_SHELTER: Value<'ADOPT', 'CAT', 'SHELTER'>
    readonly RETURN_DOG_PERSON: Value<'RETURN', 'DOG', 'PERSON'>
    readonly RETURN_DOG_SHELTER: Value<'RETURN', 'DOG', 'SHELTER'>
    readonly RETURN_CAT_PERSON: Value<'RETURN', 'CAT', 'PERSON'>
    readonly RETURN_CAT_SHELTER: Value<'RETURN', 'CAT', 'SHELTER'>
}
/** Whether the decoded type of a slice admits a value of each class. */
type AdmittedBy<S, C> = {
    readonly [K in keyof C]: [C[K]] extends [S] ? true : false
}

const ownerRow = (type: Owner): AttributeValue => ({
    M: {
        type: { S: type },
        ...(type === 'PERSON'
            ? { name: { S: 'ann' } }
            : { id: { S: 'shelter-1' } }),
    },
})
const rowOf = (
    kind: Kind,
    category: Category,
    type: Owner,
): AttributeValue => ({
    M: {
        kind: { S: kind },
        pet: { M: { category: { S: category }, owner: ownerRow(type) } },
        ...(kind === 'RETURN' ? { note: { S: 'scratched' } } : {}),
    },
})
const classes: Record<string, AttributeValue> = Object.fromEntries(
    (['ADOPT', 'RETURN'] as const).flatMap((kind) =>
        (['DOG', 'CAT'] as const).flatMap((category) =>
            (['PERSON', 'SHELTER'] as const).map((type) => [
                `${kind}_${category}_${type}`,
                rowOf(kind, category, type),
            ]),
        ),
    ),
)
/** Whether the run time keeps a value of each class. */
const keptBy = (slice: { readonly decode: (a: AttributeValue) => unknown }) =>
    Object.fromEntries(
        Object.entries(classes).map(([name, row]) => [
            name,
            !failed(slice.decode(row)),
        ]),
    )

const none = {
    ADOPT_DOG_PERSON: false,
    ADOPT_DOG_SHELTER: false,
    ADOPT_CAT_PERSON: false,
    ADOPT_CAT_SHELTER: false,
    RETURN_DOG_PERSON: false,
    RETURN_DOG_SHELTER: false,
    RETURN_CAT_PERSON: false,
    RETURN_CAT_SHELTER: false,
} as const
const all = {
    ADOPT_DOG_PERSON: true,
    ADOPT_DOG_SHELTER: true,
    ADOPT_CAT_PERSON: true,
    ADOPT_CAT_SHELTER: true,
    RETURN_DOG_PERSON: true,
    RETURN_DOG_SHELTER: true,
    RETURN_CAT_PERSON: true,
    RETURN_CAT_SHELTER: true,
} as const

describe('every summand fits a member of the union pattern in part', () => {
    // each summand of `pet` fits each member in part: a PERSON owner fits one, a SHELTER owner the other
    const both = object({
        pet: union([
            object({ owner: object({ type: string('PERSON') }) }),
            object({ owner: object({ type: string('SHELTER') }) }),
        ]),
    })
    const kept = extract(order, both)
    const rest = exclude(order, both)

    it('keeps every class that the pattern describes, and the type admits each of them', () => {
        expect(keptBy(kept)).toEqual(all)
        expectTypeOf<AdmittedBy<Decoded<typeof kept>, Classes>>().toEqualTypeOf<
            typeof all
        >()
    })

    it('rejects no class, and the type admits none', () => {
        expect(keptBy(rest)).toEqual(none)
        expectTypeOf<AdmittedBy<Decoded<typeof rest>, Classes>>().toEqualTypeOf<
            typeof none
        >()
    })
})

describe('one summand fits a member in part and another fits a member whole', () => {
    // DOG fits the first member in part (its PERSON owners), and CAT fits the second member whole
    const mixed = object({
        pet: union([
            object({ owner: object({ type: string('PERSON') }) }),
            object({ category: string('CAT') }),
        ]),
    })
    const keptClasses = {
        ADOPT_DOG_PERSON: true,
        ADOPT_DOG_SHELTER: false,
        ADOPT_CAT_PERSON: true,
        ADOPT_CAT_SHELTER: true,
        RETURN_DOG_PERSON: true,
        RETURN_DOG_SHELTER: false,
        RETURN_CAT_PERSON: true,
        RETURN_CAT_SHELTER: true,
    } as const
    const restClasses = {
        ADOPT_DOG_PERSON: false,
        ADOPT_DOG_SHELTER: true,
        ADOPT_CAT_PERSON: false,
        ADOPT_CAT_SHELTER: false,
        RETURN_DOG_PERSON: false,
        RETURN_DOG_SHELTER: true,
        RETURN_CAT_PERSON: false,
        RETURN_CAT_SHELTER: false,
    } as const
    const kept = extract(order, mixed)
    const rest = exclude(order, mixed)

    it('keeps the part of the summand that fits, and the type admits it', () => {
        expect(keptBy(kept)).toEqual(keptClasses)
        expectTypeOf<AdmittedBy<Decoded<typeof kept>, Classes>>().toEqualTypeOf<
            typeof keptClasses
        >()
    })

    it('rejects the part of the summand that does not fit, and the type admits it', () => {
        expect(keptBy(rest)).toEqual(restClasses)
        expectTypeOf<AdmittedBy<Decoded<typeof rest>, Classes>>().toEqualTypeOf<
            typeof restClasses
        >()
    })
})

describe('a pattern that is a union of objects splits the option', () => {
    // the control: the union is the pattern itself, so the run time and the type both split
    const eitherOwner = union([
        object({ pet: object({ owner: object({ type: string('PERSON') }) }) }),
        object({ pet: object({ owner: object({ type: string('SHELTER') }) }) }),
    ])
    const kept = extract(order, eitherOwner)
    const rest = exclude(order, eitherOwner)

    it('keeps every class, and the type admits each of them', () => {
        expect(keptBy(kept)).toEqual(all)
        expectTypeOf<AdmittedBy<Decoded<typeof kept>, Classes>>().toEqualTypeOf<
            typeof all
        >()
    })

    it('rejects no class, and the type admits none', () => {
        expect(keptBy(rest)).toEqual(none)
        expectTypeOf<AdmittedBy<Decoded<typeof rest>, Classes>>().toEqualTypeOf<
            typeof none
        >()
    })
})

describe('the partial fit sits two levels down', () => {
    // a PERSON owner holds a contact that is a union, so the pattern fits the owner in part
    const contact = union([
        object({ via: string('PHONE'), number: string }),
        object({ via: string('EMAIL'), address: string }),
    ])
    const owners = union([
        object({ type: string('PERSON'), name: string, contact }),
        object({ type: string('SHELTER'), id: string }),
    ])
    const deep = union([
        object({ category: string('DOG'), owner: owners }),
        object({ category: string('CAT'), owner: owners }),
    ])
    const adoption = union([
        object({ kind: string('ADOPT'), pet: deep }),
        object({ kind: string('RETURN'), pet: deep, note: string }),
    ])
    type Contact = 'PHONE' | 'EMAIL'
    type DeepOwner<O extends Owner | Contact> = O extends 'PHONE'
        ? {
              readonly type: 'PERSON'
              readonly name: string
              readonly contact: {
                  readonly via: 'PHONE'
                  readonly number: string
              }
          }
        : O extends 'EMAIL'
          ? {
                readonly type: 'PERSON'
                readonly name: string
                readonly contact: {
                    readonly via: 'EMAIL'
                    readonly address: string
                }
            }
          : { readonly type: 'SHELTER'; readonly id: string }
    type DeepValue<
        K extends Kind,
        C extends Category,
        O extends Owner | Contact,
    > = K extends 'RETURN'
        ? {
              readonly kind: K
              readonly pet: {
                  readonly category: C
                  readonly owner: DeepOwner<O>
              }
              readonly note: string
          }
        : {
              readonly kind: K
              readonly pet: {
                  readonly category: C
                  readonly owner: DeepOwner<O>
              }
          }
    type DeepClasses = {
        readonly ADOPT_DOG_PHONE: DeepValue<'ADOPT', 'DOG', 'PHONE'>
        readonly ADOPT_DOG_EMAIL: DeepValue<'ADOPT', 'DOG', 'EMAIL'>
        readonly ADOPT_DOG_SHELTER: DeepValue<'ADOPT', 'DOG', 'SHELTER'>
        readonly ADOPT_CAT_PHONE: DeepValue<'ADOPT', 'CAT', 'PHONE'>
        readonly ADOPT_CAT_EMAIL: DeepValue<'ADOPT', 'CAT', 'EMAIL'>
        readonly ADOPT_CAT_SHELTER: DeepValue<'ADOPT', 'CAT', 'SHELTER'>
        readonly RETURN_DOG_PHONE: DeepValue<'RETURN', 'DOG', 'PHONE'>
        readonly RETURN_DOG_EMAIL: DeepValue<'RETURN', 'DOG', 'EMAIL'>
        readonly RETURN_DOG_SHELTER: DeepValue<'RETURN', 'DOG', 'SHELTER'>
        readonly RETURN_CAT_PHONE: DeepValue<'RETURN', 'CAT', 'PHONE'>
        readonly RETURN_CAT_EMAIL: DeepValue<'RETURN', 'CAT', 'EMAIL'>
        readonly RETURN_CAT_SHELTER: DeepValue<'RETURN', 'CAT', 'SHELTER'>
    }
    const deepOwnerRow = (o: Owner | Contact): AttributeValue =>
        o === 'SHELTER'
            ? { M: { type: { S: 'SHELTER' }, id: { S: 'shelter-1' } } }
            : {
                  M: {
                      type: { S: 'PERSON' },
                      name: { S: 'ann' },
                      contact: {
                          M:
                              o === 'PHONE'
                                  ? {
                                        via: { S: 'PHONE' },
                                        number: { S: '555' },
                                    }
                                  : {
                                        via: { S: 'EMAIL' },
                                        address: { S: 'a@b' },
                                    },
                      },
                  },
              }
    const deepClasses: Record<string, AttributeValue> = Object.fromEntries(
        (['ADOPT', 'RETURN'] as const).flatMap((kind) =>
            (['DOG', 'CAT'] as const).flatMap((category) =>
                (['PHONE', 'EMAIL', 'SHELTER'] as const).map((o) => [
                    `${kind}_${category}_${o}`,
                    {
                        M: {
                            kind: { S: kind },
                            pet: {
                                M: {
                                    category: { S: category },
                                    owner: deepOwnerRow(o),
                                },
                            },
                            ...(kind === 'RETURN'
                                ? { note: { S: 'scratched' } }
                                : {}),
                        },
                    },
                ]),
            ),
        ),
    )
    const keptDeep = (slice: {
        readonly decode: (a: AttributeValue) => unknown
    }) =>
        Object.fromEntries(
            Object.entries(deepClasses).map(([name, row]) => [
                name,
                !failed(slice.decode(row)),
            ]),
        )
    const phoneOrCat = object({
        pet: union([
            object({
                owner: object({ contact: object({ via: string('PHONE') }) }),
            }),
            object({ category: string('CAT') }),
        ]),
    })
    const keptClasses = {
        ADOPT_DOG_PHONE: true,
        ADOPT_DOG_EMAIL: false,
        ADOPT_DOG_SHELTER: false,
        ADOPT_CAT_PHONE: true,
        ADOPT_CAT_EMAIL: true,
        ADOPT_CAT_SHELTER: true,
        RETURN_DOG_PHONE: true,
        RETURN_DOG_EMAIL: false,
        RETURN_DOG_SHELTER: false,
        RETURN_CAT_PHONE: true,
        RETURN_CAT_EMAIL: true,
        RETURN_CAT_SHELTER: true,
    } as const
    const kept = extract(adoption, phoneOrCat)

    it('keeps the contact part that fits, and the type admits it', () => {
        expect(keptDeep(kept)).toEqual(keptClasses)
        expectTypeOf<
            AdmittedBy<Decoded<typeof kept>, DeepClasses>
        >().toEqualTypeOf<typeof keptClasses>()
    })
})

describe('a dissection keeps its members whole', () => {
    it('refuses a pattern that covers a summand in part, and keeps no value that the type drops', () => {
        const byKind = discriminatedUnion('kind', [
            object({ kind: string('ADOPT'), pet: pets }),
            object({ kind: string('RETURN'), pet: pets, note: string }),
        ])
        const part = object({
            pet: union([
                object({ owner: object({ type: string('PERSON') }) }),
                object({
                    category: string('DOG'),
                    owner: object({ type: string('SHELTER') }),
                }),
            ]),
        })
        const slice = () => extract(byKind, part)
        expect(slice).toThrow(/keeps its members whole/)
    })

    it('keeps a member whole where the pattern covers each part of the member, though no pattern option covers the member', () => {
        const byKind = discriminatedUnion('kind', [
            object({ kind: string('ADOPT'), pet: pets }),
            object({ kind: string('RETURN'), pet: pets, note: string }),
        ])
        const cover = object({
            pet: union([
                object({ owner: object({ type: string('PERSON') }) }),
                object({ owner: object({ type: string('SHELTER') }) }),
            ]),
        })
        expect(extract(byKind, cover).def).toEqual(byKind.def)
    })
})
