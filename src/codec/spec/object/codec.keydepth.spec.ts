/**
 * A depth keeps that many components of a key, so it is a non-negative integer.
 *
 * A depth that is no non-negative integer keeps no whole number of components, and the key it
 * names does not exist. A depth of 0 keeps none, and the model prints the empty prefix. The type
 * accepts a literal non-negative integer, because the type of the key follows the count. The run
 * time refuses the rest, for a caller without the type. A depth above the count keeps the whole key.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import type { ErrorMessage } from '../../../utils'

type Pet = { shelterId: string; petId: string }

const Pets = tableEntry<Pet>()({ SK: ['shelterId', 'petId'] })

describe('a depth is a non-negative integer', () => {
    it('keeps that many components', () => {
        expect(
            Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 1 }),
        ).toBe('SHELTERID#s')
        expectTypeOf(
            Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 1 }),
        ).toEqualTypeOf<'SHELTERID#s'>()
    })

    it('keeps the whole key where the depth is above the count', () => {
        expect(
            Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 9 }),
        ).toBe('SHELTERID#s#PETID#p')
    })

    it('keeps no component at a depth of 0, and the key is the empty prefix, with or without the boundary', () => {
        const attributes = { shelterId: 's', petId: 'p' }
        expect(Pets.key('SK', attributes, { depth: 0 })).toBe('')
        expect(
            Pets.key('SK', attributes, { depth: 0, enforceBoundary: true }),
        ).toBe('')
        expectTypeOf(
            Pets.key('SK', attributes, { depth: 0, enforceBoundary: true }),
        ).toEqualTypeOf<''>()
        expectTypeOf(
            Pets.key('SK', attributes, { depth: 0 }),
        ).toEqualTypeOf<''>()
    })

    it.each([-1, 1.5, Number.NaN])(
        'refuses the depth %s at run time, and the error names the key',
        (depth) => {
            // a caller without the type: the cast through `unknown` stands for it, because the
            // generic signature is too deep to compare with this one
            const untyped = Pets.key as unknown as (
                name: string,
                attributes: object,
                config: object,
            ) => unknown
            expect(() =>
                untyped('SK', { shelterId: 's', petId: 'p' }, { depth }),
            ).toThrow(
                new RotoriseError('Key SK: depth is a non-negative integer'),
            )
        },
    )

    it('refuses in the type a depth that is a number, a negative and a fraction', () => {
        const depth: number = 1
        const refused = () => {
            // @ts-expect-error a number does not say how many components the key keeps
            void Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth })
            // @ts-expect-error a negative depth keeps no component
            void Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: -1 })
            // @ts-expect-error a fraction keeps no whole number of components
            void Pets.key('SK', { shelterId: 's', petId: 'p' }, { depth: 1.5 })
        }
        expect(typeof refused).toBe('function')
    })
})

/**
 * The type of `key` is a function of the three slots of the config. A slot that holds one literal, or
 * nothing, says which key the call builds and which components the call must give. A wide type, or
 * a union, says neither, so the type refuses the slot.
 */
describe('a slot of the config states one literal, or nothing', () => {
    const attributes = { shelterId: 's', petId: 'p' } as const
    const lacking: string = ''

    it('refuses a boolean enforceBoundary, because the two values build two keys', () => {
        const build = (flag: boolean) =>
            // @ts-expect-error a boolean does not say whether the key ends with the separator
            Pets.key('SK', attributes, { depth: 1, enforceBoundary: flag })
        expect(build(true)).toBe('SHELTERID#s#')
        expect(build(false)).toBe('SHELTERID#s')
        expectTypeOf(
            Pets.key('SK', attributes, { depth: 1, enforceBoundary: true }),
        ).toEqualTypeOf<'SHELTERID#s#'>()
        expectTypeOf(
            Pets.key('SK', attributes, { depth: 1, enforceBoundary: false }),
        ).toEqualTypeOf<'SHELTERID#s'>()
    })

    it('refuses a boolean allowPartial, because the two values build two keys', () => {
        const partial = { shelterId: 's', petId: lacking } as const
        const build = (flag: boolean) =>
            // @ts-expect-error a boolean does not say whether the key stops at an empty component
            Pets.key('SK', partial, { allowPartial: flag })
        expect(build(true)).toBe('SHELTERID#s')
        expect(() => build(false)).toThrow(/Attribute petId not found/)
        expectTypeOf(
            Pets.key('SK', partial, { allowPartial: true }),
        ).toEqualTypeOf<'SHELTERID#s' | `SHELTERID#s#PETID#${string}`>()
    })

    it('refuses a depth that is a number or undefined, because no depth builds the whole key', () => {
        const build = (depth?: number) =>
            // @ts-expect-error an optional depth does not say how many components the key keeps
            Pets.key('SK', { shelterId: 's' }, { depth })
        expect(build(1)).toBe('SHELTERID#s')
        expect(() => build()).toThrow(/Attribute petId not found/)
    })

    it('refuses an optional literal depth, because an absent depth keeps the whole key', () => {
        const config: { depth?: 1 } = {}
        // @ts-expect-error a depth that can be absent does not say how many components the key keeps
        const build = () => Pets.key('SK', { shelterId: 's' }, config)
        expect(build).toThrow(/Attribute petId not found/)
    })

    it('refuses two literal depths, because the boundary follows one depth', () => {
        const build = (depth: 1 | 2) =>
            // @ts-expect-error two depths do not say whether the key stops before the last component
            Pets.key('SK', attributes, { depth, enforceBoundary: true })
        expect(build(1)).toBe('SHELTERID#s#')
        expect(build(2)).toBe('SHELTERID#s#PETID#p')
    })

    it('states one reason for each refused depth, so the caller reads the cause', () => {
        // the type that a call of `key` asks of the slot `depth`
        type Asked<Config> = NonNullable<Config> extends { depth: infer Depth }
            ? Depth
            : never
        type Attributes = typeof attributes
        type Wide = Asked<
            Parameters<
                typeof Pets.key<'SK', { readonly depth: number }, Attributes>
            >[2]
        >
        type Negative = Asked<
            Parameters<
                typeof Pets.key<'SK', { readonly depth: -1 }, Attributes>
            >[2]
        >
        type Fraction = Asked<
            Parameters<
                typeof Pets.key<'SK', { readonly depth: 1.5 }, Attributes>
            >[2]
        >
        type TwoDepths = Asked<
            Parameters<
                typeof Pets.key<'SK', { readonly depth: 1 | 1.5 }, Attributes>
            >[2]
        >
        type NoLiteral =
            ErrorMessage<`${string}is one literal or absent${string}`>
        expectTypeOf<Wide>().toMatchTypeOf<NoLiteral>()
        expectTypeOf<Negative>().toMatchTypeOf<
            ErrorMessage<`${string}a negative depth keeps${string}`>
        >()
        expectTypeOf<Fraction>().toMatchTypeOf<
            ErrorMessage<`${string}this depth keeps${string}`>
        >()
        // two depths where one is a fraction owe one reason: two reasons at one slot leave `never`
        expectTypeOf<TwoDepths>().toMatchTypeOf<NoLiteral>()
        expectTypeOf<Wide>().not.toBeNever()
        expectTypeOf<Negative>().not.toBeNever()
        expectTypeOf<Fraction>().not.toBeNever()
        expectTypeOf<TwoDepths>().not.toBeNever()
    })

    it('accepts a depth of undefined alone, a config with no slot, and no config', () => {
        expect(Pets.key('SK', attributes, { depth: undefined })).toBe(
            'SHELTERID#s#PETID#p',
        )
        expect(Pets.key('SK', attributes, {})).toBe('SHELTERID#s#PETID#p')
        expect(Pets.key('SK', attributes)).toBe('SHELTERID#s#PETID#p')
        expectTypeOf(
            Pets.key('SK', attributes, { depth: undefined }),
        ).toEqualTypeOf<'SHELTERID#s#PETID#p'>()
    })
})
