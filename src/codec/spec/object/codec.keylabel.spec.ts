/**
 * The type of a key prints the label that the transform function gives.
 *
 * The run time prints the tag that the function returns, in front of the value. The type reads the
 * tag from the return type of the function. A return type that holds a literal tag gives the label.
 * A function with no annotation and no `as const` returns the tag as `string`, because the
 * constraint of the schema gives the return expression no contextual type, so the type states a
 * text with a `#` and no label.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'

type Pet = { petId: string; shelterId: string; name: string; note?: string }
const rex: Pet = { petId: 'p1', shelterId: 's1', name: 'rex' }

describe('the label of a component whose transform function gives the tag', () => {
    const Literal = tableEntry<Pet>()({
        PK: ['petId'],
        SK: [['name', (name: string) => ({ tag: 'T', value: name }) as const]],
    })
    const Declared = tableEntry<Pet>()({
        PK: ['petId'],
        SK: [
            [
                'name',
                (name: string): { tag: 'T'; value: string } => ({
                    tag: 'T',
                    value: name,
                }),
            ],
        ],
    })
    const Wide = tableEntry<Pet>()({
        PK: ['petId'],
        SK: [['name', (name: string) => ({ tag: 'T', value: name })]],
    })
    const Either = tableEntry<Pet>()({
        PK: ['petId'],
        SK: [
            [
                'name',
                (name: string) =>
                    ({ tag: name === 'rex' ? 'P' : 'N', value: name }) as const,
            ],
        ],
    })

    it('states the label where the function returns the tag with `as const`, and refuses a text with another label', () => {
        const key = () => Literal.unsafeKey('SK', rex)
        expectTypeOf(
            Literal.unsafeKey('SK', rex),
        ).toEqualTypeOf<`T#${string}`>()
        // @ts-expect-error the label is `T`
        const other: ReturnType<typeof key> = '~T#rex'
        expect(Literal.unsafeKey('SK', rex)).toBe('T#rex')
        expect(other).toBe('~T#rex')
    })

    it('states the label where the function declares a return type that holds the tag', () => {
        expectTypeOf(
            Declared.unsafeKey('SK', rex),
        ).toEqualTypeOf<`T#${string}`>()
        expect(Declared.unsafeKey('SK', rex)).toBe('T#rex')
    })

    it('states the text with no label where the function returns the tag as a string, as the run time prints the label', () => {
        const key = () => Wide.unsafeKey('SK', rex)
        expectTypeOf(
            Wide.unsafeKey('SK', rex),
        ).toEqualTypeOf<`${string}#${string}`>()
        const other: ReturnType<typeof key> = '~T#rex'
        expect(Wide.unsafeKey('SK', rex)).toBe('T#rex')
        expect(other).toBe('~T#rex')
    })

    it('states the union of the labels where the function returns one of two tags with `as const`', () => {
        expectTypeOf(Either.unsafeKey('SK', rex)).toEqualTypeOf<
            `N#${string}` | `P#${string}`
        >()
        expect(Either.unsafeKey('SK', rex)).toBe('P#rex')
        expect(Either.unsafeKey('SK', { ...rex, name: 'bea' })).toBe('N#bea')
    })
})
