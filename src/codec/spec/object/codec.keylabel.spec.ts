/**
 * **The tag of a key component is data of the schema.** A component is a name, or a record that holds
 * the name at `at`, a constant `tag`, a function at `value`, and a `default`. The tag is a constant,
 * so the number of segments and each label are known from the schema, and the type of a key states
 * the literal tag with no `as const`. A record with no tag prints the name, and `tag: false` prints no
 * label, so the component is one segment. A schema that holds a tag that cannot print as one segment,
 * an array in place of a record, or a property that the record does not have is refused where the
 * schema is read. The type refuses an array and a record with no name at `at`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'

type Pet = {
    petId: string
    shelterId: string
    name: string
    note?: string
    shelter: { code: string }
    kind: 'X' | 'Y'
}
const rex: Pet = {
    petId: 'p1',
    shelterId: 's1',
    name: 'rex',
    shelter: { code: 'c1' },
    kind: 'X',
}

const refusal = (run: () => unknown): RotoriseError => {
    try {
        run()
    } catch (thrown) {
        if (thrown instanceof RotoriseError) return thrown
        throw thrown
    }
    throw new Error('the schema was not refused')
}

describe('the label of a record is its tag, as a literal in the type and as text at run time', () => {
    it('prints the tag at a name, and the type states the literal with no `as const`', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'name', tag: 'T' }],
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<`T#${string}`>()
        expect(Pets.unsafeKey('SK', rex)).toBe('T#rex')
    })

    it('prints the tag at a name with a function, and the type states the literal', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'name', tag: 'T', value: (name: string) => name }],
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<`T#${string}`>()
        expect(Pets.unsafeKey('SK', rex)).toBe('T#rex')
    })

    it('prints the tag at a path in place of the last name, and the type states the literal', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'shelter.code', tag: 'AT' }],
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<`AT#${string}`>()
        expect(Pets.unsafeKey('SK', rex)).toBe('AT#c1')
    })

    it('prints the tag in an arm of a match, and the type states the literal of each arm', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: {
                discriminator: 'kind',
                spec: {
                    X: [{ at: 'name', tag: 'EX' }],
                    Y: [{ at: 'name', tag: 'WHY' }],
                },
            },
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<
            `EX#${string}` | `WHY#${string}`
        >()
        expect(Pets.unsafeKey('SK', rex)).toBe('EX#rex')
        expect(Pets.unsafeKey('SK', { ...rex, kind: 'Y' })).toBe('WHY#rex')
    })

    it('prints the name of the attribute where the record has no tag', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'name', value: (name: string) => name.toUpperCase() }],
        })
        expectTypeOf(
            Pets.unsafeKey('SK', rex),
        ).toEqualTypeOf<`NAME#${string}`>()
        expect(Pets.unsafeKey('SK', rex)).toBe('NAME#REX')
    })

    it('prints one segment where the tag is false, and the type counts one segment', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'name', tag: false, value: (name: string) => name }],
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<string>()
        expect(Pets.unsafeKey('SK', rex)).toBe('rex')
    })

    it('prints the default under the tag where the value is absent, and the value where it is present', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'note', tag: 'N', default: 'none' }],
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<`N#${string}`>()
        expect(Pets.unsafeKey('SK', rex)).toBe('N#none')
        expect(Pets.unsafeKey('SK', { ...rex, note: 'z' })).toBe('N#z')
    })

    it('reads the default through the function, where the value is absent', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [
                {
                    at: 'note',
                    tag: false,
                    value: (note: string) => note.trim(),
                    default: ' none ',
                },
            ],
        })
        expect(Pets.unsafeKey('SK', rex)).toBe('none')
        expect(Pets.unsafeKey('SK', { ...rex, note: ' z ' })).toBe('z')
    })

    it('prints an empty segment where the function gives null, after the tag', () => {
        const Pets = tableEntry<Pet>()({
            PK: ['petId'],
            SK: [{ at: 'name', tag: 'T', value: () => null }],
        })
        expectTypeOf(Pets.unsafeKey('SK', rex)).toEqualTypeOf<'T#'>()
        expect(Pets.unsafeKey('SK', rex)).toBe('T#')
    })
})

describe('a tag that cannot print as one segment is refused where the schema is read', () => {
    it('refuses a tag that holds the separator, and names the tag and the separator', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                SK: [{ at: 'name', tag: 'A#B' }],
            }),
        )
        expect(refused.kind).toBe('refused')
        expect(refused.message).toContain(
            "the tag of name holds the separator '#'",
        )
    })

    it('refuses a tag that holds the separator that the options give, and only that one', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()(
                { PK: ['petId'], SK: [{ at: 'name', tag: 'A-B' }] },
                { separator: '-' },
            ),
        )
        expect(refused.message).toContain("holds the separator '-'")
        expect(() =>
            tableEntry<Pet>()(
                { PK: ['petId'], SK: [{ at: 'name', tag: 'A#B' }] },
                { separator: '-' },
            ),
        ).not.toThrow()
    })

    it('refuses a tag in an arm of a match', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                SK: {
                    discriminator: 'kind',
                    spec: { X: [{ at: 'name', tag: 'A#B' }], Y: ['name'] },
                },
            }),
        )
        expect(refused.message).toContain('holds the separator')
    })

    it('refuses the empty text as a tag, and says that false is the form with no tag', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                SK: [{ at: 'name', tag: '' }],
            }),
        )
        expect(refused.message).toContain('a non-empty text, or false')
    })

    it('refuses a tag that is no text', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                SK: [{ at: 'name', tag: 5 as never }],
            }),
        )
        expect(refused.message).toContain('a non-empty text, or false')
    })
})

describe('a component is a name or a record', () => {
    it('refuses an array, and names the record form', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                // @ts-expect-error an array is no component: write a record
                SK: [['name', (name: string) => name]],
            }),
        )
        expect(refused.kind).toBe('refused')
        expect(refused.message).toContain('a component is a name or a record')
        expect(refused.message).toContain("{ at: 'name'")
    })

    it('refuses an array in an arm of a match', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                // @ts-expect-error an array is no component: write a record
                SK: {
                    discriminator: 'kind',
                    spec: {
                        X: [['name', { tag: 'T' }]],
                        Y: ['name'],
                    },
                },
            }),
        )
        expect(refused.message).toContain('a component is a name or a record')
    })

    it('refuses a property that the record does not have', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                SK: [{ at: 'name', tags: 'T' }],
            }),
        )
        expect(refused.message).toContain("and no 'tags'")
    })

    it('refuses a record with no attribute at `at`', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                // @ts-expect-error a record names its attribute at `at`
                SK: [{ tag: 'T' }],
            }),
        )
        expect(refused.message).toContain('at `at`')
    })

    it('refuses a value that is no function', () => {
        const refused = refusal(() =>
            tableEntry<Pet>()({
                PK: ['petId'],
                SK: [{ at: 'name', value: 'x' as never }],
            }),
        )
        expect(refused.message).toContain('is a function')
    })
})
