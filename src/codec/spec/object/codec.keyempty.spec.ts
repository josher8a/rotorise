/**
 * A key has no empty text, whether the key is full or partial.
 *
 * DynamoDB stores no empty key, so a full key that prints the empty string addresses no item. A key
 * of one attribute has no part, so its key is full, and an empty value refuses on every route. A list
 * of components prints the name of each component, so a full key of a list is empty only where
 * a transform prints a value with no tag, and the value is empty. A partial
 * key is a call with `allowPartial`, or with a `depth` below the count of components, and the public
 * `key` returns it as a `begins_with` prefix. A partial key of no component has no text, so the run
 * time refuses it and the type of the call is `never`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, tableEntry } from '../../../Rotorise'

type Pet = { petId: string; shelterId: string; nick: string }

const Pets = tableEntry<Pet>()(
    {
        PK: ['petId'],
        SK: 'nick',
        GSI1PK: ['shelterId'],
        GSI1SK: 'nick',
        GSI2SK: [{ at: 'petId', value: (_id: string) => '' }],
        GSI3SK: [{ at: 'nick', tag: false, value: (text: string) => text }],
    },
    {
        key: { partition: 'PK', sort: 'SK' },
        indexes: {
            GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' },
            GSI2: { partition: 'GSI1PK', sort: 'GSI2SK' },
            GSI3: { partition: 'GSI1PK', sort: 'GSI3SK' },
        },
    },
)

const unnamed = { petId: 'p1', shelterId: 's1', nick: '' }

describe('a full key of one attribute refuses the empty string, on every route', () => {
    it('refuses in key, and names the key and the attribute', () => {
        {
            const refused = Pets.key('SK', unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(['key', 'separator', 'decided', 'rewrite']).toContain(
                    refused.kind,
                )
        }
        {
            const refused = Pets.key('SK', unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    "Key SK: the attribute 'nick' is empty",
                )
        }
    })

    it('refuses in key under allowPartial, because one attribute has no part', () => {
        {
            // @ts-expect-error the type gives a key of one attribute no config, and a caller with no type passes one
            const refused: unknown = Pets.key('SK', unnamed, {
                allowPartial: true,
            })
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    "the attribute 'nick' is empty",
                )
        }
    })

    it('refuses in keys and in toEntry', () => {
        {
            const refused = Pets.keys(['SK'], unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    "the attribute 'nick' is empty",
                )
        }
        {
            const refused = Pets.toEntry(unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    "the attribute 'nick' is empty",
                )
        }
    })

    it('refuses in keyUpdates, on a key that is not a key of the table', () => {
        const Indexed = tableEntry<Pet>()(
            { PK: ['petId'], GSI1SK: 'nick' },
            { key: { partition: 'PK' } },
        )
        {
            const refused = Indexed.keyUpdates({ nick: '' })
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    "cannot be rebuilt from this change: Key GSI1SK: the attribute 'nick' is empty",
                )
        }
    })

    it('refuses a condition on the sort key, and does not drop the condition', () => {
        {
            const refused = Pets.keyCondition('GSI1', unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    "the attribute 'nick' is empty",
                )
        }
    })
})

describe('a full key of a list of components prints the name of a tagged component', () => {
    it('prints the name of a component whose transform prints the empty string', () => {
        expect(Pets.unsafeKey('GSI2SK', unnamed)).toBe('PETID#')
    })
})

describe('a full key whose print is the empty text refuses, as a key of one attribute does', () => {
    it('refuses where one component prints a value with no tag and the value is empty', () => {
        {
            const refused = Pets.key('GSI3SK', unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(['key', 'separator', 'decided', 'rewrite']).toContain(
                    refused.kind,
                )
        }
        {
            const refused = Pets.key('GSI3SK', unnamed)
            expect(refused).toBeInstanceOf(CodecError)
            if (refused instanceof CodecError)
                expect(refused.message).toContain(
                    'Key GSI3SK: the print of the components is empty',
                )
        }
    })

    it('refuses the same print as a partial key of no component, because a key of no component has no text', () => {
        expect(() => Pets.unsafeKey('GSI3SK', unnamed, { depth: 0 })).toThrow(
            /no component/,
        )
    })

    it('refuses a closed key of no component where the first component has no tag, because nothing prints', () => {
        expect(() =>
            Pets.unsafeKey('GSI3SK', unnamed, {
                depth: 0,
                enforceBoundary: true,
            }),
        ).toThrow(/has no tag/)
    })
})

describe('a partial key of no component has no text, because the empty text has no representation', () => {
    it('refuses a depth of 0', () => {
        expect(() => Pets.unsafeKey('PK', unnamed, { depth: 0 })).toThrow(
            /no component/,
        )
    })

    it('refuses allowPartial where no part is present, and the type has no success value', () => {
        const call = () => Pets.unsafeKey('PK', {}, { allowPartial: true })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(/no component/)
        const absent = () =>
            Pets.unsafeKey('PK', { petId: undefined }, { allowPartial: true })
        expectTypeOf(absent).returns.toEqualTypeOf<never>()
        expect(absent).toThrow(/no component/)
    })

    it('prints the first tag and the separator for a closed key of no component', () => {
        const key = Pets.unsafeKey(
            'PK',
            {},
            {
                allowPartial: true,
                enforceBoundary: true,
            },
        )
        expectTypeOf(key).toEqualTypeOf<'PETID#'>()
        expect(key).toBe('PETID#')
    })

    it('is the prefix of the first part where only the first part is present', () => {
        const Two = tableEntry<Pet>()({ PK: ['petId', 'shelterId'] })
        const key = Two.unsafeKey('PK', { petId: 'p1' }, { allowPartial: true })
        expectTypeOf(key).toEqualTypeOf<'PETID#p1'>()
        expect(key).toBe('PETID#p1')
    })

    it('refuses a hole, where only the second part is present, because the print would drop it', () => {
        const Two = tableEntry<Pet>()({ PK: ['petId', 'shelterId'] })
        const call = () =>
            Two.unsafeKey('PK', { shelterId: 's1' }, { allowPartial: true })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(/would drop 'shelterId'/)
    })

    it('refuses a part of another type, as a full key does', () => {
        const key = () =>
            // @ts-expect-error petId is a string
            Pets.unsafeKey('PK', { petId: 5 }, { allowPartial: true })
        expect(key()).toBe('PETID#5')
    })

    it('is not empty where a part is present', () => {
        expect(Pets.unsafeKey('PK', unnamed, { allowPartial: true })).toBe(
            'PETID#p1',
        )
    })
})

describe('the type of a key counts the segments that a print holds, and not the text', () => {
    type Tagless = { petId: string; shelterId: string; nick: string }
    const hidden = (_nick: string): null => null
    const vip = (nick: string): 'VIP' | null => (nick === 'x' ? null : 'VIP')
    const blank = (_nick: string): '' => ''
    const tagless: Tagless = { petId: 'p1', shelterId: 's1', nick: 'rex' }
    const quiet: Tagless = { petId: 'p1', shelterId: 's1', nick: 'x' }

    it('keeps the separator of a first component that prints one empty segment', () => {
        const Hidden = tableEntry<Tagless>()({
            PK: [{ at: 'nick', tag: false, value: hidden }, 'petId'],
        })
        const key = Hidden.unsafeKey('PK', tagless)
        expectTypeOf(key).toEqualTypeOf<`#PETID#${string}`>()
        expect(key).toBe('#PETID#p1')
        const entry = Hidden.unsafeToEntry(tagless).PK
        expectTypeOf(entry).toEqualTypeOf<`#PETID#${string}`>()
        expect(entry).toBe('#PETID#p1')
    })

    it('keeps one separator for each leading empty segment', () => {
        const Hidden = tableEntry<Tagless>()({
            PK: [
                { at: 'nick', tag: false, value: hidden },
                { at: 'shelterId', tag: false, value: hidden },
                'petId',
            ],
        })
        const key = Hidden.unsafeKey('PK', tagless)
        expectTypeOf(key).toEqualTypeOf<`##PETID#${string}`>()
        expect(key).toBe('##PETID#p1')
    })

    it('holds both prints where the value is a literal or null, and the run time gives each', () => {
        const Vip = tableEntry<Tagless>()({
            PK: [{ at: 'nick', tag: false, value: vip }, 'petId'],
        })
        const key = Vip.unsafeKey('PK', tagless)
        expectTypeOf(key).toEqualTypeOf<
            `VIP#PETID#${string}` | `#PETID#${string}`
        >()
        expect(key).toBe('VIP#PETID#p1')
        expect(Vip.unsafeKey('PK', quiet)).toBe('#PETID#p1')
    })

    it('keeps the separator where the value is the empty text', () => {
        const Blank = tableEntry<Tagless>()({
            PK: [{ at: 'nick', tag: false, value: blank }, 'petId'],
        })
        const key = Blank.unsafeKey('PK', tagless)
        expectTypeOf(key).toEqualTypeOf<`#PETID#${string}`>()
        expect(key).toBe('#PETID#p1')
    })

    it('holds the print of an empty segment that is not first, as before', () => {
        const Hidden = tableEntry<Tagless>()({
            PK: ['petId', { at: 'nick', tag: false, value: hidden }],
        })
        const key = Hidden.unsafeKey('PK', tagless)
        expectTypeOf(key).toEqualTypeOf<`PETID#${string}#`>()
        expect(key).toBe('PETID#p1#')
    })
})

describe('the type of a full key has no success value that the run time refuses, because the key is never the empty text', () => {
    type Blank = {
        petId: string
        lit: ''
        kind: 'x' | ''
        nick: string
    }
    const blank = (_nick: string): '' => ''
    const same = (nick: string): string => nick
    const Keys = tableEntry<Blank>()({
        PK: ['petId'],
        ONE_LIT: 'lit',
        ONE_UNION: 'kind',
        LIST: ['petId', 'lit'],
        NOTAG: [{ at: 'lit', tag: false }],
        FN_EMPTY: [{ at: 'nick', tag: false, value: blank }],
        FN_WIDE: [{ at: 'nick', tag: false, value: same }],
        FN_TWO: [
            { at: 'nick', tag: false, value: blank },
            { at: 'nick', tag: false, value: blank },
        ],
        FN_TAG: [{ at: 'nick', value: blank }],
    })

    it('has no success value for a key of one attribute whose value is the empty literal', () => {
        const call = () => Keys.unsafeKey('ONE_LIT', { lit: '' })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(/the attribute 'lit' is empty/)
    })

    it('drops the empty text from a union that holds it, and keeps the other member', () => {
        const empty = () => Keys.unsafeKey('ONE_UNION', { kind: '' })
        expectTypeOf(empty).returns.toEqualTypeOf<never>()
        expect(empty).toThrow(/the attribute 'kind' is empty/)
        const key = Keys.unsafeKey('ONE_UNION', { kind: 'x' })
        expectTypeOf(key).toEqualTypeOf<'x'>()
        expect(key).toBe('x')
    })

    it('has no success value for a list that holds a plain component with the empty text', () => {
        const call = () => Keys.unsafeKey('LIST', { petId: 'p', lit: '' })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(CodecError)
    })

    it('has no success value for a record with no tag over the empty text', () => {
        const call = () => Keys.unsafeKey('NOTAG', { lit: '' })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(CodecError)
    })

    it('has no success value for a function that returns the empty text, where no tag follows', () => {
        const call = () => Keys.unsafeKey('FN_EMPTY', { nick: 'rex' })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(/the print of the components is empty/)
    })

    it('keeps the success value `#` where two records with no tag print the empty text, because the key is not empty', () => {
        const key = Keys.unsafeKey('FN_TWO', { nick: 'rex' })
        expectTypeOf(key).toEqualTypeOf<'#'>()
        expect(key).toBe('#')
    })

    it('keeps the label where a tag follows a function that returns the empty text', () => {
        const key = Keys.unsafeKey('FN_TAG', { nick: 'rex' })
        expectTypeOf(key).toEqualTypeOf<'NICK#'>()
        expect(key).toBe('NICK#')
    })

    it('has no success value for a key of one attribute at the arm of a match', () => {
        type Armed =
            | { id: string; type: 'a'; lit: '' }
            | { id: string; type: 'b'; nick: string }
        const Arms = tableEntry<Armed>()({
            PK: ['id'],
            ARM: { discriminator: 'type', spec: { a: 'lit', b: 'nick' } },
        })
        const call = () => Arms.unsafeKey('ARM', { type: 'a', lit: '' })
        expectTypeOf(call).returns.toEqualTypeOf<never>()
        expect(call).toThrow(/the attribute 'lit' is empty/)
    })

    it('keeps `string` where a function returns a wide text, because the run time decides', () => {
        const key = Keys.unsafeKey('FN_WIDE', { nick: 'rex' as string })
        expectTypeOf(key).toEqualTypeOf<string>()
        expect(key).toBe('rex')
        expect(() => Keys.unsafeKey('FN_WIDE', { nick: '' as string })).toThrow(
            /the print of the components is empty/,
        )
    })
})
