/**
 * **A tag at a path takes a default, as a transform does.** The default stands for a value that is
 * `undefined`, and for an object above the path that is absent. A present value prints under the tag,
 * so the key is the tag and the value, or the tag and the default. An empty text is a value that a
 * component with no transform does not print, and the default does not stand for it. The type states
 * the default as the value at the path, and refuses a default of another type on the element that
 * holds it. A tag at a top level name stays refused. A value that can be `null` needs a transform
 * that reads the `null`, because a default stands for an absent value only.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, tableEntry } from '../../../Rotorise'

type Pet = { petId: string; owner?: { id: string } }
type Housed = { petId: string; shelter: { code: string } | null }
type Leaf = { petId: string; shelter: { code: string | null } }

describe('a tag at a path takes a default', () => {
    const Pets = tableEntry<Pet>()({
        PK: ['petId'],
        SK: [['owner.id', { tag: 'ID' }, 'none']],
    })

    it('prints the value under the tag where the object is present', () => {
        const pet: Pet = { petId: 'p1', owner: { id: 'o1' } }
        expect(Pets.unsafeKey('SK', pet)).toBe('ID#o1')
        expect(Pets.unsafeToEntry(pet).SK).toBe('ID#o1')
    })

    it('prints the default under the tag where the object above the path is absent', () => {
        const pet: Pet = { petId: 'p1' }
        expect(Pets.unsafeKey('SK', pet)).toBe('ID#none')
        expect(Pets.unsafeToEntry(pet).SK).toBe('ID#none')
        expect(Pets.unsafeKey('SK', pet, { allowPartial: true })).toBe(
            'ID#none',
        )
    })

    it('states the key as the tag and the default where the object is absent, and as the tag and the value where it may be present', () => {
        const absent = Pets.unsafeKey('SK', {})
        expectTypeOf(absent).toEqualTypeOf<'ID#none'>()
        const present = Pets.unsafeKey('SK', { owner: { id: 'o1' } })
        expectTypeOf(present).toEqualTypeOf<'ID#none' | 'ID#o1'>()
        expectTypeOf(
            Pets.unsafeKey('SK', {}, { allowPartial: true }),
        ).toEqualTypeOf<'ID#none'>()
        const held: Pet = { petId: 'p1' }
        const either = Pets.unsafeKey('SK', held)
        expectTypeOf(either).toEqualTypeOf<`ID#${string}`>()
        expectTypeOf(Pets.key('SK', held)).toEqualTypeOf<
            typeof either | CodecError
        >()
    })

    it('does not stand for an empty text: the value is present and prints nothing', () => {
        const refused = Pets.key('SK', { owner: { id: '' } })
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError)
            expect(refused.message).toMatch(/Attribute owner\.id not found/)
    })

    it('refuses a default of another type on the element that holds it', () => {
        tableEntry<Pet>()({
            PK: ['petId'],
            // @ts-expect-error the value at `owner.id` is a string, so the default is a string
            SK: [['owner.id', { tag: 'ID' }, 5]],
        })
    })
})

describe('a tag with a default meets the rules of a component with no transform', () => {
    it('stands for the value where the object above the path is null, because the path reads nothing there', () => {
        const Houses = tableEntry<Housed>()({
            PK: ['petId'],
            SK: [['shelter.code', { tag: 'AT' }, 'x']],
        })
        expect(Houses.unsafeKey('SK', { shelter: null })).toBe('AT#x')
        expect(Houses.unsafeKey('SK', { shelter: { code: 'c1' } })).toBe(
            'AT#c1',
        )
    })

    it('refuses a value that can be null, because a default stands for an absent value only', () => {
        const Leaves = tableEntry<Leaf>()({
            PK: ['petId'],
            // @ts-expect-error the value can be null, and a default does not stand for a null
            SK: [['shelter.code', { tag: 'AT' }, 'x']],
        })
        const refused = Leaves.key('SK', { shelter: { code: null } })
        expect(refused).toBeInstanceOf(CodecError)
    })

    it('stays refused at a top level name, where the options object is for a path only', () => {
        tableEntry<{ petId: string; note?: string }>()({
            PK: ['petId'],
            // @ts-expect-error a tag is for a path, and a top level name takes a transform
            SK: [['note', { tag: 'DOSE' }, 'x']],
        })
    })
})
