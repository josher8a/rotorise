/**
 * A refusal carries its kind as data.
 *
 * A reader that tells one refusal from another reads `kind`. The wording of a message is for a
 * person, and a reworded message must not change what a reader decides. Each source below states
 * the kind that its refusal carries.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, RotoriseError, tableEntry } from '../../../Rotorise'
import {
    at as atOf,
    held,
    item as itemOf,
    narrow,
    never,
    number,
    object,
    optional,
    refine,
    string,
    union,
} from '../../codec'
import { Disagreement } from '../../result'
import { checkEquivalent } from '../../testing'

describe('a refusal of `at`', () => {
    it('a path that no variant declares is vacant, because the walk finds no attribute', () => {
        const Pet = itemOf(object({ name: string }))
        try {
            // @ts-expect-error there is no such attribute
            atOf(Pet, ['owner'])
            expect.unreachable()
        } catch (thrown) {
            expect(thrown).toBeInstanceOf(CodecError)
            expect((thrown as CodecError).kind).toBe('vacant')
        }
    })

    it('a clause that separates every option is vacant, because no codec stands at the path', () => {
        const Pet = itemOf(
            object({
                pet: union([
                    object({ kind: string('dog'), name: string }),
                    object({ kind: string('cat'), name: string }),
                ]),
            }),
        )
        const none = atOf(
            narrow(
                atOf(Pet, ['pet']),
                // @ts-expect-error the clause separates every member
                object({ kind: string('bird') }),
            ),
            ['name'],
        )
        const written = none.encode('Rex')
        expect(written).toBeInstanceOf(CodecError)
        expect((written as CodecError).kind).toBe('vacant')
    })

    it('a path that some variants declare only is someVariants, because a write leaves another variant unreadable', () => {
        const empty = object({ kind: string('dog'), tag: optional(never) })
        const full = object({ kind: string('cat'), tag: string })
        // @ts-expect-error a variant does not declare `tag`, so the path refuses at the type as on use
        const tag = atOf(itemOf(object({ pet: union([empty, full]) })), [
            'pet',
            'tag',
        ])
        const read = tag.decode({ S: 'v' })
        expect(read).toBeInstanceOf(CodecError)
        expect((read as CodecError).kind).toBe('someVariants')
        const written = tag.encode('v')
        expect(written).toBeInstanceOf(CodecError)
        expect((written as CodecError).kind).toBe('someVariants')
    })

    it('a path that the variants declare differently is ambiguous, because no one codec encodes it', () => {
        const Pet = itemOf(
            object({
                pet: union([
                    object({ kind: string('dog'), age: number }),
                    object({ kind: string('cat'), age: string }),
                ]),
            }),
        )
        // @ts-expect-error the variants declare `age` differently, so the path refuses at the type as on use
        const age = atOf(Pet, ['pet', 'age'])
        const read = age.decode({ S: '3' })
        expect(read).toBeInstanceOf(CodecError)
        expect((read as CodecError).kind).toBe('ambiguous')
        const written = age.encode('3')
        expect(written).toBeInstanceOf(CodecError)
        expect((written as CodecError).kind).toBe('ambiguous')
    })

    it('a refusal of a value is refused, because no reader tells it from another', () => {
        const refusal = string.decode({ N: '1' })
        expect(refusal).toBeInstanceOf(CodecError)
        expect((refusal as CodecError).kind).toBe('refused')
    })
})

describe('a refusal of the key builder', () => {
    type Adoption = {
        adoptionId: string
        petId: string
        status: 'OPEN' | 'CLOSED'
        updatedAt: string
    }
    const Adoptions = tableEntry<Adoption>()(
        {
            PK: ['adoptionId'],
            SK: ['petId'],
            GSI1PK: ['status'],
            GSI1SK: ['status', 'updatedAt'],
        },
        {
            codec: {
                adoptionId: string,
                petId: string,
                status: string('OPEN', 'CLOSED'),
                updatedAt: string,
            },
            key: { partition: 'PK', sort: 'SK' },
        },
    )
    const kindOf = (run: () => unknown) => {
        try {
            run()
        } catch (thrown) {
            expect(thrown).toBeInstanceOf(RotoriseError)
            return (thrown as RotoriseError).kind
        }
        return expect.unreachable()
    }

    it('a segment that holds the separator is a separator refusal, because the key reads back as two', () => {
        const item = {
            adoptionId: 'a#b',
            petId: 'p1',
            status: 'OPEN',
            updatedAt: 'now',
        } as const
        expect(kindOf(() => Adoptions.key('PK', item))).toBe('separator')
    })

    it('a change to a table key is a rewrite refusal, because DynamoDB cannot update a key attribute', () => {
        const untyped = Adoptions.keyUpdates as (c: object) => unknown
        expect(kindOf(() => untyped({ adoptionId: 'other' }))).toBe('rewrite')
    })

    it('a change that leaves a component of a touched key out is a rewrite refusal, because the key cannot be rebuilt', () => {
        const untyped = Adoptions.keyUpdates as (c: object) => unknown
        expect(kindOf(() => untyped({ updatedAt: 'later' }))).toBe('rewrite')
    })

    it('a write of a decided attribute at another value is a decided refusal, because the codec admits one value', () => {
        type Litter = { litterId: string; species: 'DOG'; born: string }
        const Litters = tableEntry<Litter>()(
            { PK: ['litterId'], GSI1PK: ['species', 'born'] },
            {
                codec: {
                    litterId: string,
                    species: string('DOG'),
                    born: string,
                },
            },
        )
        const untyped = Litters.keyUpdates as (c: object) => unknown
        expect(kindOf(() => untyped({ species: 'CAT', born: 'x' }))).toBe(
            'decided',
        )
    })

    it('any other refusal is refused, because no reader tells it apart', () => {
        expect(
            kindOf(() => {
                throw new RotoriseError('a refusal of no kind')
            }),
        ).toBe('refused')
    })
})

describe('a failed property check', () => {
    const short = (name: string): name is string => name.length < 3
    const throughHeld = (
        encode: (value: string) => string,
        decode: (value: string) => string,
    ) => held(string, string, { encode, decode })
    const same = (value: string) => value

    it('two codecs that disagree on whether a value can be written are a disagreement, not a refusal of a value', () => {
        expect(() =>
            checkEquivalent(string, refine(string, short), { count: 50 }),
        ).toThrow(Disagreement)
    })

    it('two codecs that write one value differently are a disagreement, because the check compares the written value', () => {
        const upper = throughHeld((value) => value.toUpperCase(), same)
        expect(() => checkEquivalent(string, upper, { count: 50 })).toThrow(
            Disagreement,
        )
    })

    it('two codecs that disagree on whether a written value can be read are a disagreement', () => {
        const reads = throughHeld(same, (value) => {
            if (!short(value)) throw new Error('too long to read')
            return value
        })
        expect(() => checkEquivalent(string, reads, { count: 50 })).toThrow(
            Disagreement,
        )
    })

    it('two codecs that read one written value differently are a disagreement, because the check compares the read value', () => {
        const marked = throughHeld(same, (value) => `${value}!`)
        expect(() => checkEquivalent(string, marked, { count: 50 })).toThrow(
            Disagreement,
        )
    })
})
