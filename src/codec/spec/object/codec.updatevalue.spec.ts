/**
 * `keyUpdates` returns each refusal of a change as a value, and `unsafeKeyUpdates` throws it.
 *
 * A change that writes a decided attribute at another value, a change that touches a key and lacks a
 * component of the key, and a change that would rewrite a key of the table are failures of the
 * argument, so a caller that holds a change of the declared type reads a `CodecError` and never a
 * throw. The error has the kind `decided` or the kind `rewrite`. The type of a literal change refuses some of these calls, and
 * a change in a variable of type `Partial<Entity>` reaches the run time, so the failure is a value.
 * The twin throws the value that the method returns, so it throws a `CodecError`.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { CodecError, tableEntry } from '../../../Rotorise'
import { item as itemOf, object, string } from '../../codec'

type Pet = { petId: string; shelterId: string; nick: string }

const Pets = tableEntry<Pet>()(
    {
        PK: ['petId'],
        GSI1PK: ['shelterId'],
        GSI1SK: ['nick', 'shelterId'],
    },
    { key: { partition: 'PK' } },
)

type Decided = { TAG: 'PET'; id: string }
const Tagged = tableEntry<Decided>()(
    { PK: ['TAG', 'id'] },
    { codec: itemOf(object({ TAG: string('PET'), id: string })) },
)

// a change in a variable of the declared type, so no literal check of the type refuses it
const change = (given: Partial<Pet>): never => given as never

describe('keyUpdates returns the refusal of a change as a value', () => {
    it('returns the refusal of a change that would rewrite a key of the table, with the kind rewrite', () => {
        const refused = Pets.keyUpdates(change({ petId: 'p2' }))
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError) {
            expect(refused.kind).toBe('rewrite')
            expect(['key', 'separator', 'decided', 'rewrite']).toContain(
                refused.kind,
            )
            expect(refused.message).toContain("is the table's own key")
        }
    })

    it('returns the refusal of a change that touches a key and lacks a component of it', () => {
        const refused = Pets.keyUpdates(change({ nick: 'rex' }))
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError) {
            expect(refused.kind).toBe('rewrite')
            expect(refused.message).toContain('has to be rebuilt')
        }
    })

    it('returns the refusal of a decided attribute that the change writes at another value', () => {
        const refused = Tagged.keyUpdates({ TAG: 'OTHER' } as never)
        expect(refused).toBeInstanceOf(CodecError)
        if (refused instanceof CodecError) {
            expect(refused.kind).toBe('decided')
            expect(refused.message).toContain("'TAG' is decided by the codec")
        }
    })

    it('gives the patch where the change rebuilds each key that it touches', () => {
        expect(Pets.keyUpdates({ shelterId: 's2', nick: 'rex' })).toEqual({
            set: {
                GSI1PK: { S: 'SHELTERID#s2' },
                GSI1SK: { S: 'NICK#rex#SHELTERID#s2' },
            },
            remove: [],
        })
    })
})

describe('keyUpdates never throws for a change of the declared type', () => {
    it('returns a value for each partial entity of a list', () => {
        const given: Partial<Pet>[] = [
            {},
            { petId: 'p1' },
            { nick: 'rex' },
            { shelterId: 's1' },
            { nick: '', shelterId: '' },
            { nick: '#', shelterId: '#' },
        ]
        for (const one of given)
            expect(() => Pets.keyUpdates(change(one))).not.toThrow()
    })
})

describe('unsafeKeyUpdates throws what keyUpdates returns', () => {
    const thrownBy = (run: () => unknown): unknown => {
        try {
            run()
        } catch (thrown) {
            return thrown
        }
        return undefined
    }

    it('throws a CodecError with the kind and the reason of the value', () => {
        const calls: [() => unknown, () => unknown][] = [
            [
                () => Pets.keyUpdates(change({ petId: 'p2' })),
                () => Pets.unsafeKeyUpdates(change({ petId: 'p2' })),
            ],
            [
                () => Pets.keyUpdates(change({ nick: 'rex' })),
                () => Pets.unsafeKeyUpdates(change({ nick: 'rex' })),
            ],
            [
                () => Tagged.keyUpdates({ TAG: 'OTHER' } as never),
                () => Tagged.unsafeKeyUpdates({ TAG: 'OTHER' } as never),
            ],
        ]
        for (const [method, twin] of calls) {
            const returned = method()
            const thrown = thrownBy(twin)
            expect(returned).toBeInstanceOf(CodecError)
            expect(thrown).toBeInstanceOf(CodecError)
            if (
                returned instanceof CodecError &&
                thrown instanceof CodecError
            ) {
                expect(thrown.kind).toBe(returned.kind)
                expect(thrown.reason).toBe(returned.reason)
                expect(['key', 'separator', 'decided', 'rewrite']).toContain(
                    thrown.kind,
                )
            }
        }
    })

    it('gives the patch where keyUpdates gives the patch', () => {
        expect(Pets.unsafeKeyUpdates({ shelterId: 's2', nick: 'rex' })).toEqual(
            Pets.keyUpdates({ shelterId: 's2', nick: 'rex' }),
        )
    })

    it('has the type that the method had, and the method has that type or the error', () => {
        const patch = Pets.unsafeKeyUpdates({ shelterId: 's2', nick: 'rex' })
        expectTypeOf(
            Pets.keyUpdates({ shelterId: 's2', nick: 'rex' }),
        ).toEqualTypeOf<typeof patch | CodecError>()
        expectTypeOf(patch.remove).toEqualTypeOf<readonly never[]>()
    })
})
