/**
 * The keys of an entry follow the model of a derived key.
 *
 * The codec writes no key name, the components that the codec decides are no vertex of a key, a
 * default stands for an undefined value only, and each key value has one owner of its rule.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { RotoriseError, tableEntry } from '../../../Rotorise'
import { number, string, union } from '../../codec'

/** The entry, without the types that a cast would otherwise ask for. */
const loose = (schema: unknown, options?: unknown) =>
    (tableEntry as unknown as () => (...a: unknown[]) => any)()(schema, options)

describe('a codec writes no key name', () => {
    it('refuses a codec that declares a name that the schema computes as a key, at construction', () => {
        const build = () =>
            loose({ PK: ['petId'] }, { codec: { PK: string, petId: string } })
        expect(build).toThrow(RotoriseError)
        expect(build).toThrow(
            /'PK' is a key of the schema and a field of the codec/,
        )
    })

    it('refuses the same declaration at the type, on the key', () => {
        expect(() =>
            tableEntry<{ PK: string; petId: string }>()(
                // @ts-expect-error the codec declares PK, which the schema computes
                { PK: ['petId'] },
                { codec: { PK: string, petId: string } },
            ),
        ).toThrow(RotoriseError)
    })
})

describe('the codec decides a component, so no caller passes it', () => {
    type Pet = { TAG: 'PET'; petId: string; createdAt: string }
    const Pets = tableEntry<Pet>()(
        { PK: ['TAG', 'petId'], SK: ['TAG', 'createdAt'] },
        {
            codec: { TAG: string('PET'), petId: string, createdAt: string },
            key: { partition: 'PK', sort: 'SK' },
        },
    )

    it('builds the partition key from the attributes without the constant, as keyUpdates does', () => {
        expect(Pets.keyCondition({ petId: 'p1', createdAt: '2026' })).toEqual({
            partition: { name: 'PK', value: { S: 'TAG#PET#PETID#p1' } },
            sort: { name: 'SK', equals: { S: 'TAG#PET#CREATEDAT#2026' } },
        })
    })

    it('gives the prefix of the decided component where the attributes give no other part of the sort key', () => {
        expect(Pets.keyCondition({ petId: 'p1' }).sort).toEqual({
            name: 'SK',
            beginsWith: { S: 'TAG#PET#' },
        })
    })

    it('refuses a value other than the constant in keys and in keyCondition, as keyUpdates refuses it', () => {
        const other = { TAG: 'OTHER', petId: 'p1', createdAt: 'c' } as never
        expect(() => Pets.keys(other)).toThrow(
            /'TAG' is decided by the codec as 'PET'/,
        )
        expect(() => Pets.keyCondition(other)).toThrow(
            /'TAG' is decided by the codec as 'PET'/,
        )
        expect(() => Pets.keyUpdates(other)).toThrow(
            /'TAG' is decided by the codec as 'PET'/,
        )
        expect(Pets.keys({ TAG: 'PET', petId: 'p1', createdAt: 'c' })).toEqual({
            PK: { S: 'TAG#PET#PETID#p1' },
            SK: { S: 'TAG#PET#CREATEDAT#c' },
        })
    })

    it('reads the key of keys over the decided values, and names the component that is still absent', () => {
        expect(() => Pets.keys({ petId: 'p1' })).toThrow(/createdAt not found/)
        // the call above compiles: the type of keys asks for no constant
        expectTypeOf(Pets.keys({ petId: 'p1', createdAt: '2026' })).toBeObject()
    })
})

describe('a default stands for an undefined value only', () => {
    type Pet = { petId: string; nickname?: string | null }
    const Pets = tableEntry<Pet>()({
        PK: ['petId'],
        GSI1SK: [['nickname', (n: string | null) => n ?? 'NONE', 'ANON']],
    })

    it('gives the transform a null value, which the type of the transform admits', () => {
        expect(Pets.key('GSI1SK', { nickname: null })).toBe('NICKNAME#NONE')
    })

    it('gives the default where the value is undefined', () => {
        expect(Pets.key('GSI1SK', {})).toBe('NICKNAME#ANON')
    })
})

describe('a sort condition reads the parts that print', () => {
    const Pets = tableEntry<{
        petId: string
        shelterId: string
        status: string
        nickname?: string | null
        updatedAt: string
    }>()(
        {
            PK: ['petId'],
            GSI1PK: ['shelterId'],
            GSI1SK: ['status', 'updatedAt'],
            GSI2SK: [['nickname', (n: string | null) => n ?? 'NONE', 'ANON']],
        },
        {
            key: { partition: 'PK' },
            indexes: {
                GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' },
                GSI2: { partition: 'GSI1PK', sort: 'GSI2SK' },
            },
        },
    )

    it('gives no sort condition where the only given component is empty, because an empty value does not print', () => {
        const condition = Pets.keyCondition('GSI1', {
            shelterId: 's1',
            status: '',
        })
        expect('sort' in condition).toBe(false)
    })

    it('gives equals where the only given component has a transform and a null value, because the transform prints', () => {
        expect(
            Pets.keyCondition('GSI2', { shelterId: 's1', nickname: null }).sort,
        ).toEqual({ name: 'GSI2SK', equals: { S: 'NICKNAME#NONE' } })
    })
})

describe('a key value has one owner of its rule', () => {
    it('refuses a key value that is no S, N or B in an entry, as asKey refuses it', () => {
        const Pets = loose({ PK: ['id'], GSI1PK: 'flag' })
        expect(() => Pets.toEntry({ flag: true, id: 'a' })).toThrow(
            /cannot store as a key/,
        )
    })
})

describe('the label of a key attribute that stores two members', () => {
    it('names one field stored as more than one type, where one slot stores both', () => {
        const build = () =>
            loose({ PK: 'id' }, { codec: { id: union([string, number]) } })
        expect(build).toThrow(/stored as more than one type \(S and N\)/)
        expect(build).not.toThrow(/another variant/)
    })
})
