import { attest } from '@ark/attest'
import { describe, it } from 'vitest'
import { never, nullable, object, opaque, string, union } from './codec/codec'
import { tableEntry } from './Rotorise'

describe('Rotorise Performance Baseline', () => {
    type User = {
        id: string
        orgId: string
        role: 'admin' | 'user' | 'guest'
        metadata: {
            lastLogin: number
            tags: string[]
        }
    }

    const userSchema = tableEntry<User>()({
        PK: [
            ['orgId', (id: string) => `ORG:${id}`],
            ['id', (id: string) => `USER:${id}`],
        ],
        SK: ['role'],
        GSI1PK: [['role', (role: string) => `ROLE:${role}`]],
    })

    it('measures instantiation count for tableEntry', () => {
        // Measure performance of the tableEntry definition
        attest.instantiations([16, 'instantiations'])
    })

    it('measures instantiation count for key generation', () => {
        userSchema.key('PK', { orgId: '123', id: '456' })
        attest.instantiations([16, 'instantiations'])
    })

    it('verifies type outputs with snapshots', () => {
        attest(
            userSchema.key('PK', { orgId: '123', id: '456' }),
        ).type.toString.snap('`ORGID#${string}#ID#${string}`')
        attest(userSchema.key('SK', { role: 'admin' })).type.toString.snap(
            '"ROLE#admin"',
        )
    })

    describe('Error Diagnostics', () => {
        it('reports error for invalid schema key', () => {
            const invalidSchema = tableEntry<User>()({
                // @ts-expect-error
                INVALID: 123,
            })
            attest(
                invalidSchema.infer.INVALID,
            ).type.toString.snap(`  | ErrorMessage<"Invalid schema definition">
  | undefined`)
        })

        it('reports error for invalid top-level key in .key()', () => {
            attest(() =>
                // @ts-expect-error
                userSchema.key('NON_EXISTENT', { id: '123' }),
            ).throws.snap('RotoriseError: Key NON_EXISTENT not found in schema')
        })

        it('reports error for invalid Spec type', () => {
            const invalidSchema = tableEntry<User>()({
                // @ts-expect-error
                BAD_SPEC: { invalid: 'logic' },
            })
            attest(
                invalidSchema.infer.BAD_SPEC,
            ).type.toString.snap(`  | ErrorMessage<"Invalid schema definition">
  | undefined`)
        })
    })
})

/**
 * **A union's type leaves compatibility to the declaration.**
 *
 * A union is the join of its options, and the type cannot see whether a pair is compatible: two
 * options that decode to one type can be two restrictions of one base, or a base and an adapter
 * that writes another attribute. So the type refuses no pair, and `union` refuses at the
 * declaration a pair that it cannot show compatible.
 */
describe('the union a caller declares at compile time', () => {
    it('types overlapping, nested and repeated options, because compatibility is decided at the declaration', () => {
        attest(union([string, string('A')]).def.kind).equals('union')
        attest(union([opaque, string]).def.kind).equals('union')
        attest(union([string, never]).def.kind).equals('union')
        attest(
            union([object({ a: string }), object({ a: string })]).def.kind,
        ).equals('union')
    })
})

describe('a path that the type does not see', () => {
    it('names the gap of the type, and not a member that the codec writes', () => {
        attest(() =>
            tableEntry<{ id: string; meta: { note: string } | null }>()(
                // @ts-expect-error the type does not see below nullable
                { PK: ['id'], GSI1SK: 'meta.note' },
                {
                    codec: {
                        id: string,
                        meta: nullable(object({ note: string })),
                    },
                },
            ),
        ).type.errors.snap(
            'Type \'"meta.note"\' is not assignable to type \'"meta.note" & NoPathMember<"GSI1SK", "meta.note">\'.Type \'string\' is not assignable to type \'NoPathMember<"GSI1SK", "meta.note">\'.',
        )
    })

    it('names the member rule for an object at a path of an entry with no codec, because no codec has a gap', () => {
        attest(() =>
            tableEntry<{ id: string; meta: { note: { text: string } } }>()({
                PK: ['id'],
                // @ts-expect-error an object is none of S, N and B
                GSI1SK: 'meta.note',
            }),
        ).type.errors.snap(
            'Type \'"meta.note"\' is not assignable to type \'"meta.note" & NoKeyMember<"GSI1SK", "meta.note">\'.Type \'string\' is not assignable to type \'NoKeyMember<"GSI1SK", "meta.note">\'.',
        )
    })
})
