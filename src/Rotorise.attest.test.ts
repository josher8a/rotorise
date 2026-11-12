import { attest } from '@ark/attest'
import { describe, it } from 'vitest'
import {
    array,
    held,
    never,
    nullable,
    object,
    opaque,
    string,
    union,
} from './codec/codec'
import type { StandardSchemaV1 } from './codec/standard'
import { tableEntry } from './Rotorise'

/**
 * The pins of `attest.instantiations` measure the block of one `it` apart from the file: attest
 * type-checks the file with each `it` call removed, then adds the block at the top level of that
 * file, and reports the difference. A name that the block reads from the scope of `describe` is
 * unbound at the top level, so the block measures an error. The type and the entry that the blocks
 * read are declared at the top level for that reason.
 *
 * A pin fails where the count rises above the threshold of attest. Where the count falls, attest
 * prints a line and the pin passes, so a block that measures an error passes.
 */
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

describe('Rotorise Performance Baseline', () => {
    it('measures instantiation count for tableEntry', () => {
        // the block declares its own entity: an entry outside the block over the same type pays
        // for a part of the count, and the pin reads the rest only
        type Member = {
            id: string
            orgId: string
            role: 'admin' | 'user' | 'guest'
            metadata: {
                lastLogin: number
                tags: string[]
            }
        }
        tableEntry<Member>()({
            PK: [
                ['orgId', (id: string) => `ORG:${id}`],
                ['id', (id: string) => `USER:${id}`],
            ],
            SK: ['role'],
            GSI1PK: [['role', (role: string) => `ROLE:${role}`]],
        })
        attest.instantiations([2091, 'instantiations'])
    })

    it('measures instantiation count for key generation', () => {
        userSchema.key('PK', { orgId: '123', id: '456' })
        // 3751 -> 3823: the builder of the key type reads the case of each component (can be
        // absent, never absent, always absent). Each call pays the read, and a partial call also
        // derives the case from the value of the component
        attest.instantiations([3823, 'instantiations'])
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
            "Type '\"meta.note\"' is not assignable to type '\"meta.note\" & ErrorMessage<\"[tableEntry] 'GSI1SK' is built from 'meta.note', and the type gives no member for that path. Address the attribute itself, or a path that the type enters. The codec has no field there, or the type does not see below nullable, a ref, a union with a leaf option, or the open rest of the item\">'.Type 'string' is not assignable to type 'ErrorMessage<\"[tableEntry] 'GSI1SK' is built from 'meta.note', and the type gives no member for that path. Address the attribute itself, or a path that the type enters. The codec has no field there, or the type does not see below nullable, a ref, a union with a leaf option, or the open rest of the item\">'.",
        )
    })

    it('names the instruction first for a component that the codec cannot address, because the compiler cuts the print of a long type', () => {
        attest(() =>
            tableEntry<{ id: string; meta: { note: string } | string }>()(
                {
                    PK: ['id'],
                    // @ts-expect-error the type does not see below a union with a leaf option
                    GSI1SK: ['meta.note'],
                },
                {
                    codec: {
                        id: string,
                        meta: union([object({ note: string }), string]),
                    },
                },
            ),
        ).type.errors.snap(
            "Type '\"meta.note\"' is not assignable to type '\"meta.note\" & ErrorMessage<\"[tableEntry] 'meta.note' is a component, and the codec cannot address that path. Address the attribute itself, or a path that the type enters. The codec has no field there, or the type does not see below nullable, a ref, a union with a leaf option, or the open rest of the item\">'.Type 'string' is not assignable to type 'ErrorMessage<\"[tableEntry] 'meta.note' is a component, and the codec cannot address that path. Address the attribute itself, or a path that the type enters. The codec has no field there, or the type does not see below nullable, a ref, a union with a leaf option, or the open rest of the item\">'.",
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
            "Type '\"meta.note\"' is not assignable to type '\"meta.note\" & ErrorMessage<\"[tableEntry] 'GSI1SK' is built from 'meta.note', which is stored as none of S, N and B. A key attribute of DynamoDB is S, N or B\">'.Type 'string' is not assignable to type 'ErrorMessage<\"[tableEntry] 'GSI1SK' is built from 'meta.note', which is stored as none of S, N and B. A key attribute of DynamoDB is S, N or B\">'.",
        )
    })

    it('names the member rule for a list at a plain name, because a key attribute of DynamoDB is S, N or B', () => {
        attest(() =>
            tableEntry<{ id: string; tags: string[] }>()(
                {
                    PK: ['id'],
                    // @ts-expect-error a list is none of S, N and B
                    GSI1SK: 'tags',
                },
                { codec: { id: string, tags: array(string) } },
            ),
        ).type.errors.snap(
            "Type '\"tags\"' is not assignable to type '\"tags\" & ErrorMessage<\"[tableEntry] 'GSI1SK' is built from 'tags', which is stored as none of S, N and B. A key attribute of DynamoDB is S, N or B\">'.Type 'string' is not assignable to type 'ErrorMessage<\"[tableEntry] 'GSI1SK' is built from 'tags', which is stored as none of S, N and B. A key attribute of DynamoDB is S, N or B\">'.",
        )
    })
})

describe('a component whose value can be null', () => {
    it('names the transform that reads the null, because a default stands for an absent value only', () => {
        attest(() =>
            tableEntry<{ id: string; chip: { serial: string | null } }>()({
                PK: ['id'],
                // @ts-expect-error a component with no transform does not print a null
                SK: ['chip.serial'],
            }),
        ).type.errors.snap(
            "Type '\"chip.serial\"' is not assignable to type '\"chip.serial\" & ErrorMessage<\"'chip.serial' can be null: give a transform that reads the null\">'.Type 'string' is not assignable to type 'ErrorMessage<\"'chip.serial' can be null: give a transform that reads the null\">'.",
        )
    })
})

describe('an entity that is a union', () => {
    type Housed = { petId: string; species: 'CAT'; adopted: boolean }
    type Kennelled = { petId: string; species: 'DOG'; adopted: boolean }
    const flag: StandardSchemaV1<boolean> = {
        '~standard': {
            version: 1,
            vendor: 'probe',
            validate: (v) =>
                typeof v === 'boolean'
                    ? { value: v }
                    : { issues: [{ message: 'no' }] },
        },
    }
    const Adopted = held(string('Y', 'N'), flag, {
        encode: (b: boolean) => (b ? 'Y' : 'N'),
        decode: (s: string) => s === 'Y',
    })

    it('refuses a record of codecs at the option codec, because a record states the attributes of one variant', () => {
        attest(() =>
            tableEntry<Housed | Kennelled>()(
                { PK: ['petId'], SK: 'adopted' },
                {
                    // @ts-expect-error a record of codecs names the attributes of one variant
                    codec: {
                        petId: string,
                        species: string('CAT', 'DOG'),
                        adopted: Adopted,
                    },
                },
            ),
        ).type.errors.snap(
            'Type \'{ petId: StringCodec; species: AttributeCodec<"CAT" | "DOG", Attribute<"S">> & TermMark<["union", [LitT<"string", "CAT">, LitT<"string", "DOG">]]>; adopted: AttributeCodec<...> & ... 1 more ... & Free<...>; }\' is not assignable to type \'ErrorMessage<"[tableEntry] an entity that is a union takes a codec `union` built with a discriminator, because a record of codecs states the attributes of one variant"> & { ...; }\'.Property \'[errorMessage]\' is missing in type \'{ petId: StringCodec; species: AttributeCodec<"CAT" | "DOG", Attribute<"S">> & TermMark<["union", [LitT<"string", "CAT">, LitT<"string", "DOG">]]>; adopted: AttributeCodec<...> & ... 1 more ... & Free<...>; }\' but required in type \'ErrorMessage<"[tableEntry] an entity that is a union takes a codec `union` built with a discriminator, because a record of codecs states the attributes of one variant">\'.',
        )
    })

    it('refuses a key of a boolean attribute where the entry has no codec, because native stores no member for a boolean', () => {
        attest(() =>
            tableEntry<Housed | Kennelled>()({
                PK: ['petId'],
                // @ts-expect-error a boolean is none of S, N and B
                SK: 'adopted',
            }),
        ).type.errors.snap(
            "Type '\"adopted\"' is not assignable to type '\"adopted\" & ErrorMessage<\"[tableEntry] 'SK' is built from 'adopted', which is stored as none of S, N and B. A key attribute of DynamoDB is S, N or B\">'.Type 'string' is not assignable to type 'ErrorMessage<\"[tableEntry] 'SK' is built from 'adopted', which is stored as none of S, N and B. A key attribute of DynamoDB is S, N or B\">'.",
        )
    })
})
