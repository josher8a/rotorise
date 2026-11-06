/**
 * The type states what the run time does. Each test names a fact that the run time decides, and the
 * type has to agree: a refusal of the run time is a refusal of the type, and a type that decodes is
 * the type that the run time returns.
 *
 * A `@ts-expect-error` that becomes unused is the failure of a refusal that the type lost. An
 * `expectTypeOf` is the failure of a type that differs.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import type { Decoded } from '../../codec'
import {
    at,
    CodecError,
    decimal,
    discriminatedUnion,
    held,
    item,
    legacy,
    nullable,
    number,
    object,
    optional,
    scope,
    string,
} from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

/** A Standard Schema v1 written by hand: a foreign held side that admits a `Date`. */
const dateSchema: StandardSchemaV1<Date> = {
    '~standard': {
        version: 1,
        vendor: 'handwritten',
        validate: (value) =>
            value instanceof Date
                ? { value }
                : { issues: [{ message: 'not a Date' }] },
    },
}
const born = () =>
    held(string, dateSchema, {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
    })

describe('a read widening has no set, in the type of a scope entry as in the run time', () => {
    it('refuses `.set()` of an entry over a `legacy`', () => {
        const { Rate } = scope({
            Rate: legacy({ current: decimal, older: string }),
        })
        // @ts-expect-error a `legacy` widens a read, and a set has no such law in the model
        expect(() => Rate.set()).toThrow(CodecError)
    })
})

describe('nullable refuses a term whose null point no term decides, in the type as in the run time', () => {
    it('refuses a `legacy`', () => {
        const older = { decode: (value: unknown) => String(value) }
        // @ts-expect-error a function of the caller decides the point, and the type reads no function
        expect(() => nullable(legacy({ current: string, older }))).toThrow(
            CodecError,
        )
    })

    it('refuses a `held` over a foreign schema', () => {
        // @ts-expect-error the schema is the top at run time, so it may reach the point
        expect(() => nullable(born())).toThrow(CodecError)
    })

    it('admits a `held` whose held side and inner term both exclude null', () => {
        const trimmed = nullable(
            held(string, string, {
                encode: (text: string) => text.trim(),
                decode: (text: string) => text,
            }),
        )
        expectTypeOf(trimmed.unsafeDecode).returns.toEqualTypeOf<
            string | null
        >()
    })
})

describe('a held over a foreign schema decodes the output of the schema, wherever the type reads the term', () => {
    const Pet = object({ name: string, born: born() })

    it('decodes a `Date` at a path', () => {
        const atBorn = at(Pet, ['born'])
        expectTypeOf(atBorn.unsafeDecode).returns.toEqualTypeOf<Date>()
        expect(
            atBorn.unsafeDecode({ S: '2026-01-01T00:00:00.000Z' }),
        ).toBeInstanceOf(Date)
    })

    it('decodes a `Date` in an entry of a scope', () => {
        const entry = scope({ Pet }).Pet
        expectTypeOf<Decoded<typeof entry>['born']>().toEqualTypeOf<Date>()
    })
})

describe('a variant with a rest keeps the rest in the decoded type', () => {
    const Pets = discriminatedUnion('kind', [
        object({ kind: string('dog') }, [string, optional(string)]),
        object({ kind: string('cat'), lives: number }),
    ])

    it('admits an undeclared name that the run time writes', () => {
        const written = Pets.unsafeEncode({ kind: 'dog', nickname: 'Rex' })
        expect(written).toEqual({
            M: { kind: { S: 'dog' }, nickname: { S: 'Rex' } },
        })
        expectTypeOf<{ kind: 'dog'; nickname: string }>().toMatchTypeOf<
            Decoded<typeof Pets>
        >()
    })
})

describe('a decimal literal is the spelling that the store returns, in the type as in the run time', () => {
    it('refuses a spelling that the store would normalise', () => {
        // @ts-expect-error the store returns '1.5' for '1.50'
        expect(() => decimal('1.50')).toThrow(CodecError)
        // @ts-expect-error the store returns '7' for '007'
        expect(() => decimal('007')).toThrow(CodecError)
    })

    it('admits the stored spelling', () => {
        expectTypeOf(decimal('1.5').unsafeDecode).returns.toEqualTypeOf<'1.5'>()
    })
})

describe('the row that tableEntry writes is the row that the codec of the entry writes', () => {
    type Keys = { TAG: 'META'; id: string }
    type Meta = Keys & { [key: string]: string }
    const Attributes = item(
        object({ TAG: string('META'), id: string }, [string, optional(string)]),
    )
    const Entry = tableEntry<Meta, never, Keys>()(
        { PK: ['id'] },
        { codec: Attributes },
    )

    it('types an undeclared name as the rest and the declared fields, and not as any attribute', () => {
        const meta = { TAG: 'META', id: 'b', extra: 'kept' } as Meta
        const row = Entry.unsafeToItem(meta)
        const encoded = Attributes.unsafeEncode(meta)
        expectTypeOf(row.extra).toEqualTypeOf(encoded.extra)
    })
})
