/**
 * The type of an operation says what the run time does.
 *
 * Each test holds one operation at the type and at run time. A directive `@ts-expect-error` states
 * a refusal of the type, and the call below it states the refusal of the run time. A type that
 * accepts where the run time refuses leaves the directive unused, and the type check fails.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { z } from 'zod'
import type { ConstantAttributes } from '../../../Rotorise'
import { tableEntry } from '../../../Rotorise'
import type { B, M, N, S } from '../../attribute'
import { DynamoNumber } from '../../attribute'
import {
    at,
    binary,
    CodecError,
    constantOf,
    decimal,
    dynamoNumber,
    held,
    item,
    legacy,
    list,
    meet,
    narrow,
    number,
    object,
    refine,
    string,
    termOf,
    union,
} from '../../codec'
import { native } from '../../native'

/** A caller's adapter over a string: each call builds its own pair of functions. */
const adoptedOn = () =>
    held(string('2026-01-01'), z.date(), {
        encode: (day: Date) => day.toISOString().slice(0, 10) as '2026-01-01',
        decode: (text: string) => new Date(text),
    })
const stamp = () =>
    held(string, z.date(), {
        encode: (day: Date) => day.toISOString(),
        decode: (text: string) => new Date(text),
    })

describe('a path reaches one codec where two variants hold one adapter', () => {
    it('refuses two caller adapters of one type, because two closures are two codecs', () => {
        const Pets = union([
            object({ kind: string('DOG'), seenAt: stamp() }),
            object({ kind: string('CAT'), seenAt: stamp() }),
        ])
        // @ts-expect-error the two adapters hold two functions, so no one codec stands at the path
        const seenAt = at(Pets, ['seenAt'])
        expect(() => seenAt.unsafeEncode(new Date(0))).toThrow(CodecError)
    })

    it('resolves two calls of one library adapter, because a library adapter is one pair', () => {
        const Pets = union([
            object({ kind: string('DOG'), weight: decimal('1') }),
            object({ kind: string('CAT'), weight: decimal('1') }),
        ])
        const weight = at(Pets, ['weight'])
        expect(weight.unsafeEncode('1')).toEqual({ N: '1' })
    })
})

describe('a meet refuses at the type what it refuses at run time', () => {
    it('refuses a held part over a foreign schema that fits neither side', () => {
        const dates = stamp()
        // @ts-expect-error the caller view of the part is opaque, so the two parts overlap and no function decides
        expect(() => meet(dates, string)).toThrow(CodecError)
    })

    it('meets a union and an option of the union at that option, and drops each meet at never', () => {
        const either = union([
            object({ k: string('a') }),
            object({ k: string('b') }),
        ])
        const met = meet(either, object({ k: string('a') }))
        expect(termOf(met).kind).toBe('object')
        expect(Object.keys(met.spec)).toEqual(['k'])
    })
})

describe('a set of a refinement is refused at the type where the term reaches a legacy', () => {
    it('refuses refine over legacy, as construction refuses', () => {
        const widened = legacy({
            current: string,
            older: { decode: () => 'x' },
        })
        const isText = (value: string): value is string => value.length > 0
        // @ts-expect-error a read widening has no set in the model
        expect(() => refine(widened, isText).set()).toThrow(CodecError)
    })
})

describe('a constant is decided at the type where it is decided at run time', () => {
    it('decides a dynamoNumber literal and a binary literal', () => {
        const five = DynamoNumber.from('5') as unknown as DynamoNumber<'5'>
        const spec = {
            n: dynamoNumber(five),
            b: binary(new Uint8Array([1])),
            id: string,
        }
        expectTypeOf<ConstantAttributes<typeof spec>>().toEqualTypeOf<
            'n' | 'b'
        >()
        expect(constantOf(spec.n)).toEqual(five)
        expect(constantOf(spec.b)).toEqual(new Uint8Array([1]))
    })

    it('decides a caller adapter over a literal, so keyUpdates asks no component of it', () => {
        const Pets = tableEntry<{ adoptedOn: Date; petId: string }>()(
            { PK: ['adoptedOn', 'petId'] },
            { codec: item(object({ adoptedOn: adoptedOn(), petId: string })) },
        )
        const patch = Pets.keyUpdates({ petId: 'p1' })
        expect(Object.keys(patch.set)).toEqual(['PK'])
    })
})

describe('a narrow by a list pattern resolves at the type as at run time', () => {
    it('keeps the option whose list the clause does not separate', () => {
        const Pets = union([
            object({ k: list(string('a')), x: string }),
            object({ k: list(string('b')), x: number }),
        ])
        const kept = narrow(at(Pets, []), object({ k: list(string('a')) }))
        const x = at(kept, ['x'])
        expect(x.unsafeEncode('s')).toEqual({ S: 's' })
    })
})

describe('a numeral has one text at the type', () => {
    it('keeps an option whose number literal prints with an exponent, where the clause names the same digits', () => {
        const big = DynamoNumber.from(
            '1000000000000000000000',
        ) as unknown as DynamoNumber<'1000000000000000000000'>
        const Pets = union([
            object({ k: string('a'), n: number(1e21), x: string }),
            object({ k: string('b'), n: number(2), x: number }),
        ])
        const kept = narrow(at(Pets, []), object({ n: dynamoNumber(big) }))
        const x = at(kept, ['x'])
        expect(x.unsafeEncode('s')).toEqual({ S: 's' })
    })
})

describe('native.Encode follows the marshaller branch for branch', () => {
    it('writes a typed array, an ArrayBuffer and a DataView as B', () => {
        expectTypeOf<native.Encode<Int32Array>>().toEqualTypeOf<B>()
        expectTypeOf<native.Encode<ArrayBuffer>>().toEqualTypeOf<B>()
        expectTypeOf<native.Encode<DataView>>().toEqualTypeOf<B>()
        expect(native.encode(new Int32Array(1))).toHaveProperty('B')
        expect(native.encode(new DataView(new ArrayBuffer(1)))).toHaveProperty(
            'B',
        )
    })

    it('drops a function member of a map', () => {
        expectTypeOf<
            native.Encode<{ name: string; bark: () => void }>
        >().toEqualTypeOf<M<{ name: S }>>()
        expect(native.encode({ name: 'Rex', bark: () => 1 })).toEqual({
            M: { name: { S: 'Rex' } },
        })
    })

    it('writes a Map as the M of its values', () => {
        expectTypeOf<native.Encode<Map<string, number>>>().toEqualTypeOf<
            M<{ readonly [key: string]: N }>
        >()
        expect(native.encode(new Map([['age', 3]]))).toEqual({
            M: { age: { N: '3' } },
        })
    })

    it('refuses a set of two families', () => {
        expectTypeOf<native.Encode<Set<string | number>>>().toBeNever()
        expect(
            native.encode(new Set<string | number>(['a', 1])),
        ).toBeInstanceOf(CodecError)
    })
})
