/**
 * `opaque.Encode` against `encodeUnknown`, branch for branch.
 *
 * The type is only worth having if it says what the function does, so each case asserts both: the
 * type with `attest`, the runtime with an encode. A refusal is checked the same way — the type
 * resolves to an `ErrorMessage` exactly where the function returns a `CodecError`.
 *
 * This is the pair `native.ItemEncode` is for the AWS SDK's marshaller, and the two are not the same
 * function: this one holds a number as a `DynamoNumber` and refuses a JS number, refuses `bigint`,
 * refuses a `Map`, and refuses a class instance. A team whose own marshaller resembles `opaque`
 * diffs against this.
 */
import { attest } from '@ark/attest'
import { describe, expect, it } from 'vitest'
import type { ErrorMessage } from '../../../utils'
import type {
    AttributeValue,
    B,
    BOOL,
    BS,
    L,
    M,
    N,
    NS,
    NULL,
    S,
    SS,
} from '../../attribute'
import { DynamoNumber } from '../../attribute'
import type { AttributeCodec } from '../../codec'
import { CodecError, failed, opaque, orThrow } from '../../codec'
import type { native } from '../../native'

/**
 * That it refuses, rather than the words it refuses with.
 *
 * The reason text is documentation and will be reworded; being a refusal at all is the contract, and
 * the runtime half below checks the wording where it matters.
 */
type Refuses<T> = [T] extends [ErrorMessage<string>] ? true : false

const wrote = (value: unknown) => opaque('lossy').encode(value)
const refused = (value: unknown, codec: AttributeCodec<unknown> = opaque) => {
    const out = codec.encode(value)
    return failed(out) ? out.reason : undefined
}

describe('what opaque writes, as a type and as a function', () => {
    it('on the scalars it carries', () => {
        attest<[opaque.Encode<null>], [NULL]>()
        attest<[opaque.Encode<string>], [S]>()
        attest<[opaque.Encode<boolean>], [BOOL]>()
        attest<[opaque.Encode<Uint8Array>], [B]>()

        expect(wrote(null)).toEqual({ NULL: true })
        expect(wrote('a')).toEqual({ S: 'a' })
        expect(wrote(true)).toEqual({ BOOL: true })
        expect(wrote(Uint8Array.from([1]))).toEqual({ B: Uint8Array.from([1]) })
    })

    it('on a DynamoNumber, which the canonical codec holds exactly', () => {
        attest<[opaque.Encode<DynamoNumber>], [N]>()
        expect(opaque.encode(orThrow(DynamoNumber.from('1.50')))).toEqual({
            N: '1.5',
        })
    })

    it('on a JS number, only once a policy says what to do with N', () => {
        attest<[opaque.Encode<number, 'lossy'>], [N]>()
        expect(wrote(1.5)).toEqual({ N: '1.5' })

        // the canonical codec refuses a float, and names the exact carrier and the policy
        attest<[Refuses<opaque.Encode<number>>], [true]>()
        expect(refused(1.5)).toMatch(/`DynamoNumber`.*opaque\('lossy'\)/)
        // and the refusing policy refuses it as before it was a `held`
        attest<[Refuses<opaque.Encode<number, 'refuse'>>], [true]>()
        expect(refused(1.5, opaque('refuse'))).toMatch(
            /a number cannot be stored/,
        )
    })

    it('on the sets it carries, and the one it does not', () => {
        attest<[opaque.Encode<ReadonlySet<string>>], [SS]>()
        attest<[opaque.Encode<ReadonlySet<Uint8Array>>], [BS]>()
        expect(wrote(new Set(['b', 'a']))).toEqual({ SS: ['a', 'b'] })

        // the canonical codec writes a set of `DynamoNumber`s as the `NS` it reads back
        attest<[opaque.Encode<ReadonlySet<DynamoNumber>>], [NS]>()
        expect(
            opaque.encode(
                new Set([
                    orThrow(DynamoNumber.from('2')),
                    orThrow(DynamoNumber.from('1')),
                ]),
            ),
        ).toEqual({ NS: ['1', '2'] })
        // a set of JS numbers has no member, and the policies write no `NS` at all
        attest<[Refuses<opaque.Encode<ReadonlySet<number>>>], [true]>()
        attest<[Refuses<opaque.Encode<ReadonlySet<number>, 'lossy'>>], [true]>()
        expect(refused(new Set([1, 2]))).toMatch(/each holds one kind/)
        expect(refused(new Set([1, 2]), opaque('lossy'))).toMatch(
            /a set of numbers cannot be stored/,
        )
    })

    it('on a bigint and a Map, which decode back as something else', () => {
        attest<[Refuses<opaque.Encode<bigint>>], [true]>()
        expect(refused(1n)).toMatch(/a bigint cannot be stored/)
        expect(refused(new Map([['a', 1]]))).toMatch(/a Map cannot be stored/)
    })

    it('on a list, and on a list of something refused', () => {
        attest<[opaque.Encode<readonly string[]>], [L<S>]>()
        expect(wrote(['a'])).toEqual({ L: [{ S: 'a' }] })

        // the refusal is the answer, rather than something buried inside an `L`
        attest<
            [opaque.Encode<readonly bigint[]>],
            [
                ErrorMessage<'[opaque] a bigint writes `N` and reads back as a `DynamoNumber`, so `1n` would not come back as `1n`. Pass `DynamoNumber.from(value.toString())`'>,
            ]
        >()
        attest<
            [opaque.Encode<readonly bigint[], 'lossy'>],
            [
                ErrorMessage<'[opaque] a bigint shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`'>,
            ]
        >()
        expect(refused([1n])).toMatch(/a bigint cannot be stored/)
        expect(refused([1n], opaque('lossy'))).toMatch(/come back as `1`/)
    })

    it('on a plain object, nested', () => {
        type Row = { id: string; note?: string; inner: { at: string } }
        attest<
            [opaque.ItemEncode<Row>],
            [{ id: S; inner: M<{ at: S }>; note?: S }]
        >()
        attest<
            [opaque.Encode<Row>],
            [M<{ id: S; inner: M<{ at: S }>; note?: S }>]
        >()

        expect(wrote({ id: 'i', inner: { at: 'now' } })).toEqual({
            M: { id: { S: 'i' }, inner: { M: { at: { S: 'now' } } } },
        })
    })

    it('carries a refused attribute out of the object containing it', () => {
        attest<[Refuses<opaque.Encode<{ id: string; big: bigint }>>], [true]>()
        expect(refused({ id: 'i', big: 1n })).toMatch(/a bigint cannot be/)
    })

    /**
     * The one place the type is more permissive than the function, said out loud.
     *
     * A class instance is refused at runtime by reading the prototype, which no type can do. `Date`
     * is named because the runtime's own message names it, but an arbitrary instance is described as
     * a map where `encode` refuses it.
     */
    it('refuses a Date in both, and an arbitrary instance only at runtime', () => {
        attest<[Refuses<opaque.Encode<Date>>], [true]>()
        expect(refused(new Date(0))).toMatch(/cannot be stored/)

        class Thing {
            constructor(readonly id: string) {}
        }
        // described as a map, because the type cannot see the prototype
        attest<[opaque.Encode<Thing>], [M<{ id: S }>]>()
        // ...and refused all the same when it runs
        expect(refused(new Thing('t'))).toMatch(/an instance of Thing/)
    })
})

/**
 * One entry point, its only parameter optional — the shape {@link native} takes.
 *
 * `opaque` is the canonical codec, and a call chooses a numeric policy. The policy is the one knob
 * it has, so unlike `native` it is *fully* reflected in the type: `Encode<DynamoNumber>` is `N`,
 * `Encode<number>` is a refusal, and `Encode<number, 'lossy'>` is `N`.
 */
describe('opaque is one codec and one optional policy', () => {
    it('is the canonical codec without being called, which refuses a float', () => {
        expect(failed(opaque.encode(1))).toBe(true)
        attest<[Refuses<opaque.Encode<number>>], [true]>()
        attest<[opaque.Decode<N>], [DynamoNumber]>()
    })

    it('and calling it with no argument means the same thing', () => {
        expect(failed(opaque().encode(1))).toBe(true)
        expect(opaque().decode({ N: '1.50' })).toEqual(
            orThrow(DynamoNumber.from('1.5')),
        )
    })

    it('takes the other policy as an argument', () => {
        expect(opaque('lossy').encode(1.5)).toEqual({ N: '1.5' })
        attest<[opaque.Encode<number, 'lossy'>], [N]>()
    })

    /** The policy type travelled in with it, so `opaque` is the only name to import. */
    it('names its own policy', () => {
        const policy: opaque.Numbers = 'lossy'
        expect(opaque(policy).encode(1.5)).toEqual({ N: '1.5' })
    })
})

/**
 * What opaque reads back, as a type and as a function — the other direction.
 *
 * Each case asserts both, because the value this type has is that it says what `decodeUnknown` does,
 * and `decodeUnknown` is not the SDK's function. The three places they differ are asserted against
 * {@link native.Decode} directly, so the divergence is recorded rather than described.
 */
describe('what opaque reads back, as a type and as a function', () => {
    const read = (
        attribute: AttributeValue,
        numbers: opaque.Numbers = 'refuse',
    ) => {
        const out = opaque(numbers).decode(attribute)
        return failed(out) ? 'refused' : out
    }

    it('on the scalars', () => {
        attest<[opaque.Decode<NULL>], [null]>()
        attest<[opaque.Decode<S>], [string]>()
        attest<[opaque.Decode<BOOL>], [boolean]>()
        attest<[opaque.Decode<B>], [Uint8Array]>()

        expect(read({ NULL: true })).toBe(null)
        expect(read({ S: 'a' })).toBe('a')
        expect(read({ BOOL: true })).toBe(true)
        expect(read({ B: Uint8Array.from([1]) })).toEqual(Uint8Array.from([1]))
    })

    it('on an N, which is a DynamoNumber, a float under lossy, and a refusal under refuse', () => {
        attest<[opaque.Decode<N>], [DynamoNumber]>()
        attest<[Refuses<opaque.Decode<N, 'refuse'>>], [true]>()
        attest<[opaque.Decode<N, 'lossy'>], [number]>()

        expect(opaque.decode({ N: '1.5' })).toEqual(
            orThrow(DynamoNumber.from('1.5')),
        )
        expect(read({ N: '1.5' })).toBe('refused')
        expect(read({ N: '1.5' }, 'lossy')).toBe(1.5)
    })

    /** Every native set comes back as a `Set`, which is not what `.set()` decodes to. */
    it('on the three native sets', () => {
        attest<[opaque.Decode<SS>], [Set<string>]>()
        attest<[opaque.Decode<BS>], [Set<Uint8Array>]>()

        expect(read({ SS: ['a', 'b'] })).toEqual(new Set(['a', 'b']))
    })

    it('on a list and a map, nested', () => {
        attest<[opaque.Decode<L<S>>], [string[]]>()
        attest<
            [opaque.ItemDecode<{ id: S; inner: M<{ at: S }> }>],
            [{ id: string; inner: { at: string } }]
        >()

        expect(read({ L: [{ S: 'a' }] })).toEqual(['a'])
        expect(read({ M: { id: { S: 'i' } } })).toEqual({ id: 'i' })
    })

    it('carries a refused member out of the collection holding it', () => {
        attest<[Refuses<opaque.Decode<L<N>, 'refuse'>>], [true]>()
        attest<[Refuses<opaque.Decode<M<{ big: N }>, 'refuse'>>], [true]>()

        expect(read({ L: [{ N: '1' }] })).toBe('refused')
        expect(read({ M: { big: { N: '1' } } })).toBe('refused')
    })

    it('keeps an optional attribute optional', () => {
        attest<
            [opaque.ItemDecode<{ id: S; note?: S }>],
            [{ id: string; note?: string }]
        >()
    })

    /**
     * The places this differs from the SDK's reading, asserted rather than described.
     *
     * `N` and `NS` are the ones that matter: their members are decimal strings, and nothing
     * without a schema can say which of them a JS number holds faithfully. The SDK guesses. The
     * canonical codec reads the exact `DynamoNumber`, and the refusing policy refuses.
     */
    it('differs from native.Decode where the two disagree', () => {
        attest<[native.Decode<NS>], [Set<number | bigint>]>()
        attest<[opaque.Decode<NS>], [Set<DynamoNumber>]>()
        attest<[Refuses<opaque.Decode<NS, 'refuse'>>], [true]>()

        attest<[native.Decode<N>], [number | bigint]>()
        attest<[opaque.Decode<N>], [DynamoNumber]>()
        attest<[Refuses<opaque.Decode<N, 'refuse'>>], [true]>()

        // and the runtime agrees: a stored NS is exact, or refused under a policy, never guessed
        expect(opaque.decode({ NS: ['1', '2'] })).toEqual(
            new Set([
                orThrow(DynamoNumber.from('1')),
                orThrow(DynamoNumber.from('2')),
            ]),
        )
        expect(read({ NS: ['1', '2'] })).toBe('refused')
    })
})

describe('every N it writes is a numeral', () => {
    /**
     * `ran(e) ⊆ 𝔸`, the write half of C1's embedding obligation.
     *
     * §1's `Carries('N')` is `Numerals` — 38 significant digits, magnitude `1e-130 … 9.9…e125` —
     * and `Number.isFinite`, which is what this checked, is not that test. `5e-324` is a finite
     * double outside the range and is the specification's own example of the bound going
     * unchecked; `opaque('lossy')` wrote it, along with `1e200` and `1e-200`.
     *
     * `number` has gated on this since the numeral domain was tightened, and `literal` since its
     * `ℓ ⊆ D` premise. `opaque` is the third term that writes an `N` from a JS number, and the
     * audit that found it is the one C1 now states: four members carry a refinement, and every
     * term that writes one has to check it.
     */
    it('refuses a magnitude outside what an N holds', () => {
        const lossy = opaque('lossy')
        for (const v of [5e-324, 1e200, 1e-200, 1e126]) {
            expect(() => lossy.unsafeEncode(v)).toThrow(
                /magnitude 1e-130 to 9.9e125/,
            )
        }
    })

    it('keeps the clearer message for the ones that are not numbers at all', () => {
        const lossy = opaque('lossy')
        expect(() => lossy.unsafeEncode(NaN)).toThrow(/no number for NaN/)
        expect(() => lossy.unsafeEncode(Infinity)).toThrow(
            /no number for Infinity/,
        )
    })

    it('applies the gate everywhere a number can be nested', () => {
        const lossy = opaque('lossy')
        expect(() => lossy.unsafeEncode([5e-324])).toThrow(/magnitude/)
        expect(() => lossy.unsafeEncode({ a: 5e-324 })).toThrow(/magnitude/)
    })

    /**
     * A set of numbers never reaches the gate, because `opaque` has no `NS` write path — and
     * now has no `NS` read either, which is the fix rather than the defect.
     *
     * It used to read `NS` as `Set<string>`, so re-encoding what it read produced `SS`: an
     * `NS` attribute silently becoming an `SS` on a read-modify-write. **(MP)**, and the only
     * law watching, since `opaque`'s `μ` is `⊤`. A codec is a pair, and a member it cannot
     * write is a member it cannot read — `Calculus.Alg.Lawful.no_read_without_write`.
     */
    it('refuses a set of numbers on both sides, which is what a pair means', () => {
        const lossy = opaque('lossy')
        expect(() => lossy.unsafeEncode(new Set([5e-324]))).toThrow(
            /NS decodes as strings|no counterpart/,
        )
        expect(() => lossy.unsafeEncode(new Set([1]))).toThrow(CodecError)
        expect(() => lossy.unsafeDecode({ NS: ['1'] })).toThrow(
            /no counterpart this codec can write/,
        )
    })

    /**
     * And the read side of `N` is gated the way `number`'s is, which it was not.
     *
     * `Number` reads far more than an `N` carries, so `{ N: 'abc' }` decoded to `NaN` and
     * `{ N: '1e400' }` to `Infinity` — values this codec's own `encode` refuses, which is
     * **(C)** failing. `checkDecodesAreWritable` catches exactly this and had never been
     * pointed at `opaque`; it is now, below.
     */
    it('gates the N it reads, as number does', () => {
        const lossy = opaque('lossy')
        for (const text of ['', ' ', '0x10', 'abc', 'NaN', '1e400']) {
            expect(() => lossy.unsafeDecode({ N: text })).toThrow(
                /is not a numeral/,
            )
        }
        expect(lossy.unsafeDecode({ N: '1.50' })).toBe(1.5)
        expect(lossy.unsafeDecode({ N: '0' })).toBe(0)
    })

    /**
     * **The digits written are the normal form of `DynamoNumber`**, which is the form the store
     * returns. `String(1e125)` is `1e+125`, and the policy writes the digits in full. The number is
     * the same, so a read gives back the float that was written.
     */
    it('still writes the range that is stored, including the ends, in the normal form', () => {
        const lossy = opaque('lossy')
        expect(lossy.unsafeEncode(1e125)).toEqual({ N: `1${'0'.repeat(125)}` })
        expect(lossy.unsafeEncode(1e-130)).toEqual({
            N: `0.${'0'.repeat(129)}1`,
        })
        expect(lossy.unsafeEncode(1e21)).toEqual({
            N: '1000000000000000000000',
        })
        expect(lossy.unsafeEncode(5e-7)).toEqual({ N: '0.0000005' })
        expect(lossy.unsafeDecode(lossy.unsafeEncode(1e-130))).toBe(1e-130)
        expect(lossy.unsafeEncode(0)).toEqual({ N: '0' })
        expect(lossy.unsafeEncode(-1.5)).toEqual({ N: '-1.5' })
    })
})
