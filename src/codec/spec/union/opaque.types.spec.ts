/**
 * `opaque.Encode` against `encodeUnknown`, branch for branch.
 *
 * The type is only worth having if it says what the function does, so each case asserts both: the
 * type with `attest`, the runtime with an encode. A refusal is checked the same way — the type
 * resolves to an `ErrorMessage` exactly where the function returns a `CodecError`.
 *
 * This is the pair `native.ItemEncode` is for the AWS SDK's marshaller, and the two are not the same
 * function: this one refuses numbers by default, refuses `bigint`, refuses a set of numbers, refuses
 * a `Map`, and refuses a class instance. A team whose own marshaller resembles `opaque` diffs
 * against this.
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
import type { AttributeCodec } from '../../codec'
import { CodecError, failed, opaque } from '../../codec'
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

    it('on a number, only once told what to do with N', () => {
        attest<[opaque.Encode<number, 'lossy'>], [N]>()
        expect(wrote(1.5)).toEqual({ N: '1.5' })

        // and refused by default, in both
        attest<[Refuses<opaque.Encode<number>>], [true]>()
        expect(refused(1.5)).toMatch(/a number cannot be stored/)
    })

    it('on the sets it carries, and the one it does not', () => {
        attest<[opaque.Encode<ReadonlySet<string>>], [SS]>()
        attest<[opaque.Encode<ReadonlySet<Uint8Array>>], [BS]>()
        expect(wrote(new Set(['b', 'a']))).toEqual({ SS: ['a', 'b'] })

        // a set of numbers reaches `NS`, which decodes as strings — so neither will write it
        attest<[Refuses<opaque.Encode<ReadonlySet<number>>>], [true]>()
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
                ErrorMessage<'[opaque] a bigint shares `N` with `number` and decodes as one, so `1n` would come back as `1`. Use `decimal` and pass `value.toString()`'>,
            ]
        >()
        expect(refused([1n])).toMatch(/a bigint cannot be stored/)
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
 * `opaque` is the refusing codec and calling it chooses the other policy. It was three names for two
 * codecs, and the policy is the one knob it has, so unlike `native` it is *fully* reflected in the
 * type: `Encode<number>` is a refusal and `Encode<number, 'lossy'>` is `N`, which is the whole of
 * what the runtime decides.
 */
describe('opaque is one codec and one optional policy', () => {
    it('refuses by default, without being called', () => {
        expect(failed(opaque.encode(1))).toBe(true)
        attest<[Refuses<opaque.Encode<number>>], [true]>()
    })

    it('and calling it with no argument means the same thing', () => {
        expect(failed(opaque().encode(1))).toBe(true)
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

    it('on an N, which is a refusal until a policy is chosen', () => {
        attest<[Refuses<opaque.Decode<N>>], [true]>()
        attest<[opaque.Decode<N, 'lossy'>], [number]>()

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
        attest<[Refuses<opaque.Decode<L<N>>>], [true]>()
        attest<[Refuses<opaque.Decode<M<{ big: N }>>>], [true]>()

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
     * The three places this differs from the SDK's reading, asserted rather than described.
     *
     * `NS` is the one that matters: its members are decimal strings, and nothing without a schema can
     * say which of them a JS number holds faithfully. The SDK guesses; this does not.
     */
    it('differs from native.Decode where the two disagree', () => {
        attest<[native.Decode<NS>], [Set<number | bigint>]>()
        attest<[Refuses<opaque.Decode<NS>>], [true]>()

        attest<[native.Decode<N>], [number | bigint]>()
        attest<[Refuses<opaque.Decode<N>>], [true]>()

        // and the runtime agrees: a stored NS is refused, not guessed at
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
     * write is a member it cannot read — `Calculus.Lawful.no_read_without_write`.
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

    it('still writes the range that is stored, including the ends', () => {
        const lossy = opaque('lossy')
        expect(lossy.unsafeEncode(1e125)).toEqual({ N: '1e+125' })
        expect(lossy.unsafeEncode(1e-130)).toEqual({ N: '1e-130' })
        expect(lossy.unsafeEncode(0)).toEqual({ N: '0' })
        expect(lossy.unsafeEncode(-1.5)).toEqual({ N: '-1.5' })
    })
})
