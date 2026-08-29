/**
 * **(U), as a property test.**
 *
 * The last row of `docs/codec-formalization.md` §5's table, and the only law there with no harness.
 * `Calculus.UniqueAdmission` says it for the model; {@link checkUniqueAdmission} says it for a
 * shipped codec, reading admission off the *definition* rather than off the union's own matcher —
 * a test that asked `union` which option it picked would be checking the implementation against
 * itself.
 *
 * Why this file and not a corollary of {@link checkRoundTrip}: (U) is not a round-trip. A union
 * that resolves ambiguity by declaration order round-trips perfectly and violates (U) at every
 * ambiguous input, and the damage shows up later — as a variant that stops being reachable when a
 * sibling grows an attribute. The same gap `checkDecodesAreWritable` was written for, one law over.
 *
 * The planted cases at the bottom are what makes a pass mean something: the harness is shown
 * failing on a union that genuinely has two admitters, and on one that has none.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    boolean,
    carries,
    custom,
    decimal,
    held,
    discriminatedUnion,
    literal,
    nullable,
    number,
    object,
    optional,
    record,
    set,
    string,
    union,
    writes,
} from './codec'
import { checkUniqueAdmission } from './testing'
import { Attribute } from './Rotorise'

const seed = 20260829

describe('the unions this library ships', () => {
    it('holds for a union of objects told apart by their names', () => {
        checkUniqueAdmission(
            union([
                object({ petId: string, price: decimal }),
                object({ petIds: array(string) }),
            ]),
            { seed },
        )
    })

    it('holds for a union of ground codecs told apart by what they carry', () => {
        checkUniqueAdmission(union([string, number, boolean]), { seed })
    })

    it('holds for literals, which are told apart by nothing else', () => {
        checkUniqueAdmission(union([literal('A'), literal('B')]), { seed })
    })

    it('holds for a discriminated union', () => {
        checkUniqueAdmission(
            discriminatedUnion('type', [
                object({ type: literal('CHECKUP'), petId: string }),
                object({ type: literal('SHOT'), vaccine: string }),
            ]),
            { seed },
        )
    })

    it('holds for a variant answering to two tags', () => {
        checkUniqueAdmission(
            discriminatedUnion('carrierId', [
                object({ carrierId: literal('ACME', 'GLOBEX'), at: string }),
                object({ carrierId: literal('LOCAL'), depot: string }),
            ]),
            { seed },
        )
    })

    it('holds for a union nested inside an entity, which is where they live', () => {
        checkUniqueAdmission(
            object({
                petId: string,
                shipping: union([
                    object({ pickup: boolean }),
                    object({ address: string, postcode: string }),
                ]),
            }),
            { seed },
        )
    })

    it('holds for a mixed union — a map option and a bare one', () => {
        checkUniqueAdmission(union([object({ at: string }), string]), { seed })
    })

    it('holds under a set and an array element', () => {
        checkUniqueAdmission(array(union([string, number])), { seed })
        checkUniqueAdmission(record(union([string, boolean])), { seed })
    })
})

describe('a codec with no union', () => {
    /** Silence is not a pass, and a harness that says nothing on `string` would report one. */
    it('is reported rather than passing vacuously', () => {
        expect(() => checkUniqueAdmission(string, { seed })).toThrow(
            /has none/,
        )
    })
})

describe('the harness, against planted violations', () => {
    /**
     * Two options that both admit the same value, which neither guard can see.
     *
     * `union` refuses an ambiguous pair twice — `ValidateOptions` at the type level where the two
     * read back as the same type, and the `carries` scan at construction where they take the same
     * kind of value. A `custom` slips both: it reads back as `number`, so the types are told apart,
     * and it declares no `carries`, so it is not compared. What it actually does at runtime is
     * accept any string, which is the situation both guards exist to prevent and neither sees.
     */
    it('reports a value two options admit', () => {
        const loose = custom<number, Attribute<'S'>>({
            encode: (v) => ({ S: String(v) }),
            decode: (a) => Number(a.S),
            arbitrary: () => 1,
        })
        expect(() =>
            checkUniqueAdmission(union([string, loose]), { seed }),
        ).toThrow(/\(U\) fails on the write side/)
    })

    /**
     * An option nothing admits on the read side.
     *
     * The value side is fine — `never` writes an `S` and only it is asked — but what it writes is
     * an `S` no option reads back, so the attribute has no admitter at all. That is the shape (R)
     * loses at a canonical attribute, which is exactly the residue `uAtCan_of_separated` names.
     */
    it('reports an attribute no option admits', () => {
        const writeOnly = custom<string, Attribute<'S'>>({
            encode: (v) => ({ S: v }),
            decode: () => {
                throw new Error('this one never reads')
            },
            arbitrary: () => 'x',
        })
        expect(() =>
            checkUniqueAdmission(union([writeOnly, number]), { seed }),
        ).toThrow(/\(U\) fails on the read side/)
    })
})

describe('what (U) says about nullable, which the model reads as a union', () => {
    /**
     * `nullable(c)` is `union(c, ⟨NULL⟩)` in the model and a wrapper here, so it is not a union
     * *site* — nothing walks into it looking for options. Recorded rather than asserted: the model
     * has `nullOption` and this harness has no counterpart, so (U) for `nullable` is checked in
     * Lean and nowhere here.
     */
    it('is not a union site, and this says so', () => {
        expect(() => checkUniqueAdmission(nullable(string), { seed })).toThrow(
            /has none/,
        )
    })
})

describe('an object option with attributes it does not declare', () => {
    /**
     * The names matcher reads the *spec*, and a `rest` policy is not in it — so an entity carrying
     * an undeclared attribute is admitted by no option, and the union cannot write a value the
     * option itself can.
     */
    it('is where (U) and a rest policy meet', () => {
        checkUniqueAdmission(
            union([
                object({ a: string, b: optional(string) }),
                object({ c: set(string) }),
            ]),
            { seed },
        )
    })
})

describe('the defect (U) found: an option with no κ on the write side', () => {
    /**
     * **A union this library builds, decodes from, and cannot encode into.**
     *
     * `union([held(decimal, dateAdapter), string])` is a natural thing to write — a timestamp or a
     * raw string — and it is accepted at the declaration, reads back correctly from both `N` and
     * `S`, and throws on **every** `Date` handed to `encode`. Measured, not inferred; the two calls
     * below are the measurement.
     *
     * The cause is one asymmetry in `κ`, and both of this library's guards exempt exactly the same
     * options:
     *
     * - `writes(held(decimal, …))` is `'N'` — the stored member is the *inner* codec's, so the read
     *   side has a `κ` and tells the two options apart.
     * - `carries(held(decimal, …))` is `undefined` — the adapter's carrier is a caller's type, and
     *   §1's `Value` has no point for a `Date`. So there is no `κ` on the write side, and
     *   `shapeOf(new Date())` is `undefined` too: the filter cannot even be applied to the value.
     *
     * With no `κ`, admission falls back to the attempt — and `string.encode(new Date())` *succeeds*,
     * because encoding does not validate. Two options admit, and the union reports ambiguity rather
     * than choosing, which is the correct behaviour for a union that genuinely cannot tell them
     * apart. The declaration-time guard would have caught it, except that it skips an option whose
     * `carries` is unknown for the same reason — and it must, or it would refuse
     * `union([held(…), object({ … })])`, which works, because names decide there.
     *
     * So neither guard is wrong on its own. The gap is that they are exempt on the same options, and
     * nothing at either time is left to notice. That is what (U) sees and a round-trip cannot: no
     * generated value reaches this, because the value that breaks it is one `encode` never produces.
     *
     * Recorded rather than repaired — the fix is a choice between refusing the declaration and
     * giving `held` a write-side `κ`, and both are the specification's call. See
     * `docs/codec-formalization.md` §4.
     */
    const asDate = {
        encode: (at: Date) => String(at.getTime()),
        decode: (at: string) => new Date(Number(at)),
    }

    it('has a κ on the read side and none on the write side', () => {
        expect(writes(held(decimal, asDate))).toBe('N')
        expect(carries(held(decimal, asDate))).toBeUndefined()
    })

    it('reads back from either member', () => {
        const either = union([held(decimal, asDate), string])
        expect(either.unsafeDecode({ N: '0' })).toEqual(new Date(0))
        expect(either.unsafeDecode({ S: 'hi' })).toBe('hi')
    })

    it('cannot encode a Date at all', () => {
        const either = union([held(decimal, asDate), string])
        expect(() => either.unsafeEncode(new Date(0) as never)).toThrow(
            /both admit this value/,
        )
    })

    it('is what checkUniqueAdmission reports, on the write side', () => {
        expect(() =>
            checkUniqueAdmission(union([held(decimal, asDate), string]), {
                seed,
            }),
        ).toThrow(/\(U\) fails on the write side/)
    })
})
