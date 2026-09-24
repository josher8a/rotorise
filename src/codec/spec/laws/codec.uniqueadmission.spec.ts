/**
 * **(U), as a property test.**
 *
 * The last law of the specification, and the only one with no harness.
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
import type { Attribute } from '../../attribute'
import { DynamoNumber, memberOf } from '../../attribute'
import type { AnyCodec } from '../../codec'
import {
    array,
    boolean,
    CodecError,
    codecOfTerm,
    decimal,
    discriminatedUnion,
    held,
    nullable,
    number,
    object,
    optional,
    string,
    union,
    valueKinds,
} from '../../codec'
import type { StandardSchemaV1 } from '../../standard'
import { checkUniqueAdmission } from '../../testing'

/** A Standard Schema v1 written by hand: a foreign held side that admits a `Date`. */
const date: StandardSchemaV1<Date> = {
    '~standard': {
        version: 1,
        vendor: 'handwritten',
        validate: (value) =>
            value instanceof Date
                ? { value }
                : { issues: [{ message: 'expected a Date' }] },
    },
}

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
        checkUniqueAdmission(union([string('A'), string('B')]), { seed })
    })

    it('holds for a discriminated union', () => {
        checkUniqueAdmission(
            discriminatedUnion('type', [
                object({ type: string('CHECKUP'), petId: string }),
                object({ type: string('SHOT'), vaccine: string }),
            ]),
            { seed },
        )
    })

    /**
     * This asked the same question of a variant answering to *two* tags, which arity one refuses
     * at the declaration. The case is gone, the property is not: what it was really checking is
     * (U) at a `dunion` whose options carry different attribute sets, which is what the two
     * options below are — restated at one tag each, on the same seed.
     */
    it('holds for options with different attributes at one tag each', () => {
        checkUniqueAdmission(
            discriminatedUnion('carrierId', [
                object({ carrierId: string('ACME'), at: string }),
                object({ carrierId: string('LOCAL'), depot: string }),
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
        checkUniqueAdmission(
            object([string, optional(union([string, boolean]))]),
            { seed },
        )
    })
})

describe('a codec with no union', () => {
    /** Silence is not a pass, and a harness that says nothing on `string` would report one. */
    it('is reported rather than passing vacuously', () => {
        expect(() => checkUniqueAdmission(string, { seed })).toThrow(CodecError)
    })
})

describe('the harness, against planted violations', () => {
    /**
     * Two options that both admit the same value, which the guard cannot see.
     *
     * `union` reads the terms at construction, and accepts a pair of adapters only where it can
     * separate them. Two adapters whose held sides understate their admission slip it: the terms
     * say `number` against `string`, so the pair is separated. What the conversions do at runtime
     * is accept a `Date` too, which is the situation the guard exists to prevent and does not see.
     * @anchored
     */
    /**
     * **Pins wording, and not because no law has it — because the *message* is the only channel
     * this fact travels on.** Which side of (U) fails is an algebraic distinction, and both
     * failures are one `CodecError`: swapping these to the type would collapse this test and its
     * sibling into the same assertion and lose the write/read split that is the pair's whole
     * point. Kept for the opposite reason to the diagnostics elsewhere in this batch.
     */
    it('reports a value two options admit', () => {
        // two adapters whose held sides understate their admission: each term says it writes one
        // primitive kind, and each conversion accepts a `Date` too. The guard reads the terms, sees
        // `number` against `string` and `N` against `S`, and refuses neither half. The harness
        // filters by kind, and a `Date` has no kind, so it asks both options, and both admit it.
        // Only library code reaches this construction: the public `held` checks its held side
        // before `encode`, so a caller cannot build it. The runtime detection is defence in depth
        const asNumber = codecOfTerm<number, Attribute<'N'>>({
            kind: 'held',
            inner: { kind: 'number' },
            outer: { kind: 'number' },
            f: ((v: number | Date) => DynamoNumber.from(String(Number(v)))) as (
                value: never,
            ) => unknown,
            g: ((a: DynamoNumber) => a.toNumber()) as (held: never) => unknown,
            arbitrary: () => new Date(0),
        })
        const asText = codecOfTerm<string, Attribute<'S'>>({
            kind: 'held',
            inner: { kind: 'string' },
            outer: { kind: 'string' },
            f: ((v: string | Date) =>
                v instanceof Date ? v.toISOString() : v) as (
                value: never,
            ) => unknown,
            g: ((a: string) => a) as (held: never) => unknown,
        })
        expect(() =>
            checkUniqueAdmission(union([asText, asNumber]), { seed }),
        ).toThrow(/\(U\) fails on the write side/)
    })

    /**
     * An option nothing admits on the read side.
     *
     * The value side is fine — `never` writes an `S` and only it is asked — but what it writes is
     * an `S` no option reads back, so the attribute has no admitter at all. That is the shape (R)
     * loses at a canonical attribute, which is exactly the residue `uAtCan_of_separated` names.
     * @anchored
     */
    /**
     * **Pins wording, and not because no law has it — because the *message* is the only channel
     * this fact travels on.** Which side of (U) fails is an algebraic distinction, and both
     * failures are one `CodecError`: swapping these to the type would collapse this test and its
     * sibling into the same assertion and lose the write/read split that is the pair's whole
     * point. Kept for the opposite reason to the diagnostics elsewhere in this batch.
     */
    it('reports an attribute no option admits', () => {
        const writeOnly = held(string, string, {
            encode: (v: string) => v,
            decode: () => new CodecError('this one never reads'),
            arbitrary: () => 'x',
        })
        expect(() =>
            checkUniqueAdmission(union([writeOnly, number]), { seed }),
        ).toThrow(/\(U\) fails on the read side/)
    })
})

describe('what (U) says about nullable, which is a union', () => {
    /**
     * `nullable(c)` builds `union([c, null])`, so it is a union *site* and (U) is asked of it here
     * like any other. It was checked in Lean and nowhere here while the wrapper was its own kind,
     * because nothing walked into a wrapper looking for options.
     *
     * (U) is what makes the null point safe to add: `c` and the null term must be separated, or a
     * stored `NULL` would be claimed by two options and the union would write nothing.
     */
    it('a nullable is a union site, and its two options are separated', () => {
        expect(() =>
            checkUniqueAdmission(nullable(string), { seed }),
        ).not.toThrow()
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
                object({ c: string.set() }),
            ]),
            { seed },
        )
    })
})

describe('a foreign held side writes every kind, so a union beside it needs a discriminator', () => {
    /**
     * **The defect (U) found, and the rule that closes it at the declaration.**
     *
     * `union([held(decimal, <a Date schema>, asDate), string])` is a natural thing to write — a
     * timestamp or a raw string. It was accepted at the declaration while the write side of a
     * `held` was unknown, and an unknown side did not count as a meeting. That is the permissive
     * direction, and it is unsound: nothing proved that the two options admit no common value.
     *
     * A foreign held side is not this library's to rule. The library reads a foreign schema through
     * `validate` only, so the write occupancy of the `held` is the top, every kind. The top meets
     * `string`, and the union is refused where it is declared. A caller who needs both options
     * gives the entity a discriminator.
     *
     * The read side still has a `κ`: the stored member is the *inner* codec's, `N`.
     */
    const asDate = {
        encode: (at: Date) => String(at.getTime()),
        decode: (at: string) => new Date(Number(at)),
    }
    // declared through a cast, as a caller passing an erased list would
    const declare = union as unknown as (
        options: readonly AnyCodec[],
    ) => unknown

    it('has a κ on the read side, and every kind on the write side', () => {
        // the member is asked of the attribute, because that is the law; the value kinds stay a
        // reader call because the *reader's answer* is the subject here
        const at = held(decimal, date, asDate)
        expect(memberOf(at.encode(new Date(0)) as never)).toBe('N')
        expect(valueKinds(at.def)).toEqual(valueKinds({ kind: 'opaq' }))
    })

    it('refuses the union at the declaration, because the top meets string', () => {
        expect(() => declare([held(decimal, date, asDate), string])).toThrow(
            CodecError,
        )
    })
})
