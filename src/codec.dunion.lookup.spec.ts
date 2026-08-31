/**
 * **The lookup table a discriminated union normalizes into, and two ways it was not a lookup.**
 *
 * `discriminatedUnion(d, options)` does not keep the option list. It reads each option's own
 * `literal(...)` for the values that option answers to and writes them into a table keyed by tag,
 * then hands that table to the internal `tagged`. Every later decision — which variant encodes,
 * which variant a stored item decodes as — is one read of that table. Both defects here are
 * properties of the table rather than of the options, which is why neither showed up in a
 * round-trip test: each option round-trips perfectly on its own.
 *
 * The model states the first as a premise. `Calculus.Typed.dunion` carries `hdisj`, that the
 * options' tag sets are pairwise disjoint, so a union with two options answering to one tag is not
 * a `dunion` the calculus types. The library built it anyway and let the earlier option be
 * overwritten — the same shape as the four `native.ts` findings in §9 of `docs/codec-audit.md`: a
 * model premise the host did not check.
 */
import { describe, expect, it } from 'vitest'
import type { AnyObjectCodec } from './codec'
import { discriminatedUnion, literal, object, string } from './codec'
import { CodecError } from './Rotorise'

/** The constructor with its declaration-time constraint forgotten, so the runtime can be asked. */
const declare = discriminatedUnion as unknown as (
    discriminator: string,
    options: readonly AnyObjectCodec[],
) => unknown

describe('two options answering to the same tag', () => {
    /**
     * The table is a key written twice: the second write wins, and the first option becomes
     * unreachable. It failed later and elsewhere — `encode` of a value of the *first* variant
     * reported a required attribute of the *second* one missing, naming a field the caller had
     * never heard of.
     *
     * `union` refuses its own ambiguity where the declaration is, for the reason its docstring
     * gives: two options no value can choose between is a fact about the declaration, not about
     * any particular value. A repeated tag is more decidable than that, and was not refused.
     */
    it('is refused at the declaration', () => {
        const _wrong = () =>
            // @ts-expect-error both options answer to 'A', so a lookup reaches only one
            discriminatedUnion('type', [
                object({ type: literal('A'), x: string }),
                object({ type: literal('A'), y: string }),
            ])
        expect(typeof _wrong).toBe('function')
    })

    it('and the runtime refuses it too, where the declaration is', () => {
        expect(() =>
            declare('type', [
                object({ type: literal('A'), x: string }),
                object({ type: literal('A'), y: string }),
            ]),
        ).toThrow(/two options answer to 'type' = 'A'/)
    })

    /**
     * A variant may answer to several tags, and this codebase relies on it, so the overlap can be
     * partial: one option covering `ACME` and `GLOBEX` beside one covering `GLOBEX` leaves the
     * first working at one of its own tags and shadowed at the other. That is the case a check
     * written against whole options would miss.
     */
    it('is refused when only one tag of a multi-tag variant collides', () => {
        const _wrong = () =>
            // @ts-expect-error 'GLOBEX' is already taken by the option above
            discriminatedUnion('carrierId', [
                object({ carrierId: literal('ACME', 'GLOBEX'), at: string }),
                object({ carrierId: literal('GLOBEX'), depot: string }),
            ])
        expect(typeof _wrong).toBe('function')
        expect(() =>
            declare('carrierId', [
                object({ carrierId: literal('ACME', 'GLOBEX'), at: string }),
                object({ carrierId: literal('GLOBEX'), depot: string }),
            ]),
        ).toThrow(/two options answer to 'carrierId' = 'GLOBEX'/)
    })

    /** And the feature the refusal must not take with it. */
    it('still accepts a multi-tag variant that collides with nothing', () => {
        const u = discriminatedUnion('carrierId', [
            object({ carrierId: literal('ACME', 'GLOBEX'), at: string }),
            object({ carrierId: literal('LOCAL'), depot: string }),
        ])
        expect(u.encode({ carrierId: 'ACME', at: 'x' })).toEqual({
            M: { carrierId: { S: 'ACME' }, at: { S: 'x' } },
        })
        expect(u.encode({ carrierId: 'GLOBEX', at: 'x' })).toEqual({
            M: { carrierId: { S: 'GLOBEX' }, at: { S: 'x' } },
        })
    })
})

describe('a stored tag that names a member of Object.prototype', () => {
    const visit = discriminatedUnion('type', [
        object({ type: literal('CHECKUP'), petId: string }),
        object({ type: literal('SHOT'), vaccine: string }),
    ])
    const stored = (tag: string) => ({
        M: { type: { S: tag }, petId: { S: 'p' } },
    })

    /**
     * The table was a plain object, so the lookup inherited. A stored discriminator of `toString`
     * returned `Object.prototype.toString` — truthy, so the "not a variant" branch never ran — and
     * the caller got `TypeError: variant.decode is not a function`.
     *
     * Reachable from data this library does not control: the tag is read off the stored item. And
     * a raw `TypeError` is the one thing every other failure here is careful not to be — the
     * library's contract is that what a caller has to handle is a `CodecError`.
     */
    it.each(['toString', 'constructor', '__proto__', 'valueOf'])(
        'decodes to a CodecError, not a TypeError, at %s',
        (tag) => {
            const result = visit.decode(stored(tag))
            expect(result).toBeInstanceOf(CodecError)
            expect((result as CodecError).reason).toMatch(
                new RegExp(`'${tag}' is not a variant of 'type'`),
            )
        },
    )

    it('reports the same on the writing half', () => {
        const write = visit.encode as unknown as (v: unknown) => unknown
        expect(write({ type: 'toString', petId: 'p' })).toBeInstanceOf(
            CodecError,
        )
    })

    /** An ordinary unknown tag was always reported properly, and still is. */
    it('leaves an ordinary unknown tag alone', () => {
        const result = visit.decode(stored('NOPE'))
        expect(result).toBeInstanceOf(CodecError)
        expect((result as CodecError).reason).toMatch(
            /'NOPE' is not a variant of 'type'; expected 'CHECKUP', 'SHOT'/,
        )
    })

    /** And the variants that exist still resolve. */
    it('still decodes a real variant', () => {
        expect(visit.decode(stored('CHECKUP'))).toEqual({
            type: 'CHECKUP',
            petId: 'p',
        })
    })
})
