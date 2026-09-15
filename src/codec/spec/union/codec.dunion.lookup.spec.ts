/**
 * **The lookup table a discriminated union normalizes into, and two ways it was not a lookup.**
 *
 * `discriminatedUnion(d, options)` does not keep the option list. It reads each option's own
 * literal for the values that option answers to and writes them into a table keyed by tag,
 * then hands that table to the internal `tagged`. Every later decision — which variant encodes,
 * which variant a stored item decodes as — is one read of that table. Both defects here are
 * properties of the table rather than of the options, which is why neither showed up in a
 * round-trip test: each option round-trips perfectly on its own.
 *
 * The model makes the first unstatable rather than refusing it. `Calculus.Typed.dunion` keys its
 * variants by tag, so a table cannot hold two entries for one key and there is no tag set left to
 * compare; the one premise that remains, `hone`, says a variant's own discriminator field agrees
 * with its key. So a union with two options answering to one tag is not a `dunion` the calculus
 * types. The library built it anyway and let the earlier option be overwritten: a model fact the
 * host did not carry.
 */
import { describe, expect, it } from 'vitest'
import { CodecError } from '../../../Rotorise'
import type { AnyObjectCodec } from '../../codec'
import { discriminatedUnion, object, string } from '../../codec'

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
                object({ type: string('A'), x: string }),
                object({ type: string('A'), y: string }),
            ])
        expect(typeof _wrong).toBe('function')
    })

    it('and the runtime refuses it too, where the declaration is', () => {
        expect(() =>
            declare('type', [
                object({ type: string('A'), x: string }),
                object({ type: string('A'), y: string }),
            ]),
        ).toThrow(/two options answer to 'type' = 'A'/)
    })

    /**
     * **Two tests stood here and are gone, and what removed them is a premise rather than a
     * repair.** One exhibited a *partial* collision — an option covering `ACME` and `GLOBEX`
     * beside one covering `GLOBEX`, the first working at one of its own tags and shadowed at the
     * other — and the second was labelled "the feature the refusal must not take with it",
     * asserting that a multi-tag variant colliding with nothing still encodes.
     *
     * Arity one at the discriminator (`36df8e7`, `Typed.dunion`'s `hone`) makes neither
     * expressible: an option's literal admits one value, so an overlap cannot be partial and
     * there is no multi-tag variant to accept. The same closure `HOpaque`'s `set []` got — a
     * witness that a case is handled is worth having exactly while the case can be written down,
     * and when the type stops admitting it the witness stops being a theorem and becomes the
     * refusal below.
     *
     * The `@ts-expect-error` on the first of them is the reason this is a deletion and not an
     * update: under arity one that annotation is satisfied by the *arity* error, not the
     * collision error it names, so the test would have gone on passing while checking something
     * else. A silent pass is worse than a missing test.
     */
    it('refuses a literal admitting several values at the discriminator', () => {
        const _wrong = () =>
            // @ts-expect-error one option, two tags — a variant answers to exactly one
            discriminatedUnion('carrierId', [
                object({ carrierId: string('ACME', 'GLOBEX'), at: string }),
                object({ carrierId: string('LOCAL'), depot: string }),
            ])
        expect(typeof _wrong).toBe('function')
    })

    it('and the runtime refuses it too, where the declaration is', () => {
        expect(() =>
            declare('carrierId', [
                object({ carrierId: string('ACME', 'GLOBEX'), at: string }),
                object({ carrierId: string('LOCAL'), depot: string }),
            ]),
        ).toThrow(
            /'carrierId' names 2 values at one option \(ACME, GLOBEX\), and a variant answers to exactly one tag/,
        )
    })
})

describe('a stored tag that names a member of Object.prototype', () => {
    const visit = discriminatedUnion('type', [
        object({ type: string('CHECKUP'), petId: string }),
        object({ type: string('SHOT'), vaccine: string }),
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
     *
     * **The class of defect is gone rather than guarded now, and the message says so.** A
     * dissection's term is a union, so decoding resolves by structural admission — the names the
     * item carries, then the literal at each — and reaches no lookup keyed by attacker-controlled
     * text. The rule this pins is the one it always pinned: a stored tag naming a member of
     * `Object.prototype` is a `CodecError` and never a `TypeError`. What moved is which sentence
     * the caller reads, because there is no table to miss.
     */
    it.each(['toString', 'constructor', '__proto__', 'valueOf'])(
        'decodes to a CodecError, not a TypeError, at %s',
        (tag) => {
            const result = visit.decode(stored(tag))
            expect(result).toBeInstanceOf(CodecError)
            expect(result).not.toBeInstanceOf(TypeError)
            expect((result as CodecError).reason).toMatch(/no option admits/)
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
        expect((result as CodecError).reason).toMatch(/no option admits/)
    })

    /** And the variants that exist still resolve. */
    it('still decodes a real variant', () => {
        expect(visit.decode(stored('CHECKUP'))).toEqual({
            type: 'CHECKUP',
            petId: 'p',
        })
    })
})
