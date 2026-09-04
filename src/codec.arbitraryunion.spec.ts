/**
 * A union of anything, not only of objects.
 *
 * `union` used to take specs, so every option was a map. The options are codecs now, and the rule
 * that picks one is the same rule it always was — **exactly one option must match** — but what
 * "match" means has to be stated twice, because encoding and decoding know different things.
 *
 * Decoding knows the member the attribute carries, which is a fact about the data. Encoding knows
 * only the JavaScript value — and it could not once ask the codecs directly, because **encoding did
 * not validate**: a codec's input is typed, so `number` given `'x'` wrote `{ N: 'x' }` rather than
 * failing. That was the whole reason `carries` exists.
 *
 * It asks now. Every row validates, `admits` is an iff with `encode`, and the write side resolves by
 * asking each option rather than by writing through it. `carries` survives as the *declaration*'s
 * filter, which is a question about two codecs rather than about a value.
 */
import { describe, expect, it } from 'vitest'
import type { AnyCodec, UnionCodec } from './codec'
import {
    array,
    binary,
    boolean,
    CodecError,
    decimal,
    number,
    object,
    optional,
    string,
    union,
} from './codec'
import { checkRoundTrip } from './testing'

describe('a union of bare attributes', () => {
    const Scalar = union([string, number])

    it('writes the member of whichever option takes the value', () => {
        expect(Scalar.unsafeEncode('x')).toEqual({ S: 'x' })
        expect(Scalar.unsafeEncode(4)).toEqual({ N: '4' })
    })

    it('reads back the option the member names', () => {
        expect(Scalar.unsafeDecode({ S: 'x' })).toBe('x')
        expect(Scalar.unsafeDecode({ N: '4' })).toBe(4)
    })

    it('says what it holds, per option, rather than "some attribute"', () => {
        const written = Scalar.unsafeEncode('x')
        // the type is `S | N`, so reading either member needs the narrowing to have happened
        expect('S' in written ? written.S : written.N).toBe('x')
    })

    /**
     * **Pins wording no law has, deliberately.** The refusal is asserted as a `CodecError` beside
     * it; what the regex adds is the diagnostic, which is this test's subject. Here it is that the refusal
     * *lists the options*, so a caller of a generated union learns what it could have passed.
     */
    it('refuses a value no option takes, naming the options', () => {
        expect(() => Scalar.unsafeEncode(true as never)).toThrow(CodecError)
        expect(() => Scalar.unsafeEncode(true as never)).toThrow(
            /no option admits this value; options are string \| number/,
        )
    })

    it('refuses a member no option writes', () => {
        expect(() => Scalar.unsafeDecode({ BOOL: true })).toThrow(CodecError)
    })

    it('round-trips, held by an entity that generates both options', () => {
        checkRoundTrip(object({ v: Scalar }).item, {
            count: 200,
            seed: 20260827,
        })
    })
})

describe('the kind of value is a filter, not the answer', () => {
    /**
     * Two options that take the same kind of value and are still never ambiguous.
     *
     * Filtering by kind leaves both, so both are tried, and exactly one accepts the value. This is
     * the case that rules out deciding by kind alone.
     */
    const Tag = union([string('A'), string('B')])

    it('is settled by trying, where the kind cannot settle it', () => {
        expect(Tag.unsafeEncode('A')).toEqual({ S: 'A' })
        expect(Tag.unsafeEncode('B')).toEqual({ S: 'B' })
        expect(Tag.unsafeDecode({ S: 'B' })).toBe('B')
    })

    it('refuses a string neither literal admits', () => {
        expect(() => Tag.unsafeEncode('C' as never)).toThrow(CodecError)
    })

    /**
     * And the pair that is refused before any value exists.
     *
     * `string` and `decimal` both read back as `string`, so the union's entity type *is* `string` and
     * nothing about a value says which option produced it — `decode ∘ encode = id` cannot hold. That
     * is a fact about the declaration, so it is reported there rather than on the first encode.
     *
     * Trying could not have saved it either: neither validates on the way in, so `decimal` given
     * `'x'` writes `{ N: 'x' }` rather than failing. Encoding trusts its types.
     */
    it('is refused at the declaration when two options read back the same', () => {
        const _wrong = () =>
            // @ts-expect-error both read back as `string`, so no value chooses between them
            union([string, decimal])
        expect(typeof _wrong).toBe('function')
    })

    it('and the runtime refuses it too, where the declaration is', () => {
        const declare = union as unknown as (
            options: readonly AnyCodec[],
        ) => UnionCodec<string, readonly AnyCodec[]>
        // both are handed a string and neither checks it, which is a fact about the declaration
        expect(() => declare([string, decimal])).toThrow(CodecError)
    })
})

describe('mixed kinds', () => {
    const Note = union([object({ at: string, text: string }), string])

    it('takes a map or a bare string', () => {
        expect(Note.unsafeEncode({ at: 'now', text: 't' })).toEqual({
            M: { at: { S: 'now' }, text: { S: 't' } },
        })
        expect(Note.unsafeEncode('bare')).toEqual({ S: 'bare' })
    })

    it('reads either back', () => {
        expect(Note.unsafeDecode({ S: 'bare' })).toBe('bare')
        expect(
            Note.unsafeDecode({ M: { at: { S: 'now' }, text: { S: 't' } } }),
        ).toEqual({ at: 'now', text: 't' })
    })

    it('nests, like any other attribute codec', () => {
        const Held = object({ note: Note, n: optional(number) })
        expect(Held.unsafeEncode({ note: 'hi' })).toEqual({
            M: { note: { S: 'hi' } },
        })
    })

    it('has no whole-item reading, because an item is always a map', () => {
        // @ts-expect-error the union can hold an `S`, so there is no item to read
        const _no = () => Note.item.unsafeEncode({ at: 'a', text: 't' })
        expect(typeof _no).toBe('function')
    })

    it('and an all-object union still has one', () => {
        const Line = union([
            object({ petId: string, price: decimal }),
            object({ petIds: array(string) }),
        ])
        expect(Line.item.unsafeEncode({ petId: 'p', price: '1' })).toEqual({
            petId: { S: 'p' },
            price: { N: '1' },
        })
    })
})

describe('what the value cannot tell apart', () => {
    /**
     * A set and a list, which the value *does* tell apart — because a set is held as a `Set`.
     *
     * This is the case that decided it. Held as an array, a set and a list were given the same value
     * and read back as the same type, so nothing chose between them and the union was refused. Held
     * as a `Set` they are disjoint in both directions: `Set<string>` against `readonly string[]` at
     * the declaration, and `SS` against `L` in the table.
     */
    const Tags = union([string.set(), array(string)])

    it('writes SS for a set and L for a list', () => {
        expect(Tags.unsafeEncode(new Set(['b', 'a']))).toEqual({
            SS: ['a', 'b'],
        })
        expect(Tags.unsafeEncode(['b', 'a'])).toEqual({
            L: [{ S: 'b' }, { S: 'a' }],
        })
    })

    it('and reads each back as what it is', () => {
        expect(Tags.unsafeDecode({ SS: ['a', 'b'] })).toEqual(
            new Set(['a', 'b']),
        )
        expect(Tags.unsafeDecode({ L: [{ S: 'b' }, { S: 'a' }] })).toEqual([
            'b',
            'a',
        ])
    })

    it('which is the distinction the ordering of a list depends on', () => {
        // a list keeps the order it was given; a set has none to keep
        expect(Tags.unsafeDecode(Tags.unsafeEncode(['c', 'a', 'b']))).toEqual([
            'c',
            'a',
            'b',
        ])
    })

    it('and kinds that differ are not ambiguous at all', () => {
        const Blob = union([binary, boolean])
        expect(Blob.unsafeEncode(true)).toEqual({ BOOL: true })
        expect(Blob.unsafeEncode(Uint8Array.from([1]))).toEqual({
            B: Uint8Array.from([1]),
        })
    })
})
