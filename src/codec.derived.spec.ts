/**
 * The three facts a codec used to store, read from its definition instead.
 *
 * `child`, `member` and `constant` were fields every constructor had to set and every wrapper had
 * to carry, and the carrying is what kept going wrong: `refine` dropped `child` and `member`;
 * `item`, `map`, `tagged` and `untagged` each wrote an `M` without saying so; `optional` kept a
 * `constant` it had no business keeping. There was a list — `inherited` — naming which survived a
 * wrapper, and it existed only because they were stored.
 *
 * `writes`, `decides` and `deeper` read them off `def` instead, so there is nothing to forget.
 * `inherited` is down to `arbitrary` and `shrink`, which are the escape hatch and not facts.
 */
import { describe, expect, it } from 'vitest'
import type { Attribute } from './attribute'
import type { AttributeCodec } from './codec'
import {
    array,
    binary,
    boolean,
    CodecError,
    decides,
    decimal,
    deeper,
    discriminatedUnion,
    fallback,
    lazy,
    legacy,
    literal,
    nullable,
    nullValue,
    number,
    object,
    opaque,
    optional,
    record,
    refine,
    set,
    string,
    tuple,
    union,
    writes,
} from './codec'

const isTag = (v: string): v is `t-${string}` => v.startsWith('t-')

describe('the member a codec writes', () => {
    it.each([
        { kind: 'string', codec: string, member: 'S' },
        { kind: 'literal', codec: literal('A'), member: 'S' },
        { kind: 'decimal', codec: decimal, member: 'N' },
        { kind: 'number', codec: number, member: 'N' },
        { kind: 'literal(N)', codec: literal(0, 1), member: 'N' },
        { kind: 'boolean', codec: boolean, member: 'BOOL' },
        { kind: 'null', codec: nullValue, member: 'NULL' },
        { kind: 'binary', codec: binary, member: 'B' },
        { kind: 'array', codec: array(string), member: 'L' },
        { kind: 'tuple', codec: tuple(string), member: 'L' },
        { kind: 'record', codec: record(string), member: 'M' },
        { kind: 'attributes', codec: object({ a: string }), member: 'M' },
    ])('$kind writes $member', ({ codec, member }) => {
        expect(writes(codec)).toBe(member)
    })

    /** The rule `inherited` used to state, now a recursive case rather than a list entry. */
    it('a wrapper writes what it wraps', () => {
        expect(writes(refine(decimal, isTag as never))).toBe('N')
        expect(writes(optional(decimal))).toBe('N')
        expect(writes(fallback(decimal, () => '0'))).toBe('N')
        expect(writes(legacy({ current: decimal, older: string }))).toBe('N')
    })

    it('is none where more than one member is written, or none is known', () => {
        expect(writes(nullable(string))).toBeUndefined()
        expect(writes(opaque)).toBeUndefined()
    })

    /** What `set` reads, and the reason a codec has to be able to say it at all. */
    it('is what lets a refined scalar still be a set element', () => {
        expect(() => set(refine(string, isTag))).not.toThrow()
        expect(() => set(nullable(string))).toThrow(CodecError)
    })

    /**
     * `item`, `map`, `tagged` and `untagged` all left this blank while writing an `M`, so a set of
     * one reported "no single member" instead of naming what it found.
     */
    it('is `M` for every composite, which none of them used to say', () => {
        expect(writes(object({ a: string }))).toBe('M')
    })
})

describe('the value a codec decides', () => {
    it('is the one a single-valued literal admits', () => {
        expect(decides(literal('ONLY'))).toBe('ONLY')
        expect(decides(literal('A', 'B'))).toBeUndefined()
    })

    /**
     * Not recursive through the wrappers `writes` descends: a constant is a claim about the value,
     * and each of these may change values or admit absence.
     */
    it('does not survive a wrapper that may change the value', () => {
        expect(decides(refine(literal('ONLY'), isTag as never))).toBeUndefined()
        expect(
            decides(
                legacy({ current: literal('ONLY'), older: literal('ONLY') }),
            ),
        ).toBeUndefined()
        expect(decides(nullable(literal('ONLY')))).toBeUndefined()
        expect(decides(optional(literal('ONLY')))).toBeUndefined()
    })

    /** `fallback` always writes the attribute, and its replacement is typed to the same value. */
    it('survives fallback, which is the one that keeps it', () => {
        expect(decides(fallback(literal('ONLY'), () => 'ONLY' as const))).toBe(
            'ONLY',
        )
    })
})

describe('what is one segment deeper', () => {
    it('finds an attribute of an item, and nothing past the schema', () => {
        const Pet = object({ id: string })
        expect(deeper(Pet, 'id')?.def?.kind).toBe('string')
        expect(deeper(Pet, 'nope')).toBeUndefined()
    })

    it('descends a list by index, a record by key, a tuple by position', () => {
        expect(deeper(array(decimal), 0)?.def?.kind).toBe('decimal')
        expect(deeper(record(decimal), 'anything')?.def?.kind).toBe('decimal')
        expect(deeper(tuple(string, decimal), 1)?.def?.kind).toBe('decimal')
    })

    /** A set is unordered, so no document path addresses a member of one. */
    it('refuses to descend a set', () => {
        expect(deeper(set(string), 0)).toBeUndefined()
    })

    it('descends through a wrapper to what it wraps', () => {
        expect(deeper(optional(array(decimal)), 0)?.def?.kind).toBe('decimal')
        expect(deeper(nullable(array(decimal)), 0)?.def?.kind).toBe('decimal')
    })

    it('descends into a recursive entity without forcing it early', () => {
        type Tree = { name: string; children?: readonly Tree[] }
        let built = 0
        const Tree: AttributeCodec<Tree, Attribute<'M'>> = lazy(() => {
            built++
            return object({
                name: string,
                children: optional(array(Tree)),
            })
        })
        expect(built).toBe(0)
        expect(deeper(Tree, 'name')?.def?.kind).toBe('string')
        expect(built).toBe(1)
    })

    it('branches where the variants disagree, and agrees where they do not', () => {
        type Visit =
            | { type: 'CHECKUP'; petId: string }
            | { type: 'SHOT'; petId: string }
        const Visits = discriminatedUnion('type', [
            object({ type: literal('CHECKUP'), petId: string }),
            object({ type: literal('SHOT'), petId: string }),
        ])
        // both variants declare `petId` the same way, so there is nothing to choose between
        expect(deeper(Visits, 'petId')?.def?.kind).toBe('string')
        expect(deeper(Visits, 'nope')).toBeUndefined()
    })

    it('gives no answer where the variants disagree, rather than a fabricated one', () => {
        const Ops = discriminatedUnion('type', [
            object({ type: literal('A'), amount: number }),
            object({ type: literal('B'), amount: string }),
        ])
        // two codecs are one segment down and neither is *the* one, so there is nothing to return.
        // `ItemCodec.at` carries the disagreement instead, and reports it if the path ends on it
        expect(deeper(Ops, 'amount')).toBeUndefined()
    })

    it('reaches a member-specific attribute of an untagged union', () => {
        type Line = { petId: string } | { petIds: readonly string[] }
        const Lines = union([
            object({ petId: string }),
            object({ petIds: array(string) }),
        ])
        expect(deeper(Lines, 'petId')?.def?.kind).toBe('string')
        expect(deeper(Lines, 'petIds')?.def?.kind).toBe('array')
    })
})
