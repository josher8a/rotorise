/**
 * The slice of a union: `extract` and `exclude`, over a dissection and over a plain union of
 * objects.
 *
 * `Calculus.AltClause` at the host. A clause names some keys and admits a set of tags at each; the
 * extraction keeps the members it describes and the exclusion keeps the rest. Both give a codec
 * over the **same keys** and fewer members, which is the ruling the model's `Slice.lean` carries:
 * no normalisation drops a constant key, because the codec writes the tag out of the member's own
 * field whatever the key set says.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import { DynamoNumber } from '../../attribute'
import {
    at,
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    exclude,
    extract,
    held,
    mdunion,
    number,
    object,
    optional,
    ref,
    scope,
    string,
    union,
} from '../../codec'
import { failed, orThrow } from '../../result'

const pet = object({ kind: string('pet'), size: string('small'), toy: string })
const dog = object({ kind: string('pet'), size: string('large'), pen: string })
const food = object({
    kind: string('food'),
    size: string('small'),
    gram: boolean,
})

const twoKey = mdunion(['kind', 'size'], [pet, dog, food])

describe('the extraction keeps the members a clause describes', () => {
    /**
     * A clause admits a **set** at each key, which is what makes this more than a lookup: naming
     * one tag reaches one member, and naming two reaches the fibre over both.
     */
    it('keeps every member whose tags lie inside the clause set', () => {
        const small = extract(
            twoKey,
            object({ size: string('small', 'large') }),
        )
        // all three, because every member's `size` is one of the two named
        expect(
            small.unsafeEncode({ kind: 'pet', size: 'small', toy: 't' }),
        ).toEqual({
            M: {
                kind: { S: 'pet' },
                size: { S: 'small' },
                toy: { S: 't' },
            },
        })
        expect(
            small.unsafeEncode({ kind: 'food', size: 'small', gram: true }),
        ).toEqual({
            M: {
                kind: { S: 'food' },
                size: { S: 'small' },
                gram: { BOOL: true },
            },
        })
    })

    it('drops the members the clause does not describe', () => {
        const pets = extract(twoKey, object({ kind: string('pet') }))
        // `food` is gone, so the codec that admitted it no longer does — which is the whole of
        // what an extraction is, and it is visible only as a refusal
        expect(
            failed(
                pets.encode({
                    kind: 'food',
                    size: 'small',
                    gram: true,
                } as never),
            ),
        ).toBe(true)
        expect(
            pets.unsafeEncode({ kind: 'pet', size: 'large', pen: 'p' }),
        ).toEqual({
            M: { kind: { S: 'pet' }, size: { S: 'large' }, pen: { S: 'p' } },
        })
    })

    /**
     * **No key is dropped, and a pinned key is not special.** A key the clause pins to one tag says
     * the same thing of every member kept, and it stays a key: the field is still a required
     * literal in every member's body, so every item still carries it.
     */
    it('keeps every key, so a one-member result still reads its key', () => {
        const one = extract(
            twoKey,
            object({
                kind: string('pet'),
                size: string('large'),
            }),
        )
        expect(one.item.keys).toEqual(['kind', 'size'])
        const written = one.unsafeEncode({
            kind: 'pet',
            size: 'large',
            pen: 'p',
        })
        // the two discriminators are written, not normalised away, and the item reads back
        expect(written).toEqual({
            M: { kind: { S: 'pet' }, size: { S: 'large' }, pen: { S: 'p' } },
        })
        expect(one.unsafeDecode(written)).toEqual({
            kind: 'pet',
            size: 'large',
            pen: 'p',
        })
    })

    /**
     * **An extraction that keeps nothing is the bottom, and the bottom has one name.** Not an empty
     * dissection, which `dissect` refuses: an empty option list is what a typo produces, so a rule
     * reading it as the bottom would read that accident as intent.
     *
     * Reached through the containment rule rather than through an unknown tag: a tag no member
     * carries is refused at the call, so what is left to keep nothing is a clause the members' own
     * tags do not fit inside.
     */
    it('answers never where the clause keeps no member', () => {
        const spans = union([
            object({ tier: string('gold', 'silver'), n: boolean }),
            object({ tier: string('bronze'), m: boolean }),
        ])
        const none = extract(spans, object({ tier: string('gold') }))
        expect(none.def).toEqual({ kind: 'never' })
        expect(failed(none.encode({} as never))).toBe(true)
    })

    /**
     * A member whose literal spans several tags is kept only where **all** of them lie inside the
     * clause. Keeping it on a one-tag overlap would make the extraction admit a value the clause
     * does not describe, which is why the model's `altsSub` reads containment and not membership.
     */
    it('drops a member whose tags reach outside the clause', () => {
        // a `union` and not an `mdunion`: a dissection refuses a member spanning two tags at a key,
        // because a lookup reaches one member per tag. A union has no such rule, so it is where the
        // containment reading can be seen at all
        const tiers = union([
            object({ tier: string('gold', 'silver'), n: boolean }),
            object({ tier: string('bronze'), m: boolean }),
        ])
        expect(extract(tiers, object({ tier: string('gold') })).def).toEqual({
            kind: 'never',
        })
        expect(
            extract(tiers, object({ tier: string('gold', 'silver') })).def.kind,
        ).toBe('union')
    })
})

/**
 * **The same tag text at two bases is two clauses.**
 *
 * `string('1')` and `decimal('1')` carry the same character and are read from different members;
 * `number(1)` is a third thing again. This is the whole reason a clause value is a codec and not a
 * tag: a tag is text, and text does not say which base it was written at. `Calculus.AltClause`
 * carries `Alts` per key for the same reason, and `altsSub` declines across bases.
 */
describe('a clause is a literal at a base', () => {
    const byBase = union([
        object({ k: string('1'), a: string }),
        object({ k: decimal('1'), b: boolean }),
    ])

    it('keeps the string member for a string literal', () => {
        const kept = extract(byBase, object({ k: string('1') }))
        expect(kept.unsafeEncode({ k: '1', a: 'x' })).toEqual({
            M: { k: { S: '1' }, a: { S: 'x' } },
        })
        expect(failed(kept.encode({ k: '1', b: true } as never))).toBe(true)
    })

    it('keeps the decimal member for a decimal literal, at the same text', () => {
        const kept = extract(byBase, object({ k: decimal('1') }))
        expect(kept.unsafeEncode({ k: '1', b: true } as never)).toEqual({
            M: { k: { N: '1' }, b: { BOOL: true } },
        })
        expect(failed(kept.encode({ k: '1', a: 'x' } as never))).toBe(true)
    })

    /**
     * A base no member carries at the key is the same class of fact as a key no member pins: it
     * describes no member whatever the alternatives are, and it is decidable from the declaration.
     * So it is refused where the foreign key is refused, rather than answered with the empty
     * extraction — which stays the answer where the bases agree and the alternatives do not meet.
     */
    it('refuses a base no member carries at that key', () => {
        // the type catches this one too — `number(1)` decodes to `1` and the members carry `'1'` —
        // so the cast is a caller reaching past it, which is who the runtime refusal is for. What
        // the type cannot catch is `string('1')` against `decimal('1')`: both decode to `'1'`, and
        // the base is exactly what an entity type does not carry
        expect(() =>
            extract(byBase, object({ k: number(1) }) as never),
        ).toThrow(CodecError)
        expect(() =>
            extract(byBase, object({ k: number(1) }) as never),
        ).toThrow(
            /`number` literal under an adapter and no member pins 'k' at that base and adapter/,
        )
    })

    /**
     * The adapter is part of the form, as the base is: a plain literal and a literal under an
     * adapter never match. So a key that the members pin under an adapter alone refuses a plain
     * clause, as the model refuses a clause that is not keyed (`Calculus.AltClause.keyedC`).
     */
    it('refuses a plain clause at a key that the members pin under an adapter alone', () => {
        const toX = held(string('a'), string, {
            encode: (v: string) =>
                v === 'x' ? 'a' : new CodecError(`'${v}' is not 'x'`),
            decode: () => 'x',
        })
        const viaX = union([
            object({ t: toX, k: string('h') }),
            object({ k: string('p') }),
        ])
        expect(() =>
            extract(viaX, object({ t: string('a') }) as never),
        ).toThrow(
            /`string` literal and no member pins 't' at that base and adapter/,
        )
    })

    /**
     * **The slice acts on the structure, so the type it carries follows the members kept.** A union
     * is a pair — the entity type and the member specs — and the filter runs over the specs, which
     * is the only place the base lives. So `string('1')` and `decimal('1')` part company at the
     * type as they do at run time, and the entity type of the result is the kept member's alone.
     */
    it('narrows the entity type to the member kept, and no further', () => {
        const kept = extract(byBase, object({ k: string('1') }))
        // the kept member is exactly what the result carries, asserted both ways with no call
        type Kept = ReturnType<typeof kept.unsafeDecode>
        const read: { readonly k: '1'; readonly a: string } = {} as Kept
        const write: Kept = { k: '1', a: 'x' }
        expect(read).toEqual({})
        expect(kept.unsafeEncode(write)).toEqual({
            M: { k: { S: '1' }, a: { S: 'x' } },
        })
        // and the dropped member is gone from the type, not merely refused at run time
        // @ts-expect-error the decimal member is no longer part of this union
        kept.encode({ k: '1', b: true })
    })

    /**
     * **A base is a pattern too.** The argument is a codec, so `string` says "a key that holds a
     * string", and a member whose key pins a string literal fits it. A member whose key holds
     * another base does not.
     */
    it('keeps the members whose key fits a base codec', () => {
        const kept = extract(byBase, object({ k: string }))
        expect(kept.unsafeEncode({ k: '1', a: 'x' })).toEqual({
            M: { k: { S: '1' }, a: { S: 'x' } },
        })
        expect(failed(kept.encode({ k: '1', b: true } as never))).toBe(true)
        expectTypeOf<ReturnType<typeof kept.unsafeDecode>>().toEqualTypeOf<{
            readonly k: '1'
            readonly a: string
        }>()
    })

    /**
     * **An adapter is part of what a clause names.** The form reads the kind of the held side, and
     * a caller's adapter over `string('a')` has the form of `string('a')` while the member decodes
     * `'x'`. Kept on the form, the extraction decodes a value outside the clause. So a clause keeps
     * a member pinned through an adapter only where the clause sits under the same adapter.
     */
    it('a slice keeps a member pinned through an adapter only against a clause with the same adapter', () => {
        const toX = held(string('a'), string, {
            encode: (v: string) =>
                v === 'x' ? 'a' : new CodecError(`'${v}' is not 'x'`),
            decode: () => 'x',
        })
        const viaX = union([
            object({ t: toX, k: string('h') }),
            object({ t: string('z'), k: string('p') }),
        ])
        // the other member pins `t` at a plain string, so the clause is answered, and it keeps nothing
        const plain = extract(viaX, object({ t: string('a') }))
        expect(plain.def).toEqual({ kind: 'never' })
        const same = extract(viaX, object({ t: toX }))
        expect(
            same.unsafeDecode({ M: { t: { S: 'a' }, k: { S: 'h' } } }),
        ).toEqual({ t: 'x', k: 'h' })

        const one = orThrow(DynamoNumber.from('1'))
        const toText = held(dynamoNumber(one), string, {
            encode: (v: string) =>
                v === 'one' ? one : new CodecError(`'${v}' is not 'one'`),
            decode: () => 'one',
        })
        const viaText = union([
            object({ t: toText, k: string('h') }),
            object({ t: decimal('2'), k: string('p') }),
        ])
        const text = extract(viaText, object({ t: decimal('1') }))
        expect(text.def).toEqual({ kind: 'never' })

        const toTwo = held(dynamoNumber(one), number, {
            encode: (v: number) =>
                v === 2 ? one : new CodecError(`${v} is not 2`),
            decode: () => 2,
        })
        const viaTwo = union([
            object({ t: toTwo, k: string('h') }),
            object({ t: number(3), k: string('p') }),
        ])
        const two = extract(viaTwo, object({ t: number(1) }))
        expect(two.def).toEqual({ kind: 'never' })

        // a library adapter carries one identity for each name, so its members stay kept
        const byDecimal = union([
            object({ t: decimal('1'), k: string('a') }),
            object({ t: decimal('2'), k: string('b') }),
        ])
        expect(
            extract(byDecimal, object({ t: decimal('1') })).unsafeDecode({
                M: { t: { N: '1' }, k: { S: 'a' } },
            }),
        ).toEqual({ t: '1', k: 'a' })
        const byNumber = union([
            object({ t: number(1), k: string('a') }),
            object({ t: number(2), k: string('b') }),
        ])
        expect(
            extract(byNumber, object({ t: number(1) })).unsafeDecode({
                M: { t: { N: '1' }, k: { S: 'a' } },
            }),
        ).toEqual({ t: 1, k: 'a' })
    })
})

describe('the exclusion is the complement of the same clause', () => {
    it('keeps exactly the members the extraction drops, over the same keys', () => {
        const kept = exclude(twoKey, object({ kind: string('pet') }))
        expect(kept.item.keys).toEqual(['kind', 'size'])
        expect(
            kept.unsafeEncode({ kind: 'food', size: 'small', gram: true }),
        ).toEqual({
            M: {
                kind: { S: 'food' },
                size: { S: 'small' },
                gram: { BOOL: true },
            },
        })
        expect(
            failed(
                kept.encode({
                    kind: 'pet',
                    size: 'small',
                    toy: 't',
                } as never),
            ),
        ).toBe(true)
    })

    it('answers never where the clause describes every member', () => {
        expect(
            exclude(twoKey, object({ size: string('small', 'large') })).def,
        ).toEqual({
            kind: 'never',
        })
    })
})

describe('the clause carries no order', () => {
    /**
     * `Calculus.AltClause` is a key set and a function on it, and the host's clause is an object
     * literal for the same reason: an object type has no order on its keys, so two spellings of one
     * clause are one clause.
     */
    it('gives the same result whichever order the keys are written in', () => {
        const one = extract(
            twoKey,
            object({
                kind: string('pet'),
                size: string('large'),
            }),
        )
        const other = extract(
            twoKey,
            object({
                size: string('large'),
                kind: string('pet'),
            }),
        )
        expect(one.def).toEqual(other.def)
    })

    /**
     * **The members shrink with the entity type**, which is what makes a dissected codec
     * deterministic at both levels: a clause that keeps only a member the slice dropped is a type
     * error, where a slice that kept every member would answer with a path over `never`.
     */
    it('drops the member from the slice, so a clause that keeps only that member is a type error', () => {
        const Holder = object({
            x: extract(twoKey, object({ kind: string('pet') })),
        }).item
        expect(
            at(
                Holder,
                (p) =>
                    p.x.narrow({ kind: string('pet'), size: string('large') })
                        .pen,
            ).unsafeEncode('p1'),
        ).toEqual({ S: 'p1' })
        // @ts-expect-error `food` is not a member of the extraction
        at(Holder, (p) => p.x.narrow({ kind: string('food') }))
    })

    it('gives the same members whichever order they were declared in', () => {
        const reversed = mdunion(['kind', 'size'], [food, dog, pet])
        const fromOne = extract(twoKey, object({ kind: string('pet') }))
            .def as {
            readonly options: readonly unknown[]
        }
        const fromOther = extract(reversed, object({ kind: string('pet') }))
            .def as {
            readonly options: readonly unknown[]
        }
        // the same two members, and the declaration order each was written in is what each keeps —
        // a selection reorders nothing
        expect(fromOne.options).toHaveLength(2)
        expect(fromOther.options).toHaveLength(2)
        expect([...fromOther.options].reverse()).toEqual(fromOne.options)
    })
})

describe('a clause key no member pins is refused', () => {
    /**
     * The model cannot have this failure: its clause keys are a subset of the dissection's by the
     * type. Here a clause is an object literal a caller writes, and an empty result is a legitimate
     * answer, so a typo would read as "no member matched" rather than as the typo it is.
     */
    it('names the keys a clause may use', () => {
        expect(() =>
            extract(twoKey, object({ colour: string('red') }) as never),
        ).toThrow(CodecError)
        expect(() =>
            extract(twoKey, object({ colour: string('red') }) as never),
        ).toThrow(/'kind', 'size'/)
    })

    it('refuses a key declared without a literal, which pins nothing', () => {
        // `toy` is declared by one member and is a plain `string`, so no clause can select on it
        expect(() =>
            extract(twoKey, object({ toy: string('t') }) as never),
        ).toThrow(CodecError)
    })

    /**
     * **A `ref` pins no key at the type.** A `ref` carries the term of a name and no literal mark,
     * and the decoded type cannot say whether a literal constructor built the codec: a caller's
     * adapter decodes to a literal type over a term that pins nothing. So the type refuses the key,
     * and the runtime, which resolves the `ref`, still pins it.
     */
    it('refuses at the type a key pinned through a ref, and the runtime pins the key', () => {
        const { Large } = scope({
            Large: object({
                kind: string('pet'),
                size: string('large'),
                colour: ref('Colour'),
            }),
            Colour: string('red', 'blue'),
        })
        const viaRef = mdunion(['kind', 'size'], [pet, Large])
        const kept = extract(
            viaRef,
            // @ts-expect-error the type reads no literal mark through a ref
            object({ colour: string('red', 'blue') }),
        )
        // the runtime answers for a caller who reaches past the type
        expect(
            kept.unsafeEncode({
                kind: 'pet',
                size: 'large',
                colour: 'red',
            } as never),
        ).toEqual({
            M: {
                kind: { S: 'pet' },
                size: { S: 'large' },
                colour: { S: 'red' },
            },
        })
    })

    /**
     * **A union option that a `ref` names pins its literal once the scope binds the name.** The
     * union reads the literals of each option through the `ref`, so the clause keeps the member.
     * The type reads no literal mark through a `ref`, so the type refuses the key.
     */
    it('reads a key whose union option is a ref, because the union then pins its literals', () => {
        const { Large } = scope({
            Large: object({
                kind: string('pet'),
                size: string('large'),
                colour: union([ref('Red'), string('blue')]),
            }),
            Red: string('red'),
        })
        const viaOption = mdunion(['kind', 'size'], [pet, Large])
        const kept = extract(
            viaOption,
            // @ts-expect-error the type reads no literal mark through a ref
            object({ colour: string('red', 'blue') }),
        )
        expect(
            kept.unsafeEncode({
                kind: 'pet',
                size: 'large',
                colour: 'blue',
            } as never),
        ).toEqual({
            M: {
                kind: { S: 'pet' },
                size: { S: 'large' },
                colour: { S: 'blue' },
            },
        })
    })
})

/**
 * **A key is pinned where a literal constructor built its codec**, at the type as at the term. A
 * caller's adapter can decode to a literal type over a term that pins nothing, and the runtime reads
 * the term. So the type reads which constructor built the codec, and not the decoded type.
 */
describe('the type pins a key only where a literal constructor built the codec', () => {
    const tagA = held(string, string('A'), {
        encode: (v: 'A') => v,
        decode: (v: string) =>
            v === 'A' ? ('A' as const) : new CodecError(`'${v}' is not 'A'`),
    })
    const adapterOrB = union([
        object({ k: tagA, a: string }),
        object({ k: string('B'), b: string }),
    ])
    const threeWays = union([
        object({ k: tagA, x: string }),
        object({ k: string('A'), a: string }),
        object({ k: string('B'), b: string }),
    ])

    it('answers a literal that only an adapter decodes to with no member, because a plain clause never meets an adapter', () => {
        const kept = extract(adapterOrB, object({ k: string('A') }))
        expect(kept.def).toEqual({ kind: 'never' })
    })

    it('accepts a literal that a literal constructor pins', () => {
        const kept = extract(adapterOrB, object({ k: string('B') }))
        expect(
            kept.unsafeDecode({ M: { k: { S: 'B' }, b: { S: 'y' } } }),
        ).toEqual({ k: 'B', b: 'y' })
    })

    it('keeps the adapter member in the exclusion, as the runtime keeps it', () => {
        const rest = exclude(threeWays, object({ k: string('A') }))
        // the type of the result admits the row of the adapter member, which the runtime decodes
        const adapterRow: ReturnType<typeof rest.unsafeDecode> = {
            k: 'A',
            x: 'y',
        }
        expect(
            rest.unsafeDecode({ M: { k: { S: 'A' }, x: { S: 'y' } } }),
        ).toEqual(adapterRow)
    })

    it('drops the adapter member from the extraction, as the runtime drops it', () => {
        const kept = extract(threeWays, object({ k: string('A') }))
        const adapterRow: ReturnType<typeof kept.unsafeDecode> = {
            k: 'A',
            // @ts-expect-error the extraction keeps the member with the literal only
            x: 'y',
        }
        expect(
            failed(kept.decode({ M: { k: { S: 'A' }, x: { S: 'y' } } })),
        ).toBe(true)
        expect(adapterRow).toEqual({ k: 'A', x: 'y' })
    })
})

describe('a union of objects has the same slice', () => {
    /**
     * A dissection is a union of objects with a tag table over it, so the operation is one
     * implementation and not two. What the union has and the dissection does not is that a member
     * need not carry a tag at every key — the clause simply describes fewer of them.
     */
    const plain = union([
        object({ kind: string('a'), x: string }),
        object({ kind: string('b'), x: boolean }),
        object({ kind: string('c'), x: boolean, extra: optional(string) }),
    ])

    it('keeps the options the clause describes, and rebuilds a union', () => {
        const kept = extract(plain, object({ kind: string('a', 'b') }))
        expect(kept.def.kind).toBe('union')
        expect(kept.unsafeEncode({ kind: 'a', x: 'v' })).toEqual({
            M: { kind: { S: 'a' }, x: { S: 'v' } },
        })
        expect(failed(kept.encode({ kind: 'c', x: true } as never))).toBe(true)
    })

    /**
     * **A tag no option carries is answered at the type as at run time.** The base matches and the
     * alternatives do not meet: that is a fact about the values, and its answer is the empty
     * extraction (`Calculus.AltClause.extractC`). The model refuses only a clause that it cannot
     * answer (`Calculus.AltClause.keyedC`).
     */
    it('answers a tag no option carries with no member, at the type as at run time', () => {
        const none = extract(plain, object({ kind: string('z') }))
        expect(none.def).toEqual({ kind: 'never' })
    })

    /**
     * **The slice runs the declaration guard again, and it has to.** A sub-selection of a certified
     * union is certified and a sub-selection of an uncertified one is not. The model's slice keeps
     * pairwise compatibility with no certificate (`Calculus.AltClause.pairs_extractC`), and the host
     * certifies, so rebuilding through `union` is how the host keeps it.
     */
    it('rebuilds through the declaration guard rather than assembling the term', () => {
        const kept = exclude(plain, object({ kind: string('c') }))
        // two options with one name set, told apart by their required literals — which stands only
        // because structural admission decides it, and the guard is what says so
        expect(
            kept.unsafeDecode({ M: { kind: { S: 'b' }, x: { BOOL: true } } }),
        ).toEqual({ kind: 'b', x: true })
    })
})

describe('discriminatedUnion slices like the dissection it is', () => {
    const visit = discriminatedUnion('type', [
        object({ type: string('CHECKUP'), petId: string }),
        object({ type: string('SHOT'), vaccine: string }),
    ])

    it('keeps the variant named and still reads its discriminator', () => {
        const only = extract(visit, object({ type: string('CHECKUP') }))
        const written = only.unsafeEncode({ type: 'CHECKUP', petId: 'p1' })
        expect(written).toEqual({
            M: { type: { S: 'CHECKUP' }, petId: { S: 'p1' } },
        })
        expect(only.unsafeDecode(written)).toEqual({
            type: 'CHECKUP',
            petId: 'p1',
        })
        expect(only.item.discriminator).toBe('type')
    })

    it('excludes it and leaves the other', () => {
        const rest = exclude(visit, object({ type: string('CHECKUP') }))
        expect(rest.unsafeEncode({ type: 'SHOT', vaccine: 'v' })).toEqual({
            M: { type: { S: 'SHOT' }, vaccine: { S: 'v' } },
        })
    })
})

/**
 * **A clause at a carrier literal is answered.** The model answers such a clause
 * (`Calculus.AltClause.keyedC` holds), so the type answers it too. A `dynamoNumber` literal decodes
 * a `DynamoNumber` whose type holds the stored text, so the type compares the numerals as the run
 * time does. A `binary` literal decodes a `Uint8Array`, which has no literal type, and a numeral
 * from text that is no literal holds `string`. Where only such values decide a member, the
 * extraction and the exclusion each keep the member: each result type admits every member that the
 * run time keeps, and some that it drops.
 */
describe('a clause at a literal whose carrier is no primitive', () => {
    const one = orThrow(DynamoNumber.from('1'))
    const two = orThrow(DynamoNumber.from('2'))

    it('keeps at a `dynamoNumber` literal exactly the members that the run time keeps', () => {
        const byNumeral = union([
            object({ k: string('a'), n: dynamoNumber(one) }),
            object({ k: string('b'), n: dynamoNumber(two) }),
        ])
        const kept = extract(byNumeral, object({ n: dynamoNumber(one) }))
        expect(kept.unsafeEncode({ k: 'a', n: one })).toEqual({
            M: { k: { S: 'a' }, n: { N: '1' } },
        })
        // @ts-expect-error the run time drops the member at `2`, and the type compares the numerals
        expect(failed(kept.encode({ k: 'b', n: two }))).toBe(true)

        const rest = exclude(byNumeral, object({ n: dynamoNumber(one) }))
        expect(rest.unsafeEncode({ k: 'b', n: two })).toEqual({
            M: { k: { S: 'b' }, n: { N: '2' } },
        })
        // @ts-expect-error the run time drops the member at `1`, and the type compares the numerals
        expect(failed(rest.encode({ k: 'a', n: one }))).toBe(true)
    })

    it('compares two spellings of one number as one numeral, because the type holds the stored text', () => {
        const byNumeral = union([
            object({ k: string('a'), n: dynamoNumber(one) }),
            object({ k: string('b'), n: dynamoNumber(two) }),
        ])
        const kept = extract(
            byNumeral,
            object({
                n: dynamoNumber(orThrow(DynamoNumber.from('1.0'))),
            }),
        )
        expect(kept.unsafeEncode({ k: 'a', n: one })).toEqual({
            M: { k: { S: 'a' }, n: { N: '1' } },
        })
        // @ts-expect-error the run time drops the member at `2`, and the type compares the numerals
        expect(failed(kept.encode({ k: 'b', n: two }))).toBe(true)
    })

    it('answers a clause at a numeral that no member pins, and keeps no member, as the run time does', () => {
        const byNumeral = union([
            object({ k: string('a'), n: dynamoNumber(one) }),
            object({ k: string('b'), n: dynamoNumber(two) }),
        ])
        const none = extract(
            byNumeral,
            object({
                n: dynamoNumber(orThrow(DynamoNumber.from('3'))),
            }),
        )
        expect(none.def).toEqual({ kind: 'never' })
        // @ts-expect-error the run time keeps no member, and the type compares the numerals
        expect(failed(none.encode({ k: 'a', n: one }))).toBe(true)
    })

    it('admits every member that the run time keeps, where the type holds no text for the numeral', () => {
        const spelled: string = '1'
        const byNumeral = union([
            object({ k: string('a'), n: dynamoNumber(one) }),
            object({ k: string('b'), n: dynamoNumber(two) }),
        ])
        const kept = extract(
            byNumeral,
            object({
                n: dynamoNumber(orThrow(DynamoNumber.from(spelled))),
            }),
        )
        expect(kept.unsafeEncode({ k: 'a', n: one })).toEqual({
            M: { k: { S: 'a' }, n: { N: '1' } },
        })
        // the run time drops the member at `2`; the type holds no text for the clause, so it admits it
        const coarse: Parameters<typeof kept.encode>[0] = { k: 'b', n: two }
        expect(failed(kept.encode(coarse))).toBe(true)
    })

    it('answers a clause at a `binary` literal, and its type admits every member that the run time keeps', () => {
        const ab = new Uint8Array([1, 2])
        const cd = new Uint8Array([3, 4])
        const byBytes = union([
            object({ k: string('a'), b: binary(ab) }),
            object({ k: string('b'), b: binary(cd) }),
        ])
        const kept = extract(byBytes, object({ b: binary(ab) }))
        expect(kept.unsafeEncode({ k: 'a', b: ab })).toEqual({
            M: { k: { S: 'a' }, b: { B: ab } },
        })
        // the run time drops the member at other bytes; the type admits it, as it cannot compare bytes
        const coarse: Parameters<typeof kept.encode>[0] = { k: 'b', b: cd }
        expect(failed(kept.encode(coarse))).toBe(true)
    })
})
