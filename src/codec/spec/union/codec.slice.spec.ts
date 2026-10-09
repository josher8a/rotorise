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
import { describe, expect, it } from 'vitest'
import { type Attribute, DynamoNumber } from '../../attribute'
import {
    binary,
    boolean,
    CodecError,
    decimal,
    discriminatedUnion,
    dynamoNumber,
    held,
    lazy,
    mdunion,
    number,
    object,
    optional,
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
        const small = twoKey.extract({ size: string('small', 'large') })
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
        const pets = twoKey.extract({ kind: string('pet') })
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
        const one = twoKey.extract({
            kind: string('pet'),
            size: string('large'),
        })
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
        const none = spans.extract({ tier: string('gold') })
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
        expect(tiers.extract({ tier: string('gold') }).def).toEqual({
            kind: 'never',
        })
        expect(tiers.extract({ tier: string('gold', 'silver') }).def.kind).toBe(
            'union',
        )
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
        const kept = byBase.extract({ k: string('1') })
        expect(kept.unsafeEncode({ k: '1', a: 'x' })).toEqual({
            M: { k: { S: '1' }, a: { S: 'x' } },
        })
        expect(failed(kept.encode({ k: '1', b: true } as never))).toBe(true)
    })

    it('keeps the decimal member for a decimal literal, at the same text', () => {
        const kept = byBase.extract({ k: decimal('1') })
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
        expect(() => byBase.extract({ k: number(1) } as never)).toThrow(
            CodecError,
        )
        expect(() => byBase.extract({ k: number(1) } as never)).toThrow(
            /`number` literal under an adapter and no member pins 'k' at that base and adapter/,
        )
    })

    /**
     * The adapter is part of the form, as the base is: a plain literal and a literal under an
     * adapter never match. So a key that the members pin under an adapter alone refuses a plain
     * clause, as the model refuses a clause that is not keyed (`Calculus.AltClause.keyed`).
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
        expect(() => viaX.extract({ t: string('a') } as never)).toThrow(
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
        const kept = byBase.extract({ k: string('1') })
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

    it('refuses a clause value that is no literal at all', () => {
        expect(() =>
            // @ts-expect-error a bare tag says nothing about the base
            byBase.extract({ k: '1' }),
        ).toThrow(CodecError)
        expect(() =>
            // @ts-expect-error the plain base admits more than a literal does
            byBase.extract({ k: string }),
        ).toThrow(/is not a literal codec/)
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
        const plain = viaX.extract({ t: string('a') })
        expect(plain.def).toEqual({ kind: 'never' })
        const same = viaX.extract(
            // @ts-expect-error a clause pins a literal at the type, and `toX` decodes `string`
            { t: toX },
        )
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
        const text = viaText.extract({ t: decimal('1') })
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
        const two = viaTwo.extract({ t: number(1) })
        expect(two.def).toEqual({ kind: 'never' })

        // a library adapter carries one identity for each name, so its members stay kept
        const byDecimal = union([
            object({ t: decimal('1'), k: string('a') }),
            object({ t: decimal('2'), k: string('b') }),
        ])
        expect(
            byDecimal
                .extract({ t: decimal('1') })
                .unsafeDecode({ M: { t: { N: '1' }, k: { S: 'a' } } }),
        ).toEqual({ t: '1', k: 'a' })
        const byNumber = union([
            object({ t: number(1), k: string('a') }),
            object({ t: number(2), k: string('b') }),
        ])
        expect(
            byNumber
                .extract({ t: number(1) })
                .unsafeDecode({ M: { t: { N: '1' }, k: { S: 'a' } } }),
        ).toEqual({ t: 1, k: 'a' })
    })
})

describe('the exclusion is the complement of the same clause', () => {
    it('keeps exactly the members the extraction drops, over the same keys', () => {
        const kept = twoKey.exclude({ kind: string('pet') })
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
        expect(twoKey.exclude({ size: string('small', 'large') }).def).toEqual({
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
        const one = twoKey.extract({
            kind: string('pet'),
            size: string('large'),
        })
        const other = twoKey.extract({
            size: string('large'),
            kind: string('pet'),
        })
        expect(one.def).toEqual(other.def)
    })

    /**
     * **The members shrink with the entity type**, which is what makes a dissected codec
     * deterministic at both levels: a clause that keeps only a member the slice dropped is a type
     * error, where a slice that kept every member would answer with a path over `never`.
     */
    it('drops the member from the slice, so a clause that keeps only that member is a type error', () => {
        const Holder = object({
            x: twoKey.extract({ kind: string('pet') }),
        }).item
        expect(
            Holder.at(
                (p) =>
                    p.x.narrow({ kind: string('pet'), size: string('large') })
                        .pen,
            ).unsafeEncode('p1'),
        ).toEqual({ S: 'p1' })
        // @ts-expect-error `food` is not a member of the extraction
        Holder.at((p) => p.x.narrow({ kind: string('food') }))
    })

    it('gives the same members whichever order they were declared in', () => {
        const reversed = mdunion(['kind', 'size'], [food, dog, pet])
        const fromOne = twoKey.extract({ kind: string('pet') }).def as {
            readonly options: readonly unknown[]
        }
        const fromOther = reversed.extract({ kind: string('pet') }).def as {
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
            twoKey.extract({ colour: string('red') } as never),
        ).toThrow(CodecError)
        expect(() =>
            twoKey.extract({ colour: string('red') } as never),
        ).toThrow(/'kind', 'size'/)
    })

    it('refuses a key declared without a literal, which pins nothing', () => {
        // `toy` is declared by one member and is a plain `string`, so no clause can select on it
        expect(() => twoKey.extract({ toy: string('t') } as never)).toThrow(
            CodecError,
        )
    })

    it('reads a key pinned through a thunk, because the thunk resolves to the literal', () => {
        const colour = string('red', 'blue')
        const viaThunk = mdunion(
            ['kind', 'size'],
            [
                pet,
                object({
                    kind: string('pet'),
                    size: string('large'),
                    colour: lazy(() => colour),
                }),
            ],
        )
        const kept = viaThunk.extract({ colour: string('red', 'blue') })
        expect(
            kept.encode({ kind: 'pet', size: 'large', colour: 'red' }),
        ).toEqual({
            M: {
                kind: { S: 'pet' },
                size: { S: 'large' },
                colour: { S: 'red' },
            },
        })
    })

    it('reads a key whose union option is a thunk, because the union then pins its literals', () => {
        const red = string('red')
        const viaOption = mdunion(
            ['kind', 'size'],
            [
                pet,
                object({
                    kind: string('pet'),
                    size: string('large'),
                    colour: union([lazy(() => red), string('blue')]),
                }),
            ],
        )
        const kept = viaOption.extract({ colour: string('red', 'blue') })
        expect(
            kept.encode({ kind: 'pet', size: 'large', colour: 'blue' }),
        ).toEqual({
            M: {
                kind: { S: 'pet' },
                size: { S: 'large' },
                colour: { S: 'blue' },
            },
        })
    })

    /**
     * **A thunk with explicit type arguments pins no key at the type.** A recursive declaration
     * writes its type arguments, because the codec of the thunk is not declared yet. The arguments
     * state the decoded type alone, and the decoded type cannot say whether a literal constructor
     * built the codec: a caller's adapter decodes to a literal type over a term that pins nothing.
     * So the type refuses the key, and the runtime, which resolves the thunk, still pins it.
     */
    it('refuses at the type a key pinned through a thunk with explicit type arguments', () => {
        const colour = string('red', 'blue')
        const explicit = mdunion(
            ['kind', 'size'],
            [
                pet,
                object({
                    kind: string('pet'),
                    size: string('large'),
                    colour: lazy<'red' | 'blue', Attribute<'S'>>(() => colour),
                }),
            ],
        )
        const kept = explicit.extract(
            // @ts-expect-error the type reads no literal constructor through the explicit form
            { colour: string('red', 'blue') },
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
        const kept = adapterOrB.extract({ k: string('A') })
        expect(kept.def).toEqual({ kind: 'never' })
    })

    it('accepts a literal that a literal constructor pins', () => {
        const kept = adapterOrB.extract({ k: string('B') })
        expect(
            kept.unsafeDecode({ M: { k: { S: 'B' }, b: { S: 'y' } } }),
        ).toEqual({ k: 'B', b: 'y' })
    })

    it('keeps the adapter member in the exclusion, as the runtime keeps it', () => {
        const rest = threeWays.exclude({ k: string('A') })
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
        const kept = threeWays.extract({ k: string('A') })
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
        const kept = plain.extract({ kind: string('a', 'b') })
        expect(kept.def.kind).toBe('union')
        expect(kept.unsafeEncode({ kind: 'a', x: 'v' })).toEqual({
            M: { kind: { S: 'a' }, x: { S: 'v' } },
        })
        expect(failed(kept.encode({ kind: 'c', x: true } as never))).toBe(true)
    })

    /**
     * **A tag no option carries is answered at the type as at run time.** The base matches and the
     * alternatives do not meet: that is a fact about the values, and its answer is the empty
     * extraction (`Calculus.AltClause.extract`). The model refuses only a clause that it cannot
     * answer (`Calculus.AltClause.keyed`).
     */
    it('answers a tag no option carries with no member, at the type as at run time', () => {
        const none = plain.extract({ kind: string('z') })
        expect(none.def).toEqual({ kind: 'never' })
    })

    /**
     * **The slice runs the declaration guard again, and it has to.** A sub-selection of a certified
     * union is certified and a sub-selection of an uncertified one is not. The model's slice keeps
     * pairwise compatibility with no certificate (`Calculus.pairwiseCompat_extract`), and the host
     * certifies, so rebuilding through `union` is how the host keeps it.
     */
    it('rebuilds through the declaration guard rather than assembling the term', () => {
        const kept = plain.exclude({ kind: string('c') })
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
        const only = visit.extract({ type: string('CHECKUP') })
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
        const rest = visit.exclude({ type: string('CHECKUP') })
        expect(rest.unsafeEncode({ type: 'SHOT', vaccine: 'v' })).toEqual({
            M: { type: { S: 'SHOT' }, vaccine: { S: 'v' } },
        })
    })
})

/**
 * **A literal whose carrier has no literal type is answered, and coarsely.** A `dynamoNumber`
 * literal decodes a `DynamoNumber` and a `binary` literal a `Uint8Array`, so the type reads the form
 * of the clause and not its alternatives. The model answers such a clause (`Calculus.AltClause.keyed`
 * holds), so the type answers it too. Where only the alternatives decide a member, the extraction
 * and the exclusion each keep the member: each result type admits every member that the run time
 * keeps, and some that it drops. A literal type for the numeral is a later pass.
 */
describe('a clause at a literal whose carrier has no literal type', () => {
    const one = orThrow(DynamoNumber.from('1'))
    const two = orThrow(DynamoNumber.from('2'))

    it('answers a clause at a `dynamoNumber` literal, and its type admits every member that the run time keeps', () => {
        const byNumeral = union([
            object({ k: string('a'), n: dynamoNumber(one) }),
            object({ k: string('b'), n: dynamoNumber(two) }),
        ])
        const kept = byNumeral.extract({ n: dynamoNumber(one) })
        expect(kept.unsafeEncode({ k: 'a', n: one })).toEqual({
            M: { k: { S: 'a' }, n: { N: '1' } },
        })
        // the run time drops the member at `2`; the type cannot compare the numerals, so it admits it
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
        const kept = byBytes.extract({ b: binary(ab) })
        expect(kept.unsafeEncode({ k: 'a', b: ab })).toEqual({
            M: { k: { S: 'a' }, b: { B: ab } },
        })
        // the run time drops the member at other bytes; the type admits it, as it cannot compare bytes
        const coarse: Parameters<typeof kept.encode>[0] = { k: 'b', b: cd }
        expect(failed(kept.encode(coarse))).toBe(true)
    })
})
