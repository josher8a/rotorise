/**
 * Attributes a spec does not declare.
 *
 * Some entity types are genuinely open — `{ vendorId } & { [Key in string]?: string | number |
 * boolean }` — so their extra keys are the domain rather than a surprise, and a codec that dropped
 * them would be wrong about what the entity *is*. It is the one thing total coverage cannot say.
 */
import { describe, expect, it } from 'vitest'
import { tableEntry } from '../../../Rotorise'
import type { AnyCodec } from '../../codec'
import {
    CodecError,
    codecOfTerm,
    object,
    opaque,
    optional,
    refine,
    string,
    termOf,
    withLegacyRead,
} from '../../codec'
import { checkMembersStable, checkRoundTrip } from '../../testing'

type VendorMeta = {
    readonly vendorId: 'ACME' | 'GLOBEX'
} & { [key: string]: string | number | boolean | undefined }

/**
 * The provider's own keys, whatever they are — numbers included, so `lossy` is stated.
 *
 * Refined rather than passed straight through, and the `as never` this replaces was hiding why.
 * `opaque` decodes to `unknown`, and this entity says its extra values are scalars — so the codec
 * cannot claim to produce what the index signature promises. An {@link AttributeCodec} carries its
 * value type in `encode`'s parameter *and* `decode`'s result, which makes it invariant, so the
 * mismatch is real rather than a variance technicality. Where an entity is honestly open —
 * `{ [key: string]: unknown }` — `opaque('lossy')` fits with nothing around it.
 */
const scalar = refine(
    opaque('lossy'),
    (value): value is string | number | boolean | undefined =>
        value === undefined ||
        typeof value === 'string' ||
        typeof value === 'number' ||
        typeof value === 'boolean',
    {
        describe: 'a string, number or boolean',
        // `opaque` also generates lists, maps and sets, which this rejects; saying what one looks
        // like keeps the property run the size it claims to be
        arbitrary: (rng) =>
            [undefined, 'a', '', 0, 1, -1, 1.5, true, false][
                Math.floor(rng() * 9)
            ] as string | number | boolean | undefined,
    },
)

const Meta = object({ vendorId: string('ACME', 'GLOBEX') }, [
    string,
    optional(scalar),
]).item

describe('an open type', () => {
    const meta: VendorMeta = {
        vendorId: 'ACME',
        holdId: 'lock-1',
        expiresIn: 30,
        renewable: true,
    }

    it('carries the keys the spec does not name', () => {
        const item = Meta.unsafeEncode(meta)
        expect(item.vendorId).toEqual({ S: 'ACME' })
        expect(item.holdId).toEqual({ S: 'lock-1' })
        expect(item.expiresIn).toEqual({ N: '30' })
        expect(item.renewable).toEqual({ BOOL: true })
    })

    it('round-trips them', () => {
        expect(Meta.unsafeDecode(Meta.unsafeEncode(meta))).toEqual(meta)
    })

    it('keeps them across a read-modify-write', () => {
        expect(() =>
            checkMembersStable(Meta, [Meta.unsafeEncode(meta)]),
        ).not.toThrow()
    })

    it('decodes an attribute no version of the code has ever seen', () => {
        const fromTheFuture = {
            ...Meta.unsafeEncode(meta),
            addedLastWeek: { S: 'by another service' },
        }
        expect(Meta.unsafeDecode(fromTheFuture).addedLastWeek).toBe(
            'by another service',
        )
    })
})

describe('an open object entry', () => {
    it('refuses a required wildcard because it means at least one matching key', () => {
        expect(() =>
            // @ts-expect-error a wildcard cannot require an unnamed attribute
            object([string, scalar]),
        ).toThrow(
            /an open key entry must be optional, because a required wildcard means at least one matching key/,
        )
        expect(() =>
            // @ts-expect-error a stand-in marks a required object slot
            object([
                string,
                withLegacyRead({
                    current: string,
                    whenMissing: 'current',
                }),
            ]),
        ).toThrow(
            /an open key entry must be optional, because a required wildcard means at least one matching key/,
        )
    })

    it('allows a required literal key set', () => {
        const Declared = object([string('current'), string]).item
        expect(Declared.unsafeDecode({ current: { S: 'v1' } })).toEqual({
            current: 'v1',
        })
    })
})

describe('a strict object', () => {
    const Closed = object({ id: string }).item

    it('refuses an undeclared attribute on the way in', () => {
        expect(() =>
            Closed.unsafeDecode({ id: { S: 'w1' }, retired: { S: 'x' } }),
        ).toThrow(CodecError)
    })

    it('refuses a read-modify-write that contains an undeclared attribute', () => {
        const stored = { id: { S: 'w1' }, retired: { S: 'x' } }
        expect(() => Closed.unsafeEncode(Closed.unsafeDecode(stored))).toThrow(
            CodecError,
        )
    })

    it('refuses an undeclared attribute in a patch', () => {
        expect(() =>
            Closed.unsafeEncodePartial({ retired: 'x' } as never),
        ).toThrow(CodecError)
    })

    it('is what the member law is told, rather than left to infer', () => {
        // the undeclared attribute refuses on the way in, so no re-encode can lose it
        expect(() =>
            checkMembersStable(Closed, [
                { id: { S: 'w1' }, retired: { S: 'x' } },
            ]),
        ).toThrow(CodecError)
    })
})

describe("'refuse', for a service that owns its table", () => {
    const Strict = object({ id: string }).item

    /**
     * **Pins wording no law has, deliberately.** The refusal is asserted as a `CodecError` beside
     * it; what the regex adds is the diagnostic, which is this test's subject. Here it is that `'refuse'`
     * says the schema and the data have *drifted*.
     */
    it('reports drift instead of ignoring it', () => {
        expect(() =>
            Strict.unsafeDecode({ id: { S: 'w1' }, addedLastWeek: { S: 'x' } }),
        ).toThrow(CodecError)
        expect(() =>
            Strict.unsafeDecode({ id: { S: 'w1' }, addedLastWeek: { S: 'x' } }),
        ).toThrow(/the schema and the data have drifted apart/)
    })

    it('is untroubled by an item that carries exactly what it declares', () => {
        expect(Strict.unsafeDecode({ id: { S: 'w1' } })).toEqual({ id: 'w1' })
        checkRoundTrip(Strict, { count: 50, seed: 1 })
    })
})

/**
 * **The policy, in the term.**
 *
 * `Term` is this library's own abstract syntax, and `src/codec/lean.ts` reads it to reconstruct the
 * equivalent term in `formal/`. The body records the model's open block: absent for the closed
 * body, and the block's term where the body is open.
 *
 * `.item.rest` did carry the policy the whole time, so this was reachable from a *top-level* codec.
 * It is not reachable from a definition walk, which is the only surface a consumer has once it has
 * descended into a nested `object(...)`: `def.of` is typed `Record<string, AnyCodec>`, and `AnyCodec`
 * has no `item`. The last test here is that walk.
 */
describe('the rest policy a definition records', () => {
    it('records the strict policy', () => {
        const def = object({ id: string }).def
        expect(def.kind).toBe('object')
        expect(def.kind === 'object' && def.body.rest).toBe(undefined)
    })

    /**
     * The policy is recorded as the rest codec's **term**, and identity is what is asserted.
     *
     * A definition's children are terms, so the third policy is `scalar`'s term rather than
     * `scalar`. What the rule needs is unchanged and is what this checks: the two states are
     * two values, and the open one is enough to rebuild the codec a consumer must run. `codecOfTerm`
     * memoises on the frozen term, so rebuilding it runs what was declared.
     *
     * The rebuilt codec is not `scalar` itself, and that is the design rather than a loss:
     * `refine` returns `setCapable(codecOfTerm(...))`, so `.set` is a capability sitting *above*
     * the term's codec. What the walk owes is the behaviour, which is what the second line asks.
     */
    it('records a rest codec as its term, not as a flag', () => {
        const def = object({ vendorId: string('ACME', 'GLOBEX') }, [
            string,
            optional(scalar),
        ]).def
        expect(def).toMatchObject({ kind: 'object' })
        expect(def.kind === 'object' && def.body.rest).toBe(scalar.def)
        expect(codecOfTerm(termOf(scalar)).encode('x' as never)).toEqual(
            scalar.encode('x'),
        )
    })

    /**
     * The refusal that only a cast can reach, and it had no test.
     *
     * `termOf` is the one place a child is taken from something a caller handed over, and since a
     * codec's definition became a term the checker refuses a field before the call is written. That
     * makes the branch look dead and it is not: a brand is not a proof and a cast defeats a brand.
     * Deleting the branch keeps the whole suite green and `tsc` alone objects, which is how this test
     * came to be written — the refusal is load bearing for the type and was unpinned for behaviour.
     */
    it('refuses a field where a term is taken, reached past a cast', () => {
        expect(() => termOf(optional(string) as unknown as AnyCodec)).toThrow(
            /marks a \*field\*/,
        )
        expect(() =>
            termOf(
                withLegacyRead({
                    current: string,
                    whenMissing: 'x',
                }) as unknown as AnyCodec,
            ),
        ).toThrow(/this position takes a term/)
    })

    it('agrees with the policy the item codec reports', () => {
        const closed = object({ id: string })
        expect(closed.item.rest).toBe('refuse')
        expect(closed.def.kind === 'object' && closed.def.body.rest).toBe(
            undefined,
        )
        const open = object({ id: string }, [string, optional(string)])
        expect(open.def.kind === 'object' && open.def.body.rest).toBe(
            termOf(open.item.rest),
        )
    })

    /**
     * The defect, as a consumer would have met it: two specs differing only in a *nested* policy.
     *
     * A definition walk hands out a term, and a term has no `.item`, so the term alone must say
     * whether the nested body is closed.
     *
     * The walk is one step shorter than it was: a field holds the child's *term*, so descending
     * into a nested object is a field lookup rather than a field lookup and then a `.def` read.
     */
    it('survives a walk into a nested object, where `.item` is not offered', () => {
        const restOfNested = (codec: AnyCodec): unknown => {
            const def = codec.def
            if (def?.kind !== 'object') throw new Error('not an object')
            const innerDef = def.body.fields.inner?.t
            if (innerDef?.kind !== 'object') throw new Error('not nested')
            return innerDef.body.rest
        }

        expect(restOfNested(object({ inner: object({ id: string }) }))).toBe(
            undefined,
        )
    })
})

/**
 * Reaching a rest policy from `tableEntry`.
 *
 * `tableEntry` used to take a spec and build the codec itself, with every option at its default —
 * so the policy an open type needs could not be reached from the entry point a repository uses. It
 * takes a built codec now, which carries its own options and needs no signature change here for
 * whatever `item` grows next.
 */
describe('a built codec passed to tableEntry', () => {
    /**
     * The closed part, named on its own so the key schema can be checked against it.
     *
     * An entity with a string index signature states no attribute name `keyof` can find, so a
     * schema checked against `Meta` is checked against nothing — `['nonsense']` would be as valid
     * as `['id']`. `MetaKeys` is the type `Meta` was built from, so naming it costs nothing.
     */
    type MetaKeys = { TAG: 'META'; id: string }
    type Meta = MetaKeys & { [key: string]: unknown }

    const Attributes = object({ TAG: string('META'), id: string }, [
        string,
        optional(opaque('lossy')),
    ]).item
    it('round-trips the attributes the spec does not name', () => {
        // generation reaches the rest policy now, so this exercises the open part and not only the
        // closed one — which is what the definition recording `rest` bought
        checkRoundTrip(Attributes, { count: 200, seed: 20260828 })
    })

    const Entry = tableEntry<Meta, never, MetaKeys>()(
        { PK: ['id'], SK: ['TAG'] },
        { codec: Attributes },
    )

    it('checks a key component against the attributes the entity states', () => {
        const _typo = () =>
            tableEntry<Meta, never, MetaKeys>()(
                // @ts-expect-error there is no `nonsense` attribute to build a key from
                { PK: ['nonsense'] },
                { codec: Attributes },
            )
        expect(typeof _typo).toBe('function')
    })
    const meta = { TAG: 'META', id: 'b', extra: 'kept', n: 3 } as Meta

    it('carries the policy the spec form could not express', () => {
        const item = Entry.unsafeToItem(meta)
        expect(item.extra).toEqual({ S: 'kept' })
        expect(item.n).toEqual({ N: '3' })
    })

    it('still computes the keys', () => {
        const item = Entry.unsafeToItem(meta)
        expect(item.PK).toEqual({ S: 'ID#b' })
        expect(item.SK).toEqual({ S: 'TAG#META' })
    })

    it('keeps the computed keys out of the entity', () => {
        // a rest policy sweeps up what the spec does not declare, and the keys are not declared —
        // so they are removed before decoding rather than left to be swept in
        const back = Entry.unsafeFromItem(Entry.unsafeToItem(meta))
        expect(back).toEqual(meta)
        expect(back).not.toHaveProperty('PK')
        expect(back).not.toHaveProperty('SK')
    })

    it('takes a plain spec too, which is the short form', () => {
        type Closed = { id: string; name: string }
        const Short = tableEntry<Closed>()(
            { PK: ['id'] },
            {
                codec: { id: string, name: string },
            },
        )
        expect(Short.unsafeToItem({ id: 'a', name: 'n' })).toEqual({
            id: { S: 'a' },
            name: { S: 'n' },
            PK: { S: 'ID#a' },
        })
    })
})
