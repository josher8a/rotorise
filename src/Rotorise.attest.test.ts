import { attest } from '@ark/attest'
import { describe, it } from 'vitest'
import type { Decoded } from './codec/codec'
import { never, object, opaque, string, union } from './codec/codec'
import { tableEntry } from './Rotorise'

describe('Rotorise Performance Baseline', () => {
    type User = {
        id: string
        orgId: string
        role: 'admin' | 'user' | 'guest'
        metadata: {
            lastLogin: number
            tags: string[]
        }
    }

    const userSchema = tableEntry<User>()({
        PK: [
            ['orgId', (id: string) => `ORG#${id}`],
            ['id', (id: string) => `USER#${id}`],
        ],
        SK: ['role'],
        GSI1PK: [['role', (role: string) => `ROLE#${role}`]],
    })

    it('measures instantiation count for tableEntry', () => {
        // Measure performance of the tableEntry definition
        attest.instantiations([16, 'instantiations'])
    })

    it('measures instantiation count for key generation', () => {
        userSchema.key('PK', { orgId: '123', id: '456' })
        attest.instantiations([16, 'instantiations'])
    })

    it('verifies type outputs with snapshots', () => {
        attest(
            userSchema.key('PK', { orgId: '123', id: '456' }),
        ).type.toString.snap('`ORGID#${string}#ID#${string}`')
        attest(userSchema.key('SK', { role: 'admin' })).type.toString.snap(
            '"ROLE#admin"',
        )
    })

    describe('Error Diagnostics', () => {
        it('reports error for invalid schema key', () => {
            const invalidSchema = tableEntry<User>()({
                // @ts-expect-error
                INVALID: 123,
            })
            attest(
                invalidSchema.infer.INVALID,
            ).type.toString.snap(`  | ErrorMessage<"Invalid schema definition">
  | undefined`)
        })

        it('reports error for invalid top-level key in .key()', () => {
            attest(() =>
                // @ts-expect-error
                userSchema.key('NON_EXISTENT', { id: '123' }),
            ).throws.snap('RotoriseError: Key NON_EXISTENT not found in schema')
        })

        it('reports error for invalid Spec type', () => {
            const invalidSchema = tableEntry<User>()({
                // @ts-expect-error
                BAD_SPEC: { invalid: 'logic' },
            })
            attest(
                invalidSchema.infer.BAD_SPEC,
            ).type.toString.snap(`  | ErrorMessage<"Invalid schema definition">
  | undefined`)
        })
    })
})

/**
 * **The refusal a caller reads, pinned as the type it is.**
 *
 * A refusal that lands at compile time travels on its *message* alone — there is no value, no
 * stack and no log line, so the words are the whole of what the caller gets. The run-time test in
 * `codec.union.spec.ts` asserts that such a union throws; nothing asserted what the type says
 * until here, and the two failures are not interchangeable: the type is the one a typed caller
 * meets, and it was giving advice that does not apply.
 */
describe('the union refusals a caller reads at compile time', () => {
    /**
     * `opaque` admits every value the other options admit, so no value selects between them and
     * the others can never be chosen. **A discriminator does not fix it and no ranking resolves
     * it** — the option has to go, which is what this message has to say.
     *
     * It reads back as `unknown`, so the overlap clause would otherwise fire and offer the
     * discriminator advice. The order of the clauses is what this pins.
     */
    it('names the option to remove, rather than offering a discriminator', () => {
        attest(() =>
            // @ts-expect-error the clause under test
            union([opaque, string]),
        ).type.errors.snap(
            "Argument of type '[AttributeCodec<unknown, AttributeValue> & { readonly def: { readonly kind: \"opaq\"; }; } & ((numbers?: Numbers | undefined) => OpaqueCodec), StringCodec]' is not assignable to parameter of type 'readonly [AttributeCodec<unknown, AttributeValue> & { readonly def: { readonly kind: \"opaq\"; }; } & ((numbers?: Numbers | undefined) => OpaqueCodec), StringCodec] & ErrorMessage<...>'.Property '[errorMessage]' is missing in type '[AttributeCodec<unknown, AttributeValue> & { readonly def: { readonly kind: \"opaq\"; }; } & ((numbers?: Numbers | undefined) => OpaqueCodec), StringCodec]' but required in type 'ErrorMessage<\"[union] one option is `opaque`, which admits every value the others admit — so no value can select between them and the others can never be chosen. Remove the `opaque` option; a discriminator does not fix this\">'.",
        )
    })

    /**
     * **The same rule two widths narrower**, and the clause order is what this pins: a literal is
     * assignable to its base, so the overlap clause would fire and offer a discriminator, which is
     * the advice that cannot help. `Restricting` sits ahead of it and names the option to remove.
     */
    it('names a literal inside its own base as the option to remove', () => {
        attest(() =>
            // @ts-expect-error the clause under test
            union([string, string('A')]),
        ).type.errors.snap(
            'Argument of type \'[StringCodec, ConstantCodec<"A", Attribute<"S">>]\' is not assignable to parameter of type \'readonly [StringCodec, ConstantCodec<"A", Attribute<"S">>] & ErrorMessage<"[union] option 1 inside option 0: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this">\'.Property \'[errorMessage]\' is missing in type \'[StringCodec, ConstantCodec<"A", Attribute<"S">>]\' but required in type \'ErrorMessage<"[union] option 1 inside option 0: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this">\'.',
        )
    })

    /** …and the same at one spelling out: a set of a literal inside the plain set at its base. */
    it('names a set of a literal inside the plain set at its base', () => {
        attest(() =>
            // @ts-expect-error the clause under test
            union([string.set(), string.set('a', 'b')]),
        ).type.errors.snap(
            'Argument of type \'[AttributeCodec<ReadonlySet<string>, SS>, AttributeCodec<ReadonlySet<"a" | "b">, SS>]\' is not assignable to parameter of type \'readonly [AttributeCodec<ReadonlySet<string>, SS>, AttributeCodec<ReadonlySet<"a" | "b">, SS>] & ErrorMessage<"[union] option 1 inside option 0: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this">\'.Property \'[errorMessage]\' is missing in type \'[AttributeCodec<ReadonlySet<string>, SS>, AttributeCodec<ReadonlySet<"a" | "b">, SS>]\' but required in type \'ErrorMessage<"[union] option 1 inside option 0: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this">\'.',
        )
    })

    /**
     * **`never` reads back as `never`**, which is what makes the containment clause fire on it
     * without a row of its own: `[never] extends [X]` for every `X`, and no `X` extends `never`.
     */
    it('reads never back as never', () => {
        attest<never>({} as Decoded<typeof never>)
    })

    /**
     * **The same rule at its widest on the other side.** `opaque` admits every value, so every
     * other option is inside it; `never` admits none, so it is inside every other option. Both
     * are the containment clause and both name the option to remove.
     */
    it('names never as the option to remove', () => {
        attest(() =>
            // @ts-expect-error the clause under test
            union([string, never]),
        ).type.errors.snap(
            'Argument of type \'[StringCodec, AttributeCodec<never, never> & { readonly def: { readonly kind: "never"; }; }]\' is not assignable to parameter of type \'readonly [StringCodec, AttributeCodec<never, never> & { readonly def: { readonly kind: "never"; }; }] & ErrorMessage<"[union] option 1 inside option 0: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this">\'.Property \'[errorMessage]\' is missing in type \'[StringCodec, AttributeCodec<never, never> & { readonly def: { readonly kind: "never"; }; }]\' but required in type \'ErrorMessage<"[union] option 1 inside option 0: every value the narrower option admits, the wider one admits too, so no value can ever select it. Remove the narrower option; a discriminator does not fix this">\'.',
        )
    })

    /** And a pair that is merely ambiguous still gets the advice that does apply. */
    it('still offers a discriminator where a discriminator is the answer', () => {
        attest(() =>
            // @ts-expect-error two object options declaring the same names
            union([object({ a: string }), object({ a: string })]),
        ).type.errors.snap(
            'Argument of type \'[ObjectCodec<{ readonly a: StringCodec; }, "refuse">, ObjectCodec<{ readonly a: StringCodec; }, "refuse">]\' is not assignable to parameter of type \'readonly [ObjectCodec<{ readonly a: StringCodec; }, "refuse">, ObjectCodec<{ readonly a: StringCodec; }, "refuse">] & ErrorMessage<"[untagged] variants 0 and 1 can hold the same attributes and cannot be told apart; give them a discriminator, or a literal field that tells them apart">\'.Property \'[errorMessage]\' is missing in type \'[ObjectCodec<{ readonly a: StringCodec; }, "refuse">, ObjectCodec<{ readonly a: StringCodec; }, "refuse">]\' but required in type \'ErrorMessage<"[untagged] variants 0 and 1 can hold the same attributes and cannot be told apart; give them a discriminator, or a literal field that tells them apart">\'.',
        )
    })
})
