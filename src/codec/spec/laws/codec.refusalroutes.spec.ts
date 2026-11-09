/**
 * A refusal is one value, whatever route reaches it.
 *
 * A refusal states where the item went wrong (`path`) and why (`reason`). Two routes that refuse one
 * value must state one refusal, or a caller reads a different answer from a write and from a patch.
 * Each law below compares the whole refusal, not only whether a route refused:
 *
 * - **place**: a foreign value at one name gives a refusal at that name. An absent name and an
 *   undeclared name are refusals of the item itself, so their path is empty, as the error path spec
 *   states.
 * - **route**: `encode` and `encodePartial` refuse one foreign value with one path and one reason.
 *   A patch of a union carries the tags of its variant, because the tags choose the variant.
 * - **value**: each route returns a refusal, and throws nothing.
 * - **names**: a codec whose names are names of `Object.prototype` answers each row as the same codec
 *   with plain names.
 *
 * The pool holds one codec per constructor that refuses a name or a tag, and the codecs of the
 * refusals that a review found. It is no random draw of codecs.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    CodecError,
    discriminatedUnion,
    held,
    item,
    mdunion,
    number,
    object,
    optional,
    string,
} from '../../codec'
import { arbitraryOf, rngFrom } from '../../testing'

type Routes = {
    readonly encode: (value: unknown) => unknown
    readonly encodePartial: (value: unknown) => unknown
    readonly decode: (row: unknown) => unknown
}
type Entry = { readonly codec: Routes; readonly tags: readonly string[] }

const routes = (codec: unknown): Routes => codec as Routes

const Dog = held(string('D'), string('dog'), {
    encode: (_: 'dog') => 'D' as const,
    decode: (_: 'D') => 'dog' as const,
})
const only = (tag: string, text: 'D' | 'C') =>
    held(string(text), string, {
        encode: (v: string) =>
            v === tag ? text : new CodecError(`only ${tag}`),
        decode: () => tag,
        arbitrary: () => tag,
    })

const pool: Record<string, Entry> = {
    'an object with a literal, a list and an optional name': {
        codec: routes(
            item(
                object({
                    name: string,
                    age: number,
                    tags: array(string),
                    kind: string('a', 'b'),
                    nick: optional(string),
                }),
            ),
        ),
        tags: [],
    },
    'a discriminated union': {
        codec: routes(
            item(
                discriminatedUnion('species', [
                    object({ species: string('cat'), name: string }),
                    object({ species: string('dog'), name: string }),
                ]),
            ),
        ),
        tags: ['species'],
    },
    'a tag under a caller adapter': {
        codec: routes(
            item(
                discriminatedUnion('kind', [
                    object({ kind: Dog, bark: string }),
                    object({ kind: string('cat'), lives: number }),
                ]),
            ),
        ),
        tags: ['kind'],
    },
    'a tag that two adapters refuse': {
        codec: routes(
            item(
                discriminatedUnion('kind', [
                    object({ kind: only('dog', 'D'), bark: string }),
                    object({ kind: only('cat', 'C'), lives: number }),
                ] as never),
            ),
        ),
        tags: ['kind'],
    },
    'a union of two tags': {
        codec: routes(
            item(
                mdunion(['kind', 'size'], [
                    object({ kind: Dog, size: string('small'), bark: string }),
                    object({
                        kind: string('cat'),
                        size: string('large'),
                        lives: number,
                    }),
                ] as never) as never,
            ),
        ),
        tags: ['kind', 'size'],
    },
}

const FOREIGN: readonly unknown[] = [
    42,
    'bird',
    true,
    null,
    [1],
    { q: 1 },
    Object.create(null),
]
const UNDECLARED = 'undeclaredName'

type Outcome =
    | { readonly kind: 'written'; readonly value: unknown }
    | {
          readonly kind: 'refused'
          readonly path: readonly (string | number)[]
          readonly reason: string
      }
    | { readonly kind: 'threw'; readonly what: string }

const outcome = (run: () => unknown): Outcome => {
    try {
        const value = run()
        return value instanceof CodecError
            ? { kind: 'refused', path: value.path, reason: value.reason }
            : { kind: 'written', value }
    } catch (thrown) {
        return { kind: 'threw', what: String(thrown) }
    }
}

const drawn = (codec: Routes, count: number): Record<string, unknown>[] => {
    const rng = rngFrom(17)
    const out: Record<string, unknown>[] = []
    while (out.length < count) {
        out.push(arbitraryOf(codec as never, rng, 3) as Record<string, unknown>)
    }
    return out
}

/** Each case: the entity with one name replaced, the patch of that name, and both outcomes. */
const cases = ({ codec, tags }: Entry) =>
    drawn(codec, 20).flatMap((entity) =>
        [...Object.keys(entity), UNDECLARED].flatMap((name) =>
            (name === UNDECLARED ? ['x'] : FOREIGN).map((value) => {
                const own = Object.fromEntries(tags.map((t) => [t, entity[t]]))
                return {
                    name,
                    value,
                    whole: outcome(() =>
                        codec.encode({ ...entity, [name]: value }),
                    ),
                    patch: outcome(() =>
                        codec.encodePartial({ ...own, [name]: value }),
                    ),
                }
            }),
        ),
    )

describe('a refusal is one value, whatever route reaches it', () => {
    for (const [what, entry] of Object.entries(pool)) {
        const all = cases(entry)

        it(`refuses at the name that holds the foreign value, for ${what}`, () => {
            const misplaced = all.flatMap(({ name, value, whole, patch }) =>
                [whole, patch].flatMap((o) =>
                    o.kind === 'refused' &&
                    name !== UNDECLARED &&
                    o.path[0] !== name
                        ? [
                              `${name} = ${JSON.stringify(value)}: ${JSON.stringify(o)}`,
                          ]
                        : [],
                ),
            )
            expect(all.length).toBeGreaterThan(0)
            expect(misplaced).toEqual([])
        })

        it(`gives one refusal on a write and on a patch, for ${what}`, () => {
            const apart = all.flatMap(({ name, value, whole, patch }) =>
                whole.kind === 'written' && patch.kind === 'written'
                    ? []
                    : JSON.stringify(whole) === JSON.stringify(patch) ||
                        (whole.kind === 'refused' &&
                            patch.kind === 'refused' &&
                            JSON.stringify([whole.path, whole.reason]) ===
                                JSON.stringify([patch.path, patch.reason]))
                      ? []
                      : [
                            `${name} = ${JSON.stringify(value)}: ${JSON.stringify(whole)} / ${JSON.stringify(patch)}`,
                        ],
            )
            expect(apart).toEqual([])
        })

        it(`returns each refusal as a value, for ${what}`, () => {
            const thrown = all.flatMap(({ whole, patch }) =>
                [whole, patch].filter((o) => o.kind === 'threw'),
            )
            expect(thrown).toEqual([])
        })
    }
})

describe('a name of Object.prototype is a name like any other', () => {
    const PLAIN = ['kind', 'x', 'y'] as const
    const PROTO = ['constructor', 'toString', 'valueOf'] as const
    const make = ([tag, a, b]: readonly string[]) =>
        routes(
            item(
                discriminatedUnion(
                    tag as 'kind',
                    [
                        object({
                            [tag as 'kind']: string('a'),
                            [a as 'x']: string,
                        }),
                        object({
                            [tag as 'kind']: string('b'),
                            [b as 'y']: number,
                        }),
                    ] as never,
                ),
            ),
        )
    const renamed = (
        row: Record<string, unknown>,
        from: readonly string[],
        to: readonly string[],
    ) =>
        Object.fromEntries(
            Object.entries(row).map(([k, v]) => [to[from.indexOf(k)] ?? k, v]),
        )
    const back = (text: string) =>
        PROTO.reduce(
            (s, name, i) => s.replaceAll(name, PLAIN[i] as string),
            text,
        )

    it('reads each row, and each row less one name, as the codec with plain names', () => {
        const plain = make(PLAIN)
        const proto = make(PROTO)
        const apart: string[] = []
        for (const entity of drawn(plain, 20)) {
            const row = plain.encode(entity) as Record<string, unknown>
            const rows = [
                row,
                ...Object.keys(row).map((name) =>
                    Object.fromEntries(
                        Object.entries(row).filter(([k]) => k !== name),
                    ),
                ),
            ]
            for (const one of rows) {
                const a = outcome(() => plain.decode(one))
                const b = outcome(() =>
                    proto.decode(renamed(one, PLAIN, PROTO)),
                )
                const bPlain =
                    b.kind === 'written'
                        ? {
                              kind: b.kind,
                              value: renamed(
                                  b.value as Record<string, unknown>,
                                  PROTO,
                                  PLAIN,
                              ),
                          }
                        : b
                if (JSON.stringify(a) !== back(JSON.stringify(bPlain))) {
                    apart.push(
                        `${JSON.stringify(one)}: ${JSON.stringify(a)} / ${JSON.stringify(b)}`,
                    )
                }
            }
        }
        expect(apart).toEqual([])
    })
})

/**
 * A required name that the item lacks is a refusal of the item. `encode` states it with the empty
 * path and one text, as `decode` does, and the field codec of the name is never asked: it would
 * refuse `undefined` with another text at the path of the name.
 */
describe('a missing required name is refused by the object that requires it', () => {
    const Pet = routes(item(object({ name: string, age: number })))

    it('names the item, not the field, and says that the name was not given', () => {
        const refused = outcome(() => Pet.encode({ age: 3 }))
        expect(refused).toEqual({
            kind: 'refused',
            path: [],
            reason: "'name' is required and was not given",
        })
    })
})
