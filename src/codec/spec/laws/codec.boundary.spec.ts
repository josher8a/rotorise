/**
 * `decode` is the boundary: a stored value that no codec of this library writes is a `CodecError`
 * value, and never a throw.
 *
 * An attribute from outside the program is unparsed data, so each read of a member checks the
 * payload before the payload is used. Each test hands a decode a value that the type forbids, and
 * a throw out of the decode fails the test, because the call stands outside any `expect(...).toThrow`.
 */
import { describe, expect, it } from 'vitest'
import {
    array,
    CodecError,
    decimal,
    discriminatedUnion,
    fill,
    held,
    item,
    legacy,
    nullValue,
    number,
    object,
    opaque,
    refine,
    string,
    union,
} from '../../codec'
import type { StandardSchemaV1 } from '../../standard'

/** The refusal that a call returns, where a call that throws fails the test. */
const refusal = (call: () => unknown): CodecError => {
    const result = call()
    expect(result).toBeInstanceOf(CodecError)
    return result as CodecError
}

/** A value with no `toString`, `valueOf` or `Symbol.toPrimitive`, which `String` cannot render. */
const bare = (): never => Object.create(null) as never

const pets = discriminatedUnion('species', [
    object({ species: string('cat'), name: string }),
    object({ species: string('dog'), name: string }),
] as never)

describe('a stored tag or key is read through its payload check', () => {
    it('refuses a tag whose payload is no string, and names the tag', () => {
        const read = refusal(() =>
            (item(pets as never) as any).decode({
                species: { S: bare() },
                name: { S: 'Rex' },
            }),
        )
        expect(read.message).toMatch(/'species' chooses the variant/)
    })

    it('refuses a literal key whose payload is no string', () => {
        refusal(() => string('cat', 'dog').decode({ S: bare() } as never))
    })
})

describe('a value that is no attribute is refused, where it sits in a list or a map', () => {
    it('refuses a null list member, and names the position', () => {
        const read = refusal(() => array(string).decode({ L: [null] } as never))
        expect(read.message).toMatch(/at \[0\]: a stored member is null/)
    })

    it('refuses an undefined list member of an untyped read', () => {
        refusal(() => opaque.decode({ L: [undefined] } as never))
    })

    it('refuses a null map member, and names the name', () => {
        const read = refusal(() =>
            item(object({ a: string })).decode({ a: null } as never),
        )
        expect(read.message).toMatch(/at a: a stored member is null/)
    })
})

describe('a whole-item decode refuses an item that is no plain object', () => {
    const entries = {
        'an object': item(object({ name: string, species: string })),
        'a union of objects': item(
            union([object({ a: string }), object({ b: string })]),
        ),
        'a dissection': item(pets as never),
    } as Record<string, { decode: (item: never) => unknown }>

    for (const [name, codec] of Object.entries(entries)) {
        for (const stored of [undefined, null, 'text', []]) {
            it(`refuses ${JSON.stringify(stored) ?? 'undefined'} for ${name}`, () => {
                const read = refusal(() => codec.decode(stored as never))
                expect(read.message).toMatch(/an item is a plain object/)
            })
        }
    }
})

describe('a value that cannot be written refuses as a value, whatever it holds', () => {
    it('refuses a bigint at the null codec, which JSON cannot render', () => {
        refusal(() => nullValue.encode(1n as never))
    })

    it('refuses a cyclic value at the null codec, which JSON cannot render', () => {
        const owner: Record<string, unknown> = {}
        owner.self = owner
        refusal(() => nullValue.encode(owner as never))
    })
})

describe('a stored set refuses two members that read to one value', () => {
    /**
     * The model's `setImage` refuses an image that is not injective. A `Set` would merge the two
     * members, and the value read would write back as one member, so the pair disagrees.
     */
    it('refuses two numerals that read to one float, and names the two positions', () => {
        const read = refusal(() =>
            number.set().decode({ NS: ['0.1', '0.10000000000000001'] }),
        )
        expect(read.message).toMatch(
            /members 0 and 1 of this NS read to one value/,
        )
    })

    it('reads two numerals that read to two values', () => {
        const read = number.set().decode({ NS: ['0.1', '0.2'] })
        expect(read).toEqual(new Set([0.1, 0.2]))
    })
})

describe('a throw of a value that cannot render is a refusal, and never a TypeError', () => {
    /** What `String` says of a value with no `toString`: the failure to render, and not the throw. */
    const primitive = /Cannot convert object to primitive value/

    const throwsBare: StandardSchemaV1<Date> = {
        '~standard': {
            version: 1,
            vendor: 'handwritten',
            validate: () => {
                throw bare()
            },
        },
    }

    it('refuses at a conversion of `held`', () => {
        const converted = held(string, string, {
            encode: (_text: string): string => {
                throw bare()
            },
            decode: (text: string) => text,
        })
        expect(refusal(() => converted.encode('Rex')).message).not.toMatch(
            primitive,
        )
    })

    it('refuses at the older reader of `legacy`', () => {
        const Rate = legacy({
            current: decimal,
            older: {
                decode: () => {
                    throw bare()
                },
            },
        })
        expect(refusal(() => Rate.decode({ BOOL: true })).message).not.toMatch(
            primitive,
        )
    })

    it('refuses at the fill value of a codec that throws', () => {
        const strict = refine(string, (_text): _text is string => {
            throw bare()
        })
        expect(() => fill(strict, 'x')).toThrow(CodecError)
        expect(() => fill(strict, 'x')).not.toThrow(primitive)
    })

    it('refuses at the held side that is a codec which throws', () => {
        const outer = refine(string, (_text): _text is string => {
            throw bare()
        })
        const converted = held(string, outer, {
            encode: (text: string) => text,
            decode: (text: string) => text,
        })
        expect(refusal(() => converted.encode('Rex')).message).not.toMatch(
            primitive,
        )
    })

    it('refuses at the held side that is a schema which throws', () => {
        const converted = held(string, throwsBare, {
            encode: (day: Date) => day.toISOString(),
            decode: (text) => new Date(text),
        })
        expect(
            refusal(() => converted.encode(new Date(0))).message,
        ).not.toMatch(primitive)
    })
})
