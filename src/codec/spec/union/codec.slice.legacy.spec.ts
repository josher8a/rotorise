/**
 * A pattern that reads an older encoding names the keys of its current form, and no other key.
 *
 * The opening of a pattern is open at every object, so an option with more keys fits the pattern
 * `object({ kind: string('dog') })`. A `legacy` around that object holds each pair of the
 * current form, so the pattern reads through it. The type and the run time read the pattern as the
 * plain pattern, and each row states both.
 */
import { describe, expect, expectTypeOf, it } from 'vitest'
import type { AnyCodec, Decoded } from '../../codec'
import {
    exclude,
    extract,
    fits,
    legacy,
    number,
    object,
    string,
    termOf,
    union,
} from '../../codec'
import { sameTerm } from '../../term'

const older = { decode: () => ({ kind: 'dog' as const }) }
const olderKind = { decode: () => 'dog' as const }

const dog = object({ kind: string('dog'), age: number })
const cat = object({ kind: string('cat'), age: number })
const dogKey = object({ kind: string('dog') })
const catKey = object({ kind: string('cat') })

/** Options with one key more than the pattern names. */
const wider = union([dog, cat])
/** Options that name the key of the pattern and no other. */
const equal = union([dogKey, catKey])

const plain = dogKey
const aroundObject = legacy({ current: dogKey, older })
const aroundSlot = object({
    kind: legacy({ current: string('dog'), older: olderKind }),
})

const same = (a: AnyCodec, b: AnyCodec) =>
    expect(sameTerm(termOf(a), termOf(b))).toBe(true)

describe('a pattern around an older reading is read as the plain pattern', () => {
    it('extracts the option with more keys, in the type and at run time', () => {
        const kept = extract(wider, aroundObject)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof dog>
        >()
        same(kept, extract(wider, plain))
        same(kept, union([dog]))
    })

    it('excludes the option with more keys, in the type and at run time', () => {
        const rest = exclude(wider, aroundObject)
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof cat>
        >()
        same(rest, exclude(wider, plain))
        same(rest, union([cat]))
    })

    it('extracts and excludes the option that names the key and no other', () => {
        const kept = extract(equal, aroundObject)
        const rest = exclude(equal, aroundObject)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof dogKey>
        >()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof catKey>
        >()
        same(kept, union([dogKey]))
        same(rest, union([catKey]))
    })

    it('reads an older reading around a literal slot as it reads the plain slot', () => {
        const kept = extract(wider, aroundSlot)
        const rest = exclude(wider, aroundSlot)
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof dog>
        >()
        expectTypeOf<Decoded<typeof rest>>().toEqualTypeOf<
            Decoded<typeof cat>
        >()
        same(kept, union([dog]))
        same(rest, union([cat]))
    })

    it('fits an option with more keys, as the plain pattern does', () => {
        expect(fits(termOf(dog), termOf(aroundObject))).toBe(true)
        expect(fits(termOf(cat), termOf(aroundObject))).toBe(false)
        expect(fits(termOf(dog), termOf(plain))).toBe(true)
    })

    it('fits an older reading of one reader at its current form', () => {
        const wide = legacy({
            current: dog,
            older: { decode: () => ({ kind: 'dog' as const, age: 1 }) },
        })
        expect(fits(termOf(wide), termOf(wide))).toBe(true)
    })

    it('keeps an option that reads older forms through the same older reading, in the type and at run time', () => {
        const reader = { decode: () => ({ kind: 'dog' as const, age: 1 }) }
        const wide = legacy({ current: dog, older: reader })
        const adopted = object({ tag: string('adopted'), pet: wide })
        const options = union([adopted, object({ tag: string('stray') })])
        const named = legacy({ current: dogKey, older: reader })
        const kept = extract(options, object({ pet: named }))
        expectTypeOf<Decoded<typeof kept>>().toEqualTypeOf<
            Decoded<typeof adopted>
        >()
        same(kept, union([adopted]))
    })
})
