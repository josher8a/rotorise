/**
 * Caller code never escapes a codec as an exception, and a refusal that a caller returns is never
 * changed.
 *
 * A predicate of `refine` and a conversion of `held` are the caller's code. A throw of either is a
 * refusal of the value, so a read of a stored row returns a `CodecError` and a union reads the next
 * option. A container writes its path on the refusal that it receives, so a refusal that an adapter
 * returns reaches each read as a copy, and the error object of the caller keeps its message.
 */
import { describe, expect, it } from 'vitest'
import { CodecError, failed } from '../../../Rotorise'
import { held, item, object, refine, string, union } from '../../codec'
import { RecursionRefused } from '../../term'

describe('a refinement whose predicate throws', () => {
    type Url = string & { readonly url: true }
    const isUrl = (text: string): text is Url => {
        new URL(text)
        return true
    }
    const homepage = refine(string, isUrl, { describe: 'a URL' })

    it('refuses the row, as held refuses a conversion that throws', () => {
        expect(homepage.decode({ S: 'not a url' })).toBeInstanceOf(CodecError)
        expect(homepage.encode('not a url' as Url)).toBeInstanceOf(CodecError)
        const Shelter = item(object({ name: string, homepage }))
        expect(
            Shelter.decode({ name: { S: 'Paws' }, homepage: { S: 'x' } }),
        ).toBeInstanceOf(CodecError)
    })

    it('leaves the next option of a union to read the row, on both sides', () => {
        const Link = union([homepage, string])
        expect(Link.decode({ S: 'not a url' })).toBe('not a url')
        expect(Link.encode('not a url' as never)).toEqual({ S: 'not a url' })
    })
})

describe('a refusal that an adapter returns', () => {
    it('names the path of its own read only, and the error of the caller keeps its message', () => {
        const notTitled = new CodecError('the name is not in title case')
        const Name = held(string, string, {
            encode: (text) => text,
            decode: (text) => (text === text.toLowerCase() ? notTitled : text),
        })
        const Pet = item(object({ name: Name }))
        const row = { name: { S: 'rex' } }
        const first = Pet.decode(row)
        const second = Pet.decode(row)
        expect(failed(first) && first.message).toBe(
            'at name: the name is not in title case',
        )
        expect(failed(second) && second.message).toBe(
            'at name: the name is not in title case',
        )
        expect(first).not.toBe(notTitled)
        expect(notTitled.message).toBe('the name is not in title case')
        expect(notTitled.path).toEqual([])
        expect(failed(first) && typeof first.stack).toBe('string')
    })
})

describe('a refusal at a deeper level', () => {
    it('keeps its class and the fields that its class carries', () => {
        const refused = new RecursionRefused(
            { kind: 'never' } as never,
            2,
            'the cycle has no guard',
        )
        const deeper = refused.under('owner').under(0)
        expect(deeper).toBeInstanceOf(RecursionRefused)
        expect([deeper.term, deeper.use, deeper.path]).toEqual([
            { kind: 'never' },
            2,
            [0, 'owner'],
        ])
        expect(refused.path).toEqual([])
    })
})
