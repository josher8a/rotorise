/**
 * A clause is open at each object, at the type and at run time. The path type that knows the codecs
 * drops an option whose object lacks a key that a nested object of the clause requires.
 */
import { describe, expect, it } from 'vitest'
import { type Decoded, number, object, pathBuilder, string } from '../../codec'

const A = object({ data: object({ n: number }), tag: string })
const B = object({ data: object({ m: string }), tag: string })
type Frontier =
    | {
          readonly spec: typeof A.spec
          readonly rest: undefined
          readonly t: Decoded<typeof A>
      }
    | {
          readonly spec: typeof B.spec
          readonly rest: undefined
          readonly t: Decoded<typeof B>
      }
const p = pathBuilder<Decoded<typeof A> | Decoded<typeof B>, Frontier>()

describe('a nested clause on a known frontier', () => {
    it('separates the option whose closed object lacks the key of the clause', () => {
        const kept = p.narrow(object({ data: object({ n: number }) }))
        expect(kept.data.n.toString()).toBe('data.n')
        // @ts-expect-error the option that declares `m` is separated
        expect(kept.data.m.toString()).toBe('data.m')
    })
})
