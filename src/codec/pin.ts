import type { AttributeValue } from './attribute'
import type { AttributeCodec, Decoded } from './codec'

type Primitive = string | number | boolean | bigint | symbol | null | undefined
type Mark<T, K extends keyof T> = Record<never, never> extends Pick<T, K>
    ? '?'
    : ''
type IsTuple<T extends readonly unknown[]> = number extends T['length']
    ? false
    : true

/** Every key path of a type, each with its optional mark, through unions, lists, tuples and records. */
type KeyPaths<
    T,
    P extends string = '',
    D extends unknown[] = [],
> = D['length'] extends 12
    ? never
    : T extends
            | Primitive
            | ((...a: never[]) => unknown)
            | ReadonlySet<unknown>
            | ReadonlyMap<unknown, unknown>
      ? never
      : T extends readonly unknown[]
        ? IsTuple<T> extends true
            ?
                  | {
                        [I in keyof T & `${number}`]:
                            | `${P}[${I}]`
                            | KeyPaths<T[I], `${P}[${I}]`, [...D, 0]>
                    }[keyof T & `${number}`]
                  | `${P}#${T['length']}`
            : `${P}[]` | KeyPaths<T[number], `${P}[]`, [...D, 0]>
        : {
              [K in keyof T & (string | number)]-?: string extends K
                  ? `${P}.[string]` | KeyPaths<T[K], `${P}.[string]`, [...D, 0]>
                  :
                        | `${P}.${K}${Mark<T, K>}`
                        | KeyPaths<NonNullable<T[K]>, `${P}.${K}`, [...D, 0]>
          }[keyof T & (string | number)]

type PinCheck<A, T> = [
    Exclude<KeyPaths<A>, KeyPaths<T>>,
    Exclude<KeyPaths<T>, KeyPaths<A>>,
] extends [infer Plus extends string, infer Minus extends string]
    ? [Plus | Minus] extends [never]
        ? unknown
        : {
              readonly '[pin] key paths that differ': {
                  readonly codecOnly: Plus
                  readonly modelOnly: Minus
              }
          }
    : never

/**
 * Pins a codec to a model: the decoded type and `T` are assignable both ways, and have the same key paths.
 *
 * `satisfies AttributeCodec<T>` checks the mutual assignability only. Mutual assignability cannot see an
 * optional key: an object without `k?` is assignable to an object with it, and back. So the pin also
 * compares the key paths, where each path carries its optional mark, at each depth and in each union
 * member. The type error names each path that only one side has.
 *
 * The TypeScript equality idiom `(<X>() => X extends A ? 1 : 2) extends (<X>() => X extends B ? 1 : 2)`
 * is not the check. The idiom compares the spelling of a type: the idiom refuses `{ a } & { b }` against
 * `{ a; b }`, and a union that the model splits in a different place than the codec.
 *
 * The pin does not compare a `readonly` modifier on a property, because assignability ignores the
 * modifier. Assignability does compare a readonly array with a mutable array.
 *
 * @example
 * ```ts
 * const Pet = pin<PetEntry>()(object({ id: string, soldAt: optional(string) }))
 * ```
 */
export const pin =
    <T, A extends AttributeValue = AttributeValue>() =>
    <C extends AttributeCodec<T, A>>(codec: C & PinCheck<Decoded<C>, T>): C =>
        codec
