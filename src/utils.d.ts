// Lighter Exact implementation — catches excess top-level properties only.
// Does not recursively check nested objects/arrays. This is intentional:
// DynamoDB entity shapes are flat at the key level.
// Uses DistributiveKeyof so that union-typed Shape (discriminated unions)
// exposes keys from ALL variants, not just the common keys.
type DistributiveKeyof<T> = T extends unknown ? keyof T : never

export type Exact<Shape, Candidate> = Candidate & {
    [K in keyof Candidate]: K extends DistributiveKeyof<Shape>
        ? Candidate[K]
        : never
}

export type ValueOf<
    ObjectType,
    ValueType = keyof ObjectType,
> = ValueType extends keyof ObjectType ? ObjectType[ValueType] : never

/**
 * Force an operation like `{ a: 0 } & { b: 1 }` to be computed so that it displays `{ a: 0; b: 1 }`.
 * This version is distributive, meaning it will preserve union types while flattening each member.
 */
export type show<T> = T extends unknown
    ? { [K in keyof T]: T[K] } & unknown
    : never

export type DistributivePick<T, K> = T extends unknown
    ? K extends keyof T
        ? Pick<T, K>
        : never
    : never

export type DistributiveOmit<T, K extends keyof T> = T extends unknown
    ? Omit<T, K>
    : never

export type SliceFromStart<
    T,
    End extends number,
    Acc extends unknown[] = [],
> = End extends 0
    ? []
    : End extends 1
      ? T extends [infer Head, ...unknown[]]
          ? [Head]
          : []
      : T extends unknown[]
        ? Acc['length'] extends End
            ? Acc
            : T extends [infer Head, ...infer Tail]
              ? SliceFromStart<Tail, End, [...Acc, Head]>
              : Acc
        : never

export type MergeIntersectionObject<T, Keys extends keyof T = keyof T> = {
    [K in Keys]: T[K]
}

export type NonEmptyArray<T> = [T, ...T[]]

export type Replace<T, U, V> = T extends U ? V : T

/**
 * Represents a type-level error message. Used to provide helpful feedback in the IDE.
 */
export declare const errorMessage: unique symbol
export type ErrorMessage<T extends string> = {
    readonly [errorMessage]: T
}
