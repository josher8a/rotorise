/**
 * The Standard Schema interface, version 1: the types only, copied from the specification.
 *
 * Source: https://standardschema.dev, the package `@standard-schema/spec`, version 1. The copy
 * holds the types that `held` reads, and adds no dependency. The specification declares the
 * members inside a namespace `StandardSchemaV1`. This copy declares each member as a flat type,
 * with the same fields.
 *
 * A schema of another library crosses the boundary here. The library reads the schema through
 * `validate` only, and the result can arrive as a `Promise`, so the caller converts the result
 * into a value one time, where the call happens.
 */

/** A schema that implements the interface. */
export type StandardSchemaV1<Input = unknown, Output = Input> = {
    readonly '~standard': StandardSchemaProps<Input, Output>
}

/** The properties under `~standard`. */
export type StandardSchemaProps<Input = unknown, Output = Input> = {
    readonly version: 1
    readonly vendor: string
    readonly validate: (
        value: unknown,
    ) => StandardResult<Output> | Promise<StandardResult<Output>>
    readonly types?: StandardTypes<Input, Output> | undefined
}

/** The result of `validate`: a value, or the issues. */
export type StandardResult<Output> =
    | { readonly value: Output; readonly issues?: undefined }
    | { readonly issues: readonly StandardIssue[] }

/** One issue that `validate` reports. */
export type StandardIssue = {
    readonly message: string
    readonly path?:
        | readonly (PropertyKey | { readonly key: PropertyKey })[]
        | undefined
}

/** The input type and the output type, which exist at the type level only. */
export type StandardTypes<Input, Output> = {
    readonly input: Input
    readonly output: Output
}

/** The output type of a schema. */
export type StandardOutput<S extends StandardSchemaV1> = NonNullable<
    S['~standard']['types']
>['output']
