import type { Segment } from './frontier'
import { CodecError, emptyNameReason, isEmptyName } from './result'

/**
 * **The segments of a document path in DynamoDB syntax**: a name, or a position in brackets, each
 * name after the first behind a `.`. A name holds no `.`, `[` or `]`, and has a character: the tuple
 * form carries a name with a `.`, `[` or `]`. A position with no name before it is the first part
 * only. A position is digits that print back as the same text, so `[007]` is refused. The function
 * reads more names than {@link expressionPath} prints: a name with a `-` is a name here, and has no
 * expression string. A malformed path gives the refusal, and {@link parsePath} throws it. A malformed
 * path is a defect of the caller. The type of {@link at} refuses a malformed literal first, and a
 * string that is no literal reaches the refusal.
 */
export const parsePathResult = (
    path: string,
): readonly Segment[] | CodecError => {
    if (path === '') return []
    const segments: Segment[] = []
    for (const [at, part] of path.split('.').entries()) {
        const parsed = /^([^[\]]*)((?:\[\d+\])*)$/.exec(part)
        if (parsed === null) {
            return new CodecError(
                `'${path}' is no document path: a name holds no '[' or ']', and a position is digits in brackets`,
            )
        }
        const [, name = '', positions = ''] = parsed
        // a position with no name before it reads the list that the path starts at, so only the first part has one
        if (isEmptyName(name) && (positions === '' || at > 0)) {
            return new CodecError(
                `'${path}' is no document path: a name has a character, because ${emptyNameReason}`,
            )
        }
        if (!isEmptyName(name)) segments.push(name)
        for (const [, digits = ''] of positions.matchAll(/\[(\d+)\]/g)) {
            // the text of a position is the text that the number prints, so `007` and a digit run past a float are no position
            if (String(Number(digits)) !== digits) {
                return new CodecError(
                    `'${path}' is no document path: a position is digits that print back as the same text, and '[${digits}]' does not`,
                )
            }
            segments.push(Number(digits))
        }
    }
    return segments
}

/** {@link parsePathResult}, throwing the refusal. */
export const parsePath = (path: string): readonly Segment[] => {
    const read = parsePathResult(path)
    if (read instanceof CodecError) throw read
    return read
}
