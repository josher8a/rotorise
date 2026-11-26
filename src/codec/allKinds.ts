import type { AttributeValue } from './attribute'
import { codecOfTerm as codecOfKnown } from './capabilities'
import { carryingReading } from './sums'
import type { Term } from './term'

/**
 * **The all-kinds route of a bare term.** The codec of a term that no constructor built: a term
 * that a scope closes, a term that a test or the Lean emit draws. The route knows the meaning
 * of every kind and fills the same slots that a constructor fills, so a bare term reads as the term
 * says. A constructor of one kind holds the meaning of that kind only, and imports no part of
 * this module, so no bundle of a constructor holds the meaning of every kind.
 */
export const codecOfTerm = <T, A extends AttributeValue>(
    def: Term,
): ReturnType<typeof codecOfKnown<T, A>> =>
    carryingReading(codecOfKnown<T, A>(def), def)
