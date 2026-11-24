import { caller, getBenchAssertionsAtPosition } from '@ark/attest'

/**
 * The owner limit of a change: a count moves at most 10 percent from its pin, in each direction.
 * The setup of attest owns the rise: `setupVitest.ts` sets `benchPercentThreshold` to this limit.
 */
export const PIN_LIMIT = 0.1

/** Whether `count` lies more than the limit under `pin`. Each rise is no fall. */
export const fallen = (count: number, pin: number): boolean =>
    (pin - count) / pin > PIN_LIMIT

/**
 * The pin of `attest.instantiations`, checked for a fall.
 *
 * attest passes each fall, so a block that measures no call stays green. Write the call on the line
 * after the call of attest, with the same number:
 * `attest.instantiations([3617, 'instantiations'])`, then `floor(3617)`. The call reads the count
 * that attest measured for the line above, and throws where the count lies more than the limit
 * under the pin. attest checks the rise. The call of attest stays on one line, so the lookup finds it.
 */
export const floor = (pin: number): void => {
    const at = caller()
    const entry = getBenchAssertionsAtPosition({ ...at, line: at.line - 1 })[0]
    if (entry === undefined) {
        throw new Error('attest holds no count at the call of floor')
    }
    const count = entry[1].count
    if (fallen(count, pin)) {
        throw new Error(
            `The block measures ${count} instantiations, more than ${PIN_LIMIT * 100} percent under the pin of ${pin}. The block may measure no call. Refresh the pin where the cost fell.`,
        )
    }
}
