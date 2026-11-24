/**
 * A pin of an instantiation count fails on a fall of more than 10 percent.
 *
 * attest fails a rise above its threshold, and passes each fall. A block that measures no call
 * keeps the pin green unless the pin reads the fall. The limit is the owner limit of a change, in
 * each direction, so a fall of exactly the limit and each rise pass here.
 */
import { describe, expect, it } from 'vitest'
import { fallen, PIN_LIMIT } from './attestPin'

describe('a pin fails on a fall of more than the limit', () => {
    it('keeps the limit at 10 percent', () => {
        expect(PIN_LIMIT).toBe(0.1)
    })

    it('fails the count of a block that measures no call', () => {
        expect(fallen(16, 3617)).toBe(true)
    })

    it('fails a fall above the limit, and passes a fall at the limit', () => {
        expect(fallen(899, 1000)).toBe(true)
        expect(fallen(900, 1000)).toBe(false)
        expect(fallen(950, 1000)).toBe(false)
    })

    it('passes each rise, because attest owns the rise', () => {
        expect(fallen(1000, 1000)).toBe(false)
        expect(fallen(5000, 1000)).toBe(false)
    })
})
