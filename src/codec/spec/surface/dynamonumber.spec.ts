/**
 * The carrier `N` actually has.
 *
 * `N` was carried as `string` at every surface, so the numeral predicate had to be re-checked at
 * each boundary and no type ever said it had passed. `DynamoNumber` validates once and carries the
 * result, which is what makes an unvalidated numeral unrepresentable rather than merely unlikely.
 *
 * The rules below are the ones a caller can be hurt by: that construction refuses what DynamoDB
 * refuses, that nothing rounds unless the caller asks for a JS number, and that the two equalities
 * are different questions with different answers.
 */
import { describe, expect, it } from 'vitest'
import { DynamoNumber } from '../../attribute'

describe('construction refuses what DynamoDB refuses', () => {
    it('accepts a numeral the service accepts', () => {
        expect(DynamoNumber.from('1.5')?.toString()).toBe('1.5')
        expect(DynamoNumber.from('-0.00001')?.toString()).toBe('-0.00001')
        expect(DynamoNumber.from('1e5')?.toString()).toBe('1e5')
    })

    it('refuses text that is not a numeral at all', () => {
        expect(DynamoNumber.from('abc')).toBeUndefined()
        expect(DynamoNumber.from('')).toBeUndefined()
        expect(DynamoNumber.from('1.2.3')).toBeUndefined()
    })

    it('refuses more than 38 significant digits, which the service will not store', () => {
        expect(DynamoNumber.from('1'.repeat(38))).toBeDefined()
        expect(DynamoNumber.from('1'.repeat(39))).toBeUndefined()
    })

    it('refuses a magnitude outside the range the service stores', () => {
        expect(DynamoNumber.from('1e125')).toBeDefined()
        expect(DynamoNumber.from('1e126')).toBeUndefined()
        expect(DynamoNumber.from('1e-130')).toBeDefined()
        expect(DynamoNumber.from('1e-131')).toBeUndefined()
    })
})

describe('the digits are the value, so nothing rounds on the way in', () => {
    /**
     * The reason the class exists. A JS number carries about 15 significant digits and `N` carries
     * 38, so a caller who routes through `number` loses the difference silently. Routing through
     * the digits does not.
     */
    it('keeps 38 significant digits, where a JS number keeps about 15', () => {
        const exact = '12345678901234567890123456789012345678'
        expect(DynamoNumber.from(exact)?.toString()).toBe(exact)
        expect(String(Number(exact))).not.toBe(exact)
    })

    it('converts to a JS number only when asked, and says that it is lossy', () => {
        const exact = '12345678901234567890123456789012345678'
        const n = DynamoNumber.from(exact)
        expect(n?.toString()).toBe(exact)
        expect(String(n?.toNumber())).not.toBe(exact)
    })

    it('refuses a JS number the service will not store', () => {
        expect(DynamoNumber.fromNumber(Number.NaN)).toBeUndefined()
        expect(
            DynamoNumber.fromNumber(Number.POSITIVE_INFINITY),
        ).toBeUndefined()
        expect(DynamoNumber.fromNumber(1e309)).toBeUndefined()
    })

    it('rounds at fromNumber because the float already has, which is the one lossy door', () => {
        expect(DynamoNumber.fromNumber(0.1 + 0.2)?.toString()).toBe(
            '0.30000000000000004',
        )
        expect(DynamoNumber.from('0.3')?.toString()).toBe('0.3')
    })
})

describe('the store normalises, so a written spelling is not always the one returned', () => {
    /**
     * DynamoDB hands back a normalised `N`. A codec that writes `'1.50'` reads back `'1.5'`, which
     * is a round trip failing across the database where no local law can see it. `isStored` is the
     * question a caller has to be able to ask before writing.
     */
    it('says whether the store returns this spelling unchanged', () => {
        expect(DynamoNumber.from('1.5')?.isStored).toBe(true)
        expect(DynamoNumber.from('1.50')?.isStored).toBe(false)
        expect(DynamoNumber.from('007')?.isStored).toBe(false)
        expect(DynamoNumber.from('1e5')?.isStored).toBe(false)
    })

    it('gives the spelling the store would return', () => {
        expect(DynamoNumber.from('1.50')?.normalized()?.toString()).toBe('1.5')
        expect(DynamoNumber.from('007')?.normalized()?.toString()).toBe('7')
        expect(DynamoNumber.from('1e5')?.normalized()?.toString()).toBe(
            '100000',
        )
    })

    it('is its own normal form when it is already stored', () => {
        const n = DynamoNumber.from('1.5')
        expect(n?.normalized()).toBe(n)
    })
})

describe('the two equalities are different questions', () => {
    /**
     * This is the cost of carrying `N` as text, stated as a test rather than left to a caller to
     * discover. `'1.50'` and `'1.5'` are one number and two numerals, so a carrier whose equality
     * is textual answers "different" where a caller means "same". `equals` is the carrier's
     * question and `sameNumber` is the caller's.
     */
    it('equals compares the digits, so the same number can be unequal', () => {
        const a = DynamoNumber.from('1.50')
        const b = DynamoNumber.from('1.5')
        expect(a && b && a.equals(b)).toBe(false)
    })

    it('sameNumber compares the numbers, so the same number is the same number', () => {
        const a = DynamoNumber.from('1.50')
        const b = DynamoNumber.from('1.5')
        expect(a && b && a.sameNumber(b)).toBe(true)
    })

    it('agrees with equals once both sides are in the stored form', () => {
        const a = DynamoNumber.from('1.50')?.normalized()
        const b = DynamoNumber.from('1.5')
        expect(a && b && a.equals(b)).toBe(true)
        expect(a && b && a.sameNumber(b)).toBe(true)
    })
})
