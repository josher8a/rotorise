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
import { DynamoNumber, isStoredNumeral } from '../../attribute'
import { CodecError, failed, orThrow } from '../../result'

/** The carrier, where the text is known good. */
const num = (digits: string): DynamoNumber => orThrow(DynamoNumber.from(digits))

describe('construction refuses what DynamoDB refuses', () => {
    it('accepts a numeral the service accepts, in the form the service returns', () => {
        expect(num('1.5').toString()).toBe('1.5')
        expect(num('-0.00001').toString()).toBe('-0.00001')
        // accepted as written and held as the store would hand it back
        expect(num('1e5').toString()).toBe('100000')
    })

    /**
     * A refusal is a value here, as it is everywhere else on this surface, and it names the text
     * that failed. Returning `undefined` would be a default standing in for an error, which is the
     * one thing a caller cannot act on.
     */
    it('refuses text that is not a numeral at all, as a Result', () => {
        const refused = DynamoNumber.from('abc')
        expect(failed(refused)).toBe(true)
        expect((refused as CodecError).message).toMatch(
            /'abc' is not a number DynamoDB stores/,
        )
        expect(failed(DynamoNumber.from(''))).toBe(true)
        expect(failed(DynamoNumber.from('1.2.3'))).toBe(true)
    })

    it('refuses more than 38 significant digits, which the service will not store', () => {
        expect(failed(DynamoNumber.from('1'.repeat(38)))).toBe(false)
        expect(failed(DynamoNumber.from('1'.repeat(39)))).toBe(true)
    })

    it('refuses a magnitude outside the range the service stores', () => {
        expect(failed(DynamoNumber.from('1e125'))).toBe(false)
        expect(failed(DynamoNumber.from('1e126'))).toBe(true)
        expect(failed(DynamoNumber.from('1e-130'))).toBe(false)
        expect(failed(DynamoNumber.from('1e-131'))).toBe(true)
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
        expect(num(exact).toString()).toBe(exact)
        expect(String(Number(exact))).not.toBe(exact)
    })

    it('converts to a JS number only when asked, and says that it is lossy', () => {
        const exact = '12345678901234567890123456789012345678'
        const n = num(exact)
        expect(n.toString()).toBe(exact)
        expect(String(n.toNumber())).not.toBe(exact)
    })

    it('refuses a JS number the service will not store', () => {
        const refused = DynamoNumber.fromNumber(Number.NaN)
        expect(failed(refused)).toBe(true)
        expect((refused as CodecError).message).toMatch(
            /NaN is not a number DynamoDB stores/,
        )
        expect(failed(DynamoNumber.fromNumber(Number.POSITIVE_INFINITY))).toBe(
            true,
        )
        expect(failed(DynamoNumber.fromNumber(1e309))).toBe(true)
    })

    it('rounds at fromNumber because the float already has, which is the one lossy door', () => {
        expect(orThrow(DynamoNumber.fromNumber(0.1 + 0.2)).toString()).toBe(
            '0.30000000000000004',
        )
        expect(num('0.3').toString()).toBe('0.3')
    })
})

describe('the store normalises, and so does the constructor', () => {
    /**
     * DynamoDB hands back a normalised `N`, so a carrier holding any other spelling holds one the
     * table will not give back. Normalising on the way in is what stops every comparison and round
     * trip downstream having to know that, and it is why there is no `isStored` to ask: there is no
     * `DynamoNumber` that is not stored.
     */
    it('holds the spelling the store would return, whatever it was given', () => {
        expect(num('1.50').toString()).toBe('1.5')
        expect(num('007').toString()).toBe('7')
        expect(num('1e5').toString()).toBe('100000')
        expect(num('-0').toString()).toBe('0')
        expect(num('0.0').toString()).toBe('0')
    })

    /**
     * The defect the first version shipped, kept as a test because the shape of it is easy to
     * write again. It normalised through a JS number, and `String(Number(...))` writes exponent
     * form at or above `1e21` and below `1e-6`. The store returns neither, and DynamoDB carries
     * magnitudes to `1e125`, so the answer was a numeral but not the stored one across most of the
     * range it accepts.
     */
    it('expands the digits rather than going through a JS number', () => {
        expect(num('1e21').toString()).toBe('1000000000000000000000')
        expect(num('1e-7').toString()).toBe('0.0000001')
        expect(num('-1.5e-8').toString()).toBe('-0.000000015')
    })

    it('lands on a spelling the store returns, for everything it accepts', () => {
        for (const digits of [
            '1e21',
            '1e-7',
            '1e125',
            '1e-130',
            '007',
            '1.50',
            '-0',
            '0.0',
            '-1.5e-8',
            '+1.5',
        ]) {
            expect(isStoredNumeral(num(digits).toString())).toBe(true)
        }
    })

    it('leaves a spelling the store already returns alone', () => {
        expect(num('1.5').toString()).toBe('1.5')
        expect(num('-0.00001').toString()).toBe('-0.00001')
        expect(num('0').toString()).toBe('0')
    })
})

describe('there is one equality, because there is one spelling', () => {
    /**
     * This is what normalising at construction buys, and it is the reason to do it there rather
     * than at each use. Carrying `N` as text makes two equalities: `'1.50'` and `'1.5'` are one
     * number and two numerals, so a text carrier answers "different" where a caller means "same"
     * and needs a second comparison beside the first. There is no second question to ask here.
     */
    it('the same number is the same value, however it was spelled', () => {
        expect(num('1.50').equals(num('1.5'))).toBe(true)
        expect(num('007').equals(num('7'))).toBe(true)
        expect(num('1e5').equals(num('100000'))).toBe(true)
        expect(num('-0').equals(num('0'))).toBe(true)
    })

    it('and different numbers are still different', () => {
        expect(num('1.5').equals(num('1.6'))).toBe(false)
        expect(num('1.5').equals(num('-1.5'))).toBe(false)
    })
})
