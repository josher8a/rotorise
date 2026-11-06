import { describe, expect, it } from 'vitest'
import { DynamoNumber } from '../../attribute'
import { decimal, dynamoNumber, held, number, string } from '../../codec'
import { clauseForm } from '../../term'

/**
 * The form of a numeric literal under an adapter names the held side of the adapter, so a
 * clause at a caller adapter that hands over text reads as `decimal`, as the library `decimal` does.
 */
describe('the form of a numeric literal is read off the held side of its adapter', () => {
    const litter = DynamoNumber.from('5') as unknown as DynamoNumber<'5'>

    it('reads a caller adapter that hands over text as decimal', () => {
        const asText = held(dynamoNumber(litter), string('5'), {
            encode: (text: '5') => DynamoNumber.from(text),
            decode: (stored: DynamoNumber) => stored.toString() as '5',
        })
        expect(clauseForm(asText.def)?.form).toBe('decimal')
    })

    it('reads the library adapters by their held side', () => {
        expect(clauseForm(decimal('5').def)?.form).toBe('decimal')
        expect(clauseForm(number(5).def)?.form).toBe('number')
        expect(clauseForm(dynamoNumber(litter).def)?.form).toBe('dynamoNumber')
    })
})
