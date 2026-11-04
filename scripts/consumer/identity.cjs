// One class identity across the published entries, read under node through the `exports` map.
// A class that each entry bundled for itself would give `instanceof` a second answer across entries.
const { CodecError, DynamoNumber, opaque } = require('rotorise')
const { native } = require('rotorise/native')
const { checkRoundTrip } = require('rotorise/testing')
const rows = []
const check = (name, ok) => {
    rows.push(ok)
    console.log(`${ok ? 'PASS' : 'FAIL'}  CJS ${name}`)
}
const attempt = (run) => {
    try {
        return run()
    } catch (thrown) {
        return thrown
    }
}

check(
    'a refusal of native is a CodecError of rotorise',
    native.encode(Number.NaN) instanceof CodecError,
)
check(
    'a refusal of testing is a CodecError of rotorise',
    attempt(() => checkRoundTrip(opaque, { count: 1, filter: () => false })) instanceof CodecError,
)
check(
    'checkRoundTrip(opaque) passes',
    attempt(() => checkRoundTrip(opaque, { count: 200 })) === undefined,
)
check(
    'opaque.encode accepts a DynamoNumber of rotorise',
    !(opaque.encode(DynamoNumber.from('7')) instanceof Error),
)

process.exit(rows.every(Boolean) ? 0 : 1)
