# Rotorise

Type-safe DynamoDB composite key management for TypeScript.

DynamoDB offers incredible flexibility, but managing advanced patterns and techniques can be a challenge. Rotorise simplifies complex operations by providing abstractions for key definitions, composite key constructors, partial composite keys, and advanced sort key usage in queries. It integrates seamlessly with [Brushless](https://github.com/josher8a/Brushless) for a frictionless and performant DynamoDB experience.

## Installation

```bash
npm install rotorise
```

## Quick Start

Define your entity type and schema. Rotorise infers the exact key string types.

```ts
import { tableEntry } from 'rotorise'

type User = {
  orgId: string
  id: string
  role: 'admin' | 'user' | 'guest'
  email: string
}

const UserTable = tableEntry<User>()({
  PK: ['orgId', 'id'],
  SK: ['role'],
  GSI1PK: ['role'],
  GSI1SK: 'email',
})
```

## API

### `tableEntry<Entity>()(schema, separator?)`

Entry point for defining a DynamoDB table schema. Returns an object with the methods below.

The double-call `<Entity>()(schema)` is required because TypeScript does not support partial type parameter inference — `Entity` is explicit while `Schema` is inferred from arguments.

The optional `separator` defaults to `'#'`.

### `.key(keyName, attributes, config?)`

Builds a specific key value from the given attributes.

```ts
UserTable.key('PK', { orgId: 'acme', id: '123' })
// => 'ORGID#acme#ID#123'

UserTable.key('GSI1SK', { email: 'a@b.com' })
// => 'a@b.com'
```

**`config` options:**

- **`depth`** — Limit composite key to the first N components. Useful for `begins_with` queries.
- **`allowPartial`** — When `true`, stops building the key when an attribute is missing instead of throwing. Returns a union of all valid partial prefixes at the type level.
- **`enforceBoundary`** — When `true`, appends a trailing separator if the key is partial. Ensures a `begins_with` query doesn't match unintended prefixes.

```ts
UserTable.key('PK', { orgId: 'acme' }, { allowPartial: true })
// => 'ORGID#acme'
// Type: 'ORGID#acme' | `ORGID#${string}#ID#${string}`

UserTable.key('PK', { orgId: 'acme', id: '1' }, { depth: 1 })
// => 'ORGID#acme'

UserTable.key('PK', { orgId: 'acme', id: '1' }, { depth: 1, enforceBoundary: true })
// => 'ORGID#acme#'
```

### `.toEntry(item)`

Converts a raw entity into a complete DynamoDB item with all keys computed.

```ts
const item = UserTable.toEntry({
  orgId: 'acme',
  id: '123',
  role: 'admin',
  email: 'a@b.com',
})
// => { orgId: 'acme', id: '123', role: 'admin', email: 'a@b.com',
//      PK: 'ORGID#acme#ID#123', SK: 'ROLE#admin',
//      GSI1PK: 'ROLE#admin', GSI1SK: 'a@b.com' }
```

Rejects excess properties at the type level.

### `.fromEntry(entry)`

Strips computed keys from a table entry, returning the raw entity.

```ts
const user = UserTable.fromEntry(item)
// => { orgId: 'acme', id: '123', role: 'admin', email: 'a@b.com' }
```

### `.infer`

Zero-runtime inference helper. Use with `typeof` to get the full table entry type.

```ts
type UserEntry = typeof UserTable.infer
```

### `.path()`

Creates a proxy that builds DynamoDB expression paths as strings.

```ts
UserTable.path().email.toString()       // => 'email'
UserTable.path().PK.toString()          // => 'PK'
```

## Advanced Features

### Transforms

Override how a field maps to its key segment using a transform function.

```ts
const Table = tableEntry<User>()({
  PK: [
    ['orgId', (id: string) => ({ tag: 'ORG', value: id })],
    ['id', (id: string) => ({ tag: 'USER', value: id })],
  ],
  SK: ['role'],
})

Table.key('PK', { orgId: 'acme', id: '123' })
// => 'ORG#acme#USER#123'
```

A transform returns either:
- A `joinable` value (the field name uppercased becomes the tag)
- `{ value }` (no tag segment emitted)
- `{ tag, value }` (custom tag)

### Discriminated Schemas

When your table stores a union of entity types, use a discriminator to define per-variant key specs.

```ts
type Item =
  | { kind: 'order'; orderId: string; userId: string }
  | { kind: 'refund'; refundId: string; orderId: string }

const ItemTable = tableEntry<Item>()({
  PK: {
    discriminator: 'kind',
    spec: {
      order: ['userId', 'orderId'],
      refund: ['orderId', 'refundId'],
    },
  },
  SK: ['kind'],
})

ItemTable.key('PK', { kind: 'order', userId: 'u1', orderId: 'o1' })
// => 'USERID#u1#ORDERID#o1'

ItemTable.key('PK', { kind: 'refund', orderId: 'o1', refundId: 'r1' })
// => 'ORDERID#o1#REFUNDID#r1'
```

Set a discriminated spec value to `null` to produce `undefined` (useful for GSIs that don't apply to all variants).

### Preconditions of a Narrowed Path

`at` on an item codec gives the codec at a path, together with the path. A path through a union resolves where each option that the path reaches stores one codec there. A name that only some options declare, or that options declare with different codecs, gives a codec that returns a `CodecError` on use.

`narrow(pattern)` narrows a path through a union to the options that the pattern does not separate. The pattern is an object codec, read as `extract` reads an object pattern: each object of the pattern is open. The narrowing acts at run time and in the type, and adds no segment to the path. The table can still hold an item of a dropped option. A write at the narrowed path is safe only under the preconditions of the path: put the preconditions in the `ConditionExpression` of the write.

`preconditions(at(...))` states the preconditions as data, a conjunction of `in`, `type` and `exists` facts at a path. A path with no `narrow` has no precondition. Where a clause key stores a term that no exact condition states, such as a list, `preconditions` is a `CodecError` that names the path. Test the result with `failed`.

```ts
import { at, discriminatedUnion, failed, item, narrow, number, object, path, preconditions, string } from 'rotorise'

const Order = item(object({
  pay: discriminatedUnion('tender', [
    object({ tender: string('CARD'), cardId: string }),
    object({ tender: string('CASH'), drawer: number }),
  ]),
}))

const cardId = at(narrow(at(Order, ['pay']), object({ tender: string('CARD') })), ['cardId'])
path(cardId)           // 'pay.cardId'
preconditions(cardId)  // the Result of [{ segments: ['pay', 'tender'], in: [{ S: 'CARD' }] }]
cardId.encode('c-1')   // { S: 'c-1' }

// only the CARD option declares `cardId`
at(Order, ['pay', 'cardId']).encode('c-1')   // a CodecError that names `narrow`
```

Rotorise builds no expression string. An adapter to [Brushless](https://github.com/josher8a/Brushless) is a few lines. The caller supplies the alias of each value, with no leading `:`, because Brushless adds the `:`.

```ts
import { Condition as C, AttributePath, AttributeValue, Register } from 'brushless'
import type { Precondition } from 'rotorise'

const pathOf = (segments: readonly (string | number)[]) =>
  AttributePath.fromString(
    segments.map((s, i) => (typeof s === 'number' ? `[${s}]` : i ? `.${s}` : s)).join(''),
  )

const conditionOf = (preconditions: readonly Precondition[], alias: () => string) =>
  preconditions
    .map((g) =>
      'in' in g
        ? C.inList(
            pathOf(g.segments),
            g.in.map((value) => AttributeValue.make({ value, alias: alias() })),
          )
        : 'type' in g
          ? C.attributeType(pathOf(g.segments), AttributeValue.make({ value: { S: g.type }, alias: alias() }))
          : C.attributeExists(pathOf(g.segments)),
    )
    .reduce((all, one) => C.and(all, one))

const guards = preconditions(cardId)
if (failed(guards)) throw guards
let n = 0
const register = Register.make()
C.build(conditionOf(guards, () => `v${n++}`), register)
// => '#pay.#tender IN (:v0)', and `register` holds the names and the value
```

A write with an empty precondition list needs no condition. Check the list before the fold.

### Custom Separator

```ts
const Table = tableEntry<User>()(schema, '-')
// Keys use '-' instead of '#': 'ORGID-acme-ID-123'
```

## Error Handling

All runtime errors throw `RotoriseError` (exported), so you can distinguish library errors from your own.

```ts
import { RotoriseError } from 'rotorise'

try {
  Table.key('PK', { /* missing required attrs */ })
} catch (e) {
  if (e instanceof RotoriseError) { /* ... */ }
}
```

## Contributing

Open an [issue](https://github.com/josher8a/Rotorise/issues) or a PR. We are open to any kind of contribution and feedback.

## License

[Apache-2.0](LICENSE)