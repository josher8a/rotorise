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

### `tableEntry<Entity>()(schema, options?)`

Entry point for defining a DynamoDB table schema. Returns an object with the methods below.

The double-call `<Entity>()(schema)` is required because TypeScript does not support partial type parameter inference — `Entity` is explicit while `Schema` is inferred from arguments.

`options` is an object:

- **`separator`** — Joins the components of a key. Defaults to `'#'`.
- **`key`** — The keys that address the item: `{ partition: 'PK', sort: 'SK' }`, or `{ partition: 'PK' }`. `keys` builds these with no names, and `keyUpdates` refuses a change that touches them. Construction refuses a name that is no key of the schema, and one key in the two roles.
- **`indexes`** — The keys of each secondary index, by the name of the index: `{ GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' } }`. `keyCondition` with the name of an index reads these. Construction refuses a name that is no key of the schema, and one key in the two roles of an index.
- **`codec`** — The attributes of the item, which `toItem` and `fromItem` encode and decode.

### `.key(keyName, attributes, config?)`

Builds a specific key value from the given attributes.
It throws a `RotoriseError` where a segment of a component holds the separator, because the key
would read back as another list of segments. The message names the component, and never the value.
A transform whose tag or value prints the separator is refused too, and so is `.toEntry(item)`.

```ts
UserTable.key('PK', { orgId: 'acme', id: '123' })
// => 'ORGID#acme#ID#123'

UserTable.key('GSI1SK', { email: 'a@b.com' })
// => 'a@b.com'
```

**`config` options:**

- **`depth`** — Limit composite key to the first N components. Useful for `begins_with` queries.
- **`allowPartial`** — When `true`, stops building the key at the first component whose value is `undefined`, `null` or `''`, instead of throwing. The type is the union of the prefixes that the builder can print: a component that can be absent ends a prefix there. A `string` component keeps its continuation, because a type cannot remove `''` from `string`.
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

Strips the computed keys of a table entry and returns the raw entity. A read never reads a key:
a row with a correct key, a stale key, or no key gives one entity.

```ts
const user = UserTable.fromEntry(item)
// user => { orgId: 'acme', id: '123', role: 'admin', email: 'a@b.com' }
```

`fromEntry` cannot fail. `fromItem` returns a `Result`, because the decode of the item can fail.

### `.keys(names?, attributes)`

Builds the named keys as DynamoDB attributes, which is the shape of the `Key` of a request.
Without `names`, it builds the keys that the `key` option names, the partition key first.
It throws a `RotoriseError` where the attributes build no value for a named key, because a request
cannot address an item with a key that does not exist.

```ts
import { tableEntry } from 'rotorise'

type Pet = { petId: string; species: 'CAT' | 'DOG'; shelterId: string; age: number }

const PetTable = tableEntry<Pet>()(
  { PK: ['petId'], SK: ['species'], GSI1PK: ['shelterId'], GSI1SK: 'age' },
  { key: { partition: 'PK', sort: 'SK' } },
)

PetTable.keys({ petId: 'p1', species: 'CAT' })
// => { PK: { S: 'PETID#p1' }, SK: { S: 'SPECIES#CAT' } }

PetTable.keys(['GSI1SK'], { age: 3 })
// => { GSI1SK: { N: '3' } }
```

### `.keyCondition(index?, attributes)`

Builds the condition of a query as names and encoded values. Without `index`, it reads the keys
that the `key` option names. With `index`, it reads the keys of that index, and the result carries
the name of the index.

- The attributes give every component of the partition key. A query reads one whole partition, so
  a missing component throws a `RotoriseError`.
- Where the attributes give the whole sort key, the sort condition is `equals`.
- Where the attributes give a leading part of a list sort key, the sort condition is `beginsWith`,
  with a trailing separator. The separator keeps `STATUS#AVAILABLE` from selecting
  `STATUS#AVAILABLE_SOON`.
- Where the attributes hold no component of the sort key, the result has no sort condition.
- A later component without the first, or a `null` arm, selects nothing and throws a `RotoriseError`.

```ts
const PetTable = tableEntry<Pet>()(
  { PK: ['petId'], SK: ['species'], GSI1PK: ['shelterId'], GSI1SK: ['species', 'petId'] },
  {
    key: { partition: 'PK', sort: 'SK' },
    indexes: { GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' } },
  },
)

PetTable.keyCondition('GSI1', { shelterId: 's1', species: 'CAT' })
// => { index: 'GSI1',
//      partition: { name: 'GSI1PK', value: { S: 'SHELTERID#s1' } },
//      sort: { name: 'GSI1SK', beginsWith: { S: 'SPECIES#CAT#' } } }
```

`BETWEEN` and the comparisons `<`, `<=`, `>` and `>=` are not built. An adapter to
[Brushless](https://github.com/josher8a/Brushless) is a few lines:

```ts
import { AttributeName, AttributeValue, KeyCondition, Register } from 'brushless'
import type { KeyCondition as Condition } from 'rotorise'

const toBrushless = ({ partition, sort }: Condition) => ({
  pk: {
    name: AttributeName.make(partition.name),
    value: AttributeValue.make({ value: partition.value, alias: partition.name }),
  },
  ...(sort && {
    sk:
      'equals' in sort
        ? KeyCondition.equals(
            AttributeName.make(sort.name),
            AttributeValue.make({ value: sort.equals, alias: sort.name }),
          )
        : KeyCondition.beginsWith(
            AttributeName.make(sort.name),
            AttributeValue.make({ value: sort.beginsWith, alias: sort.name }),
          ),
  }),
})

const condition = PetTable.keyCondition('GSI1', { shelterId: 's1', species: 'CAT' })
const register = Register.make()
KeyCondition.build(toBrushless(condition), register)
// => '#GSI1PK = :GSI1PK AND begins_with(#GSI1SK, :GSI1SK)', and `IndexName` is `condition.index`
```

### `.keyUpdates(changed)`

Rebuilds the keys that a change touches, as the `SET` and `REMOVE` clauses of an
`UpdateExpression`. A key that the item writes after the change is in `set`. A key that the item
omits after the change, for example at a `null` arm, is in `remove`. A key is in one of the two.

```ts
PetTable.keyUpdates({ shelterId: 's2' })
// => { set: { GSI1PK: { S: 'SHELTERID#s2' } }, remove: [] }
```

A change must give every component of each key that it touches. The keys tie their components
together, so the type and the run time refuse a change that writes part of a block, and the
message names the whole block. A change that touches a key that the `key` option names is refused,
because DynamoDB cannot update a key attribute of the table: write the new item and delete the old one.

### `.toItem(item)` and `.fromItem(row)`

With the `codec` option, the entry writes and reads DynamoDB attributes. `toItem` encodes the item
and adds its keys. `fromItem` deletes the keys and decodes the rest. Each returns a `Result`: the
value, or a `CodecError`.

```ts
import { number, string, tableEntry } from 'rotorise'

type Pet = { petId: string; age: number; name: string }

const PetTable = tableEntry<Pet>()(
  { PK: ['petId'], GSI1SK: 'age' },
  { codec: { petId: string, age: number, name: string }, key: { partition: 'PK' } },
)

PetTable.toItem({ petId: 'p1', age: 3, name: 'Rex' })
// => { petId: { S: 'p1' }, age: { N: '3' }, name: { S: 'Rex' },
//      PK: { S: 'PETID#p1' }, GSI1SK: { N: '3' } }
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

An arm can be a discriminated spec of the variants that its literal selects, so a key follows a
hierarchy of unions. An inner discriminator exists only on the variants of its arm. A literal that
names no arm throws, at each level.

```ts
type Thing =
  | { TAG: 'OBJECT'; id: string; material: string }
  | { TAG: 'ANIMAL'; SPECIE: 'CAT'; id: string; color: string }
  | { TAG: 'ANIMAL'; SPECIE: 'DOG'; BREED: 'LAB' | 'PUG'; id: string }

const ThingTable = tableEntry<Thing>()({
  PK: ['id'],
  SK: {
    discriminator: 'TAG',
    spec: {
      OBJECT: ['material', 'id'],
      ANIMAL: {
        discriminator: 'SPECIE',
        spec: {
          CAT: ['color', 'id'],
          DOG: { discriminator: 'BREED', spec: { LAB: ['BREED', 'id'], PUG: null } },
        },
      },
    },
  },
})

ThingTable.key('SK', { TAG: 'OBJECT', id: '1', material: 'wood' })
// => 'MATERIAL#wood#ID#1'

ThingTable.key('SK', { TAG: 'ANIMAL', SPECIE: 'DOG', BREED: 'LAB', id: '4' })
// => 'BREED#LAB#ID#4'
```

### Components that Read a Path

A component can name a value below the top level. A path joins names with `.` and reads into
objects only. The key prints the last name of the path, or the tag of an options object. The key
input holds the paths that the key reads, and no sibling of a path. An absent name on the path is an
absent component. A discriminator can be a path too.

```ts
type Owner = { ownerId: string; extra: { deep: { id: string; note: string } } }
type Handoff =
  | { type: 'INTAKE'; id: string; to: Owner }
  | { type: 'ADOPTION'; id: string; to: Owner; from: Owner }
  | { type: 'RELEASE'; id: string; from: Owner }

const HandoffTable = tableEntry<Handoff>()({
  PK: ['id'],
  GSI1PK: {
    discriminator: 'type',
    spec: {
      INTAKE: [['to.ownerId', { tag: 'ownerId' }]],
      ADOPTION: [['to.ownerId', { tag: 'ownerId' }], 'to.extra.deep.id'],
      RELEASE: null,
    },
  },
})

HandoffTable.key('GSI1PK', { type: 'INTAKE', to: { ownerId: 'u1' } })
// => 'ownerId#u1'

HandoffTable.key('GSI1PK', {
  type: 'ADOPTION',
  to: { ownerId: 'u1', extra: { deep: { id: 'd9' } } },
})
// => 'ownerId#u1#ID#d9'
```

A transform on a path needs an annotation on its parameter, such as
`['to.ownerId', (x: string) => x]`. The checker refuses an annotation that the value at the path
does not fit. A path whose value can be absent needs a transform with a default. The options object
is for a path only. A top-level name that the item holds as an attribute with a `.` reads as that
attribute.

### An Arm that Groups Literals

A match takes `cases` in place of `spec` when several literals share one arm. A case is a list of
literals and the arm that they share. The cases are a partition of the literals: a literal in two
cases, or a literal that no case names, is refused. An arm reads only the attributes that each
option of its case holds. A case nests, and the keys are the keys of the same match written with
`spec`.

```ts
const HandoffsByOwner = tableEntry<Handoff>()({
  PK: ['id'],
  GSI1PK: {
    discriminator: 'type',
    cases: [
      [['INTAKE', 'ADOPTION'], [['to.ownerId', { tag: 'ownerId' }]]],
      [['RELEASE'], null],
    ],
  },
})

HandoffsByOwner.key('GSI1PK', { type: 'ADOPTION', to: { ownerId: 'u1' } })
// => 'ownerId#u1'
```

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

### A Key of One Attribute

A key attribute of DynamoDB is `S`, `N` or `B`. A list key joins its parts, so it is always `S`. A
key of one attribute (`GSI1SK: 'age'`, or an attribute arm of a match) copies the attribute, so it
takes the member of that attribute: a string is `S`, a number is `N`, and a `Uint8Array` is `B`.
With a codec, the key takes the member that the codec writes for the field, so a decimal that the
codec writes as `N` is an `N` key. An `N` sort key orders by number, where an `S` key orders `'10'`
before `'9'`.

- The type refuses a key of one attribute that is none of `S`, `N` and `B`, such as a boolean.
- One key name has one member, so the type refuses a match whose arms give `S` and `N`.
- `null` and `undefined` give no key in every method.
- DynamoDB refuses an empty string or an empty `Uint8Array` at a key, so `toEntry`, `keys`, `toItem`
  and `keyUpdates` throw a `RotoriseError` for one. The message names the key and not the value.
- DynamoDB limits a partition key to 2048 bytes and a sort key to 1024 bytes. DynamoDB refuses a
  write over the limit, and Rotorise does not check the length.

### Custom Separator

```ts
const Table = tableEntry<User>()(schema, { separator: '-' })
// Keys use '-' instead of '#': 'ORGID-acme-ID-123'
```

The separator is a slot of `options`, so the type of a key holds the default `'#'` where `options`
names no separator. A bare string as the second argument is refused.

## Error Handling

The key builders throw `RotoriseError` (exported), so you can distinguish library errors from your own. `toItem` and `fromItem` return a `CodecError` as a value where the codec refuses the item or the row. A key that cannot be built throws `RotoriseError` in every method.

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