# Known defects of this repository

One entry per defect. Each entry opens with one of three words.

- **Known**: observed, and reproduced by a command in this file.
- **Suspected**: the observation is real and the effect is not established.
- **Partially mitigated**: the effect is reduced, and the entry says what remains.

Each entry gives the observation, the effect, and the pin: the test, guard or refutation that
holds the defect in place. An entry with no pin says so, because an unpinned defect is one a later
pass closes by accident and nobody notices.

Each entry names declarations and files. It points at no section number, because a section number
moves and a declaration name does not.

---

## Known: the iso premise of the wrapper rule is stronger than the proof consumes

**Observation.** The specification's wrapper rule demands total cancellation on the two carriers:
one composite is the identity on the held set and the other is the identity on the inner carrier.
The mechanization asks for less. `IsoCancels` in `Alg/Combinators.lean` is `IsoCancelsAt` at the
host. `IsoCancelsAt` restricts both directions to the values the write half accepts: one clause per
direction, each guarded by the encode being defined. The docstring of `IsoCancelsAt` says it is the
domain-restricted form the laws actually need.

**Effect.** A caller pays a premise the proof does not use. The theorems that consume the premise,
`Lawful.held1` through `Obl1`, `LawfulCore.through` and `Lawful.through`, close on the restricted
form alone, so the totality the specification asks for is never appealed to. This is the mirror of a
premise that is too weak, and the same defect class: a rule and its mechanization disagree about the
strength of an obligation, and the disagreement is in the direction that costs a user rather than
the model.

**Pin.** The blueprint asserts the gap and no theorem does. The `(held)` node in
`formal/docs/blueprint/src/content.tex` shows the total premise, links `IsoCancels`, and carries no
`\leanok`, so the rendered graph marks the rule stated rather than formalised as written.
`IsoCancels` is the restricted statement and the three theorems above are the evidence that the
restriction suffices, but no theorem states that the total form is unnecessary.

**Open.** Either the specification's premise is loosened to what the proof uses, or the model is
asked to discharge the stronger one. That is a specification decision.

---

## Known: the type of extract drops a member whose pattern splits below a union slot of a recursive union entry

**Observation.** The run time reads a `ref` to a union entry option by option, and keeps a member
where one option of the entry fits the pattern. The type reads a union entry through the specs of
its options, and reads a union slot of `ref`s through the split of its parts. A pattern that needs
the split below a union slot of `ref`s, where one of the `ref`s names a recursive union entry,
reads as no fit. Measured 2026-10-31 with `tsc --noEmit` and `npx vitest --run`:

    const s = scope({
      Leaf: object({ kind: string('leaf') }),
      Branch: object({ kind: string('branch'), kids: union([ref('Leaf'), ref('Tree')]) }),
      Tree: union([ref('Leaf'), ref('Branch')]),
      Holder: object({ tag: string('holder'), tree: ref('Tree') }),
      Other: object({ tag: string('other'), tree: ref('Leaf') }),
    })
    const p = object({ tree: object({ kind: string('branch'), kids: object({ kind: string('leaf') }) }) })
    extract(union([s.Holder, s.Other]), p)
      runtime: keeps Holder
      type:    Decoded is never

**Effect.** The type of `extract(...)` is narrower than the value: a value that the run time gives
does not fit the type. The pattern that names the branch entry alone reads exactly, and so does a
pattern that names the leaf entry and the branch entry as a union.

**Pin.** `src/codec/spec/union/codec.slice.spec.ts`: an object pattern reads each option of a union
entry that a `ref` names, an option that names another union entry, an option that is an entry of
another scope, and a base entry. No test pins the recursive case above.

---

## Known: the type of exclude keeps a member that a binary literal clause drops at run time

**Observation.** The run time compares the bytes of a binary literal clause with the bytes of each
member, and exclude drops a member whose bytes the clause names. The type carries no bytes: the
owner rules that a binary literal stays coarse at the type level. So the type keeps that member.
Measured 2026-11-10: the clause of each exclude refuse id of the type bridge is a binary literal.
One example:

    const r = exclude(union([object({ a: binary(new Uint8Array([1, 2])) }), object({ c: string })]),
      object({ a: binary(new Uint8Array([1, 2])) }))
      runtime: member 0 dropped
      type: the decoded type of r still admits member 0

**Effect.** The result type of exclude is wider than the value. Every value fits the type, and a
member that the run time dropped stays in the type.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 23 such
ids, measured 2026-11-10.

---

## Known: the type of meet builds two caller adapters of one type

**Observation.** The run time refuses a `held` part or an older reading where the two parts are
apart in neither view and neither side fits the other, because an opaque function decides which
common rows relate one value. The type states the refusal at the top node of each factor: the fit
is false in both orders, the stored views are not apart, and the decoded views overlap. One call
builds in the type and throws at run time. Measured 2026-11-01 with `npx vitest --run` and
`tsc --noEmit`:

    meet(h1, h2)                     two adapters of a caller, of one type

The run time tells two adapters of a caller apart by object identity, and a structural type holds
no identity. So `meet(h, h)` and `meet(h1, h2)` have one type, and a refusal of the pair refuses
`meet(h, h)`, which the run time builds.

**Effect.** The call builds in the type and throws at run time.

**Pin.** `src/codec/spec/object/codec.meet.spec.ts` pins the refused pairs, the pairs that build,
and the pair of one type.

---

## Known: the type of union builds two options that an adapter keeps from being shown compatible

**Observation.** The run time refuses a union where two options overlap and an adapter or a `ref`
on a side keeps the declaration from showing that a value both admit is written to one attribute.
The type of `union` states no such refusal. Measured 2026-11-01 with `npx vitest --run` and
`tsc --noEmit`:

    union([object({ x: legacy({ current: string, older: decimal }) }), object({ x: number })])
      type checker: builds
      runtime:      throws, the two options are not shown compatible

**Effect.** The call builds in the type and throws at construction.

**Pin.** `src/codec/spec/object/codec.meet.spec.ts`: the type builds an older reading below a
field, and the run time refuses the union.

---

## Partially mitigated: a term that holds no value escapes the never rules where the term does not decide it

**Observation.** The predicate in `src/codec/term.ts` that decides that a term holds no value answers `true` for `never`, for a union
whose every option holds no value, and for a `held` whose inner term holds none. The list position
rule, the field rule, the meet and `nullable` read it. One form holds no value in the model and
answers `false`:

    list(string, refine(string, (_: string): _ is string => false))   // builds

**Effect.** Such a list or object holds no value and builds. A refinement stays out because no
function decides that a closure admits nothing.

**What is mitigated.** `union([])`, a union of empty options, a `held` over each of these, and each
of these through a `ref` are refused where `never` is, in the type and at run time.

**Pin.** `src/codec/spec/surface/codec.resolution.spec.ts` pins the refinement and the `held`.

---

## Known: the type of a slice reads 63 parts of an option where the run time reads 1024

**Observation.** The run time splits an option into at most 1024 parts of its normal form before it
reads a union pattern. The type splits an option into at most 63 parts. At 64 parts the type
cannot decide the fit, and the slice keeps the option. Measured 2026-11-02 with `npx tsc --noEmit`
and the pin below:

    const big = union([object({ x: string('l00', …, 'l64') })])
    exclude(big, union([object({ x: string('l00', …, 'l31') }), object({ x: string('l32', …, 'l64') })]))
      runtime: never
      type:    the option is kept

**Effect.** The type of exclude is wider than the value past the bound. The type of extract keeps
the option, as the run time keeps it.

**Pin.** `src/codec/spec/union/codec.slice.parts.spec.ts`: a split that passes the bound keeps the
option.

---

## Known: the decoded type of an object with a rest admits the type of a declared field at an undeclared name

**Observation.** The decoded type of an object with a rest intersects the spec with an index
signature. TypeScript checks each declared key against the index of the intersection, so the index
admits the type of each declared field beside the type of the rest. The host has no type for "each
undeclared key holds the type of the rest". Measured 2026-10-28 with `npx vitest --run` and the pin
below:

    const rested = object({ a: string }, [string, optional(number)])
    const wide: Decoded<typeof rested> = { a: 'x', c: 'y' }
      type checker: accepted
      runtime:      rested.encode(wide) fails, because c holds no number

**Effect.** The decoded type is wider than the value. Each value that the run time gives fits the
type. A value with the type of a declared field at an undeclared name compiles, and the run time
refuses the value.

**Pin.** `src/codec/spec/object/codec.rest.spec.ts`: the type admits a declared field type at an
undeclared name, and the run time refuses the value.

---

## Partially mitigated: the type of a slice keeps a held option inside the union of a scope entry where the run time drops it

**Observation.** A `held` whose inner term is a `ref` to an empty entry holds no value, and an
exclusion drops it at run time. The type reads the name in the scope that binds it where the option
is the entry. Where the `held` is an option of the union of an entry, the head of the slice carries
no scope, so the type cannot read the name. Measured 2026-11-02 with `npx vitest --run` and
`npx tsc --noEmit` and the pin below:

    const { Pets } = scope({ Gone: never, Pets: union([held(ref('Gone'), string, …), object({ name: string })]) })
    exclude(Pets, object({ name: string }))
      runtime: never
      type:    the held option is kept

**Effect.** The type of exclude is wider than the value. Each value that the run time gives fits
the type.

**What is mitigated.** An option that is itself the entry is read in its scope, in the type and at
run time.

**Pin.** `src/codec/spec/union/codec.slice.empty.spec.ts`: the option that is the entry is dropped
in the type, and the held option inside the union of an entry is kept in the type and dropped at
run time.

---

## Known: the type of a slice by a union pattern stops at 90 literals of one field

**Observation.** An exclusion that splits one field of literals into two halves of a union pattern
type-checks at 89 literals and keeps the option. At 90 literals the type checker stops. The bound
of the parts does not move the wall. Measured 2026-11-10 with `tsc --noEmit` on TypeScript 7 and on
TypeScript 6:

    const big = union([object({ x: string('l00', …, 'l89') })])
    exclude(big, union([object({ x: string('l00', …, 'l44') }), object({ x: string('l45', …, 'l89') })]))
      runtime:      never
      TypeScript 7: TS5114, instantiations of type 'FlatParts' appear infinitely circular
      TypeScript 6: TS2589, type instantiation is excessively deep and possibly infinite

**Effect.** The call of the caller does not compile. A literal set at one field of 90 or more
literals cannot be sliced by a pattern that splits the set.

**Pin.** None. A pin compiles a literal set of 90 at one field in the suite, and its cost in
instantiations is not measured.

---

## Known: the options of a slice type follow the union order of the compiler

**Observation.** A slice splits an option one key at a time. The run time reads the keys in the
order of the declaration. The type reads the keys through a tuple that it builds from their union,
and the order of a union is the order of the type identities of the compiler. TypeScript 7
orders `'p' | 'q' | 'w'` as `["p", "q", "w"]`. TypeScript 6 orders it as `["w", "q", "p"]`. Measured
2026-11-06 with `npm run check` (TypeScript 7) and `npx tsc --noEmit` (TypeScript 6):

    const lit = (k, v) => object({ [k]: string(v) })
    const X = object({ p: union([lit('t','A'), lit('t','B'), lit('t','C')]),
                       q: union([lit('u','X'), lit('u','Y')]), w: union([lit('s','1'), lit('s','2')]) })
    const m1 = object({ p: lit('t','A') })
    const m2 = object({ q: lit('u','Y'), w: lit('s','1') })
    const m3 = object({ p: lit('t','B'), w: lit('s','2') })
    exclude(X, union([m1, m2, m3]))
      runtime:    3 options
      TypeScript 7: 3 options
      TypeScript 6: 2 options

**Effect.** On TypeScript 6, a slice whose pattern splits two or more keys can type a tuple of
options that differs from the options of the value. TypeScript 5 is not measured. The decoded
type admits the same rows on each compiler, because each tuple covers the same rows. A sort of the keys in the type
gives one order on each compiler. Each form of the sort that was tried stops at TS5114 on
TypeScript 7 and TS2589 on TypeScript 6.

**Pin.** `src/codec/spec/union/codec.slice.cover.spec.ts` asserts the options of the fold of
three patterns at run time only. `npm run check` and `npx tsc --noEmit` check the type of the
other rows of the spec, which agree on both compilers.

---

## Known: the type of meet builds a call of fewer than two factors

**Observation.** The run time refuses a meet of fewer than two factors at construction. The type of
`meet` takes a tuple of codecs of any length, and states no lower bound. Measured 2026-11-10 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    meet(string)
    meet()
      type checker: builds
      runtime:      throws, a meet is taken of two or more factors, and fewer were given

**Effect.** The call builds in the type and throws at construction.

**Pin.** None. No test calls `meet` with fewer than two factors.

---

## Known: the type of a literal former builds a literal of no value

**Observation.** The run time refuses a literal that names no value at construction. The type of
each literal former takes the values as a rest parameter, and states no lower bound. Measured
2026-11-10 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    string()   number()   decimal()   boolean()   binary()
      type checker: builds
      runtime:      throws, a literal admits one of a non-empty set of values

The message prints the base of the literal. The base of `decimal` is `number`, so the message of
`decimal()` names `number()`.

**Effect.** The call builds in the type and throws at construction. The message of `decimal()`
names a former that the caller did not call.

**Pin.** `src/codec/spec/literal/codec.literalbase.spec.ts` pins the throw at each base. No test
pins the text of the message.

---

## Known: the type of discriminatedUnion reads a number tag as JS prints the number, where the run time reads the stored text

**Observation.** A tag is the stored text of a literal, and the run time compares the stored text
of two tags. The type spells a number tag as a template literal spells the number. So a number that
JS prints with an exponent differs from the stored text of the number in the type. One call
disagrees in each direction. Measured 2026-11-10 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`:

    discriminatedUnion('size', [object({ size: number(1e21), a: string }),
                                object({ size: decimal('1000000000000000000000'), b: string })])
      type checker: builds
      runtime:      throws, two options answer to 'size' = '1000000000000000000000'

    discriminatedUnion('size', [object({ size: number(1e21), a: string }),
                                object({ size: string('1e+21'), b: string })])
      type checker: refused, options 0 and 1 answer to the same discriminator value
      runtime:      builds

The first call gives the same two results with `string('1000000000000000000000')` in the second
option.

**Effect.** The first call builds in the type and throws at construction. The second call does not
compile, and the run time builds the union.

**Pin.** `src/codec/spec/union/codec.dunion.lookup.spec.ts` pins the stored text of a number tag
that JS spells with an exponent, at run time, and the refusal of one text at two bases. No test
pins the two calls above.

---

## Known: the type of at refuses a path below two options that are one codec with a caller function

**Observation.** A path below a union resolves where each option gives the same codec at the path.
The run time compares the terms of the options, and tells two functions of a caller apart by object
identity. A structural type holds no identity. So where the options at the path have one type and
hold a function of a caller, the type answers that the path is ambiguous. Measured 2026-11-10 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    const h = refine(object({ x: string }), (v): v is { x: string } => v.x.length > 0)
    const Pets = item(object({ op: union([h, h]) }))
    at(narrow(at(Pets, ['op']), object({ x: string })), [])
      type checker: refused, the path is ambiguous: no one codec stands at the path
      runtime:      gives the codec

The call gives the same two results where `h` is
`legacy({ current: object({ x: string }), older: object({ x: string }) })`. The case where `h` is a
`held` of a caller adapter is not measured.

**Effect.** The call does not compile, and the run time gives the codec.

**Pin.** None.

---

## Suspected: a term that no former built is judged at its top node, at each option of a union and at the element of a set only

**Observation.** The model states the obligation of each operation at each position of a term
(`Obligations` in `Lang/ScopeSound.lean`). The compatibility of each two options of a union is one
such obligation (`TOp.obl`). The run time judges one node at a time. A former judges the node that
the former builds, so a term that the formers built is judged at each node. A slice, a meet or an
opening builds a term directly. For such a term, the function in `src/codec/capabilities.ts` that
gives the codec of a term judges the top node. In `src/codec/denote.ts`, the `union` row judges each
option, and the `set` row judges the element. No row judges a field of an object, the open block,
an element of a list, or the inner term of `held`, `refine` or `legacy`. Measured 2026-11-10 with
`npx vitest --run`, where `u` is a union of two adapters over `string`, which the judgment refuses:

    codecOfTerm(u)                                                                    throws, not shown compatible
    codecOfTerm({ kind: 'union', options: [u] })                                      throws
    codecOfTerm({ kind: 'set', elem: u })                                             throws
    codecOfTerm({ kind: 'object', body: { fields: { a: { mark: 'req', t: u } } } })   builds
    codecOfTerm({ kind: 'object', body: { fields: {}, rest: u } })                    builds
    codecOfTerm({ kind: 'list', pre: [u], suf: [] })                                  builds
    codecOfTerm({ kind: 'list', pre: [], spread: u, suf: [] })                        builds
    codecOfTerm({ kind: 'held', inner: u, outer, f, g })                              builds
    codecOfTerm({ kind: 'refine', inner: u, q })                                      builds
    codecOfTerm({ kind: 'legacy', inner: u, r })                                      builds

**Effect.** Not established. The seven terms that build are written by hand, and no call of `src/`
is shown to build such a term. An opening reaches the `union` row: `lean.pool.spec.ts` opens a
pattern and reads the refusal at an option. If a slice, a meet or an opening puts a refused union
below a field, an element or an adapter, the term has a codec that the obligations of the model do
not cover.

**Pin.** `src/codec/spec/union/codec.judgechild.spec.ts` pins the two rows that judge a child. No
test pins the seven terms that build.

---

## Suspected: the model proves no law for a term that holds an alternate reader below its top

**Observation.** `TOp.rule` in `Lang/ScopeSound.lean` answers `none` at `legacy`, so a term that
holds a `legacy` at a position is not typed. `Scoped.Closed.sound` takes a typed closed codec, so
the theorem states nothing of such a term. `Closed.extendRead_lawfulCore` in
`Dynamo/Lang/ScopeSound.lean` proves `LawfulCore` for an alternate reader over a typed closed
codec, so the reader of that theorem is at the top. `tuple_retract` and `list_retract` in
`Alg/Positions.lean` give the retraction of a list from `LawfulCore` of each element. `zip_canon`
gives the definedness clause of `canon` over a row of codecs. No theorem gives `canon` or `writes`
of a list, or a law of an object or a union, from `LawfulCore` of a child. The run time builds the
reader below a field:

    object({ rate: legacy({ current: decimal, older: string }) })

**Effect.** Not established. The three core laws of the codec of such a term rest on no theorem.
No term that breaks a core law is known.

**Pin.** `legacyClosed_untyped` in `Lang/ScopeSound.lean` pins that a term with a `legacy` is not
typed. No test and no theorem pins the laws of a term with a `legacy` below a field.

---

## Known: the type of key reads a config that can be undefined, or a slot of type `any`, as one literal

**Observation.** A slot of the config of `key` holds one literal, undefined alone, or nothing.
The type refuses `number` and each union at a slot. Two forms pass the type, and the run time
builds another key. An optional parameter strips undefined from the type of the argument, so a
config of type `{ depth: 1 } | undefined` has the type of depth 1. A slot of type `any` passes each
refusal, because a refusal is an intersection with the parameter. Measured 2026-11-11 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    const Pets = tableEntry<{ shelterId: string; petId: string }>()({ SK: ['shelterId', 'petId'] })

    const maybe = undefined as { depth: 1 } | undefined
    Pets.key('SK', { shelterId: 's' }, maybe)
      type checker: builds, with the type "SHELTERID#s"
      runtime:      throws, Attribute petId not found

    const anyDepth: any = undefined
    Pets.key('SK', { shelterId: 's' }, { depth: anyDepth })
      type checker: builds
      runtime:      throws, Attribute petId not found

**Effect.** Each call builds in the type with no second component, and throws where the value is
undefined at run time. The type of the first call is the key of depth 1, and the run time builds
the whole key.

**Pin.** None for the two forms. `src/codec/spec/object/codec.keydepth.spec.ts` pins the refusal of
an optional slot, of `number`, and of two literals at one slot.

---

## Known: the type of a key component refuses a default beside an options object, where the run time reads the default

**Observation.** A component of a key is a name, or a tuple of a name, a transform and a default.
The transform is a function, or an options object such as `{ tag: 'DOSE' }`. The type takes a
default beside a function only. The run time reads the default beside each form. Measured
2026-11-11 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Pet = { petId: string; vaccine?: { lastDose: string } }

    tableEntry<Pet>()({ PK: ['petId'], SK: [['vaccine.lastDose', { tag: 'DOSE' }, 'x']] })
      type checker: refused, 'tag' does not exist in type '(key: any) => TransformShape'
      runtime:      builds, and toEntry({ petId: 'p1' }) gives the SK "DOSE#x"

    tableEntry<Pet>()({ PK: ['petId'], SK: [['vaccine.lastDose', (dose: string) => dose, 'x']] })
      type checker: builds
      runtime:      builds, and toEntry({ petId: 'p1' }) gives the SK "LASTDOSE#x"

TypeScript 6 prints the first refusal as `is not assignable to type 'never'`, with no reason.

**Effect.** The first call does not compile, and the run time builds the entry and reads the
default.

**Pin.** None. No test gives a default beside an options object.

---

## Known: the type of a key admits a path into a union of objects where one option lacks the name

**Observation.** The type refuses a component with no default where the value at the path can be
absent. The type of a path into a union of objects is the type at the options that hold the name.
An option that lacks the name adds no undefined, so the refusal does not see the option. Measured
2026-11-11 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Doc = { id: string; meta: { kind: 'a'; a: string } | { kind: 'b'; b: string } }
    const Docs = tableEntry<Doc>()({ PK: ['id'], SK: ['meta.a'] })
      type checker: builds
      runtime:      builds

    Docs.toEntry(doc).SK   // doc: Doc
      type checker: `A#${string}`

    Docs.toEntry({ id: 'd1', meta: { kind: 'a', a: 'x' } })
      runtime:      gives the SK "A#x"

    Docs.toEntry({ id: 'd1', meta: { kind: 'b', b: 'x' } })
      runtime:      throws, Attribute meta.a not found

**Effect.** The entry builds, the type of the key states a text for each item of the entity, and
`toEntry(item)` throws for each item of the option that lacks the name.

**Pin.** None. `src/codec/spec/object/codec.keypath.spec.ts` pins the refusal of a path whose value
can be absent, for an optional name and no union.

---

## Known: a key element that two rules refuse prints `never` at the head of the error

**Observation.** A refusal of a key element is an intersection of the element with a message. Two
refusals of one element give two messages at one property, and the compiler reduces the
intersection to `never`. The head of the error then names no reason. The line below the head
prints the intersection, and can elide the second message. Measured 2026-11-11 with `tsc --noEmit`
on TypeScript 7 and on TypeScript 6:

    type Pet = { id: string; meta: { note: string } | null }
    tableEntry<Pet>()({ PK: ['id'], SK: ['meta.note'] },
                      { codec: { id: string, meta: nullable(object({ note: string })) } })
      head:      Type '"meta.note"' is not assignable to type 'never'
      next line: the two messages: the path can be absent, and the codec cannot address the path

    tableEntry<Pet>()({ PK: ['id'], SK: ['meta.note'] })
      head:      ... not assignable to type '"meta.note" & ErrorMessage<"'meta.note' can be absent:
                 give a transform with a default">'

    type Flat = { petId: string; 'owner.name': string }
    tableEntry<Flat>()({ PK: ['petId'], GSI1PK: 'owner.name' })
      head:      Type '"owner.name"' is not assignable to type 'never'
      next line: the first message, and `ErrorMessage<...>` for the second

    tableEntry<Flat>()({ PK: ['petId'], GSI1PK: ['owner.name'] })
      head:      the message: a `.` in a key name is a path separator

The run time builds the first entry, and reads the path through the codec. `toEntry(item)` gives
the SK `NOTE#n` where the value below the first name is an object, and throws
`Attribute meta.note not found` where that value is `null`.

**Effect.** A reader of the head of the error gets no reason. A reader of the whole error gets one
reason or two.

**Pin.** None for the head. `src/codec/spec/object/codec.keycomponent.spec.ts` pins the refusal of
the entity whose attribute holds the `.`, for a list.

---

## Partially mitigated: the string of a document path can hold a reserved word of DynamoDB, and DynamoDB refuses the expression

**Observation.** `path` and the `toString` of the path builder give a string where each name is a
letter, then letters, digits and `_`. A reserved word of DynamoDB has that form, so a path through
a reserved word has a string. DynamoDB refuses an expression that holds a reserved word as a bare
name. Measured 2026-11-11 with `npx vitest --run` for the string, and on DynamoDB Local
(`amazon/dynamodb-local`) with the string as the ProjectionExpression of a GetItem call:

    Pets.path().data.nested.property.toString()   // "data.nested.property"
      DynamoDB Local: refused, Attribute name is a reserved keyword; reserved keyword: data

    "checks.rabies2024.status"    refused, reserved keyword: status
    "owner.nick"                  refused, reserved keyword: owner
    "name"                        refused, reserved keyword: name
    "total"                       refused, reserved keyword: total

    "#data.#nested.#property", with each name in ExpressionAttributeNames
      DynamoDB Local: gives the attribute

Each of the four other paths gives the attribute in the same way, with a placeholder for each name.

**Effect.** A caller that writes the string into an expression gets a refusal of DynamoDB for each
path that holds a reserved word. The library holds no list of the reserved words, and refuses no
such path.

**What is mitigated.** Rotorise builds no expression. Brushless, the companion library, builds the
expression: Brushless prints each name of a path as a placeholder, and writes the name into
ExpressionAttributeNames. The adapter in `README.md` gives each path to
`AttributePath.fromString(...)` of Brushless. A caller that builds each expression with Brushless
sends no bare name. What remains is a caller that writes the string into an expression by hand.
`README.md` and the docstring of `path` state that a reserved word needs a placeholder.

**Pin.** None. No test of this repository sends an expression to DynamoDB, and no test runs
Brushless. The measurement is on DynamoDB Local, and not on the DynamoDB service.

---

## Known: a pin of an instantiation count fails on a rise above 20 percent, and passes on each fall

**Observation.** `src/Rotorise.attest.test.ts` holds two pins of an instantiation count. attest
0.34.0 fails a pin where the count rises above the pin by more than 20 percent. Where the count
falls, attest prints a line and the pin passes. Measured 2026-11-11 with `npx vitest --run`, each
line with one change of the block that the pin measures:

    pin 3751, the block reads an unbound name: 16                 passes
    pin 2091, the block builds an entry that the file holds: 577  passes
    pin 2091, one more key in the entry: 2190, 4.73 percent       passes
    pin 3751, two more calls of key: 4391, 17.06 percent          passes
    pin 2091, five more keys in the entry: 2747, 31.37 percent    fails
    pin 3751, three more calls of key: 4624, 23.27 percent        fails

**Effect.** A block that measures no call keeps the pin green. A rise of the cost below 20 percent
keeps the pin green.

**Pin.** None for a fall. A comment of `src/Rotorise.attest.test.ts` states the two facts. No check
reads the instantiation count of `npm run check`.

---

## Known: the type of keyUpdates reads a change at a name with a `.` as the attribute of that name, where the run time reads a write to the path

**Observation.** An entity can declare an attribute whose own name holds a `.` beside the object of
that path. A key name with a `.` is a path, in the type of a key and at run time. The given item of
an update is a map from a written path to a value, so the run time reads a change at `'owner.name'`
as a write to the path. The type of the change gives that name the type of the flat attribute.
Measured 2026-11-11 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Kennel = { petId: string; 'owner.name': number; owner: { name: string } }
    const Pets = tableEntry<Kennel>()({ PK: ['petId'], GSI1SK: ['owner.name'] })

    Pets.keyUpdates({ 'owner.name': 8 })
      type checker: builds
      runtime:      gives { set: { GSI1SK: { S: 'NAME#8' } }, remove: [] }

    Pets.keyUpdates({ 'owner.name': 'bea' })
      type checker: refused, Type 'string' is not assignable to type 'number'

    Pets.keyUpdates({ owner: { name: 'bea' }, 'owner.name': 8 })
      type checker: builds
      runtime:      gives { set: { GSI1SK: { S: 'NAME#8' } }, remove: [] }

    Pets.keyUpdates({ owner: { name: 'bea' } })
      runtime:      gives { set: { GSI1SK: { S: 'NAME#bea' } }, remove: [] }

The run time of the second call is not measured.

**Effect.** The type admits a number at a path that holds a string in the entity, and the key
prints the number. The type refuses the string that the path holds.

**Pin.** None for the type. `src/codec/spec/laws/codec.keyupdate.spec.ts` pins the run time: the
patch agrees with the keys of the changed pet, for a key name with a `.` also.

---

## Known: the type of a key with a component whose name is a number states no tag

**Observation.** A component of a key is a name of the entity, and the type admits a name that is a
number. The run time prints the tag of that name. The type of the key is a union of template
literal types with no tag. Measured 2026-11-11 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`:

    const Rows = tableEntry<{ 0: string; petId: string }>()({ PK: ['petId'], SK: [0] })
      type checker: builds
      runtime:      builds

    Rows.toEntry({ 0: 'zero', petId: 'p' }).SK
      type checker: a union that holds `${string}#${string}`, `${string}#false` and
                    `undefined#${bigint}`
      runtime:      gives "0#zero"

`Rows.key('SK', { 0: 'zero' })` gives the same type and the same text. A component whose name is a
string gives a type with the tag, such as `` `PETID#${string}` ``.

**Effect.** The type admits the text that the run time prints, and admits each other text with a
`#`.

**Pin.** None. No test declares a component whose name is a number.

---

## Known: the type of key refuses a partial key of no component, where the run time gives the empty string

**Observation.** The type of `key` with `allowPartial` requires the first component of the key
below. The run time gives the empty string for a partial key of no component.
Measured 2026-11-11 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    const Pets = tableEntry<{ shelterId: string; petId: string }>()({ PK: ['shelterId', 'petId'] })

    Pets.key('PK', {}, { allowPartial: true })
      type checker: refused, Property 'shelterId' is missing
      runtime:      gives ""

    Pets.key('PK', {}, { depth: 0 })
      type checker: builds, with the type ""
      runtime:      gives ""

**Effect.** The first call does not compile, and the run time gives the key. A caller writes the
empty prefix with `depth: 0`.

**Pin.** `src/Rotorise.spec.ts` pins the refusal of the type checker for the first call, with an
expected error. `src/codec/spec/object/codec.keyempty.spec.ts` pins the empty string of the run
time for the first call, behind a cast. `src/codec/spec/object/codec.keydepth.spec.ts` pins the
empty string of `depth: 0`.

---

## Known: the declaration of a consumer has no name for a cycle of a scope that goes through a list and a union only

**Observation.** A consumer that exports a codec constant with `declaration: true` needs a name for
each type that the declaration prints. The decoded type of a cyclic `scope` has a name where the
cycle goes through an object. A cycle that goes through a list and a union only has no name for
the decoded type of the union. Measured 2026-11-11 with `bash scripts/emit-check.sh --build`, with
one constant more in `scripts/emit-check/index.mts`:

    export const Cyclic = scope({ Nest: array(ref('Tags')), Tags: union([string('PUPPY'), ref('Nest')]) })
      TypeScript 5.4.5, 5.9.3, 6.0.3: no error, and the declaration holds 2 lines with the type `any`
      TypeScript 7.1.0-beta:          refused, TS5088, the inferred type references a type with a
                                      cyclic structure

**Effect.** On three compilers the reader of that declaration gets `any` in silence. On
TypeScript 7 the constant needs a type annotation.

**Pin.** None for the form: the constant is not in the project of the check. `scripts/emit-check.sh`
counts each line of a declaration that holds `any` as a failure, and a comment of
`scripts/emit-check/index.mts` states the form.

## Known: the declaration of a consumer has no name for the type of a method of an entry that the consumer exports alone, or for the function of a half-applied tableEntry

**Observation.** A consumer that exports a constant with `declaration: true` needs a name for
each type that the declaration prints. An entry that the consumer exports whole has such a
declaration, and so has the result of each method. Three methods that the consumer exports alone
have none on three compilers, and the function that `tableEntry<T>()` returns has none on each
compiler. Measured 2026-11-11 with `bash scripts/emit-check.sh --build`, with two constants more in
`scripts/emit-check/index.mts`:

    export const { key, toEntry, keys, keyCondition, keyUpdates, toItem, fromItem, path: entryPath } = CodedPets
      TypeScript 5.4.5, 5.9.3: refused at key, toEntry and keyUpdates, TS2742, the inferred type
                               cannot be named without a reference to a file of the package.
                               At key and toEntry also TS7056, the type exceeds the length that the
                               compiler prints. At toEntry also TS4023, for three marker symbols
                               that the entry does not publish
      TypeScript 6.0.3:        refused at the same three methods, with TS2883 in place of TS2742.
                               Each TS2883 line names one type that the entry does not publish
      TypeScript 7.1.0-beta:   no error
      keys, keyCondition, toItem, fromItem and path: no error on each of the four compilers
    export const forPets = R.tableEntry<PetRow>()
      each of the four compilers: refused, TS5088, the inferred type references a type with a
                               cyclic structure. Also TS2742 on TypeScript 5, TS2883 on
                               TypeScript 6 and 7, and TS7056 on each compiler but TypeScript 6.0.3

**Effect.** The build of the consumer fails, so the consumer publishes no wrong declaration. The
consumer exports the entry whole and calls the method on the entry, or writes a type annotation
on the constant. An annotation that states the whole type of one of the three methods needs
types that the entry does not publish.

**Pin.** None for the two forms: the two constants are not in the project of the check.
`scripts/emit-check/index.mts` holds each entry whole and the result of each method, and a comment
of that file states the two forms.
