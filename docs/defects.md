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

The type of exclude reads the same pattern as no fit, and admits the value that the run time
refuses. Measured 2026-11-13 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`, with the
scope and the pattern above:

    const fits = { tag: 'holder', tree: { kind: 'branch', kids: { kind: 'leaf' } } }
    exclude(union([s.Holder, s.Other]), p).encode(fits)
      type checker: builds, Decoded admits the value
      runtime:      gives a CodecError, no option admits this value with attributes 'tag', 'tree'

    extract(union([s.Holder, s.Other]), p).encode(fits)
      type checker: refused, Decoded is never
      runtime:      gives the stored value

**Effect.** The type of `extract(...)` is narrower than the value: a value that the run time gives
does not fit the type. The pattern that names the branch entry alone reads exactly, and so does a
pattern that names the leaf entry and the branch entry as a union. The type of exclude(...) admits a
value that the run time refuses.

**Pin.** `src/codec/spec/union/codec.slice.spec.ts`: an object pattern reads each option of a union
entry that a `ref` names, an option that names another union entry, an option that is an entry of
another scope, and a base entry. The baseline of the type bridge,
formal/scripts/type_bridge_baseline.txt, holds 1 id of the group exclude, for the case of exclude
above. The rows of extract hold no id: the row of the pool for that member states a refusal, where
the run time keeps the value. No test pins the recursive case of extract.

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
and the pair of one type. The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt,
holds 1 id of the group meet, for the pair of two adapters of one type.

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
undeclared name, and the run time refuses the value. The baseline of the type bridge,
formal/scripts/type_bridge_baseline.txt, holds 1 id of the group decoded, for that value.

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
in the type, and the held option inside the union of an entry is kept in the type and dropped at run
time. The type bridge holds no id for the held option inside the union of an entry, because the pool
print cannot hold the case: the printer prints a ref that closes no cycle as its body, so the print
holds the held part over the empty body, and the type drops the option as the run time does. A slice
of the entry in the pool gave no id.

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
that JS spells with an exponent, at run time, and the refusal of one text at two bases. The baseline
of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 1 id of the group declaration,
for the second call above. The first call has no row: the pool prints built codecs only. No test
pins the first call.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 1 id of the
group path, for the call above with a refinement of a caller predicate.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 8 ids of
the group key for the two forms, 4 of them on a table with the option separator.
src/codec/spec/object/codec.keydepth.spec.ts pins the refusal of an optional slot, of `number`, and
of two literals at one slot.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 3 ids of
the group construct, one for each table with a default beside an options object.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 4 ids: 1 of
the group construct, 1 of toEntry, 1 of infer and 1 of fromEntry.
src/codec/spec/object/codec.keypath.spec.ts pins the refusal of a path whose value can be absent,
for an optional name and no union.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 3 ids of
the group construct, one for each table that the type refuses and the run time builds. No test pins
the head. src/codec/spec/object/codec.keycomponent.spec.ts pins the refusal of the entity whose
attribute holds the `.`, for a list.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 1 id of the
group keyUpdates. src/codec/spec/laws/codec.keyupdate.spec.ts pins the run time: the patch agrees
with the keys of the changed pet, for a key name with a `.` also.

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

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 4 ids: 1 of
toEntry, 1 of infer and 2 of key.

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

---

## Known: a value can hold a member that its declared type does not state, and the type reads the absence

**Observation.** The type of `key` and the refusal of keyUpdates read the names that the type of
the argument states. The run time reads the names that the value holds. The host has no exact
object type, so a constant of the type `{ depth: 1 }` can hold one member more. An object literal
at the call is not affected: the type reads each member of the literal. Measured 2026-11-12 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    const Pets = tableEntry<{ shelterId: string; petId: string }>()({ SK: ['shelterId', 'petId'] })
    const shelter: { shelterId: 's' } = { shelterId: 's' }
    const full: { shelterId: 's'; petId: 'p' } = { shelterId: 's', petId: 'p' }

    Pets.key('SK', shelter, { depth: 1, enforceBoundary: true })
      type checker: builds, with the type "SHELTERID#s#"
      runtime:      gives "SHELTERID#s#"

    const wideConfig = { depth: 1, enforceBoundary: true } as const
    const narrowConfig: { depth: 1 } = wideConfig
    Pets.key('SK', shelter, narrowConfig)
      type checker: builds, with the type "SHELTERID#s"
      runtime:      gives "SHELTERID#s#"

    const pair = (c: { depth: 1 } | { depth: 1; enforceBoundary: true }) => Pets.key('SK', full, c)
    pair({ depth: 1, enforceBoundary: true })
      type checker: builds, with the type "SHELTERID#s"
      runtime:      gives "SHELTERID#s#"

    // Kennels holds the PK ['petId'], a codec, and a key block that names the PK
    const wideChange = { age: 5, petId: 'p2' }
    const narrowChange: { age: number } = wideChange
    Kennels.keyUpdates(wideChange)
      type checker: refused, 'PK' is a table key that holds 'petId'
    Kennels.keyUpdates(narrowChange)
      type checker: builds
      runtime:      throws, 'PK' is the table's own key and is built from 'petId'

**Effect.** The type of a key states a text that the run time does not give, or a change that the
type accepts throws. A caller that keeps a config or a change in a variable of a declared type, or
passes one through a parameter of a union type, gets no error from the compiler.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 3 ids: 2 of
the group key and 1 of keyUpdates.

---

## Known: the type of key states the value of the entity for a key of one attribute below a second match, where the run time gives the stored text

**Observation.** A key of one attribute is the stored value of the attribute. With a tagged codec,
the type of `key` reads the stored text of the attribute where the key is the arm of one match.
Where the key is the arm of a match inside the arm of a match, the type of `key` reads the type of
the entity. The type of toEntry reads the stored text at each depth. Measured 2026-11-12 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    // flag: a schema of boolean
    const Adopted = held(string('Y', 'N'), flag, {
        encode: (b: boolean) => (b ? 'Y' : 'N'),
        decode: (s: string) => s === 'Y',
    })
    type HousedCat = { petId: string; species: 'CAT'; status: 'IN' | 'OUT'; adopted: boolean }
    type HousedDog = { petId: string; species: 'DOG'; status: 'IN'; adopted: boolean }
    const TaggedPets = item(
        discriminatedUnion('species', [
            object({ petId: string, species: string('CAT'), status: string('IN', 'OUT'), adopted: Adopted }),
            object({ petId: string, species: string('DOG'), status: string('IN'), adopted: Adopted }),
        ]),
    )
    const housed: HousedCat = { petId: 'p1', species: 'CAT', status: 'IN', adopted: true }

    const OneLevel = tableEntry<HousedCat | HousedDog>()(
        { PK: ['petId'], SK: { discriminator: 'species', spec: { CAT: 'adopted', DOG: null } } },
        { codec: TaggedPets },
    )
    OneLevel.key('SK', housed)
      type checker: builds, with the type "N" | "Y"
      runtime:      gives "Y"

    const TwoLevels = tableEntry<HousedCat | HousedDog>()(
        {
            PK: ['petId'],
            SK: {
                discriminator: 'species',
                spec: { CAT: { discriminator: 'status', spec: { IN: 'adopted', OUT: null } }, DOG: null },
            },
        },
        { codec: TaggedPets },
    )
    TwoLevels.key('SK', housed)
      type checker: builds, with the type boolean | undefined
      runtime:      gives "Y"

    TwoLevels.toEntry(housed).SK
      type checker: "N" | "Y" | undefined
      runtime:      gives "Y"

**Effect.** The type of the second key is a boolean or undefined, and the value is a string. The
type of toEntry states the stored text for the same key, so the two methods state two types for
one value.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 2 ids of
the group key.

---

## Known: the refusal of a match in the form with `spec` names no element, or a rule that the match does not break

**Observation.** The constraint of a key spec is a union of forms, and the compiler reports a refusal
against one form of the union. In the form with `cases`, the refusal lands on the name that is wrong, or
on the discriminator, with a text that states the cause. In the form with `spec`, the refusal lands on the
whole match, or on a literal, with a text of another rule. Measured 2026-11-12 with `tsc --noEmit` on
TypeScript 7:

    type Boarder = { petId: string; status: 'IN' | 'OUT'; kennel: string; owner: { id: string } }
    type Optional =
        | { petId: string; kind?: 'CAT'; kennel: string }
        | { petId: string; kind: 'DOG'; ownerId: string }

    tableEntry<Boarder>()({
        PK: ['petId'],
        SK: { discriminator: 'status', spec: { IN: ['cage'], OUT: ['petId'] } },
    })
      type checker: refused at 'SK', Type '{ discriminator: "status"; spec: ... }' is not assignable
                    to type 'FullKeySpec<Boarder>'

    tableEntry<Boarder>()({
        PK: ['petId'],
        SK: { discriminator: 'status', cases: [[['IN'], ['cage']], [['OUT'], ['petId']]] },
    })
      type checker: refused at 'cage', 'cage' is no name or path of the entity

    tableEntry<Optional>()({
        PK: ['petId'],
        SK: { discriminator: 'kind', spec: { CAT: ['kennel'], DOG: ['ownerId'] } },
    })
      type checker: refused at 'CAT', a match holds spec or cases, not both

    tableEntry<Optional>()({
        PK: ['petId'],
        SK: { discriminator: 'kind', cases: [[['CAT'], ['kennel']], [['DOG'], ['ownerId']]] },
    })
      type checker: refused at 'kind', 'kind' can be absent, and a match selects its arm by the value
                    of 'kind'

The run time throws `Discriminator kind not found in the attributes` for a pet of no kind, and
`Attribute cage not found` for a pet of the arm IN.

**Effect.** A caller of the form with `spec` learns that the match is wrong, and learns no name and no
cause. For a discriminator that can be absent the text names a rule that the match does not break.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 21 ids of
the group construct: 15 with the prefix site, where the error starts at an arm name or at the whole
match and not at the name that the draw states, and 6 with the prefix text, where the message holds
the rule of another refusal. src/codec/spec/object/codec.keyoption.spec.ts pins each refusal, with
no text.

---

## Known: the type of a full key admits a plain component whose value is the empty text, where the run time throws

**Observation.** The run time reads a plain component whose value is the empty text as an absent
component, and a full key refuses an absent component. The type of the component is `string`. The
host has no type for a text of one character or more. Measured 2026-11-12 with `tsc --noEmit` on
TypeScript 7 and `npx vitest --run`:

    type Pet = { petId: string; name: string }
    const Pets = tableEntry<Pet>()({ PK: ['petId'], SK: ['name'] })
    const blank: Pet = { petId: 'p1', name: '' }

    Pets.toEntry(blank)
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute name not found

    Pets.key('SK', blank)
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute name not found

    Pets.key('PK', { petId: '' })
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute petId not found

    type Housed = { petId: string; shelter: { code: string } }
    const Homes = tableEntry<Housed>()({ PK: ['petId'], SK: ['shelter.code'] })

    Homes.key('SK', { petId: 'p1', shelter: { code: '' } })
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute shelter.code not found

**Effect.** The call compiles, and the run time throws. The text of the throw says that the
attribute is not found, where the item holds the attribute with the empty text. The rule is the
same for a component that is a path.

**Pin.** `src/codec/lean/lean.key.spec.ts` pins the refusal of the run time against the model, for a
composite key whose plain component is the empty text.

---

## Known: the type of key refuses an entity whose key of one path lies below an optional object, where the run time gives the key

**Observation.** For a key of one path, the parameter of `key` states each object above the last
name as required, and states the last name with undefined. An entity whose object can be absent
does not fit the parameter. The run time reads the path, and gives undefined where the object is
absent. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Owned = { petId: string; owner?: { id: string } }
    const Owners = tableEntry<Owned>()({ PK: ['petId'], SK: 'owner.id' })
    const owned: Owned = { petId: 'p1', owner: { id: 'o1' } }
    const unowned: Owned = { petId: 'p2' }

    Owners.key('SK', owned)
      type checker: refused, 'Owned' is not assignable to '{ owner: { id: string | undefined } }'
      runtime:      gives "o1"

    Owners.key('SK', unowned)
      type checker: refused, with the same text
      runtime:      gives undefined

    Owners.key('SK', { owner: { id: 'o1' } })
      type checker: builds

    Owners.toEntry(owned)
      type checker: builds
      runtime:      gives the SK "o1"

**Effect.** A caller that holds an item of the entity cannot pass the item to `key` with no cast.
An object literal that holds the object compiles.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 4 ids of
the group key.

---

## Known: the refusal of a union codec with no discriminator lands on the key, where the key reads a held codec

**Observation.** An item codec that is a `union` with no discriminator cannot name the option of an
item, and the run time refuses the codec. The type refuses the codec at the option that holds the
codec. Where a key of one attribute reads an attribute of a `held` codec, the type refuses the key
and not the codec. The text says that the attribute is stored as none of S, N and B. The `held`
codec of the measurement stores the text 'Y' or 'N'. Measured 2026-11-12 with `tsc --noEmit` on
TypeScript 7 and `npx vitest --run`:

    // flag is a schema of boolean
    const Adopted = held(string('Y', 'N'), flag, {
        encode: (b: boolean) => (b ? 'Y' : 'N'),
        decode: (s: string) => s === 'Y',
    })

    tableEntry<Cat | Dog>()(
        { PK: ['petId'], SK: 'adopted' },
        {
            codec: item(
                union([
                    object({ petId: string, species: string('CAT'), adopted: Adopted }),
                    object({ petId: string, species: string('DOG'), adopted: Adopted }),
                ]),
            ),
        },
    )
      type checker: refused at 'adopted', [tableEntry] 'SK' is built from 'adopted', which is
                    stored as none of S, N and B
      runtime:      throws, the codec passed here is neither an item codec nor a tagged one

    the same call, where each option holds adopted: string
      type checker: refused at the codec, the codec is not assignable to a tagged codec
      runtime:      throws, with the same text

**Effect.** The caller reads a refusal of the key, and the cause is the codec. A correction of the
key does not make the table build.

**Pin.** `src/codec/spec/object/codec.patch.shapes.spec.ts` pins the throw of the run time for a
codec that cannot name a variant, behind a cast.

---

## Known: a codec builds and writes an attribute name of no character, where DynamoDB refuses the name

**Observation.** The former of an object takes the empty text as the name of a field. The codec
writes the name, and reads the name back. DynamoDB refuses an item that holds an attribute name of
no character, at the top of the item and inside a map. Measured 2026-11-12 with `tsc --noEmit` on
TypeScript 7 and `npx vitest --run`, and with a PutItem call on DynamoDB Local:

    const Named = item(object({ petId: string, '': string }))
      type checker: builds
      runtime:      builds

    Named.unsafeEncode({ petId: 'p1', '': 'ball' })
      type checker: builds
      runtime:      gives { petId: { S: 'p1' }, '': { S: 'ball' } }

    PutItem, the name "" at the top of the item
      DynamoDB Local: refused, Empty attribute name

    PutItem, the name "" inside a map
      DynamoDB Local: refused, Empty attribute name

**Effect.** The codec gives an item that DynamoDB refuses. The failure arrives at the write, not
where the caller declares the field.

**Pin.** None.

---

## Known: the test of a transform at a path that the codec writes as B reads no key

**Observation.** `src/codec/spec/object/codec.keycomponent.spec.ts` holds the test 'accepts a
transform at a path that the codec writes as B, because the function prints the text'. The test
builds the entry, and asserts that the method that builds a row is a function. The test calls no
method of the entry. Measured 2026-11-12 with `npx vitest --run` and the name of the test, on a
tree where the function that builds a row throws at its first statement:

    the test of the file                                          passes
    a probe that reads the SK of the row of one pet, same tree    fails, Error: mutant

**Effect.** A change that breaks the key of such a path keeps the test green. The test fails only
where the construction of the entry throws.

**Pin.** None.

---

## Suspected: the rows of a path in the type bridge compare the kind of a value, and no value of the same kind

**Observation.** `src/codec/typeVectors.ts` writes two rows for the decoded type of a codec at a
path. The first row holds one value that the codec draws, and the type must accept the value. The
second row holds one value of another kind, and the type must refuse the value: the numeral '1'
where the draw is a number, and the number 1 otherwise. A decoded type that is widened from a
literal to the base type gives the same verdict on each row. Measured 2026-11-12 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`, for the path `['kind']` of
`object({ kind: string('DOG'), name: string })`:

                                    the decoded type, 'DOG'    the widened type, string
    the first row, 'DOG'            builds                     builds
    the second row, 1               refused                    refused
    a text of another literal       refused                    builds

**Effect.** Not established. The measurement holds the two types side by side, and no change of
the decoded type ran against the bridge. If a change widens the decoded type at a path from a
literal to the base type, the two rows give the verdict of today.

**Pin.** None.

---

## Known: item builds a union with an option that is no object, where a read or a write at that option throws a TypeError

**Observation.** An item is a map, so a union with an option that is no object has no reading as an
item. The type states the refusal as the type of the result: the call compiles, and each use of the
result does not. The run time builds the codec. A row that the first option reads gives the value.
A row or a value that reaches the option that is no object throws a TypeError of the engine, and no
CodecError. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    const Pet = object({ petId: string })
    const Rows = item(union([Pet, string]))
      type checker: builds, and the type of Rows is the message "[union] this union can hold an
                    attribute that is not a map, so it has no whole-item reading"
      runtime:      builds

    Rows.decode({ petId: { S: 'p1' } })
      type checker: refused, Property 'decode' does not exist on the type of the message
      runtime:      gives { petId: 'p1' }

    Rows.decode({ name: { S: 'Rex' } })
      type checker: refused, with the same text
      runtime:      throws, TypeError: Cannot read properties of undefined (reading 'decode')

    Rows.unsafeEncode('Rex')
      type checker: refused, Property 'unsafeEncode' does not exist on the type of the message
      runtime:      throws, TypeError: Cannot read properties of undefined (reading 'encode')

    item(union([Pet, object({ name: string })])).decode({ name: { S: 'Rex' } })
      type checker: builds
      runtime:      gives { name: 'Rex' }

**Effect.** The call compiles, and the error appears at the first use of the result. In code with
no type check, or behind a cast, the codec builds, and the failure arrives at the read of a row
that the first option does not read.

**Pin.** `src/codec/spec/object/codec.item.spec.ts` pins the type: the result holds the message and
no method. None for the run time.

---

## Known: discriminatedUnion throws a TypeError where the decoded tag of an option has no primitive form

**Observation.** A tag can be a `held` codec, and the decoded tag is then the output of a function
of the caller. The construction prints the decoded tag of each option into a text with the string
conversion of JS. An object with no prototype has no such conversion. The type refuses the call of
the measurement, so the run is behind a cast. Measured 2026-11-12 with `tsc --noEmit` on
TypeScript 7 and `npx vitest --run`:

    // anyTag is a schema of unknown, and dogTag is Object.create(null)
    const DogTag = held(string('D'), anyTag, {
        encode: (value: unknown) => (value === dogTag ? 'D' : new CodecError('only the dog tag')),
        decode: () => dogTag,
    })

    discriminatedUnion('species', [
        object({ species: DogTag, name: string }),
        object({ species: string('cat'), name: string }),
    ])
      type checker: refused, [discriminatedUnion] options 0 and 1 answer to the same
                    discriminator value
      runtime:      throws, TypeError: Cannot convert object to primitive value

    the same call, where the function gives the plain object { species: 'dog' }
      runtime:      throws, CodecError: { species, name } and { species, name } are not shown
                    compatible

The type checker of the second call is not measured.

**Effect.** The run time refuses the two calls. The first refusal is a throw of the engine, and its
text names no option and no tag.

**Pin.** None.

---

## Known: a codec reads an attribute that holds two members, and the member that it reads follows the codec and the order of the names

**Observation.** A stored attribute holds one member, and the type of an attribute refuses a value
that holds two. The run time counts no member. A codec of one member reads that member, and reads
no other name. A `union` and the opaque codec read the member whose name comes first in the object.
The run rows are behind a cast. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`:

    string.decode({ S: 'Rex', N: '1' })
      type checker: refused, '{ S: string; N: string; }' is not assignable to 'AttributeValue'
      runtime:      gives 'Rex'

    number.decode({ S: 'Rex', N: '1' })
      runtime:      gives 1

    string.encode('Rex')
      runtime:      gives { S: 'Rex' }

    union([string, number]).decode({ S: 'Rex', N: '1' })
      runtime:      gives 'Rex'

    union([string, number]).decode({ N: '1', S: 'Rex' })
      runtime:      gives 1

    opaque.decode({ S: 'Rex', N: '1' })
      runtime:      gives 'Rex'

    opaque.decode({ N: '1', S: 'Rex' })
      runtime:      gives a number whose JSON form is { digits: '1' }

**Effect.** Two objects that hold the same two members give two decoded values. An attribute that
the read admits does not write back: the write gives one member. The input is a value that the
type refuses, so the input is data with no type, or a cast.

**Pin.** None.

---

## Known: keyUpdates gives the empty patch for a change at a name that the entity does not hold, behind a cast

**Observation.** The type of the change of keyUpdates refuses a name that the entity does not hold.
The run time refuses no name. A change at a name that no key reads gives the patch of no key. A
name with a `.` is a path, so a change at the name of a path that a key reads gives the patch of
the write to that path. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`:

    type OwnedPet = { petId: string; note: string; owner: { name: string; nick: string } }
    const Pets = tableEntry<OwnedPet>()({ PK: ['petId'], GSI1PK: ['owner.name'] })

    Pets.keyUpdates({ ghost: 1 })
      type checker: refused, 'ghost' does not exist in the type of the change
      runtime:      gives { set: {}, remove: [] }

    Pets.keyUpdates({ 'owner.name': 'bob' })
      type checker: refused, ''owner.name'' does not exist in the type of the change
      runtime:      gives { set: { GSI1PK: { S: 'NAME#bob' } }, remove: [] }

    Pets.keyUpdates({ 'owner.nick': 'bob' })
      runtime:      gives { set: {}, remove: [] }

    Pets.keyUpdates({ owner: { name: 'bob', nick: 'b' } })
      type checker: builds
      runtime:      gives { set: { GSI1PK: { S: 'NAME#bob' } }, remove: [] }

**Effect.** In code with no type check, a change at a name that the caller wrote wrong gives a
patch that changes no key, and no error.

**Pin.** `src/codec/spec/object/codec.entryexact.spec.ts` pins the refusal of the type. None for
the run time.

---

## Known: the run time refuses a tag that is a union of number literals with a text that names another rule

**Observation.** A variant answers to one tag, so a tag that is a `union` of literals is refused.
The type refuses the call at each base with one text. The run time refuses a `union` of `string`
literals with the text of that rule. For a `union` of number literals, and for a `union` of decimal
literals, the text of the run time says that one option names the tag with no literal. The run rows
are behind a cast. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    discriminatedUnion('k', [
        object({ k: union([string('a'), string('b')]), a: string }),
        object({ k: string('c'), b: string }),
    ])
      type checker: refused, [discriminatedUnion] option 0 names the discriminator with a literal
                    admitting several values
      runtime:      throws, 'k' names 2 values at one option (a, b), and a variant answers to
                    exactly one tag

    the same call with number(1), number(2) and number(3)
      type checker: refused, with the same text
      runtime:      throws, every option must name 'k' with a literal

    the same call with decimal('1'), decimal('2') and decimal('3')
      type checker: refused, with the same text
      runtime:      throws, every option must name 'k' with a literal

    discriminatedUnion('k', [object({ k: decimal('1'), a: string }),
                             object({ k: decimal('3'), b: string })])
      type checker: builds
      runtime:      builds

**Effect.** The call does not compile. Behind a cast, the text of the throw says that one option
names the tag with no literal, where each option names the tag with literals. The text does not
state the rule that the call breaks.

**Pin.** `src/codec/spec/union/codec.dunion.lookup.spec.ts` pins the text of the run time for one
`string` literal of two values. None for a `union` of literals.

---

## Known: a key row of the gate gives the model each component of a composite key as a constant that the emitter evaluated

**Observation.** A row of the gate holds a key spec as a tree. An item row holds a plain component
as the name and the label: the model reads the item of the row, and applies the rule of the empty
text. A key row holds each component as a constant. The emitter of
`src/codec/lean/lean.key.spec.ts` reads the item, applies the rule of the empty text and prints the
label, and the model joins the constants. So the emitter states the two rules a second time.
Measured 2026-11-12 with `EMIT_LEAN_REFUSALS=1 npx vitest --run src/codec/lean/lean.key.spec.ts`,
on `formal/.keys.lean`:

    a leaf of a key row
      .leaf (.const 2 [some (.named "A" "1"), some (.named "B" "2")])

    a leaf of an item row
      .leaf ⟨2, [Part.named "petId" "PETID", Part.named "nick" "NICK"]⟩

    the lines of the file that hold Part.named
      12, each one a line of the item rows

**Effect.** For a composite key of a key row, the model checks the join, the separator and the read
of the key on the constants of the emitter. The read of the item and the rule of the empty text
have their statement in the emitter, and not in the model. The header of
`formal/Calculus/Bridge/KeyRows.lean` says that the host evaluated the parts.

**Pin.** The test 'reads each outcome of the builder as the model states it' of
`src/codec/lean/lean.key.spec.ts` pins the two rules of the emitter against the builder. The test
fails on a tree where the emitter reads the empty text as a present part, and on a tree where the
emitter prints the whole name as the label.

---

## Known: one term of the check of a key row reads no field of the row

**Observation.** `keyRowOk` of `formal/Calculus/Bridge/KeyRows.lean` compares what the host did
with what the model gives. Where the host and the model give no key, the check is the term
`((Codec.empty : Codec).e (Attr.s "")).isNone`. The term holds no field of the row.
`keyRowOk_iff` states the same fact in the disjunct of that arm. `nullArm_writes_nothing` of
`formal/Calculus/Dynamo/Alg/DerivedKey.lean` proves the fact for each value. Measured 2026-11-12
with `lake env lean` on a scratch file that imports `Calculus.Bridge.KeyRows`:

    example : ((Codec.empty : Codec).e (Attr.s "")).isNone = true := rfl
      accepted

    example (r : KeyRow) : keyRowOk r = keyRowOk' r
      accepted, where keyRowOk' is keyRowOk with true in place of the term

**Effect.** The term is true for each row. The arm accepts each row where the host and the model
give no key, and the term adds no check.

**Pin.** None.

---

## Known: the type of a full key admits a text that holds the separator, where the run time throws

**Observation.** A key whose component prints the separator does not read back as its components,
and the run time refuses the key. The type of the component is `string`, which holds each text.
Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Pet = { petId: string; shelterId: string; name: string; note?: string }
    const Pets = tableEntry<Pet>()({ PK: ['petId'], SK: ['name'] })
    const rex: Pet = { petId: 'p1', shelterId: 's1', name: 'rex' }
    const split: Pet = { petId: 'p1', shelterId: 's1', name: 'a#b' }

    Pets.key('SK', split)
      type checker: builds
      runtime:      throws, buildCompositeKey: the print of name holds the separator, so the key
                    cannot be read back

    Pets.key('SK', rex)
      type checker: builds
      runtime:      gives "NAME#rex"

**Effect.** The call compiles, and the run time throws for a value of the declared type.

**Pin.** `src/codec/spec/object/codec.keyrow.spec.ts` pins the refusal of the run time for a
complete key. None for the type.

---

## Known: the type of a key states no label for a component whose transform function gives the tag

**Observation.** A transform function can give an object with a tag and a value, and the run time
prints the tag as the label of the component. The type of the key states a text with a `#` and no
label. The type of a key with a plain component states the label. Measured 2026-11-12 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`, with the type Pet and the item rex of the
entry above:

    const Tagged = tableEntry<Pet>()({
        PK: ['petId'],
        SK: [['name', (name: string) => ({ tag: 'T', value: name })]],
    })

    Tagged.key('SK', rex)
      type checker: builds, and the type of the key is `${string}#${string}`
      runtime:      gives "T#rex"

    const key = () => Tagged.key('SK', rex)
    const other: ReturnType<typeof key> = '~T#rex'
      type checker: builds

    tableEntry<Pet>()({ PK: ['petId'], SK: ['name'] }).key('SK', rex)
      type checker: builds, and the type of the key is `NAME#${string}`
      runtime:      gives "NAME#rex"

**Effect.** The type of the key is wider than the value. Each value that the run time gives fits
the type, and a text with another label fits the type also.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 26 ids: 9
of toEntry, 9 of infer and 8 of key. Each is a foreign text with another label.

---

## Known: the type of key refuses an item of the entity for a key of one path through a union where one option lacks the name, where the run time gives the key

**Observation.** For a key of one path, the parameter of `key` states the object above the last
name with that name as required. An entity whose object is a union, where one option lacks the
name, does not fit the parameter. The run time reads the path, and gives undefined where the
option lacks the name. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`:

    type Doc = { id: string; meta: { kind: 'a'; a: string } | { kind: 'b'; b: string } }
    const Docs = tableEntry<Doc>()({ PK: ['id'], SK: 'meta.a' })
    const first: Doc = { id: 'd1', meta: { kind: 'a', a: 'x' } }
    const second: Doc = { id: 'd2', meta: { kind: 'b', b: 'y' } }

    Docs.key('SK', first)
      type checker: refused, 'Doc' is not assignable to '{ meta: { a: string; }; }'
      runtime:      gives "x"

    Docs.key('SK', second)
      type checker: refused, with the same text
      runtime:      gives undefined

    Docs.toEntry(first)
      runtime:      gives the SK "x"

    Docs.toEntry(second)
      runtime:      writes no SK

The type checker of the two calls of toEntry is not measured.

**Effect.** A caller that holds an item of the entity cannot pass the item to `key` with no cast.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 10 ids of
the group key.

---

## Known: the type of key refuses an item whose option holds two literals at the path of a match, where the run time gives the key

**Observation.** The parameter of `key` for a match on a path is a union with one object type for each
literal, and the literal stands at the nested path. The host decomposes an argument over a union by a
property of the top level only. An argument whose value at the path is a union of literals fits no
member. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Placed = { petId: string; meta: { status: 'IN' | 'OUT' }; kennel: string }
    const Placeds = tableEntry<Placed>()({
        PK: ['petId'],
        SK: { discriminator: 'meta.status', spec: { IN: ['kennel'], OUT: ['petId'] } },
    })
    const placed: Placed = { petId: 'p1', meta: { status: 'IN' }, kennel: 'k1' }

    Placeds.key('SK', placed)
      type checker: refused, Argument of type 'Placed' is not assignable to parameter of type
                    '{ kennel: string; meta: { status: "IN"; }; } | { meta: { status: "OUT"; }; petId: string; }'
      runtime:      gives "KENNEL#k1"

    Placeds.toEntry(placed).SK, Placeds.infer and Placeds.fromEntry(stored)
      type checker: build, with the type `KENNEL#${string}` | `PETID#${string}` for the key

    type Plain = { petId: string; status: 'IN' | 'OUT'; kennel: string }
    Plains.key('SK', plain)   // the discriminator at the top level, plain: Plain
      type checker: builds

The host has the same limit without the library. A function of the parameter
`{ a: { k: 'I' }; n: string } | { a: { k: 'O' }; m: string }` refuses
`{ a: { k: 'I' | 'O' }; n: string; m: string }`, and a function of the parameter
`{ k: 'I'; n: string } | { k: 'O'; m: string }` accepts `{ k: 'I' | 'O'; n: string; m: string }`.
A constant of the literal type, `{ meta: { status: 'IN' }, ... } as const`, fits the member of its literal.
Before the pass that moved the arm of a match to the options that can hold its literal, the table
was refused at construction, and the call was refused with a parameter of no attribute.

**Effect.** A caller with an item of the declared type of the entity cannot call `key` for a match on
a path where one option holds two literals. A cast or a constant of the literal type passes.

**Pin.** `src/codec/lean/lean.entry.spec.ts` draws the tables of the kind dpathdouble, and the
baseline of `formal/scripts/type_bridge_baseline.txt` holds 14 ids of the calls of `key` on them.

---

## Known: the type of keys and of keyCondition admits an argument that holds no component of a key, where the run time throws

**Observation.** The parameter of keys and of keyCondition is a partial entity with any other name.
The run time builds the key of the table from each component of the key, and the partition of an
index from each component of the partition. The argument can lack a component, and the type does not
read the components. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Pet = { petId: string; shelterId: string; name: string }
    const Pets = tableEntry<Pet>()(
        { PK: ['petId'], SK: ['shelterId', 'name'], GSI1PK: ['shelterId'] },
        { key: { partition: 'PK', sort: 'SK' }, indexes: { Shelter: { partition: 'GSI1PK' } } },
    )
    const full: Pet = { petId: 'p1', shelterId: 's1', name: 'rex' }
    const first: { petId: string } = { petId: 'p1' }
    const empty: Partial<Pet> = {}

    Pets.keys(full)
      type checker: builds
      runtime:      gives { PK: { S: 'PETID#p1' }, SK: { S: 'SHELTERID#s1#NAME#rex' } }

    Pets.keys(first)
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute shelterId not found

    Pets.keys(empty)
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute petId not found

    Pets.keyCondition(empty)
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute petId not found

    Pets.keyCondition('Shelter', first)
      type checker: builds
      runtime:      throws, buildCompositeKey: Attribute shelterId not found

    Pets.keyCondition(first)
      type checker: builds
      runtime:      gives { partition: { name: 'PK', value: { S: 'PETID#p1' } } }

**Effect.** The call compiles, and the run time throws for an argument of the declared type. The
type of the result is the same for each argument.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 7 ids: 3 of
the group keys and 4 of the group keyCondition. src/codec/lean/lean.entry.spec.ts draws each call.

---

## Known: the type of key refuses an argument that holds no component of the key at depth 0, where the run time gives the empty text

**Observation.** A key of depth 0 reads no component, and the run time gives the empty text for
each argument. The parameter of `key` at depth 0 states each component as optional. An argument of
a declared type that holds another name only has no property in common with the parameter, and
the type refuses the argument. The empty object compiles. Measured 2026-11-12 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`, with the entry Pets above:

    const nameOnly: { name: string } = { name: 'rex' }

    Pets.key('PK', nameOnly, { depth: 0 })
      type checker: refused, '{ name: string; }' has no properties in common with
                    '{ petId?: string | undefined; }'
      runtime:      gives ""

    Pets.key('PK', {}, { depth: 0 })
      type checker: builds
      runtime:      gives ""

**Effect.** The first call does not compile, and the run time gives the key.

**Pin.** `src/codec/spec/object/codec.keydepth.spec.ts` pins the empty text of `depth: 0` at run
time. None for the refusal.

---

## Known: the type of a key component refuses an options object at a top level name, where the run time builds the key

**Observation.** A component of a key is a name, or a tuple of a name and a transform. The
transform is a function, or an options object such as `{ tag: 'NM' }`. The type takes the options
object at a path, and refuses the options object at a name of the top level. The run time reads
the options object at each. Measured 2026-11-12 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`, with the type Pet and the item rex above:

    tableEntry<Pet>()({ PK: ['petId'], SK: [['name', { tag: 'NM' }]] })
      type checker: refused, 'tag' does not exist in type '(key: string) => TransformShape'
      runtime:      builds, and key('SK', rex) gives "NM#rex"

    type Housed = { petId: string; shelter: { code: string } }
    tableEntry<Housed>()({ PK: ['petId'], SK: [['shelter.code', { tag: 'SC' }]] })
      type checker: builds
      runtime:      builds, and key('SK', { petId: 'p1', shelter: { code: 'c1' } }) gives "SC#c1"

TypeScript 6 refuses the first call at the same line with the code TS2322.

**Effect.** The first call does not compile, and the run time builds the entry and prints the tag.

**Pin.** None for a name of the top level.
