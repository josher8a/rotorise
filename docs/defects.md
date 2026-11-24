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
formal/scripts/type_bridge_baseline.txt, holds 3 ids for the case above. The id of the group exclude
is the member row of the exclusion: the row states that the type keeps the whole option Holder, and
the run time does not keep it. The two ids of the group value are one drawn value that fits the
pattern. The id with accept states that extract gives the stored value, that the decode gives the
value back, and that the type refuses the value, because Decoded is never. The id with refuse states
that exclude gives a CodecError for the value, and that the type admits the value. The member rows
of extract hold no id: a member row states all values of the option, the run time keeps a narrowed
copy that holds some of them, and the verdict of the row, refuse, is right. No test pins the
recursive case of extract.

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

## Known: the type of meet builds a list of unknown length that holds fewer than two factors

**Observation.** The run time refuses a meet of fewer than two factors at construction. The type
of `meet` refuses the exact tuple of no factor and of one factor. A list whose length the type does
not know states no lower bound. Measured 2026-11-13 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`, where `none` is a `readonly AnyCodec[]` that holds no factor and `one` holds
one:

    meet(...none)
    meet(...one)
      type checker: builds
      runtime:      throws, a meet is taken of two or more factors, and fewer were given

**Effect.** The call builds in the type and throws at construction.

**Pin.** `src/codec/spec/object/codec.meet.spec.ts` pins the refusal of the exact tuple at the type
and the throw for a list of unknown length.

---

## Known: the type of a literal former builds a list of unknown length that names no value

**Observation.** The run time refuses a literal that names no value at construction. The type of
each literal former refuses the exact empty call. A list whose length the type does not know
states no lower bound. Measured 2026-11-13 with `tsc --noEmit` on TypeScript 7 and
`npx vitest --run`, where `none` is a `never[]`:

    string(...none)   number(...none)   decimal(...none)   dynamoNumber(...none)
    boolean(...none)  binary(...none)
      type checker: builds
      runtime:      throws, a literal admits one of a non-empty set of values

**Effect.** The call builds in the type and throws at construction.

**Pin.** `src/codec/spec/literal/codec.literalbase.spec.ts` pins the refusal of the empty call at
the type, and pins the throw and the former that the message names, for each former.

---

## Known: the type of a literal former builds a call that repeats a value

**Observation.** The run time refuses a literal call that names one value twice. A literal of the
model holds one value, so a call of several values is a union of one-value literals. A repeat gives
a union of two options that admits one value and decides no constant. The type of each former reads
the values as a tuple and states no distinctness. Measured 2026-11-13 with `tsc --noEmit
--noErrorTruncation` on TypeScript 7 and 6, and `npx vitest --run`, where `a` is a `Uint8Array` and
`d1` is a `DynamoNumber`:

    string('dog', 'dog')   number(1, 1)   decimal('1', '1')   boolean(true, true)
    binary(a, a)   dynamoNumber(d1, d1)   and `.set` of each that has one
      type checker: builds
      runtime:      throws, a literal's alternatives are distinct, and `string()` names the same
                    value at positions 0 and 1

The mark of the term at the type level keeps both options:

    string('dog', 'dog')   ["union", [LitT<"string", "dog">, LitT<"string", "dog">]]
    number(1, 1)           FloatT<["union", [LitT<"number", "1">, LitT<"number", "1">]]>
    boolean(true, true)    ["union", [LitT<"boolean", true>, LitT<"boolean", true>]]
    binary(a, a)           ["union", LitT<"binary", string>[]]

The type that reads the constant of a term gives `never` for `string('dog', 'dog')`, `number(1, 1)`
and `decimal('1', '1')`, where the same type gives the pair of `'dog'` for `string('dog')`.

**Effect.** The call builds in the type and throws at construction. `binary` and `dynamoNumber`
have one type for every value, so the type cannot tell a repeat from two values.
`decimal('1', '1.0')` does not build in the type: the spelling `'1.0'` is refused.

**Pin.** `src/codec/spec/literal/codec.literalbase.spec.ts` pins the throw for `string` and
`binary`, and the positions for `string`. The same file pins the former that the message names.
`src/codec/spec/literal/codec.setbase.spec.ts` pins the throw of `.set` at each base. No test pins
the mark of a repeat or the type that reads the constant.

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
      runtime:      returns a CodecError, Attribute petId not found

    const anyDepth: any = undefined
    Pets.key('SK', { shelterId: 's' }, { depth: anyDepth })
      type checker: builds
      runtime:      returns a CodecError, Attribute petId not found

**Effect.** Each call builds in the type with no second component, and the result holds the error
where the value is undefined at run time. The type of the first call is the key of depth 1, and a
call with the whole argument builds the whole key at run time, which the type does not state.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds no id of
this cause: the 8 ids of the group key fell, because a call that the run time refuses gives a
value that the type states. The pool draws no call with the whole argument and an undefined slot.
src/codec/spec/object/codec.keydepth.spec.ts pins the refusal of an optional slot, of `number`, and
of two literals at one slot.

---

## Known: the type refuses a key at a path below nullable, where the run time builds the entry

**Observation.** The type gives no member for a path below a codec of nullable, because the type of
nullable does not carry the spec of its inner object. The refusal lands on the component. The walk
of the run time, 'reachAt', enters nullable and reaches the path, so the construction builds the
entry. Measured 2026-11-19 with `tsc --noEmit` on TypeScript 7 and `npx vitest --run`:

    type Pet = { id: string; meta: { note: string } | null }
    tableEntry<Pet>()({ PK: ['id'], SK: ['meta.note'] },
                      { codec: { id: string, meta: nullable(object({ note: string })) } })
      type checker: refused at 'meta.note': the codec cannot address that path. A record with a
                    default for the component gives the same refusal
      runtime:      builds. toEntry gives the SK NOTE#n where meta is an object, and a CodecError,
                    "Attribute meta.note not found", where meta is null

**Effect.** A schema that the type refuses builds behind a cast. The fix changes the return type of
nullable, so each call of nullable changes.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds the id
'nullableMeta.codecPath' of the group construct for this table. The same group holds two ids for
tables where the type refuses by a rule of the owner. A name that can be absent reaches a key
through a match with a null arm, or through a record with a default, and the type refuses it as a
plain component where the author gives no default. A `.` in a key name is a path separator. src/Rotorise.attest.test.ts pins the head
of the refusal.

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
      runtime:      returns a CodecError, 'PK' is the table's own key and is built from 'petId'
                    (unsafeKeyUpdates throws it)

**Effect.** The type of a key states a text that the run time does not give, and a change that the
type accepts gives a CodecError, which the type of the result states. A caller that keeps a config
or a change in a variable of a declared type, or passes one through a parameter of a union type,
gets no error from the compiler.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 2 ids,
both of the group key. keyUpdates returns the refusal as a value, so that call is no id.

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
A match with `spec` and a discriminator that is a name has one deep member of the constraint,
'DiscriminatedSchema', and the exact check that holds the precise refusals runs only after the
constraint passes. Two forms were measured on 2026-11-23 and not built. A shallow member that takes
the match clears the 21 ids, and raises the attest pin of 18530 to 21444, 15.7 percent above a
limit of 10 percent. The form also loses two refusals of a call that gives the schema as a type
argument, because only the constraint checks such a call. A constraint without the deep member
loses the contextual type of a transform in an arm, and gives 11 compile errors in 3 spec files.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 21 ids of
the group construct: 15 with the prefix site, where the error starts at an arm name or at the whole
match and not at the name that the draw states, and 6 with the prefix text, where the message holds
the rule of another refusal. src/codec/spec/object/codec.keyoption.spec.ts pins each refusal, with
no text.

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

## Known: the type accepts a name of each member of a union that holds no literal name, where the codec refuses the value

**Observation.** ExactDeep drops a member of a union where the value holds another literal at a name
that the member holds as a literal. A union with no such name drops no member, so the type accepts
the names of every member together. With a codec, the run time asks the codec, and no option admits
a value that holds the names of two members. Measured 2026-11-19 with `npx vitest --run
src/codec/spec/object/codec.exactunion.spec.ts` and `tsc --noEmit` on TypeScript 7:

    type Plain = { petId: string; plain: { x: number } | { y: string } }
    const Plains = tableEntry<Plain>()({ PK: ['petId'] }, { codec: {
        petId: string,
        plain: union([object({ x: number }), object({ y: string })]),
    } })

    Plains.toEntry({ petId: 'p', plain: { x: 1, y: 's' } })
      type checker: builds
      runtime:      refuses, no option admits this value

**Effect.** A caller that the type checker approves learns of the names of two members at run
time, as a value of the kind 'refused'. A union that holds a literal name has no such gap.

**Pin.** `src/codec/spec/object/codec.exactunion.spec.ts` pins the acceptance of the type and the
refusal of the codec.

---

## Partially mitigated: keyUpdates of an entry with no codec gives the empty patch for a change at a name that the entity does not hold, behind a cast

**Observation.** The type of the change of keyUpdates refuses a name that the entity does not hold.
An entry with a codec refuses the same name at run time, with the refusal of the codec. An entry with
no codec holds no fact that tells a name that the entity holds from a name that the entity does not
hold, so the run time refuses only a name that is no path, or that holds a position.
Measured 2026-11-19 with `npx vitest --run src/codec/spec/object/codec.keyupdates.held.spec.ts`:

    type OwnedPet = { petId: string; note: string; owner: { name: string } }
    const Pets = tableEntry<OwnedPet>()({ PK: ['petId'], GSI1PK: ['owner.name'] })

    Pets.keyUpdates({ ghost: 1 })
      type checker: refused, 'ghost' does not exist in the type of the change
      runtime:      gives { set: {}, remove: [] }

    Pets.keyUpdates({ note: 'n' })
      type checker: builds
      runtime:      gives { set: {}, remove: [] }

**Effect.** In code with no type check, a change at a name that the caller wrote wrong gives a patch
that changes no key, and no error, where the entry has no codec.

**Pin.** `src/codec/spec/object/codec.entryexact.spec.ts` pins the refusal of the type.
`src/codec/spec/object/codec.keyupdates.held.spec.ts` pins the empty patch of the entry with no
codec, and the refusal of the codec.

---

## Partially mitigated: keyUpdates of an entry with no codec builds a key from an object that no codec reads

**Observation.** With a codec, keyUpdates asks the codec of each changed name for the value, and
refuses a value that the codec refuses. The type refuses a name in excess at each depth. An entry
with no codec holds no codec to ask, so the run time checks no value. Measured 2026-11-19 with
`npx vitest --run src/codec/spec/object/codec.keyupdates.value.spec.ts`:

    type OwnedPet = { petId: string; note: string; owner: { name: string; alias?: string } }
    const Plain = tableEntry<OwnedPet>()({ PK: ['petId'], GSI1PK: ['owner.name'] })

    Plain.keyUpdates({ owner: { name: 'b', alias: 'k', ghost: 'n' } } as never)
      type checker: refused without the cast, 'ghost' is in excess
      runtime:      gives { set: { GSI1PK: { S: 'NAME#b' } }, remove: [] }

**Effect.** In code with no type check, a change that carries a wrong value gives a key patch and
no error, where the entry has no codec.

**Pin.** `src/codec/spec/object/codec.keyupdates.value.spec.ts` pins the patch of the entry with no
codec, and the refusal of the codec.

---

## Known: a key row of the gate gives the model a tagged, transform or default component, and the read of a path, as the emitter evaluated them

**Observation.** A leaf of a key row holds each plain component as the name and the label, as an item
row does: the model reads the item of the row and applies the rule of the empty text. A leaf that
holds a component with a tag, a transform or a default holds each component as a constant that the
emitter evaluated, and the emitter states the read of the item and the rule of the empty text for
those. The model has no `Part` for a tag, and a transform is an opaque function. A path is read by
the emitter, which writes the flat name and the text in the item of the row. A leaf that mixes the
two kinds stays one constant leaf. Measured with `EMIT_LEAN_REFUSALS=1 npx vitest --run
src/codec/lean/lean.key.spec.ts`, on `formal/.keys.lean`:

    leaves of the key rows, before    7860 '.leaf (.const', 40 `Part.named`
    leaves of the key rows, after     3060 '.leaf (.const', 7204 `Part.named`
    rows of 'keyRows', before         4556
    rows of 'keyRows', after          6408

**Effect.** For a leaf of tagged, transform or default components, and for the read of a path, the
model checks the join, the separator and the read of the key on the constants of the emitter. The
statement of the read of the item and of the rule of the empty text for these has its place in the
emitter, and not in the model. A `Part` for a tag needs a new definition in the model.

**Pin.** The test 'reads each outcome of the builder as the model states it' of
`src/codec/lean/lean.key.spec.ts` pins the two rules of the emitter against the builder for the
constant leaves, and pins the rule of the oracle for the plain leaves. The test fails on a tree where
the oracle reads the empty text as a present part, and on a tree where the label of a path is the
whole name.

---

## Known: the type of a partial key admits a hole, where the run time gives an error value

**Observation.** A partial key is a position: the count `k` of the leading components that print. The
run time gives an error value for a hole, which is a component that prints after one that does not.
The type of the argument states each component as optional, and the type of the result is a union of
the prefixes that the builder can print. So the type names the prefix before an absent component,
where the run time gives the error value. The type has no success value for a key of no component:
the result is `never`, as the run time refuses that key. The type of a closed key states the tag of
the next component and the separator, and agrees with the run time. Measured 2026-11-17 with
`tsc --noEmit` on TypeScript 7 and `npx vitest --run`, with the entry Pets of
`codec.keypartial.spec.ts`:

    Pets.key('GSI1SK', { species: 'CAT', breed: undefined as Breed | undefined, age: 3 }, { allowPartial: true })
      type checker: builds, 'SPECIES#CAT' | 'SPECIES#CAT#BREED#PUG#AGE#3' | 'SPECIES#CAT#BREED#LAB#AGE#3'
      runtime:      CodecError, "'age' is given and 'breed' before it is not, so a partial key would drop 'age'"

**Effect.** A caller reads a string type and gets an error value. The type cannot refuse the hole of
a component typed 'X | undefined', because that component is a hole only where it is absent. The call
that the type decides is a first component typed as absent only, and a component typed 'undefined'
only before a component typed as present. A refusal of those calls at the argument is sound, and it
was not built. A walker that reads the case of each component, with an intersection on the parameter,
raised the attest pin of 8419 by 19.3 percent and the pin of 22543 by 10.9 percent, and the other
pins by 3.2 percent or less, against a limit of 10 percent. A form of the argument as a union of the
leading sets raised seven pins by 5 percent or more and gave 19 compile errors in 3 spec files.

**Pin.** `src/codec/spec/object/codec.keypartial.spec.ts`, `codec.keyempty.spec.ts` and
`codec.keydepth.spec.ts` pin the type of each call and the error value of the run time in the same
test.

