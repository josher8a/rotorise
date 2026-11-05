# Known defects of this repository

One entry per defect. Each entry opens with one of three words.

- **Known** — observed, and reproduced by a command in this file.
- **Suspected** — the observation is real and the effect is not established.
- **Partially mitigated** — the effect is reduced, and the entry says what remains.

Each entry gives the observation, the effect, and the pin: the test, guard or refutation that
holds the defect in place. An entry with no pin says so, because an unpinned defect is one a later
pass closes by accident and nobody notices.

Each entry names declarations and files. It points at no section number, because a section number
moves and a declaration name does not.

---

## Known: the iso premise of the wrapper rule is stronger than the proof consumes

**Observation.** The specification's wrapper rule demands total cancellation on the two carriers:
one composite is the identity on the held set and the other is the identity on the inner carrier.
The mechanization asks for less. `IsoCancels` in `Codec.lean` restricts both directions to the
values the write half accepts — one clause per direction, each guarded by the encode being defined
— and its own docstring says it is the domain-restricted form the laws actually need.

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
reads as no fit. Measured 2026-10-31 with `tsc --noEmit` and `npx vitest --run`, the same before
and after the pass that reads a union entry:

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
Measured 2026-10-13 at 3838e2f: the type bridge holds 25 exclude refuse ids, and the clause of each
one is a binary literal. One example:

    const r = exclude(union([object({ a: binary(new Uint8Array([1, 2])) }), object({ c: string })]),
      object({ a: binary(new Uint8Array([1, 2])) }))
      runtime: member 0 dropped
      type: the decoded type of r still admits member 0

**Effect.** The result type of exclude is wider than the value. Every value fits the type, and a
member that the run time dropped stays in the type.

**Pin.** The baseline of the type bridge, formal/scripts/type_bridge_baseline.txt, holds 23 such
ids, measured 2026-10-14.

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

## Known: the type of a slice by a union pattern stops at TS2589 at 89 literals of one field

**Observation.** An exclusion that splits one field of literals into two halves of a union pattern
type-checks at 88 literals and keeps the option. At 89 literals the type checker reports TS2589.
The bound of the parts does not move the wall. Measured 2026-11-02 with `npx tsc --noEmit`:

    const big = union([object({ x: string('l00', …, 'l88') })])
    exclude(big, union([object({ x: string('l00', …, 'l44') }), object({ x: string('l45', …, 'l88') })]))
      runtime:      never
      type checker: TS2589, type instantiation is excessively deep and possibly infinite

**Effect.** The call of the caller does not compile. A literal set at one field of 89 or more
literals cannot be sliced by a pattern that splits the set.

**Pin.** None. A pin compiles a literal set of 89 at one field in the suite, and its cost in
instantiations is not measured.

---

## Known: the native writer refuses a boxed primitive that the SDK writes

**Observation.** The SDK reads a value by the name of its constructor, so a boxed number, a boxed
boolean and a boxed text each write the member of the primitive. The port reads a number, a boolean
and a text by the type of the primitive, and refuses a boxed object of the three. Measured 2026-11-03 with
`npx vitest --run` and `@aws-sdk/util-dynamodb` beside the port:

    native.encode(new Number(5))         port: Unsupported type passed: 5    SDK: { N: '5' }
    native.encode(new Boolean(true))     port: Unsupported type passed: true SDK: { BOOL: true }
    native.encode(new String('a'))       port: Unsupported type passed: a    SDK: { S: 'a' }

**Effect.** A document that holds a boxed primitive writes through the SDK and is refused by the
port. The port writes no item that the store refuses.

**Pin.** None. The pool of the law in `src/codec/spec/surface/native.spec.ts` that compares the
text of a refusal with the SDK leaves the boxed primitives out.
