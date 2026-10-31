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

## Known: the type of meet states no refusal of a held or older part that the run time refuses

**Observation.** The run time refuses a `held` part or an older reading where the two parts are
apart in neither view and neither side fits the other, because an opaque function decides which
common rows relate one value. The type states the refusal for two `held` parts whose adapters
differ for certain, read at the top node of each factor. Three calls build in the type and throw at
run time. Measured 2026-10-27 with `npx vitest --run` and `tsc --noEmit`:

    meet(h1, h2)                     two adapters of a caller, of one type
    meet(withLegacyRead({ current: string, older: decimal }), decimal('1'))
    union([object({ x: withLegacyRead({ current: string, older: decimal }) }), object({ x: number })])

The run time tells two adapters of a caller apart by object identity, and a structural type holds
no identity. So `meet(h, h)` and `meet(h1, h2)` have one type, and a refusal of the pair refuses
`meet(h, h)`, which the run time builds. The mark of an older reading holds the current term only,
and the older reader is a function over any attribute, so the type holds no stored shape of the
older reading.

**Effect.** A call of the three forms builds in the type and throws at run time. A `held` part
below a field of an object is not refused in the type either.

**Pin.** `src/codec/spec/object/codec.meet.spec.ts` pins the refused pairs, the pairs that build,
the pair of one type with two results, and the older reading.

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

## Known: the type of a slice reads 32 parts of an option where the run time reads 1024

**Observation.** The run time splits an option into at most 1024 parts of its normal form before it
reads a union pattern. The type splits an option into at most 32 parts. Past 32 parts the type
cannot decide the fit, and the slice keeps the option. The checker passes its instantiation depth
between 40 and 48 literals at one field. Measured 2026-10-27 with `npx vitest --run` and the pin below:

    const big = union([object({ x: string('l00', …, 'l32') })])
    exclude(big, union([object({ x: string('l00', …, 'l16') }), object({ x: string('l17', …, 'l32') })]))
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
