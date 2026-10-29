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

## Known: the linter of this repository lints no file

**Observation.** The linter include list in `biome.json` reads "!/src/\*\*/\*.spec.ts" then "/src/\*\*". The
leading `/` matches no path. Measured 2026-09-07:

    npx biome lint src/codec/codec.ts
    Checked 0 files.  i These paths were provided but ignored: - src/codec/codec.ts

Every file of `src/` answers the same way. Dropping the leading slash makes the linter run and
report 6 errors in that one file.

**Effect.** `npm run format:ci` exits 0 and reports 71 files checked, measured 2026-09-23. Those 71
are the formatter and the import sorter. The linter contributes nothing to any gate, so a lint class this repository has
switched on is unenforced. Whole-tree counts the moment the glob is corrected: **15 errors and 13
warnings** with the spec exemption intact, and **32 errors and 35 warnings** with the specs linted,
13 spec files carrying diagnostics.

**Pin.** None. No test asserts that the linter runs, which is why the glob could stop matching
without any check moving. `biome lint <file>` is the instrument that answers; `biome ci` never
reports that the linter did nothing.

**Open.** Whether the linter should run is JH's decision, because reviving it turns the tree red by
15 errors and the spec exemption is worth 17 more.

---

## Known: a citation anchored to a line has no guard, and most of them were already wrong

**Observation.** Prose, docstrings and guard tables cite files by path, and some cite a path with a
line number. `scripts/name_drift.py` resolves the plain form: a backticked path is checked against
the files the tree holds, with a short list of prefixes for what the tree produces rather than
holds. It also refuses a `<lean file>:<line>` token as a class, because a Lean line is what an edit
moves and a declaration name is not. What has no guard is the same form aimed at a `.ts` file or a
Markdown file.

**Effect.** Six citations carry a line number that nothing checks: `docs/dynamo-datatypes.md:130`
from `Calculus/Dynamo/Lang/Store.lean`, `src/codec/attribute.ts` and `src/codec/spec/laws/codec.depth.spec.ts`;
`src/codec/spec/literal/codec.set.spec.ts:76` from `Calculus/Dynamo/Alg/Products.lean`; and
`src/codec/attribute.ts:138` and `src/codec/codec.ts:1466` from
`src/codec/lean/lean.predicates.spec.ts`. Any edit above one of those lines moves it, and every
check stays green.

**And the rot is not hypothetical.** Of the 29 line-anchored citations this repository held before
the guard landed, **19 pointed at something that was not a declaration**: a blank line, a tactic
step, a match arm, or a different concept entirely. In the combinator algebra, line 174 was cited
as `funImage` and read `· exact nomatch h`; line 409 was cited as `isStored` and read a
`funext`/`simp only` line; line 2292 was cited as a store-survival theorem for number, since retired, and was blank. The 23
aimed at Lean files are rewritten to declaration names; these six are what the class leaves behind.

**Pin.** The Lean form is pinned by `name_drift.py`, which fails on it. The six above are pinned by
this entry and by nothing else. The reason they are not rewritten with the rest: three of them
point at a row of a table in `docs/dynamo-datatypes.md`, which has no declaration to name, and a
guard that refused them would demand a name that does not exist.

---

## Known: the exact-optional-property flag is off, and turning it on does not typecheck

**Observation.** `tsconfig.json` switches on strict mode and unchecked-indexed-access and leaves the
exact-optional-property flag off. Measured 2026-09-07:

    npx tsc --noEmit --exactOptionalPropertyTypes
    9 errors

Four are in library source, three in `src/codec/codec.ts` and one in `src/Rotorise.ts`. Five are in
specs. By diagnostic code: three at 2379, two at 2375, two at 2345, one at 2344, one at 2322.

**Effect.** An optional property accepts an explicit undefined value where the declaration means the
property may be absent. The distinction matters at the boundary this library writes, because an
attribute that is absent and an attribute holding an undefined value are different wire shapes.

**Pin.** None. The flag is off, so no check fails.

---

## Partially mitigated: the corpus pins a numeric set and no scalar numeric value

**Observation.** `Value.num` carries a `WFNumeral`, which is a closed term, and `leanValueOf` emits
`Value.num (WFNumeral.of "1.5")` for a `DynamoNumber`. The set half is in the corpus: a set vector
at `dynamoNumber.set()` is in `sampleVectors`. Measured 2026-09-23 with `grep -o 'Value.numSet'`,
`Value.numSet` appears once in each committed sample, 36 times in `.vectors.full.lean`, once in
`.readvectors.lean` and 11 times in `.resolutions.lean`.

**Effect, and it is the scalar half.** Measured the same way, `Value.num` appears zero times in each
of the eight gate artifacts. The numeric entry in the four corpus lists that cross codecs against
each other is `dynamoNumber`, and it is not in `sampleVectors`, so no write vector carries a scalar
numeric value. The read side is covered: `Attr.n` appears 185 times in `.readverdicts.lean`. So one
direction of one shape is unpinned. The `decimal` vector carries `Value.str "1.5"`, which is
correct, because `decimal` is `held` over `number` with the text pair, so its value is text.

**Pin.** The set half is pinned by the set vector in `sampleVectors`, which the gate elaborates.
The scalar half has no pin, and closing it means putting a scalar `dynamoNumber` vector in
`sampleVectors` rather than only in the crossing lists.

---

## Known: the model refuses two stand-ins at one name where the host accepts two equal ones

**Observation.** The host's stand-in test accepts two fields that read a map without the name to
values that `Object.is` equates. The model decides the same test with `absentAgreeG`, and
the constants of a fill (`Sig.K`) have no decidable equality, because neither `Value` nor `Json`
derives one. So the model refuses two fills at one name whatever their constants.

**Effect.** A union of two objects that declare one stand-in at the same name is accepted by the
host and refused by `compatPair`. The model is coarser, so no verdict that the model gives is
wrong; the bridge cannot check the host's acceptance of such a union.

**Pin.** The corpus in `src/codec/lean/lean.spec.ts` puts the pair to disjointness only. To
reproduce, add the pair of two stand-in objects to fallbackPairs(), emit with
`EMIT_LEAN_REFUSALS=1`, and elaborate `formal/.separations.lean`: `decide` proves the
`compatPair` of the pair `false`.

**Open.** A decidable equality on the constants, or a constant syntax that has one, closes it.

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

## Known: a refusal renders the value it rejects, and one rendering path is unguarded

**Observation.** Naming a value runs that value's own conversion, which is caller code. A value
with no conversion, or one whose conversion throws, therefore throws from inside the refusal path
— turning an expected failure into an exception at the one place whose job is to describe a
failure.

The codec paths are guarded. The renderer in `src/codec/value.ts` catches the conversion at the
seam and falls back to a shape-only description, and the shape describer beside it composes the
two, so a value that cannot render is named by its shape alone.

**The marshaller port's fall-through refusal is not guarded.** It interpolates the value directly,
which runs the same conversion outside any catch. Reproduced 2026-09-07 with a class whose
conversion throws, marshalled with the class-instance option off:

    native({}).encode(new Hostile())
    THREW: toString threw

It throws the caller's error out of the write half instead of returning the pair's own error.

**Effect.** A caller who expects a refusal gets an exception, from the branch whose message exists
to explain the refusal. The write half stops returning an error as a value exactly where the value
is least well behaved.

**What is mitigated.** Every ground codec and both literal forms route through the guarded seam,
and a test pins it: it feeds a value built with no prototype to seven codecs and asserts each
refuses rather than throws. What remains is the marshaller port's fall-through, reached by a class
instance when the class-instance option is off.

**No total renderer exists to write instead**, because a conversion is arbitrary user code. The
repair is to route the remaining site through the same seam, not to write a renderer.


---

## Partially mitigated: the type level reads a key pinned through a ref as unpinned

**Observation.** A pattern pins a key at the term only where the term holds a literal. The type
level reads the literal from the term of the codec, as the run time does, and a refinement in a
pattern is refused at the type and at run time. A bare `ref` slot of an entry of a scope, and a bare
`ref` under `optional`, `undefinable(...)` or a fill, reads as the entry that the name binds, and
each option of a union reads under the scope of the union. One case remains. A slot that holds a
`ref` deeper, such as an option of a union inside a field, holds no scope in the term. The type
cannot decide whether the member fits, so the type keeps the member:

    a key pinned through `union([ref('Red'), string('blue')])`, where the scope binds the name Red
      type checker: the member is kept
      runtime:      the key is pinned, and the member is kept

**Effect.** The result type of extract keeps a member that the run time can drop. Every value fits
the type, and the type is wider than the value. The type bridge holds the case as `extract(...)`
refuse ids on two roots of the pool, one for each one-name clause that the pool draws and for three
union-pattern clauses: the run time drops the member, and the type keeps it. The type bridge prints a
`ref` that closes no cycle as a `ref` under a scope, so the type and the run time read one codec.
Measured 2026-10-28 with `formal/scripts/gate.sh`.

**Open.** A slot closed in its scope at any depth closes the case.

**Pin.** `src/codec/spec/union/codec.slice.spec.ts`: the type keeps a member pinned through a
`ref(...)`, the type drops a member whose `ref` binds a base, an optional key, or an entry with a
union option that names a `ref`, and the slice that keeps a member pinned through an adapter.
`src/codec/spec/union/codec.slice.pattern.spec.ts`: the refusal of a refinement.
`formal/scripts/type_bridge_baseline.txt`: the `extract(...)` refuse ids of the two roots.

---

## Known: the refusal of an empty clause below the root has no test

**Observation.** `Closed.preconditionOfC` refuses a clause with no name below the root: the clause
admits each map there, and the empty conjunction admits each attribute. No test puts the same
clause to `preconditions(at(...))`.

**Effect.** A host that drifts from that refusal passes the suite.

**Pin.** None.

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

**Observation.** The predicate in `src/codec/term.ts` that decides that a term holds no value answers `true` for `never` and for a union
whose every option holds no value. The list position rule, the field rule, the meet
and `nullable` read it. Two forms hold no value in the model and answer `false`:

    list(string, refine(string, (_: string): _ is string => false))   // builds
    list(string, held(never, boolean, adapter))                       // builds

**Effect.** Each such list or object holds no value and builds. A refinement stays out because no
function decides that a closure admits nothing. The `held` stays out because two pinned vectors
declare that `held` in a list position.

**What is mitigated.** `union([])`, a union of empty options, and each of these through a `ref`
are refused where `never` is, in the type and at run time.

**Pin.** `src/codec/spec/surface/codec.resolution.spec.ts` pins the refinement. The `held` is
declared by the shared legacy read vector of `src/codec/lean/lean.spec.ts` and by the legacy read test of
`src/codec/spec/laws/codec.held.spec.ts`.

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

## Known: a discriminator value that names a property of the prototype gives no key

**Observation.** The run-time key builder reads the arm of a discriminated spec through the
prototype chain. A value such as `constructor` finds a function, not an arm, and the builder reads
the function as an attribute name. Measured 2026-10-29 with `npx vitest --run` on the spec
`{ discriminator: 'kind', spec: { x: ['a'], z: null } }`:

    kind 'x'                                   key "A#1"
    kind 'w'                                   throws: the value names no arm
    kind 'constructor', 'toString', '__proto__' no key, no throw

**Effect.** An item whose discriminator holds such a value gets no key, and nothing reports it. The
model refuses the item (`KeyMatch.select_unknown`).

**Pin.** `src/codec/lean/lean.key.spec.ts`: a test that expects the refusal, marked to fail while
the builder reads the prototype. The fix makes the test fail, and moves the rows into the key vector
pool.
