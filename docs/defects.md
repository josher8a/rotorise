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
values that `Object.is` equates. The model decides the same test with `ObjectSlot.absentAgree`, and
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

## Known: the type level reads a literal off a type, and the term is what the runtime reads

**Observation.** `extract` and `exclude` check a clause at the type level with the type PinsALiteral in
`src/codec/codec.ts`: a member pins a key when the type that the key's codec decodes to is a
literal type. Nothing in a codec's type says which constructor built it, so no other question is
available there. At run time the slice reads the term, and a term pins a literal only where a
literal constructor built it. An adapter whose decode narrows to a literal type pins a literal at
the type level and pins none at the term. Measured 2026-09-24 with a throwaway spec and
`npx tsc --noEmit`:

    const tagA = held(string, string('A'), { encode: (v: 'A') => v, decode: ... })
    const u = union([object({ k: tagA, a: string }), object({ k: string('B'), b: string })])
    u.extract({ k: string('A') })
      type checker: accepted
      runtime:      {"kind":"never"}
    u.extract({ k: string('B') })
      runtime:      the member with the literal

**Effect.** A caller gets a green typecheck and a slice that selects no member. The union itself
has no type-level gate: `union` decides compatibility at run time only.

**Pin.** None. No test declares a clause over an adapter that narrows to a literal type.

**Fix direction.** The type-level test has to read the constructor rather than the decoded type,
which needs a codec's type to carry which constructor built it. It does not today. Widening the
term reader instead would not close it: an adapter's decode is arbitrary code, and no term says
what it returns.

---

## Known: no vector puts the preconditions of the host to `preconditionOf`

**Observation.** The model states the precondition of a clause as data (`preconditionOf`), and
`preconditionOf_exact` proves the precondition exact or refuses it. The host states the same
data as `at(...).preconditions`, computed by `preconditionsOf(...)` in `src/codec/codec.ts`. The
emitter has no form for a precondition. Measured 2026-10-09:

    grep -c -i precondition src/codec/lean.ts
    0

The path vectors state the decision of `at` and of `narrow`, and no precondition.

**Effect.** A host precondition that drifts from `preconditionOf` passes the gate. The tests of
the host pin each precondition form and the refusal of a clause key with no exact precondition.
The refusal of an empty clause below the root has no test. Measured 2026-10-09: a mutant of
`preconditionsOf(...)` that never refuses an empty clause passes `npx vitest --run src`, with 62
files and 1349 tests passed, 9 skipped. A throwaway script shows that the refusal fires at HEAD:

    object({ u: union([object({ k: number(1), a: string }), object({ k: number(2), b: string })]) })
      .item.at((p) => p.u.narrow({}).a).preconditions
      CodecError: the clause at 'u' names no key, so no precondition states that the attribute is a map

**Pin.** `src/codec/spec/union/codec.preconditions.spec.ts`, on the host side only. No vector, and
no test of the refusal of an empty clause.

---

## Known: `narrow` at a recursive union has no row in the path vectors

**Observation.** The pool states a clause path only where `unionAt(...)` in `src/codec/lean.ts`
accepts the decision of the host. `unionAt(...)` refuses a union that is a binder: the options
read the union through a variable, `narrow` reads the variable open, and the host reads the thunk
closed. The host narrows at such a union. Measured 2026-10-09 with a throwaway script:

    const Node = lazy(() => union([object({ k: string('leaf'), v: string }),
                                   object({ k: string('node'), c: array(Node) })]))
    object({ n: Node }).item.at((p) => p.n.narrow({ k: string('leaf') }).v)
      runtime: path n.v, term {"kind":"string"}
    unionAt(hostAt(object({ n: Node }), ['n']))
      false

Each `NarrowRows` of the generated path files narrows a `Term.union`, and none narrows a
`Term.mu`. The model's `narrowFrames` has a case for a recursive union, and no row reads the case.

**Effect.** The decision of the host at a clause on a recursive union reaches no kernel. A host
walk that narrows such a union wrongly passes the gate.

**Pin.** The docstring of `unionAt(...)` states the refusal. No test asserts that a recursive
union has no clause row, and no test of the host narrows a recursive union.

---

## Known: the path type of `narrow` reads the decoded literal of a caller's adapter

**Observation.** This is the defect of `extract` above, at `narrow`. The path type decides which
members a clause keeps with the types Kept and StoredApart in `src/codec/codec.ts`. StoredApart
pins a literal by the decoded type of a codec. At run time the walk of `at` narrows by the stored
view of the term, and the stored view of an adapter is its inner term. So an adapter whose decode
narrows to a literal type pins a literal in the type, and pins none in the walk. Measured
2026-10-09 with a throwaway script and `npx tsc --noEmit`:

    const tagA = held(string, string('A'), { encode: (v: 'A') => v, decode: ... })
    const M = object({ u: union([object({ k: tagA, a: string }),
                                 object({ k: string('B'), b: string })]) }).item
    M.at((p) => p.u.narrow({ k: string('B') }).b)
      type checker: accepted, a codec of string
      runtime:      term {"kind":"never"}, and encode refuses:
                    'u.b' is declared by some variants only ... Call `narrow({...})` ...
    M.at((p) => p.u.narrow({ k: string('B') }).a)
      type checker: refused

The type drops the member that holds the adapter. The walk keeps the member, because the stored
view `string` is not apart from the literal `B`.

**Effect.** A caller gets a green typecheck and a path whose codec refuses every write. The
refusal tells the caller to call `narrow`, which the caller already called.

**Pin.** None. No test declares a clause beside an adapter that narrows to a literal type.

**Fix direction.** The same as for `extract`: the type-level test has to read the constructor
rather than the decoded type, and a codec's type does not carry the constructor today.
