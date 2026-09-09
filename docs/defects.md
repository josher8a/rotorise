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

**Effect.** `npm run format:ci` exits 0 and reports 62 files checked. Those 62 are the formatter and
the import sorter. The linter contributes nothing to any gate, so a lint class this repository has
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
from `Calculus/Domain.lean`, `src/codec/attribute.ts` and `src/codec/spec/laws/codec.depth.spec.ts`;
`src/codec/spec/literal/codec.set.spec.ts:76` from `Calculus/Products.lean`; and
`src/codec/attribute.ts:138` and `src/codec/codec.ts:1466` from
`src/codec/lean/lean.predicates.spec.ts`. Any edit above one of those lines moves it, and every
check stays green.

**And the rot is not hypothetical.** Of the 29 line-anchored citations this repository held before
the guard landed, **19 pointed at something that was not a declaration**: a blank line, a tactic
step, a match arm, or a different concept entirely. In the combinator algebra, line 174 was cited
as `funImage` and read `· exact nomatch h`; line 409 was cited as `isStored` and read a
`funext`/`simp only` line; line 2292 was cited as `survivesStore_numberCodec` and was blank. The 23
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

## Partially mitigated: the numeric host is an axiom, so no numeric value can be written

**Observation.** `Double` is axiomatized deliberately, because IEEE-754 facts are not this
calculus's theorems. `Double.toDec` is a field of `NumericHost`, so `Numeral.WF d.toDec` has no
decision procedure for any `d` a proof can name, and this development holds no concrete `Double`.

**Effect.** No closed `Double` term exists, so `Value.num` is unconstructible. Three consequences
follow, and all three are structural rather than incidental. `number` and a numeric literal can
never carry a positive encode vector, so the differential corpus is silent on the one base whose
host semantics are least obvious. `Term.number` is emittable, so it appears in the refusal cross
product while its value side is blocked. And in the read-side differential the row for `.n` goes
through `Double.ofDec`, which has no computation rule, so it reduces to neither `true` nor `false`
and both assertions fail rather than one — which is how a stuck row was told apart from a
disagreement, `AdmA .decimal` and `AdmA .string` reducing on the same attribute.

**What is mitigated.** The axiom block is checkably an interface rather than binary64 under another
name. `numericHostWFNumeral` and `numericHostUnit` inhabit `NumericHost` at two types with
provably different decimal images, by `numericHost_images_differ`, and the first is built with no
`Double` axiom at all. So every theorem that is really about the interface holds of a host with no
rounding. The gate travels as the element's own second component through `WFDouble`, so admission at
a numeric literal is exact rather than over-approximating.

**What remains.** The corpus blind spot. Three pairs of the read-side differential are stuck, not
divergent, and no vector pins the numeric write path at all.

**Pin.** The stuck rows are visible in the read-side differential artifact that the gate elaborates.
The term-level twin is pinned as permanent in the bridge spec under `src/codec/lean/`.

---

## Known: the iso premise of the wrapper rule is stronger than the proof consumes

**Observation.** The specification's wrapper rule demands total cancellation on the two carriers:
one composite is the identity on the held set and the other is the identity on the inner carrier.
The mechanization asks for less. `IsoCancels` in `Codec.lean` restricts both directions to the
values the write half accepts — one clause per direction, each guarded by the encode being defined
— and its own docstring says it is the domain-restricted form the laws actually need.

**Effect.** A caller pays a premise the proof does not use. The two theorems that consume the
premise, `LawfulCore.through` and `Lawful.through`, close on the restricted form alone, so the
totality the specification asks for is never appealed to. This is the mirror of a premise that is
too weak, and the same defect class: a rule and its mechanization disagree about the strength of
an obligation, and the disagreement is in the direction that costs a user rather than the model.

**Pin.** None asserts the gap. `IsoCancels` is the restricted statement and the two `through`
theorems are the evidence that the restriction suffices, but no theorem states that the total form
is unnecessary, and nothing fails if the specification and the definition drift further apart.

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

## Known: the held-set index is not the domain of the write side at a union

**Observation.** The judgement's held-set row ran two claims together. The first, that the held set
equals the denotation's, is proved at every rule by `typed_T_identity`. The second, that the held
set equals the domain of the write side, is false at a union.

**Effect.** The two readings were treated as one, so the row appeared to be established when half of
it was refuted. The first reading is definitional at a union, which is `altCodec_T`. The second is
what remains open.

**Pin.** `not_TIsDomE_unionLiteralString` in `HeldSet.lean` is the refutation, and `HeldSet.lean`
separates the two claims so that neither can be read as the other.

**Not a candidate for closure by deleting the index.** The rules are the model's transcription of
the blueprint's `content.tex`, and a rule whose held set is spelled as the denotation's cannot be read
against the document it transcribes. The identity is what makes the transcription checked rather
than advertised, and it means that only because the two sides are written independently.
