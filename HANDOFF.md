# Handoff

**Branch `wip/map-types`, tip `5b6a0c1`, 25 commits ahead of `6b208fc`. Working tree clean.
`lake build` green and warning-free, `#assert_axioms_all` over 20 modules, `guard_reach.py`
and `name_drift.py` exit 0. TypeScript: 862 tests, `tsc --noEmit` clean on the host, biome at
its pre-existing 8.**

Delete this file once read — it is a handoff, not a document.

---

## The one idea, because everything below is an instance of it

**A row that asks its codec is exact for free.** `custom` always did it —
`adm (.custom ce _) = fun v => (ce v).isSome`, the codec's own domain rather than a description
of it. Nothing else did. Seven rows were converted this arc: `opaque` (write and read), `admA
.number`, `admALit .number`, `admALit .decimal`, `AdmALit .decimal`, and `refine`'s read side.
Every one had a recorded justification for being `⊤`, and every justification was the same
mistake in different clothes — *"the row cannot name the set"*, when the row never needed to
name it, only to ask.

The corollary that keeps paying: **a description must be kept in agreement with what it
describes; a question cannot drift.** That is why `AdmOpaqV` (a hand-written recursion stating
opaque's domain a second time) was rejected in favour of asking, and why `admALit .decimal` and
`AdmALit .decimal` are the *same function* rather than two spellings with an equality lemma.

---

## What landed, in five arcs

**Cleanup (`f739ac9`–`65042ff`).** The residue sweep: 36 declarations, 302 lines. The estimate
was ~61 and §4.1 records why the miss was systematic. The prose queue closed (items 1, 2, 3, 9,
10, 14). Item 7 removed `objectCodecCore`'s free filter — the cost was not the five signatures
but a ten-line hand re-proof at a call site that could not see the discharge.

**The bridge (`947eb82`, `c9a272b`, `af7e25b`).** C1–C3 was "a paper obligation" and §5.7 said
to fix it by differential testing, assuming Lean generates the vectors. **It cannot** — `denote`
is `noncomputable`, `#eval` fails at the first term, `Finset.sort` is stuck in the kernel. But
the kernel *evaluates* `denote` by `rfl`. So the direction is forced: the host proposes, the
model checks. `Calculus/Vectors.lean` is the checker (`aeq`, three-valued `Verdict`, so an
under-fuelled vector fails the build rather than passing quietly); `src/lean.ts` is the emitter,
reading the right-hand side out of `unsafeEncode` so what is checked is what the library
actually writes. ~90 ms per 2-deep object vector, linear, batching harmful. **CI-shaped, and CI
is parked at JH's instruction until he unparks it.**

**Library defects the model found (`7e69b0c`, `f4e1145`, `fdfa53a`).** Duplicate discriminator
tags silently shadowing a variant; a tag lookup reaching `Object.prototype` and throwing a raw
`TypeError` from stored data; no nesting-depth check, plus a `RangeError` at pathological depth;
`CodecDef` unable to tell `Rest.drop` from `Rest.refuse`. All found by asking whether the host
checks a premise the model states — the §9 question.

**Three refutations that killed planned work (`fe9d397`, and §4.1, §12.5).** The relational
format (§5.6 #4) replaces (R) *only*; (C) and (MP) fall to kernel counterexamples, and it would
require the non-malleability property **§10.3 says we deliberately fail** — two sections of one
document reaching opposite conclusions, neither citing the other. `Codec μ` (§5.6 #1): 481 of
968 signatures for ~30 obligations, and it cannot deliver the static member. The exactness
apparatus as symptom (§5.6 #3): 0 of 7 rows were loose-type. **Two more measurements killed
changes after that** — parameterizing the numeric carrier (984 of 1460) and moving `AdmOpaqV`
downhill.

**The per-codec arc (`18b2e7d`–`5b6a0c1`), which is JH's design.** `opaque` is a well-behaved
`custom` — same analysis, opposite warranty (`Obligations (.opaq _) = True`, its laws are
theorems). Sets indexed by `SetBase = string | number | decimal | binary`, four bases onto three
wire members, restriction being a refinement *of the set*. `refine` checks both directions.
`decimal` is now a `GroundKind` with carrier `StoredNumeral`.

`Analysable` and `AnalysableA` went from 14/21 and 13/21 to **19/21 on both**. The two that
decline are `union` and `nullable`, on both sides.

---

## Pick up here

### 1. `src/` is unfinished and `src/lean.ts` is now stale

Two agents were dispatched and killed by a sustained 529 outage (eight failures); their briefs
are in their transcripts and a resume would recover them. What they were to do:

- **`.set` is a capability that propagates**, not a property of the five primitives. It belongs
  on any codec reducing through `refine` and literals to a set-able base — reuse the existing
  `setBase(codec)`. So `amount.set()` exists and gives `ReadonlySet<Price>`, because the brand
  rides on `amount` where it already lives. **This is JH's correction to an earlier verdict that
  kept `set(...)` first-class on branding grounds; that verdict was right about
  `decimal.set(...)` and wrong about the conclusion.**
- **Remove `set(...)` and `literal(...)`** — not deprecate. Migrate every caller.
- **`src/lean.ts` refuses `decimal('1')` with a note that it is pending.** It is no longer
  pending: `5b6a0c1` made it emittable. Lift the refusal and add vectors.

### 2. `nullable` is the keystone, and `union` inherits from it

`ownsNull` is a computable `Bool` off the subterm's codec, so the row is the same ask-the-codec
move and needs no mutual recursion with `admA`:

```
adm (.nullable t) v  =  adm t v ∨ (v = null ∧ ¬(denote t).ownsNull)
```

and at `.null` it collapses to `((denote t).e .null).isSome ∨ ¬((denote t).p .null).isSome`.

**`union` is not independently forced.** Its counting row is unsound only while some subterm's
row is loose — a count is anti-monotone, so loosening an option adds an admitter and flips 1 to
2. After `nullable` there would be none. Two caveats: the recorded justification cites
`union [opaq true, set (held string collapse)]`, a term `SetBase` **deleted**, so the objection
is unstatable as written; and `select`'s filter is not `Adm` — `optionSemOf` builds object
options with `.byNames` (a `keysOk` name test), so the row must mirror `semsOf` rather than
count `Adm`. Carpentry, not a wall.

If both land, both sides reach 21/21 and `excuse_witnessed` becomes a theorem about an empty
set — decide what that means rather than discovering it.

### 3. Smaller, all real

- **`adm (.literal .number ls) = inL k ls` is not exact** — missing `WF d.toDec`. Deliberately
  left at `5b6a0c1`; it is an over-approximation, not a `⊤`, and tightening it breaks
  `adm_literal_num`'s `rfl` and every `SepV` over literals.
- **`admA .number`'s sibling rows** — check whether other ground rows are `⊤` for the same
  retired reason.
- **`select` over `List.attach`** — queued since `Codec μ`'s spike found it: a standalone strict
  improvement that removes the only structural obstruction in the union proofs.
- **Item 18's other half** — ~45 dangling names in `codec-formalization.md` §4. A judgement about
  whether a change log should carry names of deleted things, not an edit.
- **`ConstantCodec.constant` is a phantom** — `undefined` at runtime, never assigned.
- **`docs/codec-calculus.md` is normative and lags the model** at several `admA` rows and at
  `(set)`. Left unamended on item 10's precedent: the specification waits for JH's call.

---

## Landmines

**`lake env lean` reads the *existing* olean of a dependency.** Edit `Domain.lean`, check
`Combinators.lean`, and the new constructor is an "unknown identifier" until you
`lake build Calculus.Domain`. I warned two agents about this and then walked into it myself.

**Host writes take ~1 s to reach the container mount.** `sleep 2` after editing, before building,
or you verify a stale file.

**Never run two `lake build`s at once.** One agent in `formal/` at a time; others may use
`lake env lean`, which writes nothing.

**Four classical routes found this week, all ordinary.** `omega`; **`by_cases` and `by_contra`,
which reach `Classical.em`** — use `cases h : decide P` and `Decidable.byContradiction`;
`DecidableEq (Finset α)` (`Finset.decidableMem` is clean; `fsetEq` in `Vectors.lean` is the
repair); `Finset.filter_empty` (`rfl` is clean). **Two entered through a `def`, not a proof** —
`#print axioms` on the *definition* was already classical with no tactic at fault. Check
definitions, not only theorems.

**The axiom guard only sees imported modules.** `Axioms.lean` imports a hand-maintained list;
`scripts/guard_reach.py` now fails if any module is outside its closure. Two modules hit this
before it existed.

**`name_drift.py` cannot catch a wrong signature** — only a name that does not exist. It found
`README.md` describing `denote : Nat → Term → Codec` only because a human read it.

**`linter.unnecessarySeqFocus` was wrong once** and following it broke a proof: `try split`
leaves two goals and the `;` it suggests reaches only the first.

---

## The thing to keep

**Roughly one reading-derived verdict in three is wrong, and this arc is the evidence.** Six
"impossible"s turned out to be "did not": `denote` unevaluable (true of `#eval`, false of the
kernel); `adm` unable to state opaque's recursion; `Double.ofDec` blocking the numeric rows;
the same at numeric literals; `refine` unable to check its predicate on the read side; and
`decimal` unable to be a ground base. Three planned changes were killed by measuring first.
Three documented claims were refuted, one of which — §5.6 #4 against §10.3 — was the document
contradicting itself.

**The ones that held, held because a probe settled them in under a minute.** `DecidableEq Term`,
`Multiset Term` in a nested inductive, `Finset.toList`, `union`'s anti-monotonicity.

So: **probe, do not argue.** Write four lines and check, rather than reasoning about it. And
when an agent reports that its brief was wrong, that is usually the most valuable line in the
report — it happened in nearly every dispatch this arc, including twice where the brief was
mine and wrong about what had already landed.
