# Roadmap of the Lean development

What this system would be in the future. One entry per future state, with what decides whether the
state arrives.

An entry here is a state the system does not have. A statement of what the system *is* belongs in
the architecture. An issue belongs in `defects.md`.

An entry carries no measurement. A count is short lived: it belongs in the commit that measured it,
in `defects.md` where it pins an issue, or in the gate's output. A figure appears here only where
the figure is itself the threshold that decides the entry.

Each entry names declarations and files. It points at no section number, because a section number
moves and a declaration name does not.

---

## The term language is founded on a pre-term, so an undischargeable union has no inhabitant

**The future state.** `Term` becomes a subtype of a pre-term, carrying its own well-formedness:
`{t : PreTerm // wf t = true}`, where `wf` recurses after the inductive rather than inside it. A
union whose options are not shown compatible then has no inhabitant, so such a union is a type
error rather than a runtime refusal.

**The ruling today is no, and it is JH's.** The model's `Obligations` already carries the
compatibility of a union, and `soundness` takes it as a premise. The library refuses such a union
at construction. The re-founding buys the model a stronger statement about itself and buys the
library nothing it lacks.

**Two other shapes do not elaborate, and both were run rather than argued.** A witness indexed by
the option list it constrains is induction-induction, and the elaborator answers `unknown
identifier` on the type being defined. A field whose type is computed from the term is
induction-recursion, and the elaborator answers `invalid mutual block: either all elements of the
block must be inductive/structure declarations, or they must all be definitions`. The subtype shape
elaborates and is axiom-free, so the obstruction is not expressibility but cost.

**The obligation is a `Prop` today.** `PairwiseCompat` sits in `Obligations`, beside the
judgement, and a term that does not meet it is still a term.

**The cost is structural.** Every constructor of `Term` becomes a smart constructor carrying a proof
obligation, and every match on a term goes through the subtype's first projection. `Term` is the
vocabulary of most of `Calculus/`, so the re-founding reaches every signature that names it. The
commit that probed this holds the site count; the count moves with the tree and the shape of the
cost does not.

**What decides it.** A statement the model owes about itself that `Typed` cannot make. Until such a
statement exists, the re-founding pays the whole term language for a guarantee two other layers
already give.

**What names the guarantee instead today.** `PairwiseCompat`, one `Prop` over the option list.
`pairwiseCompat_of_HF` discharges it with no certificate, `pairwiseCompat_of_sub` through a common
bound, and `pairwiseCompat_of_separated` with `separated_of_unionOk` through the certificate.

---

## A term can be recursive

**The future state.** A term can refer to itself: `lazy` binds a name, or `denote` stages. A
recursive union then denotes the least fixed point of its unfolding, and the emitter states a
recursive schema rather than refusing it.

**The obstruction is the term language, not the union.** `Term.lazy` carries a plain `Term`, and
`denote` is structural, so no term is recursive. The host's `lazy` builds a recursive schema, and
the emitter refuses a `lazy` chain that it cannot close. The host's `union` refuses an option
whose spine reaches a recursive thunk, and keeps recursion below a list or an object. The union
is the compatible join, and where the admitting options agree, first-match resolution is monotone
and continuous (`selectF_mono_list`, `selectF_continuous_list`). Those are the two obligations of a
least-fixpoint construction. The literature is Kaarsgaard, Axelsen and Glück, "Join inverse
categories and reversible recursion" (JLAMP, 2017): an inverse category with countable joins has
morphism schemes for reversible recursion.

**The measurement decides it now: do not build.** A probe built the construct in a
standalone model: a binder over de Bruijn variables, and a denotation that budgets each input by
its own depth. The fixed point is structural and stable, a two-option `opaque` over strings and
lists is an instance of it, and its stages still reduce by `rfl`. Two kills bound the construct.

- **A `held` on the recursive path defeats the guard.** "Recursion only under a list" is not
  sufficient once an input transform sits between the list and the variable. A transform that
  wraps its input back into a list keeps the depth from falling, so each stage writes a deeper
  attribute and the budgeted unfolding never stabilizes. The guard must exclude `held`.
- **A well-founded budget stops `rfl`.** The same budgeted `opaque` by well-founded recursion
  evaluates, and the kernel does not reduce it. The budget must stay structural.

**The cost is larger than the deletion.** The construct adds a variable and a binder to `Term`,
an environment to `denote` and to each companion a stratum owes, an arm per new constructor in
each declaration that matches on a term, and an open-term restatement of each induction over
`Typed`. It deletes at most the special machinery of `Opaque.lean`.

**What would change the verdict.** A recursive schema that a caller needs and that neither
`opaque` nor recursion below a list or an object in the host can state. A deletion larger than the
construct adds. A guard that admits a `held` on the path and still stabilizes. The measurement
stays valid until the term language or the guard changes.

---

## A reader can tell what every public theorem says from its name and one line

**The future state.** Every public theorem in `Calculus/` carries a docstring, so a reader who knows
the specification can tell what the theorem says without reading its proof.

**A coverage bar is the wrong instrument, and that is settled.** A bar over the coverage this tree
has would be switched off or exempted into meaninglessness, and the fraction it would have to name
is the fraction it exists to reject. `scripts/ratchet.py` holds the count of undocumented public
theorems and fails when it rises. A ratchet costs nothing to satisfy on the day it lands, which is
why it is what runs.

**What decides it.** The ratchet reaching **zero**. That is the one figure this entry carries,
because it is the threshold and not a measurement: the state arrives when no public theorem is
undocumented, one pass at a time, and no threshold in between is worth setting. The current count is
the gate's output, not this file's.

---

## The term language separates a carrier from a restriction, and the certificate meets descriptions

**The future state.** `docs/architecture-v2.md` describes it in full and this entry does not
repeat it. In one sentence: a literal is a refinement at a singleton, an adapter re-indexes
rather than restricts, a name description is an admissible set rather than two coordinates, and
the certificate meets descriptions rather than terms.

**Why it is a roadmap entry and not the architecture.** `architecture-v2.md` states the intent
and does not govern. `architecture.md` governs. A reader who wants to know what the system is
reads the second; a reader who wants to know where it is going reads the first. Neither repeats
the other, and this entry is the only place that says how they relate.

**The ruling today is not yet.** The generated artifacts are stated over the term language, and
the gate elaborates each of them. So a change to the constructor set lands checked wherever the
change reaches an artifact.

**What decides it.** Three things together, and none is a judgment call. The structure exists
under `Calculus/`. `architecture-v2.md` replaces `architecture.md` under that name.
`formal/scripts/name_drift.py` swaps the two in its `CURRENT` list, which is what makes the new
document guarded and the old one gone. Until the third happens the new document cites names that
do not exist and nothing reports it, which is stated at its head.

---

## The value side and the attribute side are one parametrised development

**The future state.** The analysis is written once and instantiated at the value side and at the
attribute side, rather than written twice.

**The ruling today is no, on measurement.** The twins that are cheap to merge are cheap because
there is nothing in them: membership lemmas, wrappers, and one-line abbreviations. The twins that
hold the bulk of the mass are twins in name only, and the largest are the least alike —
`ExactV_set` against `ExactA_set`, `occV` against `occA`, `occV_sound` against `occA_sound`,
`AdmLit` against `AdmALit`, `Adm` against `AdmA`. A parametrised development would abstract the
boilerplate and leave the content untouched.

**This is the same fact the codec algebra states from the other side.** `carriedCodec` states one
codec for both sides precisely where the two sides are the same. Where they are not, the doubling is
content rather than repetition. The side split stays local: it does not thread through the codec
algebra. `setCodec` in `Products.lean` is the standing exception, the one product that is not an
instance.

**Do not cost this on a pair count.** A pair count is an artifact of the transform that produces it,
and successive passes have produced different ones from the same tree. Two passes over the same
bodies, differing only in whether the value-side names were renamed before comparing, disagreed on
how many pairs are near-identical and agreed on which twins sit at the bottom. The
size-against-similarity ordering is the dimension; no single count is.

**What decides it.** An ordering that survives a change of transform and puts the bulk of the twin
mass at high similarity. Until then the merge abstracts what does not matter.

---

## The development carries its own constructive `Finset` layer

Mathlib resolves `k ∈ (s : Finset α)` through `Finset.instSetLike`, whose injectivity field
is proved classically, so every statement that mentions membership in a key set carries
`Classical.choice`. No proof in `Calculus/` appeals to choice, and none needs it.

**The layer alone does not drop the axiom, and that is measured rather than expected.** The
`Finset` route is one of several. Core Lean's own string lemmas reach `Classical.propDecidable`
through the UTF-8 decoding proofs, and theorems across five modules reach choice that way; cut
`Finset.instSetLike` out of the citation graph and those theorems still reach it. One arithmetic
simp lemma is a third route. `scripts/classical_gateways.txt` holds the set, and the gate fails
on a route that is not in it. So this entry delivers a constructive membership layer, and a
constructive *base* is a further state that needs the other routes closed as well.

The state this entry names is a membership and decision layer of this development's own, over
`Multiset.Mem` rather than the coercion to `Set`, with the mathlib lemmas the tree uses restated or
bridged against it. `MapOf` in `Domain.lean` is where it starts, because the key set is a
`Finset Name` and `MapOf.at` is the first declaration that decides membership.

**What decides it.** Two local instances, membership and its decision, were measured against the
whole tree and moved a small fraction of the declarations that reach the axiom. So the entry arrives
only with the restated lemmas, not with an instance. It arrives sooner if mathlib makes the set-like
route constructive upstream, and the entry closes with no work here if that happens.
