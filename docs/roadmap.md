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
union whose options no value can separate then has no inhabitant, so a union that cannot resolve is
a type error rather than a runtime refusal.

**The ruling today is no, and it is JH's.** The model's `Typed` already makes an undischarged union
underivable, and the library already refuses such a union in its own type and at construction. The
re-founding buys the model a stronger statement about itself and buys the library nothing it lacks.

**Two other shapes do not elaborate, and both were run rather than argued.** A witness indexed by
the option list it constrains is induction-induction, and the elaborator answers `unknown
identifier` on the type being defined. A field whose type is computed from the term is
induction-recursion, and the elaborator answers `invalid mutual block: either all elements of the
block must be inductive/structure declarations, or they must all be definitions`. The subtype shape
elaborates and is axiom-free, so the obstruction is not expressibility but cost.

**A `Prop` premise on the judgement is no substitute.** `Separates` is stated on `Adm` and
`admitOptV`, and the import chain runs `Typing`, `Soundness`, `Discharge`, `ExactV`, then
`Orthogonality`. The premise would sit above the rule it constrains, in a module the rule cannot
reach.

**The cost is structural.** Every constructor of `Term` becomes a smart constructor carrying a proof
obligation, and every match on a term goes through the subtype's first projection. `Term` is the
vocabulary of most of `Calculus/`, so the re-founding reaches every signature that names it. The
commit that probed this holds the site count; the count moves with the tree and the shape of the
cost does not.

**What decides it.** A statement the model owes about itself that `Typed` cannot make. Until such a
statement exists, the re-founding pays the whole term language for a guarantee two other layers
already give.

**What names the guarantee instead today.** `Separated`, one `Prop` over the option list, with
`separated_of_orth` as the classifier's bridge into it.

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
