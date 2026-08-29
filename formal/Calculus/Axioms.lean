import Calculus.Soundnessω
import Calculus.Discharge
import Calculus.Continuity
import Calculus.Refutations
import Calculus.HeldSet
import Lean

/-!
# The axiom base, as a checked claim

`docs/codec-formalization.md` §3 advertises that the whole development stands on `propext`,
`Quot.sound`, and the `Double` axioms of §1 — **no `Classical.choice`, no `sorryAx`**. That
sentence was, until now, something a reader had to verify by hand with `#print axioms`.

Here it is a build error instead. `#assert_axioms` collects the axioms a constant actually
depends on and fails if any of them is outside the sanctioned base below.

This is not decoration. `Classical.choice` is easy to acquire by accident: mathlib proves a
great many list facts classically, and a single `by_contra` or an appeal to (say)
`List.filter_eq_nil_iff` silently widens the base of every theorem downstream. Both of those
happened while this module was being written, which is why it exists.
-/

open Lean Elab Command

namespace Calculus

/-- The sanctioned base: Lean's two propositional axioms, plus §1's `Double` interface,
    which is axiomatized deliberately (IEEE-754 facts are not this calculus's theorems). -/
def sanctionedAxioms : List Lean.Name :=
  [``propext, ``Quot.sound,
   `Calculus.Double, `Calculus.Double.decEq, `Calculus.Double.ofDec,
   `Calculus.Double.roundtrip, `Calculus.Double.toDec]

/-- `#assert_axioms c` errors unless every axiom `c` depends on is in
    `Calculus.sanctionedAxioms`. -/
syntax (name := assertAxioms) "#assert_axioms " ident : command

@[command_elab assertAxioms]
def elabAssertAxioms : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload stx[1]
  let axs ← liftCoreM <| collectAxioms name
  let stray := axs.filter (· ∉ sanctionedAxioms)
  unless stray.isEmpty do
    throwError "{name} depends on unsanctioned axiom(s): {stray.toList}\n\
      The sanctioned base is {sanctionedAxioms}. See docs/codec-formalization.md §3."

/-! ## The theorems the documentation makes claims about

§5's soundness, both halves, fueled and fuel-free. If any of these acquires an axiom, the
build stops here rather than in a reader's `#print axioms`. -/

#assert_axioms soundness
#assert_axioms soundness_core
#assert_axioms soundnessω
#assert_axioms soundness_coreω

/-! Both indices of the judgement are claims about the denotation (§3). -/

#assert_axioms typed_μSyn
#assert_axioms typed_e_mem
#assert_axioms typed_p_mem
#assert_axioms carrier_denote

/-! The dischargers of (U) (§5), and the three refutations that repaired the specification
(§4) — a counterexample proved classically would still be a counterexample, but these are
constructive and the guard records that. -/

#assert_axioms uAtCan_of_separated
#assert_axioms uAtCan_of_disjoint
#assert_axioms uniqueAdmission_byTag
#assert_axioms uniqueAdmission_of_kinds
#assert_axioms not_uAtCan_literal_string
#assert_axioms not_uAtCan_array_literals
#assert_axioms not_uAtCan_literal_held

/-! §6's `≡` is not transitive — the one refutation that is about the equational theory
rather than about a row of it. -/

#assert_axioms not_equiv_trans

/-! `ident` has no denotational content to pin — what it has is its relation to `adm`,
which is what §5 uses it for, and `SepV`'s right to drop §5's two `ident` conjuncts
rests on it. -/

#assert_axioms ident_of_adm
#assert_axioms admDisj_ident
#assert_axioms sepV_string_dunion_nil

/-! The three lemmas that pin §5's declaration-time devices to the denotation. Without
these, `κ`, `adm` and `admA` are transcriptions of a table rather than claims about the
model, so their axiom base is part of what the soundness statements rest on. -/

#assert_axioms κ_sound
#assert_axioms adm_sound
#assert_axioms admA_sound

/-! The fuel-free twins. `denoteω_eq` is the transport every ω-result travels along, so an
axiom acquired here would reach all of them at once. -/

#assert_axioms denoteω_eq
#assert_axioms carrier_denoteω
#assert_axioms typed_μSynω

/-! §3's `Uν` for `opaque`, and §1's numeral domain. `opaq_T_identity` is the row
`docs/codec-formalization.md` calls closed for `opaque`; its proof sits behind seven
`omega` calls in `HeldSet.lean`, and `omega` is a known `Classical.choice` route — which
makes it the single constant in this file with the most to lose from going unguarded. -/

#assert_axioms opaq_T_identity
#assert_axioms decimal_writes_wf
#assert_axioms decimal_reads_wf

/-! §7's continuity results — why fuel is not removable by a fixpoint. -/

#assert_axioms altCodec_not_monotone
#assert_axioms denote_not_fuel_monotone

end Calculus
