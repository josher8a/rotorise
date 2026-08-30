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
#assert_axioms uAtCan_dunion
#assert_axioms uAtCan_opaque
#assert_axioms not_uAtCan_literal_string
#assert_axioms not_uAtCan_array_literals
#assert_axioms not_uAtCan_literal_held

/-! §5's `adm` cannot pass through `legacy` on the read side — the specification defect
that had no witness until it had this one. -/

#assert_axioms not_admA_legacy

/-! §6's `≡` is not transitive — the one refutation that is about the equational theory
rather than about a row of it. -/

#assert_axioms not_equiv_trans

/-! `ident` has no denotational content to pin — what it has is its relation to `adm`,
which is what §5 uses it for, and `SepV`'s right to drop §5's two `ident` conjuncts
rests on it. -/

#assert_axioms ident_of_adm
#assert_axioms admDisj_ident
#assert_axioms sepV_string_dunion_nil

/-! §2's ideal: `e` and `p` are mutually inverse between `dom(e)` and `Can(c)`. `retract`
is one half and this is the other, so the bijection is a theorem rather than a reading. -/

#assert_axioms Lawful.can_roundTrip
#assert_axioms approx_extendRead
#assert_axioms approx_restrict
#assert_axioms Lawful.e_injective

/-! §5's two outright dischargers, as one theorem: label each side by a projection of the
input, keep the options' label sets disjoint. `uniqueAdmission_of_kinds` and
`uniqueAdmission_byTag` are its two instances. -/

#assert_axioms uniqueAdmission_of_disjoint
#assert_axioms filter_eq_singleton_of_disjoint
/-! §3's `held`/`refine` split, checked rather than asserted: both are one partial-iso
combinator, and the pair agrees on the nose. -/

#assert_axioms through_e_adapt
#assert_axioms through_p_adapt
#assert_axioms restrict_e_adapt
#assert_axioms restrict_p_adapt

/-! §1's two number gates, as instances of the same combinator. `restrict` gates both
halves by construction, which is what §3 argues an ad-hoc gate forgets. -/

#assert_axioms lawfulCore_rawNumberCodec
#assert_axioms literalSCodec_e_restrict
#assert_axioms literalSCodec_p_restrict
#assert_axioms admList_of_mem
#assert_axioms admAList_of_mem
#assert_axioms identList_of_admList
#assert_axioms uAtCan_of_refine_disjoint_of_typed
#assert_axioms uAtCan_refine_container
#assert_axioms uAtCan_boolLiterals
#assert_axioms admA_literalS_sees
#assert_axioms admA_literalN_blind
#assert_axioms literalNCodec_e_restrict
#assert_axioms literalNCodec_p_restrict
#assert_axioms uniqueAdmission_of_sharedBase
#assert_axioms uAtCan_of_literalN_disjoint
#assert_axioms numberCodec_e_restrict
#assert_axioms numberCodec_p_restrict
#assert_axioms decimalCodec_e_restrict
#assert_axioms decimalCodec_p_restrict

#assert_axioms sepV_refine_disjoint
#assert_axioms uAtCan_of_refine_disjoint
#assert_axioms Lawful.restrict
#assert_axioms admitV_kind
#assert_axioms admitV_adm
#assert_axioms admitA_member
#assert_axioms admitA_admA
#assert_axioms SVof_disjoint
#assert_axioms SAof_disjoint
#assert_axioms uAtCan_of_separated
#assert_axioms uniqueAdmission_of_labels
#assert_axioms uniqueAdmission_of_kinds
#assert_axioms uniqueAdmission_byTag
#assert_axioms filter_eq_singleton_of_labels
#assert_axioms filter_eq_singleton_of_keys
#assert_axioms byTag_admitA
#assert_axioms byTag_admitV

/-! §3 `(nullable)`'s guard. `nullHonest_of_not_ownsNull` is the premise that stopped
being one — it derives both honesty halves from lawfulness — and `withNull_ownsNull` is
why §6's idempotence is a construction rather than an equation. -/

#assert_axioms nullHonest_of_not_ownsNull
#assert_axioms lawful_withNull
#assert_axioms withNull_ownsNull
#assert_axioms withNull_idem_e
#assert_axioms withNull_idem_p

/-! `(union)`'s residue, and the bridge every discharger now crosses. The two witnesses
are one union seen by both residues: `UAtCan` refutes it at an input it never writes,
`UAtAct` holds of it. -/

#assert_axioms uAtAct_of_uAtCan
#assert_axioms uAtAct_array_literals
#assert_axioms literalS_p_none

/-! `through_p` is the fact the `held` row rests on — `g` post-processes a read and is
total, so `dom(p)` is the subterm's exactly. It is cited as a result now, so it is guarded
like one. -/

#assert_axioms through_p

/-! `admA`'s `held` row, both directions. §5 gave `held` one `⊤` row on both sides; its
opacity is one-sided — `f` gates the write, `g` only post-processes the read — so the
readable side passes through, and these two are the pair it separates and the pair it
still does not. -/

#assert_axioms sepA_literal_heldLiteral
#assert_axioms not_sepA_literal_heldLiteral

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
#assert_axioms altCodec_T
#assert_axioms not_TIsDomE_unionLiteralString
#assert_axioms decimal_writes_stored
#assert_axioms decimal_reads_stored

/-! §3's `(number)` gate and the two places the bound is forced outward. `opaq_T_identity`
above is guarded for `Uν` *after* `HOpaque.num` gained its premise, which is the half of this
change that reaches the depth machinery. The `literalN` rows are the half that does not:
they are `(literal-N)`'s `ℓ ⊆ D`, added to §3 once the shipped `literal(NaN)` settled the
question the conditional refutations leave open. -/

#assert_axioms lawful_numberCodec
#assert_axioms carrier_numberCodec
#assert_axioms lawful_literalNCodec
#assert_axioms survivesStore_numberCodec
#assert_axioms literalN_sub_number
#assert_axioms not_literalN_sub_number
#assert_axioms literalN_writes_off_numerals
#assert_axioms typed_literalN_D
#assert_axioms typed_literalN_sub_number
#assert_axioms not_typed_literalN_nonD

/-! §2's kernel and §1's store. `retract_through_store` is **(R)** with DynamoDB in the
middle — the law production actually runs — and the two `decimal` rows are what makes
`Numeral.Stored` the right held set rather than a cautious one: `η ⊆ ker p` holds after the
narrowing and fails before it. -/

/-! §2's corollary that a pair has two halves: a member a codec cannot write is one it
cannot read. The `opaque`/`NS` defect is its counterexample, and (MP) is the only law that
sees it — which is why it needs stating rather than following from the rest. -/

#assert_axioms Lawful.no_read_without_write
#assert_axioms Lawful.write_of_read

#assert_axioms Codec.ker_equivalence
#assert_axioms Lawful.stable
#assert_axioms Lawful.retract_through_store
#assert_axioms can_iff_image
#assert_axioms ker_decimalCodec
#assert_axioms survivesStore_decimalCodec
#assert_axioms not_survivesStore_decimalWF

/-! §6's Hold rows at term level. The ten `denoteω_*` bridges are `rfl` and carry no axiom
risk worth a line each; what is guarded is the twins, which go through `Codec.Equiv` and are
what a reviewer checks §6's table against. -/

#assert_axioms equiv_denoteω_held_id
#assert_axioms equiv_denoteω_held_comp
#assert_axioms equiv_denoteω_refine_meet
#assert_axioms equiv_denoteω_refine_full
#assert_axioms equiv_denoteω_legacy_self
#assert_axioms equiv_denoteω_nullable_idem
#assert_axioms denoteω_legacy_eq_on_can

/-! §7's continuity results — why fuel is not removable by a fixpoint. -/

#assert_axioms altCodec_not_monotone
#assert_axioms denote_not_fuel_monotone

end Calculus
