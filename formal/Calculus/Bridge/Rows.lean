import Calculus.Dynamo.Analysis.Compat
import Calculus.Dynamo.Lang.Store

/-!
# Separation verdicts, from a checked row list

A generated vector file states many separation verdicts of one form as a list of rows. The kernel
decides one check over all the rows of the list, and each lemma below lifts that one equation to
the verdict of each row. The verdict of a row is the full separation verdict of one pair.

A row holds the two terms that the guard reads and the two terms that compatibility reads. The
guard reads the rooted terms, and compatibility reads the open terms.
-/

namespace Calculus

/-- **An accepted pair, at each row.** The guard accepts both options, and the decision
    discharges the union's obligation at every caller table. -/
theorem accepted_of_rows {rows : List (Term × Term × Term × Term)}
    (h : rows.all (fun p => Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1 &&
      Alg.compatPair dynOracle p.2.2.1 p.2.2.2) = true) (κ : Callers) : ∀ p ∈ rows,
    (Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1) = true ∧
    ((∀ t ∈ [p.2.2.1, p.2.2.2], Lawful (denote (libTable κ) t)) →
      PairwiseCompat (libTable κ) [p.2.2.1, p.2.2.2]) := by
  intro p hp
  have h := List.all_eq_true.mp h p hp
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, fun hl => pairwiseCompat_of_compatPair h.2 hl⟩

/-- **A pair refused at compatibility, at each row.** The guard accepts both options, and the
    decision refuses the pair. -/
theorem refused_of_rows {rows : List (Term × Term × Term × Term)}
    (h : rows.all (fun p => Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1 &&
      !Alg.compatPair dynOracle p.2.2.1 p.2.2.2) = true) : ∀ p ∈ rows,
    (Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1) = true ∧
    Alg.compatPair dynOracle p.2.2.1 p.2.2.2 = false := by
  intro p hp
  have h := List.all_eq_true.mp h p hp
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

/-- **A pair refused at the guard, at each row.** The guard refuses an option. -/
theorem guardRefused_of_rows {rows : List (Term × Term)}
    (h : rows.all (fun p => !(Alg.Term.guarded p.1 && Alg.Term.guarded p.2)) = true) :
    ∀ p ∈ rows, (Alg.Term.guarded p.1 && Alg.Term.guarded p.2) = false := by
  intro p hp
  have h := List.all_eq_true.mp h p hp
  rwa [Bool.not_eq_true'] at h

end Calculus
