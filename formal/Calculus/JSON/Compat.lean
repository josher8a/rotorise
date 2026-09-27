import Calculus.JSON.Disjoint
import Calculus.Lang.Compat

/-!
# Compatibility at JSON

The decision `Alg.Term.compat` and its soundness hold at every signature. JSON supplies an oracle
that knows no orthogonality beyond the structural test, and no adapter pair to be another, so
every answer of the decision at JSON comes from its structural rows.
-/

namespace Calculus.JSON

/-- **The JSON oracle**: no closed-context orthogonality, and no adapter pair known to be
    another. -/
def jsonOracle : Alg.CompatOracle jsonSyn :=
  ⟨fun _ _ => false, fun _ _ => false, fun _ _ _ _ => false⟩

/-- The JSON oracle is sound, because it certifies nothing. -/
theorem jsonOracle_sound : Alg.OracleSound jsonOracle where
  e _ _ h := nomatch h
  p _ _ h := nomatch h
  same _ _ _ _ h := nomatch h

/-- A string held as itself, beside a number: the caller side of the `held` is disjoint from the
    number on the write half, and the stored side is disjoint on the read half. -/
example : Alg.compatPair jsonOracle (.held (.prim .str) (.prim .str) id id : Alg.Term jsonSyn)
    (.prim .num) = true := by decide

/-- …and beside a string, the decision refuses: no row bounds the `held`. -/
example : Alg.compatPair jsonOracle (.held (.prim .str) (.prim .str) id id : Alg.Term jsonSyn)
    (.prim .str) = false := by decide

/-- **The decision discharges a JSON union's obligation**: the `held` string beside the number. -/
theorem pairwiseCompat_held_num
    (hl : ∀ t ∈ [(.held (.prim .str) (.prim .str) id id : Alg.Term jsonSyn), .prim .num],
      Alg.Lawful Json.member (Alg.denote t)) :
    Alg.PairwiseCompat [(.held (.prim .str) (.prim .str) id id : Alg.Term jsonSyn), .prim .num] :=
  Alg.pairwiseCompat_of_compatPair jsonOracle_sound (by decide) hl

end Calculus.JSON
