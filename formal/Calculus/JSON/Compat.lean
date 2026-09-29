import Calculus.JSON.Disjoint
import Calculus.Lang.Compat

/-!
# Compatibility at JSON

The decision `Alg.Term.compat` and its soundness hold at every signature. JSON supplies an oracle
that knows no orthogonality beyond the structural test, so every answer of the decision at JSON
comes from its structural rows. JSON has no `held`, because it names no generator.
-/

namespace Calculus.JSON

variable {α : Alg.Table jsonSyn} {β : Alg.Table jsonSyn.op}

/-- **The JSON oracle**: no closed-context orthogonality. -/
def jsonOracle : Alg.CompatOracle jsonSyn :=
  ⟨fun _ _ => false, fun _ _ => false⟩

/-- The JSON oracle is sound, because it certifies nothing. -/
theorem jsonOracle_sound : Alg.OracleSound jsonOracle where
  e _ _ h := nomatch h
  p _ _ h := nomatch h

/-- **JSON has no `held`**: the universe names no generator at either side, so a `held` has no
    first letter. -/
theorem no_held (s : Bool) (k₀ : jsonSig.G s × Bool) : False :=
  k₀.1.elim

end Calculus.JSON
