import Calculus.JSON.Basic

/-!
# JSON has no `held`

JSON names no generator, so no codec of JSON holds a `held`.
-/

namespace Calculus.JSON

/-- **JSON has no `held`**: the universe names no generator at either side, so a `held` has no
    first letter. -/
theorem no_held (s : Bool) (k₀ : jsonSig.G s × Bool) : False :=
  k₀.1.elim

end Calculus.JSON
