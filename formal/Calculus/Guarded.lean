import Calculus.Denote
import Calculus.AlgGuarded

/-!
# The guard makes the body of a binder contractive

`Term.guarded` is a check on syntax, and `Contractive` is the premise that `Recursion.lean` asks
of a body. `contractive_body` connects the two: at a guarded `mu b`, the body
`fun c => denote b (c :: ρ)` reads `c` only one layer down. The proof is `Alg.contractive_body`,
for every universe, at the DynamoDB signature.
-/

namespace Calculus

/-- **The guard gives a contractive body.** At a guarded `mu b`, the body reads its variable one
    layer down, and every other variable is the same on both sides. -/
theorem contractive_body {b : Term} (hg : (Term.mu b).guarded = true) (ρ : List Codec) :
    Contractive fun c => denote b (c :: ρ) := by
  rw [show (fun c => denote b (c :: ρ)) = fun c => Alg.denote b (c :: ρ) from
    funext fun c => denote_eq_alg b _]
  exact Alg.contractive_body hg ρ

end Calculus
