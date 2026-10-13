import Calculus.Dynamo.Analysis.Confluence
import Calculus.Dynamo.Analysis.ScopeKernel

variable {α : Calculus.Table}

/-!
# The kernel of a read

`ker p` (`Codec.Ker`) relates two attributes that read to one value. A lawful codec is a
canonical partial bijection, so `ker p` is equality on `dom(p)` (`Lawful.ker_eq`), and a store
normalisation `η` inside `ker p` fixes every attribute the codec writes
(`Lawful.survivesStore_fix`).

A held-free term has an injective read with no premise on its laws: `confluence_R` puts the read
of the term inside the read of `opaque`, and the read of `opaque` is the identity, which is injective
(`ker_eq_of_HF`).
-/

namespace Calculus

/-- **`ker p` is equality at a held-free term.** Two attributes that the term reads to one
    value are equal, by `confluence_R` and the identity read of `opaque`. -/
theorem ker_eq_of_HF {t : Term} (h : HF t) {a a' : Attr} {v : Value}
    (hp : (denote α t).p a = some v) (hk : (denote α t).Ker a' a) : a' = a := by
  have hp' : (denote α t).p a' = some v := Eq.trans hk hp
  have h1 := Alg.canon_idCodec _ _ (confluence_R h hp)
  have h2 := Alg.canon_idCodec _ _ (confluence_R h hp')
  exact Option.some.inj (h2.symm.trans h1)

end Calculus
