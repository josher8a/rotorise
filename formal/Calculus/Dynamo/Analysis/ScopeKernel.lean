import Calculus.Dynamo.Analysis.ScopeConfluence

/-!
# The kernel of a read, over closed codecs

`ker p` (`Codec.Ker`) relates two attributes that read to one value. A lawful codec is a
canonical partial bijection, so `ker p` is equality on `dom(p)` (`Lawful.ker_eq`), and a store
normalisation `η` inside `ker p` fixes every attribute the codec writes
(`Lawful.survivesStore_fix`).

A held-free closed codec has an injective read with no premise on its laws: `Closed.confluence_R`
puts the read of the meaning inside the read of `opaque`, and the read of `opaque` is the identity,
which is injective (`Closed.ker_eq_of_HF`).
-/

namespace Calculus

/-- **`ker p` is equality at a held-free closed codec.** Two attributes that the meaning reads to
    one value are equal, by `Closed.confluence_R` and the identity read of `opaque`. -/
theorem Closed.ker_eq_of_HF {α : Table} {t : Closed} (h : t.HF) {a a' : Attr} {v : Value}
    (hp : (t.meaning α).p a = some v) (hk : (t.meaning α).Ker a' a) : a' = a := by
  have h1 := (Closed.opaq_f α .dual a).symm.trans (Closed.confluence_R h hp)
  have h2 := (Closed.opaq_f α .dual a').symm.trans (Closed.confluence_R h (Eq.trans hk hp))
  exact Option.some.inj (h2.trans h1.symm)

/-- **`ker p` is equality at a lawful codec.** Both attributes are the write of the value. -/
theorem Lawful.ker_eq {c : Codec} (hl : Lawful c) {a a' : Attr} {v : Value}
    (hp : c.p a = some v) (hk : c.Ker a' a) : a' = a := by
  have h1 := hl.canon hp
  rw [hl.canon (Eq.trans hk hp)] at h1
  exact Option.some.inj h1

/-- **A lawful codec survives the store only where `η` fixes each canonical attribute.**
    `SurvivesStore` puts `η` inside `ker p`, and `ker p` is equality. -/
theorem Lawful.survivesStore_fix {c : Codec} (hl : Lawful c) {η : Attr → Attr}
    (hs : SurvivesStore c η) {a : Attr} (hc : Can c a) : η a = a := by
  obtain ⟨v, he⟩ := hc
  exact hl.ker_eq (hl.retract he) (hs a ⟨v, he⟩)

end Calculus
