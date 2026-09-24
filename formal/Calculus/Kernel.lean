import Calculus.Confluence

/-!
# The kernel of a read

`ker p` (`Codec.Ker`) relates two attributes that read to one value. A lawful codec is a
canonical partial bijection, so `ker p` is equality on `dom(p)` (`Lawful.ker_eq`), and a store
normalisation `η` inside `ker p` fixes every attribute the codec writes
(`Lawful.survivesStore_fix`).

A held-free term has an injective read with no premise on its laws: `confluence_R` puts the read
of the term inside the read of `opaque`, and `Ω_canon` makes the read of `opaque` injective
(`ker_eq_of_HF`).
-/

namespace Calculus

/-- **`ker p` is equality at a held-free term.** Two attributes that the term reads to one
    value are equal, by `confluence_R` and `Ω_canon`. -/
theorem ker_eq_of_HF {t : Term} (h : HF t) {a a' : Attr} {v : Value}
    (hp : (denote t).p a = some v) (hk : (denote t).Ker a' a) : a' = a := by
  have hp' : (denote t).p a' = some v := Eq.trans hk hp
  have h1 := Ω_canon (confluence_R h hp)
  have h2 := Ω_canon (confluence_R h hp')
  exact Option.some.inj (h2.symm.trans h1)

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
