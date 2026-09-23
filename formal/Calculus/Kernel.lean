import Calculus.Confluence

/-!
# The kernel of a read

`ker p` (`Codec.Ker`) relates two attributes that read to one value. A held-free term has
`ker p` equality: `confluence_R` puts the read of the term inside the read of `opaque`, and
`Ω_canon` makes the read of `opaque` injective. So two attributes that read to one value are
one attribute. A set is held-free, so the fact covers the payloads of a set.

Two facts follow for a lawful held-free term. The term reads only `Can(c)`, so `e ∘ p = id`
on `dom(p)`. A store normalisation `η` inside `ker p` fixes every canonical attribute.

`held` is outside confluence (`held_violates_R`), and the fact does not reach through a
`held` in general. Under the iso premise `IsoCancels`, `g` is injective on the read of the
subterm, so a `held` keeps the kernel of its subterm.
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

/-- **A lawful held-free term reads only `Can(c)`, so `e ∘ p = id` on `dom(p)`.** `canon`
    re-encodes the value that the term reads, and `confluence_W` with `Ω_canon` gives back
    the attribute that the term read. -/
theorem e_p_of_HF {t : Term} (h : HF t) (hl : Lawful (denote t)) {a : Attr} {v : Value}
    (hp : (denote t).p a = some v) : (denote t).e v = some a := by
  obtain ⟨a', he⟩ := Option.isSome_iff_exists.mp (hl.canon hp)
  have h1 := Ω_canon (confluence_R h hp)
  have h2 := confluence_W h he
  rw [he]; exact congrArg some (Option.some.inj (h2.symm.trans h1))

/-- **A lawful held-free term survives the store only where `η` fixes each canonical
    attribute.** `SurvivesStore` puts `η` inside `ker p`, and `ker p` is equality. -/
theorem survivesStore_fix_of_HF {t : Term} (h : HF t) (hl : Lawful (denote t))
    {η : Attr → Attr} (hs : SurvivesStore (denote t) η) {a : Attr} (hc : Can (denote t) a) :
    η a = a := by
  obtain ⟨v, he⟩ := hc
  exact ker_eq_of_HF h (hl.retract he) (hs a ⟨v, he⟩)

/-- **`held` keeps the kernel of its subterm.** `IsoCancels` makes `g` injective on the read
    of a lawful subterm, so two attributes that the `held` reads to one value read to one
    value under the subterm. -/
theorem ker_through {c : Codec} (hl : Lawful c) {f g : Value → Value} (hi : IsoCancels c f g)
    {a a' : Attr} {v : Value} (hp : (c.through f g).p a = some v)
    (hk : (c.through f g).Ker a' a) : c.Ker a' a := by
  show c.p a' = c.p a
  have hp' : (c.through f g).p a' = some v := Eq.trans hk hp
  simp only [Codec.through, Option.map_eq_some_iff] at hp hp'
  obtain ⟨t, ht, rfl⟩ := hp
  obtain ⟨t', ht', hg⟩ := hp'
  have e1 := hi.2 t (hl.canon ht)
  have e2 := hi.2 t' (hl.canon ht')
  rw [ht, ht', ← e1, ← e2, hg]

end Calculus
