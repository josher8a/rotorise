/-!
# Wire-set order

§1's `SS`, `NS` and `BS` are *sets* — `℘⁺fin` — and the model represents them as lists, so
repairing that needs a canonical representative per set, which needs an order. There are
only three payload types and all three are lists of bounded naturals: `String` and
`Numeral` through their characters, `Bytes` through its octets. So the order lives on
`List Nat`, where `Nat`'s own laws are **axiom-free** — no order on `Value`, none on the
axiomatized `Double`, and nothing from mathlib.

That last point is not incidental. `LinearOrder String` and `List.sorted_insertionSort` both
depend on `Classical.choice`, so the obvious route is closed by the axiom base
`docs/codec-formalization.md` §3 advertises. `#assert_axioms_all` is what caught it.
-/

namespace Calculus
namespace Wire

/-- Lexicographic order on keys. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLe as bs

theorem lexLe_refl : ∀ xs, lexLe xs xs = true
  | [] => rfl
  | a :: as => by simp [lexLe, lexLe_refl as]

theorem lexLe_total : ∀ xs ys, lexLe xs ys = true ∨ lexLe ys xs = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: as, b :: bs => by
      simp only [lexLe]
      rcases Nat.lt_trichotomy a b with h | h | h
      · simp [h]
      · subst h; simp only [Nat.lt_irrefl, if_false]; exact lexLe_total as bs
      · simp [h, Nat.not_lt.mpr (Nat.le_of_lt h)]

theorem lexLe_antisymm : ∀ {xs ys}, lexLe xs ys = true → lexLe ys xs = true → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [lexLe] at h
  | _ :: _, [], h, _ => by simp [lexLe] at h
  | a :: as, b :: bs, h1, h2 => by
      simp only [lexLe] at h1 h2
      rcases Nat.lt_trichotomy a b with h | h | h
      · simp [h, Nat.not_lt.mpr (Nat.le_of_lt h)] at h2
      · subst h
        simp only [Nat.lt_irrefl, if_false] at h1 h2
        simp [lexLe_antisymm h1 h2]
      · simp [h, Nat.not_lt.mpr (Nat.le_of_lt h)] at h1

theorem lexLe_trans : ∀ {xs ys zs}, lexLe xs ys = true → lexLe ys zs = true →
    lexLe xs zs = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLe] at h
  | a :: as, b :: bs, c :: cs, h1, h2 => by
      simp only [lexLe] at h1 h2 ⊢
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · rcases Nat.lt_trichotomy b c with hbc | hbc | hbc
        · simp [Nat.lt_trans hab hbc]
        · subst hbc; simp [hab]
        · simp [hbc, Nat.not_lt.mpr (Nat.le_of_lt hbc)] at h2
      · subst hab
        simp only [Nat.lt_irrefl, if_false] at h1
        rcases Nat.lt_trichotomy a c with hac | hac | hac
        · simp [hac]
        · subst hac
          simp only [Nat.lt_irrefl, if_false] at h2 ⊢
          exact lexLe_trans h1 h2
        · simp [hac, Nat.not_lt.mpr (Nat.le_of_lt hac)] at h2
      · simp [hab, Nat.not_lt.mpr (Nat.le_of_lt hab)] at h1

end Wire
end Calculus
