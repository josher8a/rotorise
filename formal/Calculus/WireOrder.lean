/-!
# Wire-set order

§1's `SS`, `NS` and `BS` are *sets* — `℘⁺fin` — and the model represents them as lists.
`Attr` should not: its wire-set members carry concrete element types, so `Finset String`
compiles there and is the right type. `Value.set` cannot follow, because a `Finset Value`
nested in `Value`'s own declaration is rejected by the kernel — quotients are not polynomial
functors — so that side keeps a list under a well-formedness gate, as `Numeral.WF` gates `N`.

Either way a canonical representative is needed: reading a set back into a `List Value` is a
sort, and a sort needs an order. There are
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

section Canon
variable {α : Type}

/-- The order on a payload type, through its key into `List Nat`. -/
def leK (key : α → List Nat) (x y : α) : Bool := lexLe (key x) (key y)

/-- Total… -/
theorem leK_total (key : α → List Nat) (x y : α) :
    leK key x y = true ∨ leK key y x = true := lexLe_total _ _

/-- …transitive… -/
theorem leK_trans {key : α → List Nat} {x y z : α}
    (h1 : leK key x y = true) (h2 : leK key y z = true) : leK key x z = true :=
  lexLe_trans h1 h2

/-- …and antisymmetric, given an injective key. -/
theorem leK_antisymm {key : α → List Nat} (kinj : ∀ a b : α, key a = key b → a = b)
    {x y : α} (h1 : leK key x y = true) (h2 : leK key y x = true) : x = y :=
  kinj _ _ (lexLe_antisymm h1 h2)

section
variable [DecidableEq α]

/-- Insert into a canonical list, dropping a repeat. -/
def insCanon (key : α → List Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    if x = y then y :: ys
    else if leK key x y then x :: y :: ys
    else y :: insCanon key x ys

/-- **The canonical representative of a finite set**: strictly ascending, duplicate-free.
    This is what `Value.set`'s list must be, and what reading a wire set produces. -/
def canon (key : α → List Nat) : List α → List α
  | [] => []
  | x :: xs => insCanon key x (canon key xs)

/-- `x` is strictly below everything in the list. -/
def ltAll (key : α → List Nat) (x : α) : List α → Bool
  | [] => true
  | y :: ys => (leK key x y && !(decide (x = y))) && ltAll key x ys

/-- Strictly ascending — sortedness and duplicate-freeness in one test. -/
def sortedK (key : α → List Nat) : List α → Bool
  | [] => true
  | x :: xs => ltAll key x xs && sortedK key xs

/-- Inserting adds exactly the inserted element. -/
theorem mem_insCanon (key : α → List Nat) (x z : α) :
    ∀ l : List α, z ∈ insCanon key x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insCanon]
  | y :: ys => by
      simp only [insCanon]
      by_cases hxy : x = y
      · subst hxy; simp
      · by_cases hle : leK key x y
        · simp [hxy, hle]
        · simp [hxy, hle, mem_insCanon key x z ys, or_left_comm]

/-- …so canonicalising preserves membership, which is the only thing a set has. -/
theorem mem_canon (key : α → List Nat) (z : α) :
    ∀ l : List α, z ∈ canon key l ↔ z ∈ l
  | [] => by simp [canon]
  | x :: xs => by
      simp only [canon, mem_insCanon, mem_canon key z xs, List.mem_cons]

/-- `ltAll` in the form the proofs want. -/
theorem ltAll_iff (key : α → List Nat) (w : α) :
    ∀ l : List α, ltAll key w l = true ↔ ∀ z ∈ l, leK key w z = true ∧ w ≠ z
  | [] => by simp [ltAll]
  | y :: ys => by
      simp only [ltAll, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
                 ltAll_iff key w ys, List.mem_cons]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩ z (rfl | hz)
        · exact ⟨h1, h2⟩
        · exact h3 z hz
      · intro h
        exact ⟨⟨(h y (Or.inl rfl)).1, (h y (Or.inl rfl)).2⟩,
               fun z hz => h z (Or.inr hz)⟩

/-- Insertion preserves the invariant. -/
theorem sortedK_insCanon (key : α → List Nat) (kinj : ∀ a b : α, key a = key b → a = b)
    (x : α) : ∀ l : List α, sortedK key l = true → sortedK key (insCanon key x l) = true
  | [], _ => by simp [insCanon, sortedK, ltAll]
  | y :: ys, h => by
      simp only [sortedK, Bool.and_eq_true] at h
      obtain ⟨hy, hys⟩ := h
      simp only [insCanon]
      by_cases hxy : x = y
      · subst hxy; simp [sortedK, hy, hys]
      · by_cases hle : leK key x y
        · simp only [hxy, if_false, hle, if_true, sortedK, Bool.and_eq_true]
          refine ⟨?_, hy, hys⟩
          rw [ltAll_iff]
          intro z hzm
          rcases List.mem_cons.mp hzm with rfl | hz
          · exact ⟨hle, hxy⟩
          · obtain ⟨hyz, hyz'⟩ := (ltAll_iff key y ys).mp hy z hz
            refine ⟨leK_trans hle hyz, ?_⟩
            intro hxz
            rw [← hxz] at hyz
            exact absurd (leK_antisymm kinj hle hyz) hxy
        · have hyx : leK key y x = true := by
            rcases leK_total key x y with h' | h'
            · exact absurd h' (by simp [hle])
            · exact h'
          simp only [hxy, if_false, hle, Bool.false_eq_true, if_false, sortedK, Bool.and_eq_true]
          refine ⟨?_, sortedK_insCanon key kinj x ys hys⟩
          rw [ltAll_iff]
          intro z hz
          rcases (mem_insCanon key x z ys).mp hz with rfl | hz'
          · exact ⟨hyx, fun hc => hxy hc.symm⟩
          · exact (ltAll_iff key y ys).mp hy z hz'

/-- …so `canon` always produces it. -/
theorem sortedK_canon (key : α → List Nat) (kinj : ∀ a b : α, key a = key b → a = b) :
    ∀ l : List α, sortedK key (canon key l) = true
  | [] => rfl
  | x :: xs => sortedK_insCanon key kinj x _ (sortedK_canon key kinj xs)


/-- **Uniqueness**: a strictly ascending list is determined by its membership. -/
theorem sortedK_uniq (key : α → List Nat) (kinj : ∀ a b : α, key a = key b → a = b) :
    ∀ {xs ys : List α}, sortedK key xs = true → sortedK key ys = true →
      (∀ z, z ∈ xs ↔ z ∈ ys) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => absurd ((h y).mpr (by simp)) (by simp)
  | x :: xs, [], _, _, h => absurd ((h x).mp (by simp)) (by simp)
  | x :: xs, y :: ys, hx, hy, h => by
      simp only [sortedK, Bool.and_eq_true] at hx hy
      obtain ⟨hxa, hxs⟩ := hx
      obtain ⟨hya, hys⟩ := hy
      have hxy : x = y := by
        rcases List.mem_cons.mp ((h x).mp (by simp)) with heq | hmem
        · exact heq
        · rcases List.mem_cons.mp ((h y).mpr (by simp)) with heq | hmem'
          · exact heq.symm
          · obtain ⟨hxyle, hxyne⟩ := (ltAll_iff key x xs).mp hxa y hmem'
            obtain ⟨hyxle, -⟩ := (ltAll_iff key y ys).mp hya x hmem
            exact absurd (leK_antisymm kinj hxyle hyxle) hxyne
      subst hxy
      have hrest : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((h z).mp (List.mem_cons_of_mem _ hz)) with rfl | hz'
          · exact absurd rfl ((ltAll_iff key z xs).mp hxa z hz).2
          · exact hz'
        · intro hz
          rcases List.mem_cons.mp ((h z).mpr (List.mem_cons_of_mem _ hz)) with rfl | hz'
          · exact absurd rfl ((ltAll_iff key z ys).mp hya z hz).2
          · exact hz'
      rw [sortedK_uniq key kinj hxs hys hrest]

/-- **Therefore `canon` sees only the set.** Two lists with the same elements — in any
    order, with any repeats — canonicalise to the same list. This is what lets a wire set be
    read back deterministically without `Finset.toList`, which goes through `Quot.out`. -/
theorem canon_congr (key : α → List Nat) (kinj : ∀ a b : α, key a = key b → a = b)
    {l₁ l₂ : List α} (h : ∀ z, z ∈ l₁ ↔ z ∈ l₂) : canon key l₁ = canon key l₂ :=
  sortedK_uniq key kinj (sortedK_canon key kinj l₁) (sortedK_canon key kinj l₂)
    (fun z => by rw [mem_canon, mem_canon]; exact h z)

end
end Canon

end Wire
end Calculus
