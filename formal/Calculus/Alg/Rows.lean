import Mathlib.Data.List.Forall2

/-!
# The rows, over any carrier

A term hands up a row: a predicate on the carrier of one side. The value side and the
attribute side combine the rows of the subterms with one algebra. The carrier is the only
difference: `Value` on the write side, and `Attr` on the read side. So this module states each
combinator and each lemma one time, over a type parameter `α`, and each side instantiates it.

The module imports no `Calculus` module. A proof here therefore cannot use a fact of a carrier,
and the axiom base of each declaration is the base of the list library alone.
-/

namespace Calculus

variable {α : Type}

/-- A row that admits at least what another row admits. -/
def RowLe (P Q : α → Bool) : Prop := ∀ x, P x = true → Q x = true

/-- `⋀` over a container's elements. -/
def allP (P : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => P x && allP P xs

/-- `⋁` over a union's options. -/
def anyP : List (α → Bool) → α → Bool
  | [], _ => false
  | P :: Ps, v => P v || anyP Ps v

/-- `align`'s row: the same length discipline — fixed head positionally, tail uniformly, a
    mismatch refused — asked of the rows rather than of the codecs. §5's `⊤` on any `.arr`
    ignored all three of those things. -/
def alignP : List (α → Bool) → Option (α → Bool) → List α → Bool
  | [], none, [] => true
  | [], none, _ :: _ => false
  | [], some _, [] => true
  | [], some P, v :: vs => P v && alignP [] (some P) vs
  | _ :: _, _, [] => false
  | P :: Ps, tail, v :: vs => P v && alignP Ps tail vs

/-- The suffix's row: position for position, and a length mismatch refused. -/
def zipP : List (α → Bool) → List α → Bool
  | [], [] => true
  | P :: Ps, v :: vs => P v && zipP Ps vs
  | _, _ => false

/-- `alignL`'s row: the suffix splits off the right end, and what is left is `alignP`'s
    prefix-and-spread. A row shorter than the suffix takes `0` off the end, and `zipP`
    refuses it on the length, so no guard is owed. -/
def alignPL (pre : List (α → Bool)) (sp : Option (α → Bool)) (suf : List (α → Bool))
    (vs : List α) : Bool :=
  alignP pre sp (vs.take (vs.length - suf.length))
    && zipP suf (vs.drop (vs.length - suf.length))

/-- A suffix row that holds pins the length. -/
theorem zipP_length : ∀ (Ps : List (α → Bool)) (vs : List α),
    zipP Ps vs = true → Ps.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [zipP] at h
  | _ :: _, [], h => by simp [zipP] at h
  | _ :: Ps, _ :: vs, h => by
      simp only [zipP, Bool.and_eq_true] at h
      simp [zipP_length Ps vs h.2]

/-- A row of the wrong length holds nothing. -/
theorem zipP_false_of_length_ne (Ps : List (α → Bool)) (ws : List α)
    (h : Ps.length ≠ ws.length) : zipP Ps ws = false := by
  cases hz : zipP Ps ws with
  | false => rfl
  | true => exact absurd (zipP_length Ps ws hz) h

/-- Two rows of matching heads split. -/
theorem zipP_append : ∀ (a₁ b₁ : List (α → Bool)) (a₂ b₂ : List α), a₁.length = a₂.length →
    zipP (a₁ ++ b₁) (a₂ ++ b₂) = (zipP a₁ a₂ && zipP b₁ b₂)
  | [], _, [], _, _ => by simp [zipP]
  | P :: Ps, b₁, v :: vs, b₂, h => by
      simp only [List.cons_append, zipP, zipP_append Ps b₁ vs b₂ (by simpa using h)]
      exact (Bool.and_assoc _ _ _).symm

/-- With no spread, `alignP` IS the positionwise row: both refuse a length mismatch. -/
theorem alignP_none_eq_zipP : ∀ (pre : List (α → Bool)) (ws : List α),
    alignP pre none ws = zipP pre ws
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: Ps, _ :: vs => by simp only [alignP, zipP, alignP_none_eq_zipP Ps vs]

/-- A spread pads the row out to the value's length. -/
theorem alignP_some_eq_zipP : ∀ (pre : List (α → Bool)) (c : α → Bool) (ws : List α),
    pre.length ≤ ws.length →
    alignP pre (some c) ws = zipP (pre ++ List.replicate (ws.length - pre.length) c) ws
  | [], _, [], _ => rfl
  | [], c, _ :: vs, _ => by
      have ih := alignP_some_eq_zipP [] c vs (Nat.zero_le _)
      simp only [List.length_nil, Nat.sub_zero, List.nil_append] at ih ⊢
      simp only [alignP, List.length_cons, List.replicate_succ, zipP, ih]
  | _ :: _, _, [], h => by simp at h
  | _ :: Ps, c, _ :: vs, h => by
      have ih := alignP_some_eq_zipP Ps c vs (by simpa using h)
      simp only [alignP, List.cons_append, zipP, List.length_cons,
        Nat.succ_sub_succ_eq_sub, ih]

/-- …and refuses a row shorter than its declared positions. -/
theorem alignP_short : ∀ (pre : List (α → Bool)) (sp : Option (α → Bool)) (ws : List α),
    ws.length < pre.length → alignP pre sp ws = false
  | [], _, _, h => by simp at h
  | _ :: _, sp, [], _ => by cases sp <;> rfl
  | _ :: Ps, sp, _ :: vs, h => by
      simp only [alignP, alignP_short Ps sp vs (by simpa using h), Bool.and_false]

/-- The spread row, split at the suffix. Stated over an explicit split so no rewrite has to
    reach inside a length. -/
theorem zipP_row_split (pre suf : List (α → Bool)) (c : α → Bool) (V B : List α)
    (hB : B.length = suf.length) (hA : pre.length ≤ V.length) :
    (zipP (pre ++ List.replicate (V.length - pre.length) c) V && zipP suf B)
      = zipP (pre ++ List.replicate ((V ++ B).length - pre.length - suf.length) c ++ suf)
          (V ++ B) := by
  have hcount : (V ++ B).length - pre.length - suf.length = V.length - pre.length := by
    simp only [List.length_append, hB]; omega
  rw [hcount, zipP_append _ _ _ _
      (by simp only [List.length_append, List.length_replicate]; omega)]

/-- The fixed positions and the spread of a list admit more when each row admits more. -/
theorem alignP_mono {Ps Qs : List (α → Bool)} {sp sq : Option (α → Bool)}
    (hPQ : List.Forall₂ RowLe Ps Qs) (hs : Option.Rel RowLe sp sq) :
    ∀ vs, alignP Ps sp vs = true → alignP Qs sq vs = true := by
  induction hPQ with
  | nil =>
    cases hs with
    | none => exact fun _ h => h
    | some hr =>
      intro vs h
      induction vs with
      | nil => rfl
      | cons v vs ih =>
        simp only [alignP, Bool.and_eq_true] at h ⊢
        exact ⟨hr _ h.1, ih h.2⟩
  | cons hr _ ih =>
    intro vs h
    cases vs with
    | nil => simp [alignP] at h
    | cons v vs =>
      simp only [alignP, Bool.and_eq_true] at h ⊢
      exact ⟨hr _ h.1, ih vs h.2⟩

/-- The suffix of a list admits more when each row admits more. -/
theorem zipP_mono {Ps Qs : List (α → Bool)} (hPQ : List.Forall₂ RowLe Ps Qs) :
    ∀ vs, zipP Ps vs = true → zipP Qs vs = true := by
  induction hPQ with
  | nil => exact fun _ h => h
  | cons hr _ ih =>
    intro vs h
    cases vs with
    | nil => simp [zipP] at h
    | cons v vs =>
      simp only [zipP, Bool.and_eq_true] at h ⊢
      exact ⟨hr _ h.1, ih vs h.2⟩

/-- A list admits more when each row admits more. -/
theorem alignPL_mono {Ps Qs Ss Ts : List (α → Bool)} {sp sq : Option (α → Bool)}
    (hPQ : List.Forall₂ RowLe Ps Qs) (hs : Option.Rel RowLe sp sq)
    (hST : List.Forall₂ RowLe Ss Ts) (vs : List α) (h : alignPL Ps sp Ss vs = true) :
    alignPL Qs sq Ts vs = true := by
  unfold alignPL at h ⊢
  rw [← hST.length_eq]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨alignP_mono hPQ hs _ h.1, zipP_mono hST _ h.2⟩

/-- A list with no prefix and no suffix admits a value when the spread admits each element. -/
theorem alignPL_spread (P : α → Bool) (vs : List α) :
    alignPL [] (some P) [] vs = decide (∀ x ∈ vs, P x = true) := by
  simp only [alignPL, List.length_nil, Nat.sub_zero, List.take_length, List.drop_length, zipP,
    Bool.and_true]
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [alignP, ih]

/-! ## The row of a `list` shape

`rowOfG` assigns a shape's positions to a length. The facts below hold at any element type, so a
term row and a row of partially applied tests share them. -/

namespace Alg

/-- **The row a `list` shape assigns to `n` positions**: the prefix, the spread as often as
    the middle needs, then the suffix. `none` is the length the shape refuses. One
    definition serves both operands, because the left operand's positions are partially
    applied tests and the right operand's are terms, and the shape does not care which. -/
def rowOfG {α : Type} (pre : List α) (sp : Option α) (suf : List α) (n : Nat) :
    Option (List α) :=
  match sp with
  | some c =>
      if n < pre.length + suf.length then none
      else some (pre ++ List.replicate (n - pre.length - suf.length) c ++ suf)
  | none => if n = pre.length + suf.length then some (pre ++ suf) else none

/-- **One side dominates the other**, in the prefix and in the suffix at once.

    A fact about lengths alone. With both shapes spreading, two shapes both admit a value of
    length `n` only when `n ≥ max (p₁+s₁) (p₂+s₂)`, and the row that places every declared
    position of both shapes has `max p₁ p₂ + max s₁ s₂` positions. The second is never
    smaller, and the two are EQUAL exactly when one side's prefix and suffix are both at least
    the other's (`dominates_max`). There every common length re-spreads that one row. -/
def dominates (p₁ s₁ p₂ s₂ : Nat) : Bool :=
  (decide (p₂ ≤ p₁) && decide (s₂ ≤ s₁)) || (decide (p₁ ≤ p₂) && decide (s₁ ≤ s₂))

/-- **`alignPL` is its row, applied position for position.** This is `align_eq_zip` one level
    down, and it is what lets a proof reason about two shapes by reasoning about their rows
    at one length: the admission of a `list` at a value of length `n` is the admission of the
    row `rowOfG` assigns to `n`, position by position. -/
theorem alignPL_eq_rowOfG {α : Type} (pre : List (α → Bool)) (sp : Option (α → Bool))
    (suf : List (α → Bool)) (ws : List α) :
    alignPL pre sp suf ws
      = match rowOfG pre sp suf ws.length with
        | none => false
        | some row => zipP row ws := by
  have htl : (ws.take (ws.length - suf.length)).length = ws.length - suf.length := by
    simp only [List.length_take]; omega
  unfold alignPL
  rcases Nat.lt_or_ge ws.length (pre.length + suf.length) with hlt | hge
  · have hrow : rowOfG pre sp suf ws.length = none := by
      cases sp with
      | none => simp only [rowOfG]; rw [if_neg (by omega)]
      | some c => simp only [rowOfG]; rw [if_pos (by omega)]
    rw [hrow]
    rcases Nat.lt_or_ge ws.length suf.length with hs | hs
    · rw [zipP_false_of_length_ne _ _ (by simp only [List.length_drop]; omega), Bool.and_false]
    · rw [alignP_short _ _ _ (by omega), Bool.false_and]
  · have hdl : (ws.drop (ws.length - suf.length)).length = suf.length := by
      simp only [List.length_drop]; omega
    have hAB : ws.take (ws.length - suf.length) ++ ws.drop (ws.length - suf.length) = ws :=
      List.take_append_drop _ _
    cases sp with
    | none =>
        rw [alignP_none_eq_zipP]
        simp only [rowOfG]
        rcases Nat.eq_or_lt_of_le hge with heq | hlt2
        · rw [if_pos heq.symm]
          show _ = zipP (pre ++ suf) ws
          have hz := (zipP_append pre suf (ws.take (ws.length - suf.length))
            (ws.drop (ws.length - suf.length)) (by omega)).symm
          rw [hAB] at hz
          exact hz
        · rw [if_neg (by omega)]
          show _ = false
          rw [zipP_false_of_length_ne _ _ (by omega), Bool.false_and]
    | some c =>
        rw [alignP_some_eq_zipP _ _ _ (by omega)]
        simp only [rowOfG]
        rw [if_neg (by omega)]
        show _ = zipP (pre ++ List.replicate (ws.length - pre.length - suf.length) c ++ suf) ws
        have hz := zipP_row_split pre suf c (ws.take (ws.length - suf.length))
          (ws.drop (ws.length - suf.length)) hdl (by omega)
        rw [hAB] at hz
        exact hz


/-- A row the shape accepts has exactly the length asked of it. -/
theorem rowOfG_length {α : Type} {pre : List α} {sp : Option α} {suf : List α} {n row}
    (h : rowOfG pre sp suf n = some row) : row.length = n := by
  cases sp with
  | none =>
      simp only [rowOfG] at h
      split at h
      · next he =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_append]
          omega
      · exact absurd h (by simp)
  | some c =>
      simp only [rowOfG] at h
      split at h
      · exact absurd h (by simp)
      · next he =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_append, List.length_replicate]
          omega

/-- The row of a shape with no spread, as an `if`: the shape has a row at its own arity and
    at no other length. -/
theorem rowOfG_none_eq {α : Type} (pre suf : List α) (n : Nat) :
    rowOfG pre none suf n
      = if n = pre.length + suf.length then some (pre ++ suf) else none := rfl

/-- …and of a spreading shape, which has a row at every length from its arity up. -/
theorem rowOfG_some_eq {α : Type} (pre : List α) (c : α) (suf : List α) (n : Nat) :
    rowOfG pre (some c) suf n
      = if n < pre.length + suf.length then none
        else some (pre ++ List.replicate (n - pre.length - suf.length) c ++ suf) := rfl

/-- Two rows over the same three parts, related position for position. -/
theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ n, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => by
      simp only [List.replicate_succ]
      exact .cons hab (forall₂_replicate hab n)

/-- …and two such pairs, appended: a row built in parts carries the relation in parts. -/
theorem forall₂_append {α β : Type} {R : α → β → Prop} {a₁ a₂ : List α} {b₁ b₂ : List β} :
    List.Forall₂ R a₁ b₁ → List.Forall₂ R a₂ b₂ →
      List.Forall₂ R (a₁ ++ a₂) (b₁ ++ b₂) := by
  intro h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | cons hh _ ih => exact .cons hh ih

/-- **A row of rows is the mapped row.** The value side, the read side and the derivation
    each hold their shape as terms and read it through one map, so every row equation is
    stated over terms once. -/
theorem rowOfG_map {α β : Type} (g : α → β) (pre : List α) (sp : Option α) (suf : List α)
    (n : Nat) :
    rowOfG (pre.map g) (sp.map g) (suf.map g) n
      = (rowOfG pre sp suf n).map (List.map g) := by
  cases sp with
  | none =>
      simp only [rowOfG, Option.map_none, List.length_map]
      split <;> simp [List.map_append]
  | some c =>
      simp only [rowOfG, Option.map_some, List.length_map]
      split <;> simp [List.map_append, List.map_replicate]

/-- **The row transfers a relation.** Two shapes whose prefixes, spreads and suffixes are
    related position for position assign related rows at every length. A proof reads its
    own relation off the two rows rather than off the shapes. -/
theorem rowOfG_forall₂ {α β : Type} {R : α → β → Prop}
    {pre₁ : List α} {pre₂ : List β} {sp₁ : Option α} {sp₂ : Option β}
    {suf₁ : List α} {suf₂ : List β}
    (hp : List.Forall₂ R pre₁ pre₂)
    (hs : (sp₁ = none ∧ sp₂ = none) ∨ ∃ a b, sp₁ = some a ∧ sp₂ = some b ∧ R a b)
    (hf : List.Forall₂ R suf₁ suf₂) {n : Nat} {r₁ : List α} {r₂ : List β}
    (h₁ : rowOfG pre₁ sp₁ suf₁ n = some r₁) (h₂ : rowOfG pre₂ sp₂ suf₂ n = some r₂) :
    List.Forall₂ R r₁ r₂ := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  rcases hs with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, hab⟩
  · simp only [rowOfG] at h₁ h₂
    split at h₁
    · next he₁ =>
        split at h₂
        · next he₂ =>
            simp only [Option.some.injEq] at h₁ h₂
            subst h₁; subst h₂
            exact forall₂_append hp hf
        · exact absurd h₂ (by simp)
    · exact absurd h₁ (by simp)
  · simp only [rowOfG] at h₁ h₂
    split at h₁
    · exact absurd h₁ (by simp)
    · next he₁ =>
        split at h₂
        · exact absurd h₂ (by simp)
        · next he₂ =>
            simp only [Option.some.injEq] at h₁ h₂
            subst h₁; subst h₂
            refine forall₂_append (forall₂_append hp ?_) hf
            have hc : n - pre₁.length - suf₁.length = n - pre₂.length - suf₂.length := by omega
            rw [hc]
            exact forall₂_replicate hab _

/-- A spreading shape has a row at every length its prefix and suffix fit inside. -/
theorem rowOfG_total {α : Type} {pre suf : List α} {c : α} {n : Nat}
    (hn : pre.length + suf.length ≤ n) :
    ∃ row, rowOfG pre (some c) suf n = some row := by
  simp only [rowOfG]
  exact ⟨_, if_neg (by omega)⟩

/-- **A spreading shape's row at any length is its row at one length, re-spread.** Cut the
    shorter row at `P`, insert the spread as often as the longer length needs, and the
    longer row comes back. This is what the row relations alone cannot give: the `list` row of
    `Term.disjoint` compares the two rows at ONE length, and the disjointness obligation is at
    EVERY length. `P` and `S` are the common prefix and suffix lengths, which each operand's own
    prefix and suffix fit inside. -/
theorem rowOfG_respread {α : Type} {pre suf : List α} {c : α} {P S n : Nat}
    (hP : pre.length ≤ P) (hS : suf.length ≤ S) (hn : P + S ≤ n)
    {rN rn : List α}
    (hN : rowOfG pre (some c) suf (P + S) = some rN)
    (hm : rowOfG pre (some c) suf n = some rn) :
    rn = rN.take P ++ List.replicate (n - P - S) c ++ rN.drop P := by
  simp only [rowOfG] at hN hm
  rw [if_neg (by omega)] at hN
  rw [if_neg (by omega)] at hm
  simp only [Option.some.injEq] at hN hm
  subst hN; subst hm
  have h1 : ((pre ++ List.replicate (P + S - pre.length - suf.length) c) ++ suf).take P
      = pre ++ List.replicate (P - pre.length) c := by
    simp only [List.take_append, List.length_append, List.length_replicate,
      List.take_replicate, List.take_of_length_le hP]
    rw [show min (P - pre.length) (P + S - pre.length - suf.length) = P - pre.length by omega,
      show P - (pre.length + (P + S - pre.length - suf.length)) = 0 by omega]
    simp
  have h2 : ((pre ++ List.replicate (P + S - pre.length - suf.length) c) ++ suf).drop P
      = List.replicate (S - suf.length) c ++ suf := by
    simp only [List.drop_append, List.length_append, List.length_replicate,
      List.drop_replicate, List.drop_eq_nil_of_le hP]
    rw [show P - (pre.length + (P + S - pre.length - suf.length)) = 0 by omega,
      show P + S - pre.length - suf.length - (P - pre.length) = S - suf.length by omega]
    simp
  rw [h1, h2, show n - pre.length - suf.length
      = (P - pre.length) + ((n - P - S) + (S - suf.length)) by omega,
    List.replicate_add, List.replicate_add]
  simp only [List.append_assoc]

/-- **Dominance is exactly the equation the common row needs.** The row that places every
    declared position of both shapes has `max p₁ p₂ + max s₁ s₂` positions, and a value both
    shapes admit has at least `max (p₁+s₁) (p₂+s₂)` elements. Where one side dominates, the two
    agree, so each common length re-spreads the one row. -/
theorem dominates_max {p₁ s₁ p₂ s₂ : Nat} (h : dominates p₁ s₁ p₂ s₂ = true) :
    max p₁ p₂ + max s₁ s₂ = max (p₁ + s₁) (p₂ + s₂) := by
  simp only [dominates, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

end Alg

end Calculus
