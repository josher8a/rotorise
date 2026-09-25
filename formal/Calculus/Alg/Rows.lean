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
theorem zipP_row_split (pre suf : List (α → Bool)) (c : α → Bool) (A B : List α)
    (hB : B.length = suf.length) (hA : pre.length ≤ A.length) :
    (zipP (pre ++ List.replicate (A.length - pre.length) c) A && zipP suf B)
      = zipP (pre ++ List.replicate ((A ++ B).length - pre.length - suf.length) c ++ suf)
          (A ++ B) := by
  have hcount : (A ++ B).length - pre.length - suf.length = A.length - pre.length := by
    simp only [List.length_append, hB]; omega
  rw [hcount, zipP_append _ _ _ _
      (by simp only [List.length_append, List.length_replicate]; omega)]

/-- Two tuples of one arity: the positions meet positionwise and the tails meet. -/
theorem alignP_meet_zip :
    ∀ {Ps Qs Rs : List (α → Bool)},
      List.Forall₂ (fun (pq : (α → Bool) × (α → Bool)) r => ∀ w, r w = (pq.1 w && pq.2 w))
        (Ps.zip Qs) Rs →
      Ps.length = Qs.length →
    ∀ {pt qt rt : Option (α → Bool)},
      ((pt = none ∧ qt = none ∧ rt = none) ∨
        ∃ p q r, pt = some p ∧ qt = some q ∧ rt = some r ∧ ∀ w, r w = (p w && q w)) →
    ∀ ws, alignP Rs rt ws = (alignP Ps pt ws && alignP Qs qt ws) := by
  intro Ps Qs Rs hF hlen pt qt rt htl ws
  induction ws generalizing Ps Qs Rs with
  | nil =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, _⟩ <;> simp [alignP]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons _ _ => simp [alignP]
  | cons w ws ihw =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, hr⟩
        · simp [alignP]
        · simp only [alignP, hr, ihw (Ps := []) (Qs := []) .nil rfl]
          simp [Bool.and_assoc, Bool.and_left_comm]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons hr hrest =>
          simp only [alignP, hr, ihw hrest (by simpa using hlen)]
          simp [Bool.and_assoc, Bool.and_left_comm]

/-- A tuple with no tail pins the length of the array it admits. -/
theorem alignP_none_length : ∀ {Ps : List (α → Bool)} {ws : List α},
    alignP Ps none ws = true → ws.length = Ps.length := by
  intro Ps
  induction Ps with
  | nil => intro ws h; cases ws with
    | nil => rfl
    | cons _ _ => simp [alignP] at h
  | cons p Ps' ihp =>
    intro ws h
    cases ws with
    | nil => simp [alignP] at h
    | cons w ws' =>
      simp only [alignP, Bool.and_eq_true] at h
      simp [ihp h.2]

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

end Calculus
