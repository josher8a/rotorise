import Calculus.Lang.Meet
import Calculus.Lang.HeldFree
import Calculus.Alg.Rows

/-!
# The rows of the meet

The facts about the meet that read no admission: the rows that `rowOfG` assigns to a `list`
shape, the zip and replicate laws of `Forall₂`, dominance, the answers of the list family, and
the held-free test. Every statement holds at every signature, and most hold at any element type.
-/

namespace Calculus.Alg

open Calculus (alignPL alignP zipP zipP_false_of_length_ne alignP_short alignP_none_eq_zipP
  zipP_append alignP_some_eq_zipP zipP_row_split)

variable {S : Syn}

/-- A normalised list is a list or the bottom. -/
theorem listOf_cases (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S)) :
    Term.listOf pre sp suf = .never ∨ Term.listOf pre sp suf = .list pre sp suf := by
  unfold Term.listOf; split
  · exact Or.inl rfl
  · exact Or.inr rfl

mutual
/-- A term with no `held` is held-free. `hasHeld` is the test the meet can run, and `HF` is the
    premise `sub_denote` reads. -/
theorem HF_of_hasHeld : ∀ t : Term S, hasHeld t = false → HF t
  | .held _ _ _ _, h => by simp [hasHeld] at h
  | .refine t _, h => HF_of_hasHeld t h
  | .mu t, h => HF_of_hasHeld t h
  | .set t, h => HF_of_hasHeld t h
  | .list pre sp suf, h => by
      simp only [hasHeld, Bool.or_eq_false_iff] at h
      exact ⟨HFL_of_hasHeld pre h.1.1, HFO_of_hasHeld sp h.1.2, HFL_of_hasHeld suf h.2⟩
  | .object b, h => HFB_of_hasHeld b h
  | .union os, h => HFL_of_hasHeld os h
  | .prim _, _ | .opaq, _ | .never, _ | .var _, _ => trivial
/-- …at a body. -/
theorem HFB_of_hasHeld : ∀ b : Body S, hasHeldB b = false → HFB b
  | .mk fs f w, h => by
      simp only [hasHeldB, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists] at h
      exact ⟨fun k => HFS_of_hasHeld (f k) (by simpa using h.1 k), HFO_of_hasHeld w h.2⟩
/-- …at a slot. -/
theorem HFS_of_hasHeld : ∀ s : ObjectSlot S, hasHeldS s = false → HFS s
  | .req t, h | .optional t, h => HF_of_hasHeld t h
/-- …at a list. -/
theorem HFL_of_hasHeld : ∀ ts : List (Term S), hasHeldL ts = false → HFL ts
  | [], _ => trivial
  | t :: ts, h => by
      simp only [hasHeldL, Bool.or_eq_false_iff] at h
      exact ⟨HF_of_hasHeld t h.1, HFL_of_hasHeld ts h.2⟩
/-- …at an optional term. -/
theorem HFO_of_hasHeld : ∀ o : Option (Term S), hasHeldO o = false → HFO o
  | none, _ => trivial
  | some t, h => HF_of_hasHeld t h
end

/-- **`alignPL` is its row, applied position for position.** This is `align_eq_zip` one level
    down, and it is what lets the meet reason about two shapes by reasoning about their rows
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

/-- Every term a row holds comes from the shape: a declared position, or the spread. -/
theorem rowOfG_mem {α : Type} {pre : List α} {sp : Option α} {suf : List α} {n row}
    (h : rowOfG pre sp suf n = some row) {a : α} (ha : a ∈ row) :
    a ∈ pre ∨ a ∈ sp ∨ a ∈ suf := by
  cases sp with
  | none =>
      rw [rowOfG_none_eq] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp ha with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · exact absurd h (by simp)
  | some c =>
      rw [rowOfG_some_eq] at h
      split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp ha with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by rw [List.eq_of_mem_replicate h'']; rfl))
        · exact Or.inr (Or.inr h')

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

/-- **The three-place row relation**, carried as a `Forall₂` over the pair list, as
    `zipF_lift_terms` and `alignP_meet_zip` already carry it. The four lemmas below close it under
    the four ways the meet cuts and rebuilds a row. -/
theorem forall₂_zip_append {α β γ : Type} {R : α × β → γ → Prop}
    {a₁ a₂ : List α} {b₁ b₂ : List β} {c₁ c₂ : List γ}
    (hl : a₁.length = b₁.length)
    (h₁ : List.Forall₂ R (a₁.zip b₁) c₁) (h₂ : List.Forall₂ R (a₂.zip b₂) c₂) :
    List.Forall₂ R ((a₁ ++ a₂).zip (b₁ ++ b₂)) (c₁ ++ c₂) := by
  rw [List.zip_append hl]
  exact forall₂_append h₁ h₂

/-- …the spread, held at as many positions as the length needs. -/
theorem forall₂_zip_replicate {α β γ : Type} {R : α × β → γ → Prop} {a : α} {b : β} {c : γ}
    (h : R (a, b) c) (n : Nat) :
    List.Forall₂ R ((List.replicate n a).zip (List.replicate n b)) (List.replicate n c) := by
  rw [List.zip_replicate, Nat.min_self]
  exact forall₂_replicate h n

/-- …the prefix the answer keeps. -/
theorem forall₂_zip_take {α β γ : Type} {R : α × β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} (n : Nat),
      List.Forall₂ R (as.zip bs) cs →
      List.Forall₂ R ((as.take n).zip (bs.take n)) (cs.take n) := by
  intro as bs cs n
  induction n generalizing as bs cs with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      cases as with
      | nil => cases h; simp
      | cons a as' =>
          cases bs with
          | nil => cases h; simp
          | cons b bs' =>
              rw [List.zip_cons_cons] at h
              cases h with
              | cons hh ht => simpa using List.Forall₂.cons hh (ih ht)

/-- …and the suffix the answer keeps. -/
theorem forall₂_zip_drop {α β γ : Type} {R : α × β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} (n : Nat),
      List.Forall₂ R (as.zip bs) cs →
      List.Forall₂ R ((as.drop n).zip (bs.drop n)) (cs.drop n) := by
  intro as bs cs n
  induction n generalizing as bs cs with
  | zero => intro h; simpa using h
  | succ n ih =>
      intro h
      cases as with
      | nil => cases h; simp
      | cons a as' =>
          cases bs with
          | nil => cases h; simp
          | cons b bs' =>
              rw [List.zip_cons_cons] at h
              cases h with
              | cons _ ht => simpa using ih ht

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
    related position for position assign related rows at every length. This is the one
    lemma the meet's three semantic families share: each reads its own relation off the
    two rows rather than off the shapes. -/
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

/-- …and the row of a shape whose parts match another's lengths exists wherever that one's
    does, related to it. This is the form the meet uses: it holds the FUNCTION row and needs
    the TERM row that stands behind it. -/
theorem rowOfG_forall₂_left {α β : Type} {R : α → β → Prop}
    {pre₁ : List α} {pre₂ : List β} {sp₁ : Option α} {sp₂ : Option β}
    {suf₁ : List α} {suf₂ : List β}
    (hp : List.Forall₂ R pre₁ pre₂)
    (hs : (sp₁ = none ∧ sp₂ = none) ∨ ∃ a b, sp₁ = some a ∧ sp₂ = some b ∧ R a b)
    (hf : List.Forall₂ R suf₁ suf₂) {n : Nat} {r₂ : List β}
    (h₂ : rowOfG pre₂ sp₂ suf₂ n = some r₂) :
    ∃ r₁, rowOfG pre₁ sp₁ suf₁ n = some r₁ ∧ List.Forall₂ R r₁ r₂ := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  have hex : ∃ r₁, rowOfG pre₁ sp₁ suf₁ n = some r₁ := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, _⟩
    · simp only [rowOfG] at h₂ ⊢
      split at h₂
      · next he => exact ⟨_, if_pos (by omega)⟩
      · exact absurd h₂ (by simp)
    · simp only [rowOfG] at h₂ ⊢
      split at h₂
      · exact absurd h₂ (by simp)
      · next he => exact ⟨_, if_neg (by omega)⟩
  obtain ⟨r₁, h₁⟩ := hex
  exact ⟨r₁, h₁, rowOfG_forall₂ hp hs hf h₁ h₂⟩

/-- …and a spreading shape has a row exactly from its arity up. -/
theorem rowOfG_some_isSome {α : Type} (pre : List α) (c : α) (suf : List α) (n : Nat) :
    (rowOfG pre (some c) suf n).isSome = decide (pre.length + suf.length ≤ n) := by
  rw [rowOfG_some_eq]
  split <;> simp_all

/-- A spreading shape has a row at every length its prefix and suffix fit inside. -/
theorem rowOfG_total {α : Type} {pre suf : List α} {c : α} {n : Nat}
    (hn : pre.length + suf.length ≤ n) :
    ∃ row, rowOfG pre (some c) suf n = some row := by
  simp only [rowOfG]
  exact ⟨_, if_neg (by omega)⟩

/-- **A spreading shape's row at any length is its row at one length, re-spread.** Cut the
    shorter row at `P`, insert the spread as often as the longer length needs, and the
    longer row comes back. This is what the `list` meet owes and what the row relations
    alone cannot give: the meet builds its answer from the two rows at ONE length, and the
    admission obligation is at EVERY length. `P` and `S` are the answer's prefix and suffix
    lengths, which each operand's own prefix and suffix fit inside. -/
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

/-- **Dominance is exactly the equation the answer needs.** The widest `list` the answer can
    spell starts at `max p₁ p₂ + max s₁ s₂`, and the intersection starts at
    `max (p₁+s₁) (p₂+s₂)`. Where one side dominates, the two agree, so the answer refuses a
    length exactly where a factor does. -/
theorem dominates_max {p₁ s₁ p₂ s₂ : Nat} (h : dominates p₁ s₁ p₂ s₂ = true) :
    max p₁ p₂ + max s₁ s₂ = max (p₁ + s₁) (p₂ + s₂) := by
  simp only [dominates, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- Every answer of `listMeetRow` is the bottom or a list: each branch ends in `Term.listOf`,
    and a normalised list is one or the other. -/
theorem listMeetRow_isList {fpre : List (Term S → Option (Term S))}
    {fsp : Option (Term S → Option (Term S))} {fsuf : List (Term S → Option (Term S))}
    {pre₂ : List (Term S)} {sp₂ : Option (Term S)} {suf₂ : List (Term S)} {z : Term S}
    (h : listMeetRow fpre fsp fsuf pre₂ sp₂ suf₂ = some z) :
    z = .never ∨ ∃ p q s, z = .list p q s := by
  have hA : ∀ (o : Option (List (Term S))) (g : List (Term S) → Term S),
      (∀ row, g row = .never ∨ ∃ p q s, g row = .list p q s) →
      o.map g = some z → z = .never ∨ ∃ p q s, z = .list p q s := by
    intro o g hg ho
    obtain ⟨row, _, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact hg row
  have hTake : ∀ (P : Nat) (q : Option (Term S)) (row : List (Term S)),
      Term.listOf (row.take P) q (row.drop P) = .never ∨
        ∃ p q' s, Term.listOf (row.take P) q (row.drop P) = .list p q' s :=
    fun P q row => (listOf_cases _ _ _).imp id fun hc => ⟨_, _, _, hc⟩
  have hFlat : ∀ row : List (Term S), Term.listOf row none [] = .never ∨
      ∃ p q' s, Term.listOf row none [] = .list p q' s :=
    fun row => (listOf_cases _ _ _).imp id fun hc => ⟨_, _, _, hc⟩
  unfold listMeetRow at h
  split at h
  · split at h
    · split at h
      · exact hA _ _ (hTake _ _) h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; exact Or.inl h.symm
    · exact absurd h (by simp)
  · split at h
    · exact hA _ _ hFlat h
    · simp only [Option.some.injEq] at h; exact Or.inl h.symm
  · split at h
    · exact hA _ _ hFlat h
    · simp only [Option.some.injEq] at h; exact Or.inl h.symm

/-- …so every answer of the family is the bottom or a list. -/
theorem famList_isList {fpre : List (Term S → Option (Term S))}
    {fsp : Option (Term S → Option (Term S))} {fsuf : List (Term S → Option (Term S))} {y z : Term S}
    (h : famList fpre fsp fsuf y = some z) :
    z = .never ∨ ∃ p q s, z = .list p q s := by
  cases y <;>
    first
      | exact listMeetRow_isList h
      | (simp only [famList, Option.some.injEq] at h; exact Or.inl h.symm)
      | exact absurd h (by simp [famList])



/-! ## Reading a met term -/

/-- A list of answers that all succeeded pairs each source with its answer. -/
theorem allSome_map_forall₂ {α β : Type} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, allSome (xs.map f) = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.map_nil, allSome, Option.some.injEq] at h; subst h; exact .nil
  | cons a as ihx =>
    intro ys h
    rw [List.map_cons] at h
    cases hf : f a with
    | none => rw [hf] at h; simp only [allSome, reduceCtorEq] at h
    | some b =>
      rw [hf] at h
      simp only [allSome, Option.map_eq_some_iff] at h
      obtain ⟨zs, hzs, rfl⟩ := h
      exact .cons hf (ihx hzs)

/-- The bottom is the only term that reads as the bottom. -/
theorem eq_never_of_isNever {t : Term S} (h : t.isNever = true) : t = .never := by
  cases t <;> simp only [Term.isNever, Bool.false_eq_true] at h <;> rfl

/-- A field that admits nothing at a name that must be present is a field that must be present. -/
theorem isReq_of_isBottom {f : ObjectSlot S} (h : ObjectSlot.isBottom f = true) : ObjectSlot.isReq f = true := by
  cases f <;> simp only [ObjectSlot.isBottom, ObjectSlot.isReq, Bool.false_eq_true] at h ⊢

/-- …and the zip companion is the plain map over the zip. -/
theorem zipF_eq : ∀ (fs : List (Term S → Option (Term S))) (us : List (Term S)),
    zipF fs us = (fs.zip us).map (fun p => p.1 p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: fs, _ :: us => congrArg _ (zipF_eq fs us)

/-- The required names, read over the whole key space: an undeclared name is `optional`. -/
theorem reqs_slotAt (c : Body S) (keys : Finset String) :
    decide (∀ k : {k // k ∈ c.fields}, ObjectSlot.isReq (c.at k) = true → k.1 ∈ keys) = true ↔
    ∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ keys := by
  rw [decide_eq_true_iff]
  constructor
  · intro h k hr
    rcases Decidable.em (k ∈ c.fields) with hk | hk
    · rw [Body.slotAt_pos hk] at hr; exact h ⟨k, hk⟩ hr
    · rw [Body.slotAt_neg hk] at hr; exact absurd hr (by simp [ObjectSlot.isReq])
  · intro h k hr; exact h k.1 (by rw [Body.slotAt_pos k.2]; exact hr)

/-- **The met body's slot at every name**, from the slots at the names of either body and
    the block at the rest. A name the normal form drops states the default `never`. -/
theorem objObj_slots {a b : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)} {zb : Term S} {P : String → ObjectSlot S → Prop}
    (hall : ∀ k : {k // k ∈ a.fields ∪ b.fields}, (objSlot a b g mw k).isSome = true)
    (hslot : ∀ (k : {k // k ∈ a.fields ∪ b.fields}) s, objSlot a b g mw k = some s → P k.1 s)
    (hblk : ∀ k, k ∉ a.fields → k ∉ b.fields →
      P k (.optional (if zb.isNever then .never else zb)))
    (k : String) :
    P k (Body.slotAt (.mk ((a.fields ∪ b.fields).filter (fun k =>
          (if h : k ∈ a.fields ∪ b.fields then
            !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
          else false) = true))
        (fun k => (objSlot a b g mw ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD (.optional .never))
        (if zb.isNever then none else some zb)) k) := by
  have hblock : Body.block (.mk ((a.fields ∪ b.fields).filter (fun k =>
          (if h : k ∈ a.fields ∪ b.fields then
            !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
          else false) = true))
        (fun k => (objSlot a b g mw ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD (.optional .never))
        (if zb.isNever then none else some zb)) = (if zb.isNever then .never else zb) := by
    cases zb.isNever <;> rfl
  rcases Decidable.em (k ∈ (a.fields ∪ b.fields).filter (fun k =>
      (if h : k ∈ a.fields ∪ b.fields then
        !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
      else false) = true)) with hk | hk
  · rw [Body.slotAt_pos hk]
    simp only [Body.at_mk]
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hall ⟨k, (Finset.mem_filter.mp hk).1⟩)
    rw [hs, Option.getD_some]
    exact hslot _ s hs
  · rw [Body.slotAt_neg hk, hblock]
    rcases Decidable.em (k ∈ a.fields ∪ b.fields) with hU | hU
    · have hkeep : (!(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, hU⟩))) = false := by
        refine Bool.eq_false_iff.mpr (fun ht => hk (Finset.mem_filter.mpr ⟨hU, ?_⟩))
        rw [dif_pos hU]; exact ht
      rw [Bool.not_eq_false', Bool.and_eq_true] at hkeep
      obtain ⟨hnev, habs⟩ := hkeep
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hall ⟨k, hU⟩)
      rw [hs] at habs
      cases s with
      | req t => exact absurd habs (by simp [ObjectSlot.isAbsentOpt])
      | optional t =>
        have ht : t = .never := by
          cases t <;> simp_all [ObjectSlot.isAbsentOpt, Term.isNever]
        subst ht
        rw [hnev, if_pos rfl]
        exact hslot _ _ hs
    · have ha : k ∉ a.fields := fun h => hU (Finset.mem_union.mpr (Or.inl h))
      have hb : k ∉ b.fields := fun h => hU (Finset.mem_union.mpr (Or.inr h))
      exact hblk k ha hb

/-- The right operands `meetSRight` hands to the family: everything its own rows do not answer.
    A family's catch-all row answers the bottom, which is right for these and wrong for the six
    constructors that `meetSRight` answers itself, so the predicate carries the same split. -/
def Delegated : Term S → Prop
  | .never | .held _ _ _ _ | .refine _ _ | .union _ | .var _ | .mu _ => False
  | _ => True

/-- The list companion is the plain map, so the union row reuses the `Forall₂` machinery. -/
theorem meetSRightL_eq [Leaf S] (fam : Term S → Option (Term S)) :
    ∀ os, meetSRightL fam os = os.map (meetSRight fam)
  | [] => rfl
  | _ :: os => congrArg _ (meetSRightL_eq fam os)

/-- …and the union row's extraction, with no exclusions: the row is reached by the pattern. -/
theorem meetSRight_union [Leaf S] {fam : Term S → Option (Term S)} {os : List (Term S)} {z : Term S}
    (h : meetSRight fam (.union os) = some z) :
    ∃ zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [meetSRight] at h
  obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨zs, allSome_map_forall₂ _ ?_, (Option.some.inj hg).symm⟩
  rw [← meetSRightL_eq]
  exact hzs

/-- Two fields meet at the stronger mark, so the write bit is the join. -/
theorem isReq_Field_meet [Leaf S] : ∀ {f fl fm : ObjectSlot S}, ObjectSlot.meet f fl = some fm →
    ObjectSlot.isReq fm = (ObjectSlot.isReq f || ObjectSlot.isReq fl) := by
  intro f fl fm h
  match f, fl, h with
  | .req _, .req _, h
  | .req _, .optional _, h
  | .optional _, .req _, h
  | .optional _, .optional _, h =>
      simp only [ObjectSlot.meet, Option.map_eq_some_iff] at h
      obtain ⟨tz, _, rfl⟩ := h
      rfl

/-- The option companion is the plain map at the fixed partner. -/
theorem meetSL_eq [Leaf S] (y : Term S) : ∀ os, Term.meetSL os y = os.map (fun t => Term.meet t y)
  | [] => rfl
  | _ :: os => congrArg _ (meetSL_eq y os)

/-- A certified union distributes: every option meets, the bottoms drop, and the survivors
    carry the certificate. -/
theorem meet_union_of [Leaf S] {os : List (Term S)} {y z : Term S}
    (h : Term.meet (.union os) y = some z) (hy : y ≠ .never) :
    ∃ zs, List.Forall₂ (fun t w => Term.meet t y = some w) os zs ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [Term.meet] at h
  · obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨zs, allSome_map_forall₂ _ ?_, (Option.some.inj hg).symm⟩
    rw [← meetSL_eq]
    exact hzs
  all_goals (intros; simp_all)

/-- Two objects meet at the bottom or at an object. -/
theorem objObj_cases {a b : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)} {z : Term S} (h : objObj a g mw b = some z) :
    z = .never ∨ ∃ c, z = .object c := by
  unfold objObj at h
  split at h
  · exact Or.inl (Option.some.inj h).symm
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact Or.inr ⟨_, (Option.some.inj h).symm⟩
      · exact absurd h (by simp)

/-- A `Forall₂` relates every right element to some left one. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {b}, b ∈ bs → ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hr hrest, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨a, ha, hra⟩ := forall₂_mem_right hrest hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hra⟩

end Calculus.Alg
