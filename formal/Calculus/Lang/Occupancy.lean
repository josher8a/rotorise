import Calculus.Lang.ExactA

/-!
# Occupancy, over a universe signature

An occupancy is the shape abstraction of a term: the root shapes of the values that the term can
write, and the root shapes of the attributes that the term can read. Each occupancy
over-approximates, and over-approximation is the safe direction: if `X ⊆ X'`, `Y ⊆ Y'` and
`X' ∩ Y' = ∅`, then `X ∩ Y = ∅`. So an opaque subterm occupies every shape, and a pair with such a
subterm gets no certificate. No third truth value is necessary.

A universe supplies the shapes in two classes. `Occ` holds computable data: the two shape types,
their enumerations, the shapes of each primitive, the element shape of a set shape, and the shape
of the list and map formers. So `Orth1` stays computable, and the kernel evaluates a closed pair.
`OccSound` holds the shape maps of the two carriers and the landing fact of each former, which only
the soundness theorems read. Every other row is structure: `union`, `held`, `refine`, `mu`, `var`,
`never`, and `opaq`, which occupies every shape.
-/

namespace Calculus

/-- The occupancy of one shape. -/
def occOnly {α : Type} [DecidableEq α] (x : α) : α → Bool := fun y => decide (y = x)
/-- The occupancy of every shape. -/
def occTop {α : Type} : α → Bool := fun _ => true
/-- The occupancy of no shape. -/
def occNone {α : Type} : α → Bool := fun _ => false

end Calculus

namespace Calculus.Alg

/-- **The shape data of a universe**, computable. A shape is a root constructor of a carrier. -/
class Occ (S : Syn) where
  /-- The root shapes of a value. -/
  ShV : Type
  /-- The root shapes of an attribute. -/
  ShA : Type
  decV : DecidableEq ShV
  decA : DecidableEq ShA
  /-- Every value shape, so that a disjointness test is a `List.all`. -/
  allV : List ShV
  mem_allV : ∀ s, s ∈ allV
  /-- Every attribute shape. -/
  allA : List ShA
  mem_allA : ∀ m, m ∈ allA
  /-- The value shapes that a primitive can write. -/
  primV : S.Ground → ShV → Bool
  /-- The attribute shapes that a primitive can read. -/
  primA : S.Ground → ShA → Bool
  /-- The element shape of a set shape, where the shape is a set shape. -/
  setV : ShV → Option ShV
  /-- …on the read side. -/
  setA : ShA → Option ShA
  /-- The shape of a list value, and of a list attribute. -/
  listV : ShV
  listA : ShA
  /-- The shape of a map value, and of a map attribute. -/
  mapV : ShV
  mapA : ShA

instance (S : Syn) [Occ S] : DecidableEq (Occ.ShV S) := Occ.decV
instance (S : Syn) [Occ S] : DecidableEq (Occ.ShA S) := Occ.decA

/-- **The shape maps of a universe and the landing fact of each former.** A primitive writes and
    reads in its own shapes, a set writes a set shape whose element shape an element writes, and
    the prisms build the list and map shapes. -/
class OccSound (S : Syn) [Sem S] [Occ S] where
  /-- The root shape of a value. -/
  shapeV : S.V → Occ.ShV S
  /-- The root shape of an attribute. -/
  shapeA : Sem.A S → Occ.ShA S
  prim_e : ∀ g v, ((Sem.ground g).e v).isSome = true → Occ.primV g (shapeV v) = true
  prim_p : ∀ g a, ((Sem.ground g).p a).isSome = true → Occ.primA g (shapeA a) = true
  /-- A set that writes a value has an element that the element codec writes, and the element's
      shape is the element shape of the set's shape. -/
  set_e : ∀ L, Sem.set (S := S) = some L → ∀ c v, ((L.lift c).e v).isSome = true →
    ∃ x, (c.e x).isSome = true ∧ Occ.setV (shapeV v) = some (shapeV x)
  set_p : ∀ L, Sem.set (S := S) = some L → ∀ c a, ((L.lift c).p a).isSome = true →
    ∃ y, (c.p y).isSome = true ∧ Occ.setA (shapeA a) = some (shapeA y)
  list_e : ∀ L, Sem.list (S := S) = some L → ∀ vs, shapeV (L.pV.into vs) = Occ.listV (S := S)
  list_p : ∀ L, Sem.list (S := S) = some L → ∀ as, shapeA (L.pA.into as) = Occ.listA (S := S)
  map_e : ∀ F, Sem.map (S := S) = some F → ∀ m, shapeV (F.mV.into m) = Occ.mapV (S := S)
  map_p : ∀ F, Sem.map (S := S) = some F → ∀ m, shapeA (F.mA.into m) = Occ.mapA (S := S)

variable {S : Syn}

/-! ## Variables -/

mutual
/-- A term that reads a variable at any level has a variable. -/
theorem Term.hasVar_of_use : ∀ (t : Term S) (i : Nat), t.use i ≠ 0 → t.hasVar = true
  | .var _, _, _ => rfl
  | .refine t _, i, h => Term.hasVar_of_use t i (by simpa [Term.use] using h)
  | .mu t, i, h => Term.hasVar_of_use t (i + 1) (by simpa [Term.use] using h)
  | .set t, i, h => Term.hasVar_of_use t i (by
      simp only [Term.use, useUnder] at h; split at h <;> omega)
  | .held t P _ _, i, h => by
      simp only [Term.use, useHeld] at h
      simp only [Term.hasVar, Bool.or_eq_true]
      rcases Nat.eq_zero_or_pos (t.use i) with ht | ht
      · exact Or.inr (Term.hasVar_of_use P i (by split at h <;> omega))
      · exact Or.inl (Term.hasVar_of_use t i (by omega))
  | .list pre sp suf, i, h => by
      simp only [Term.use, useUnder] at h
      simp only [Term.hasVar, Bool.or_eq_true]
      rcases Nat.eq_zero_or_pos (Term.useL i pre) with h1 | h1
      · rcases Nat.eq_zero_or_pos (Term.useO i sp) with h2 | h2
        · exact Or.inr (Term.hasVarL_of_use suf i (by split at h <;> omega))
        · exact Or.inl (Or.inr (Term.hasVarO_of_use sp i (by omega)))
      · exact Or.inl (Or.inl (Term.hasVarL_of_use pre i (by omega)))
  | .object b, i, h => Body.hasVar_of_use b i (by
      simp only [Term.use, useUnder] at h; split at h <;> omega)
  | .union os, i, h => Term.hasVarL_of_use os i (by simpa [Term.use] using h)
  | .prim _, _, h | .opaq, _, h | .never, _, h => by simp [Term.use] at h
/-- …in a body. -/
theorem Body.hasVar_of_use : ∀ (b : Body S) (i : Nat), b.use i ≠ 0 → b.hasVar = true
  | .mk fs f w, i, h => by
      simp only [Body.use] at h
      simp only [Body.hasVar, Bool.or_eq_true, decide_eq_true_eq]
      rcases Nat.eq_zero_or_pos (Term.useO i w) with hw | hw
      · refine Or.inl (Decidable.byContradiction fun hn => h ?_)
        have hall : ∀ k : {k // k ∈ fs}, ObjectSlot.use i (f k) = 0 := fun k =>
          Decidable.byContradiction fun hk => hn ⟨k, ObjectSlot.hasVar_of_use (f k) i hk⟩
        rw [hw, Nat.max_eq_left (Nat.zero_le _)]
        exact Nat.eq_zero_of_le_zero (Finset.sup_le fun k _ => (hall k).le)
      · exact Or.inr (Term.hasVarO_of_use w i (by omega))
/-- …in a slot. -/
theorem ObjectSlot.hasVar_of_use : ∀ (s : ObjectSlot S) (i : Nat), s.use i ≠ 0 →
    s.hasVar = true
  | .req t, i, h | .optional t, i, h => Term.hasVar_of_use t i h
/-- …in a list. -/
theorem Term.hasVarL_of_use : ∀ (ts : List (Term S)) (i : Nat), Term.useL i ts ≠ 0 →
    Term.hasVarL ts = true
  | [], _, h => by simp [Term.useL] at h
  | t :: ts, i, h => by
      simp only [Term.useL] at h
      simp only [Term.hasVarL, Bool.or_eq_true]
      rcases Nat.eq_zero_or_pos (t.use i) with ht | ht
      · exact Or.inr (Term.hasVarL_of_use ts i (by omega))
      · exact Or.inl (Term.hasVar_of_use t i (by omega))
/-- …in an optional term. -/
theorem Term.hasVarO_of_use : ∀ (o : Option (Term S)) (i : Nat), Term.useO i o ≠ 0 →
    Term.hasVarO o = true
  | none, _, h => by simp [Term.useO] at h
  | some t, i, h => Term.hasVar_of_use t i h
end

/-! ## Occupancy

An occupancy is a total map from shape to `Bool`. A `ShV → Bool` is already the powerset, and the
lattice operations are `||` and `&&`. The occupancy is computed from one term, never from a pair.
-/

section Occupancy
variable [Occ S]

mutual

/-- **Which value shapes this term can write.** An over-approximation of
    `{shapeV v | Adm t v}`, and `occV_sound` is that containment.

    * `held t P f _` writes where its caller-side term `P` writes. `f` can move a value into any
      shape, but `P` restricts what the `held` writes. The read occupancy is the stored-side
      term's (`occA`), which is another coordinate.
    * `refine t q` writes where `t` writes. A refinement writes a subset of what its base writes.
    * `opaq` writes every shape.
    * `union opts` writes where one of its options writes. -/
def occV : Term S → Occ.ShV S → Bool
  | .prim g => Occ.primV g
  -- the bottom writes nothing, so it occupies no shape
  | .never => occNone
  -- a set writes the set shape of each element shape that its element writes, and every set
  -- shape where its element reads a variable
  | .set t => fun s => (Occ.setV s).elim false fun e => occV t e || t.hasVar
  | .list _ _ _ => occOnly (Occ.listV (S := S))
  | .object _ => occOnly (Occ.mapV (S := S))
  | .held _ P _ _ => occV P
  | .refine t _ => occV t
  | .union opts => occVL opts
  | .opaq => occTop
  -- a closed variable is the bottom, and a recursive term writes where its body does: its
  -- variable sits under a container, whose shape is the container's
  | .var _ => occNone
  | .mu b => occV b

/-- The options' occupancy: the union of each option's. -/
def occVL : List (Term S) → Occ.ShV S → Bool
  | [] => fun _ => false
  | t :: ts => fun s => occV t s || occVL ts s
end

mutual

/-- **Which attribute shapes this term can read.** The mirror of `occV`, and not a symmetric
    mirror: `held` reads where its stored-side term reads. -/
def occA : Term S → Occ.ShA S → Bool
  | .prim g => Occ.primA g
  | .never => occNone
  | .set t => fun m => (Occ.setA m).elim false fun e => occA t e || t.hasVar
  | .list _ _ _ => occOnly (Occ.listA (S := S))
  | .object _ => occOnly (Occ.mapA (S := S))
  | .refine t _ => occA t
  | .held t _ _ _ => occA t
  | .union opts => occAL opts
  | .opaq => occTop
  | .var _ => occNone
  | .mu b => occA b

/-- The options' read occupancy. -/
def occAL : List (Term S) → Occ.ShA S → Bool
  | [] => fun _ => false
  | t :: ts => fun m => occA t m || occAL ts m
end

/-- **The shape test**: the write occupancies disjoint, and the read occupancies disjoint.

    A `held` has its two occupancies in two coordinates: the write side is the caller-side
    term's, and the read side is the stored-side term's. So the test asks both sides. -/
def Orth1 (x y : Term S) : Bool :=
  (Occ.allV (S := S)).all (fun s => !(occV x s && occV y s)) &&
    (Occ.allA (S := S)).all (fun m => !(occA x m && occA y m))

/-- The shape test makes the write occupancies disjoint. -/
theorem occV_disjoint_of_Orth1 {x y : Term S} (h : Orth1 x y = true) {s : Occ.ShV S}
    (hx : occV x s = true) (hy : occV y s = true) : False := by
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 s (Occ.mem_allV s)
  simp_all

/-- …and the read occupancies. -/
theorem occA_disjoint_of_Orth1 {x y : Term S} (h : Orth1 x y = true) {m : Occ.ShA S}
    (hx : occA x m = true) (hy : occA y m = true) : False := by
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 m (Occ.mem_allA m)
  simp_all

/-- An occupancy of an option is inside the occupancy of the union. -/
theorem occVL_cons {t : Term S} {ts : List (Term S)} {s : Occ.ShV S}
    (h : occV t s = true ∨ occVL ts s = true) : occVL (t :: ts) s = true := by
  rcases h with h | h <;> simp [occVL, h]

/-- A read occupancy of an option is inside the read occupancy of the union. -/
theorem occAL_cons {t : Term S} {ts : List (Term S)} {m : Occ.ShA S}
    (h : occA t m = true ∨ occAL ts m = true) : occAL (t :: ts) m = true := by
  rcases h with h | h <;> simp [occAL, h]

end Occupancy

/-! ## Soundness

The statement is about the rows (`Adm`, `AdmA`), and the proof is about open terms, because a
recursive term's occupancy is its body's. A term either writes a value in its own occupancy, or one
of its variables that reads the term's own input writes the value (`occV_open`). A closed term has
no such variable, so the row lands in the occupancy (`occV_sound`). A body reads its variable under
a container, so the occupancy of `mu b` is the occupancy of `b` with the variable at no shape. This
needs no guard: a stage that writes a value writes it through the body at the stage before, and the
stages start at the bottom. -/

section Soundness
variable [Sem S] [Occ S] [OccSound S]

open OccSound (shapeV shapeA)

mutual

/-- **The write occupancy contains what an open term writes**, or a variable that reads the
    term's own input writes it. At `set t`, the set has an element, and the element's shape names
    the set shape. -/
theorem occV_open : ∀ (t : Term S) (ρ : List S.C) (v : S.V),
    ((denote t ρ).e v).isSome = true →
      occV t (shapeV v) = true ∨ ∃ i, 2 ≤ t.use i ∧ ((envAt ρ i).e v).isSome = true
  | .prim g, _, v, h => Or.inl (OccSound.prim_e g v h)
  | .never, _, _, h => by simp [denote, Codec.empty] at h
  | .opaq, _, _, _ => Or.inl rfl
  | .set t, ρ, v, h => by
      simp only [denote] at h
      split at h
      · next L hL =>
          obtain ⟨x, hx, hs⟩ := OccSound.set_e L hL _ v h
          refine Or.inl ?_
          simp only [occV, hs, Option.elim_some, Bool.or_eq_true]
          rcases occV_open t ρ x hx with h1 | ⟨i, hi, -⟩
          · exact Or.inl h1
          · exact Or.inr (Term.hasVar_of_use t i (by omega))
      · simp [Codec.empty] at h
  -- the containers write their own shape, whatever their elements write
  | .list _ _ _, _, v, h => by
      simp only [denote] at h
      split at h
      · next L hL =>
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨xs, -, hv, -, -⟩ := carried_e.mp ha
          refine Or.inl ?_
          rw [L.pV.into_out hv, OccSound.list_e L hL]
          simp [occV, occOnly]
      · simp [Codec.empty] at h
  | .object (.mk _ _ _), _, v, h => by
      simp only [denote, bodySem] at h
      split at h
      · next F hF =>
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨m, -, hv, -, -⟩ := carried_e.mp ha
          refine Or.inl ?_
          rw [F.mV.into_out hv, OccSound.map_e F hF]
          simp [occV, occOnly]
      · simp [Codec.empty] at h
  | .held t P f g, ρ, v, h => by
      have hP : ((denote P ρ).e v).isSome = true := by
        simp only [denote, restrict_e_isSome, Bool.and_eq_true] at h; exact h.1
      rcases occV_open P ρ v hP with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simp only [Term.use, useHeld]; split <;> omega, he⟩
  | .refine t p, ρ, v, h => by
      have ht : ((denote t ρ).e v).isSome = true := by
        simp only [denote, restrict_e_isSome, Bool.and_eq_true] at h; exact h.2
      rcases occV_open t ρ v ht with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .union opts, ρ, v, h => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨o, ho, hoe, -⟩ := altCodec_e_admits ha
      rcases occV_openL opts ρ v o ho hoe with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .var j, _, _, h => Or.inr ⟨j, by simp [Term.use], h⟩
  -- a stage writes through the body at the stage before, and the first stage writes nothing
  | .mu b, ρ, v, h => by
      have hs : ∀ n, ((muStage (fun c => denote b (c :: ρ)) n).e v).isSome = true →
          occV b (shapeV v) = true ∨
            ∃ i, 2 ≤ b.use (i + 1) ∧ ((envAt ρ i).e v).isSome = true := by
        intro n
        induction n with
        | zero => intro h0; simp [muStage, Codec.empty] at h0
        | succ n ih =>
          intro hn
          rcases occV_open b _ v hn with h1 | ⟨i, hi, he⟩
          · exact Or.inl h1
          · match i, hi, he with
            | 0, _, he => exact ih he
            | i + 1, hi, he => exact Or.inr ⟨i, hi, he⟩
      rcases hs _ h with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩

/-- The options' companion: an option that writes a value writes it in the union's occupancy, or
    through a variable that reads the input. -/
theorem occV_openL : ∀ (ts : List (Term S)) (ρ : List S.C) (v : S.V) (o : S.C),
    o ∈ denoteList ts ρ → (o.e v).isSome = true →
      occVL ts (shapeV v) = true ∨ ∃ i, 2 ≤ Term.useL i ts ∧ ((envAt ρ i).e v).isSome = true
  | [], _, _, _, ho, _ => nomatch ho
  | t :: ts, ρ, v, o, ho, h => by
      simp only [denoteList, List.mem_cons] at ho
      rcases ho with rfl | ho
      · rcases occV_open t ρ v h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occVL_cons (.inl h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩
      · rcases occV_openL ts ρ v o ho h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occVL_cons (.inr h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩

end

mutual

/-- **The read occupancy contains what an open term reads**, or a variable that reads the term's
    own input reads it. The mirror of `occV_open`. -/
theorem occA_open : ∀ (t : Term S) (ρ : List S.C) (a : Sem.A S),
    ((denote t ρ).p a).isSome = true →
      occA t (shapeA a) = true ∨ ∃ i, 2 ≤ t.use i ∧ ((envAt ρ i).p a).isSome = true
  | .prim g, _, a, h => Or.inl (OccSound.prim_p g a h)
  | .never, _, _, h => by simp [denote, Codec.empty] at h
  | .opaq, _, _, _ => Or.inl rfl
  | .set t, ρ, a, h => by
      simp only [denote] at h
      split at h
      · next L hL =>
          obtain ⟨y, hy, hs⟩ := OccSound.set_p L hL _ a h
          refine Or.inl ?_
          simp only [occA, hs, Option.elim_some, Bool.or_eq_true]
          rcases occA_open t ρ y hy with h1 | ⟨i, hi, -⟩
          · exact Or.inl h1
          · exact Or.inr (Term.hasVar_of_use t i (by omega))
      · simp [Codec.empty] at h
  | .list _ _ _, _, a, h => by
      simp only [denote] at h
      split at h
      · next L hL =>
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨as, -, ha, -, -⟩ := carried_p.mp hw
          refine Or.inl ?_
          rw [L.pA.into_out ha, OccSound.list_p L hL]
          simp [occA, occOnly]
      · simp [Codec.empty] at h
  | .object (.mk _ _ _), _, a, h => by
      simp only [denote, bodySem] at h
      split at h
      · next F hF =>
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨m, -, ha, -, -⟩ := carried_p.mp hw
          refine Or.inl ?_
          rw [F.mA.into_out ha, OccSound.map_p F hF]
          simp [occA, occOnly]
      · simp [Codec.empty] at h
  | .held t P f g, ρ, a, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hc, -⟩ := restrict_p.mp hw
      obtain ⟨u, hu, -⟩ := through_p.mp hc
      rcases occA_open t ρ a (by rw [hu]; rfl) with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simp only [Term.use, useHeld]; split <;> omega, he⟩
  | .refine t p, ρ, a, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hc, -⟩ := restrict_p.mp hw
      rcases occA_open t ρ a (by rw [hc]; rfl) with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .union opts, ρ, a, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨o, ho, hop, -⟩ := altCodec_p_admits hw
      rcases occA_openL opts ρ a o ho hop with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .var j, _, _, h => Or.inr ⟨j, by simp [Term.use], h⟩
  | .mu b, ρ, a, h => by
      have hs : ∀ n, ((muStage (fun c => denote b (c :: ρ)) n).p a).isSome = true →
          occA b (shapeA a) = true ∨
            ∃ i, 2 ≤ b.use (i + 1) ∧ ((envAt ρ i).p a).isSome = true := by
        intro n
        induction n with
        | zero => intro h0; simp [muStage, Codec.empty] at h0
        | succ n ih =>
          intro hn
          rcases occA_open b _ a hn with h1 | ⟨i, hi, he⟩
          · exact Or.inl h1
          · match i, hi, he with
            | 0, _, he => exact ih he
            | i + 1, hi, he => exact Or.inr ⟨i, hi, he⟩
      rcases hs _ h with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩

/-- The options' companion on the read side. -/
theorem occA_openL : ∀ (ts : List (Term S)) (ρ : List S.C) (a : Sem.A S) (o : S.C),
    o ∈ denoteList ts ρ → (o.p a).isSome = true →
      occAL ts (shapeA a) = true ∨ ∃ i, 2 ≤ Term.useL i ts ∧ ((envAt ρ i).p a).isSome = true
  | [], _, _, _, ho, _ => nomatch ho
  | t :: ts, ρ, a, o, ho, h => by
      simp only [denoteList, List.mem_cons] at ho
      rcases ho with rfl | ho
      · rcases occA_open t ρ a h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occAL_cons (.inl h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩
      · rcases occA_openL ts ρ a o ho h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occAL_cons (.inr h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩

end

/-- **The write occupancy contains the row.** A closed term's variables are the bottom, so no
    variable writes, and the open lemma lands in the occupancy. -/
theorem occV_sound [PrimAdm S] (t : Term S) (v : S.V) (h : Adm t [] v = true) :
    occV t (shapeV v) = true :=
  (occV_open t [] v ((Adm_exact t [] v).mp h)).resolve_right
    fun ⟨_, _, he⟩ => by simp [envAt, Codec.empty] at he

/-- **The read occupancy contains the row.** The mirror of `occV_sound`. -/
theorem occA_sound [PrimAdm S] [PrimAdmA S] (t : Term S) (a : Sem.A S) (h : AdmA t [] a = true) :
    occA t (shapeA a) = true :=
  (occA_open t [] a ((AdmA_exact t [] a).mp h)).resolve_right
    fun ⟨_, _, he⟩ => by simp [envAt, Codec.empty] at he

end Soundness

end Calculus.Alg
