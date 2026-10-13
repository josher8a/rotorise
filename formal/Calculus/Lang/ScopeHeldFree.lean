import Calculus.Lang.ScopeSound

/-!
# Held-free closed codecs are restrictions of the top, for every universe

A scope term is held-free when no operation of the term is a `held`, a `legacy`, or an object with
a `fill` slot (`Scoped.HF`). Such a term does not change the carrier. Each other operation either
restricts its positions or composes them through the structure that the top itself uses, so an
operation over restrictions of the top is a restriction of the top (`TOp.sub_run`).

`sub_term` lifts the fact to a scope term over restrictions of the top. `Closed.sub` states it at
each entry of a held-free closed codec: each stage of each scope is a restriction of the top, and
the solution reads each input at one stage. The top is the identity, which is canonical, so two
held-free closed codecs are compatible (`Closed.compat_of_HF`).
-/

namespace Calculus.Alg.Scoped

variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

/-! ## Held-free terms -/

/-- The operation is a `held`, a `legacy`, or an object with a `fill` slot. -/
def TOp.hasHeld : TOp B → Bool
  | .held _ _ _ | .legacy _ => true
  | .obj fs md _ => (keyPos fs).any fun x => (md x).isFill
  | _ => false

/-- Some operation of the scope term is a `held`, a `legacy`, or an object with a `fill` slot. -/
def hasHeld {c : Nat} : {w k : Nat} → Term B c w k → Bool
  | _, _, .leaf _ => false
  | _, _, .node (.inl o) args => o.hasHeld || (TOp.pos o).any fun p => hasHeld (args p)
  | _, _, .node (.inr _) _ => false

/-- A scope term is **held-free** when the test `hasHeld` answers `false`. The test is the
    definition, so a closed term is shown held-free by `rfl`. -/
abbrev HF {c w k : Nat} (t : Term B c w k) : Prop := hasHeld t = false

/-- **A closed codec is held-free** when each term of each scope is held-free. -/
def Closed.HF : {N : Nat} → Closed B N → Prop
  | _, .nil => True
  | _, .snoc d sc => Closed.HF d ∧ ∀ i, Scoped.HF (sc i)

/-! ## Confluence -/

/-- A slot that is not a `fill` is its codec, and its field is not a `fill`. -/
theorem mkField_noFill : ∀ (m : SlotMode B) (c : Mean.C B), m.isFill = false →
    (mkField m c).isFill = false ∧ (mkField m c).codec = c
  | .req, _, _ => ⟨rfl, rfl⟩
  | .opt, _, _ => ⟨rfl, rfl⟩
  | .fill _, _, h => nomatch h

/-- **A held-free operation over restrictions of the top is a restriction of the top.** -/
theorem TOp.sub_run [TopLaws ⟨B, .host⟩] {o : TOp B} (ho : o.hasHeld = false)
    {a : o.Pos → Mean.C B} (ha : ∀ p, Sub (a p) idCodec) : Sub (TOp.run τ o a) idCodec := by
  cases o with
  | prim g => exact TopLaws.ground (S := ⟨B, .host⟩) g
  | opaq => exact fun _ _ _ h => h
  | never => exact sub_empty
  | set =>
    simp only [TOp.run]
    cases hL : Mean.set (B := B) with
    | none => exact sub_empty
    | some L => exact TopLaws.set (S := ⟨B, .host⟩) L hL _ (ha ())
  | list n s m =>
    simp only [TOp.run]
    cases hL : Mean.list (B := B) with
    | none => exact sub_empty
    | some L =>
      refine sub_listCodec (fun _ => top_list (S := ⟨B, .host⟩) L.p.into) ?_ ?_ ?_
      · intro c hc; obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact ha _
      · match s with
        | ⟨0, _⟩ => exact fun _ hc => nomatch hc
        | ⟨1, _⟩ => exact fun _ hc => by cases hc; exact ha _
      · intro c hc; obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact ha _
  | refine p pA => exact sub_trans (sub_refine2_self _ _ _) (ha ())
  | held _ _ _ => exact nomatch ho
  | legacy _ => exact nomatch ho
  | obj fs md s =>
    simp only [TOp.run]
    cases hF : Mean.map (B := B) with
    | none => exact sub_empty
    | some F =>
      have hmd : ∀ x, (md x).isFill = false := fun x =>
        Bool.eq_false_iff.mpr fun h => Bool.false_ne_true
          (ho.symm.trans (List.any_eq_true.mpr ⟨x, keyPos_complete fs x, h⟩))
      refine sub_objectCodec (fun _ => top_map (S := ⟨B, .host⟩) F.p.into)
        (decide_eq_true fun x => (mkField_noFill _ _ (hmd x)).1)
        (fun x => (mkField_noFill _ _ (hmd x)).2 ▸ ha _) ?_
      match s with
      | ⟨0, _⟩ => exact fun _ hc => nomatch hc
      | ⟨1, _⟩ => exact fun _ hc => by cases hc; exact ha _
  | union m =>
    exact sub_altCodec (fun c hc => by obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact ha p) _

/-- **A held-free scope term over restrictions of the top is a restriction of the top.** -/
theorem sub_term [TopLaws ⟨B, .host⟩] {c : Nat} {κ : Fin c → Mean.C B}
    (hκ : ∀ j, Sub (κ j) idCodec) :
    ∀ {w k : Nat} (t : Term B c w k), HF t → ∀ {ρw : Fin w → Mean.C B} {ρk : Fin k → Mean.C B},
      (∀ j, Sub (ρw j) idCodec) → (∀ j, Sub (ρk j) idCodec) →
      Sub (SFlat.interp (CStep (TStep τ) c κ) t ρw ρk) idCodec
  | _, _, .leaf j, _, _, _, _, hk => hk j
  | _, _, .node (.inr j) _, _, _, _, _, _ => hκ j
  | _, _, .node (.inl o) args, h, ρw, ρk, hw, hk => by
    simp only [HF, hasHeld, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at h
    exact TOp.sub_run τ h.1 fun p =>
      sub_term hκ (args p) (h.2 p (TOp.pos_complete o p)) (Kind.envW_all (P := (Sub · idCodec)) hw _)
        (Kind.envK_all (P := (Sub · idCodec)) hw hk _)

/-- **Confluence of a closed codec**: each entry of a held-free closed codec is a restriction of
    the top. -/
theorem Closed.sub [TopLaws ⟨B, .host⟩] : ∀ {N : Nat} (d : Closed B N), Closed.HF d →
    ∀ i, Sub (d.sol (TStep τ) Mean.d i) idCodec
  | _, .nil, _, i => i.elim0
  | _, .snoc (c := c) (n := n) d sc, hh, i => by
    have hκ := Closed.sub d hh.1
    have hst : ∀ k i, Sub (Closed.stage τ d sc k i) idCodec := by
      intro k
      induction k with
      | zero => exact fun _ => sub_empty
      | succ k ih =>
        intro ⟨i, hi⟩
        induction i using Nat.strong_induction_on with
        | _ i ihi =>
          have e := interp_nf (R := CStep (TStep τ) c (d.sol (TStep τ) Mean.d)) sc
            (Closed.stage τ d sc k) ⟨i, hi⟩
          exact (congrArg (Sub · idCodec) e).mpr <|
            sub_term τ hκ (sc ⟨i, hi⟩) (hh.2 ⟨i, hi⟩) ih (fun j => ihi j.val j.isLt _)
    refine Fin.addCases (fun m => ?_) (fun i => ?_) i
    · simp only [DSys.sol, Fin.append_left]; exact hκ m
    · simp only [DSys.sol, Fin.append_right]
      exact fun o x y h => hst _ i o x y h

/-- **Confluence of a closed codec**, at a root: the meaning is a restriction of the top. -/
theorem Closed.meaning_sub [TopLaws ⟨B, .host⟩] {N : Nat} (d : Closed B N) (h : Closed.HF d)
    (root : Fin N) : Sub (Closed.meaning τ d root) idCodec :=
  Closed.sub τ d h root

/-- **Held-free closed codecs are pairwise compatible** where the second is lawful: the common
    bound is the top, which is canonical. -/
theorem Closed.compat_of_HF [TopLaws ⟨B, .host⟩] {N N' : Nat} {d : Closed B N} {d' : Closed B N'}
    (hd : Closed.HF d) (hd' : Closed.HF d') (i : Fin N) (j : Fin N')
    (hl : Lawful Mean.mem (Closed.meaning τ d' j)) :
    Compat (Closed.meaning τ d i) (Closed.meaning τ d' j) :=
  compat_of_common_bound' (Closed.meaning_sub τ d hd i) (Closed.meaning_sub τ d' hd' j)
    canon_idCodec hl

end Calculus.Alg.Scoped
