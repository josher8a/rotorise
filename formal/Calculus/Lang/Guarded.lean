import Calculus.Lang.Term

/-!
# The guard makes the body of a binder contractive, for every universe

`Term.guarded` is a check on syntax, and `Contractive` is the premise that `muCodec` asks of a
body. `contractive_body` connects the two: at a guarded `mu b`, the body
`fun c => denote b (c :: ρ)` reads `c` only one layer down.

The proof is one congruence, `denote_agree`, by one mutual induction over the term family. Its
hypothesis gives each variable the agreement that the variable's level asks (`UseAgree`). A
container passes its elements an input one layer shallower. A `held` passes its terms an input of
any depth, so it asks agreement everywhere. A nested `mu` keeps the depth, because its stages
agree stage by stage. The universe enters at three places: the depth facts of the list prisms,
the depth facts of the keyed-map prisms, and the agreement law of the set lift.
-/

namespace Calculus.Alg

variable {S : Syn} [Sem S] {α : Table S}

/-- What a level of `Term.use` asks of the two codecs that stand for one variable: nothing where
    the variable does not occur, agreement one layer down under a container, agreement at the
    input's depth where it reads the input, and agreement everywhere under a `held`. -/
def UseAgree : Nat → Nat → S.C → S.C → Prop
  | 0, _, _, _ => True
  | 1, d, c₁, c₂ => AgreeLe (Mean.d (B := S.sig)) (d - 1) c₁ c₂
  | 2, d, c₁, c₂ => AgreeLe (Mean.d (B := S.sig)) d c₁ c₂
  | _ + 3, _, c₁, c₂ => ∀ d', AgreeLe (Mean.d (B := S.sig)) d' c₁ c₂

namespace UseAgree

variable {d : Nat} {c₁ c₂ : S.C}

/-- A codec meets every level against itself. -/
theorem refl (u d : Nat) (c : S.C) : UseAgree u d c c :=
  match u with
  | 0 => trivial
  | 1 => AgreeLe.refl _ _
  | 2 => AgreeLe.refl _ _
  | _ + 3 => fun _ => AgreeLe.refl _ _

/-- Agreement everywhere meets every level. -/
theorem of_all {u : Nat} (h : ∀ d', AgreeLe (Mean.d (B := S.sig)) d' c₁ c₂) :
    UseAgree u d c₁ c₂ :=
  match u with
  | 0 => trivial
  | 1 => h _
  | 2 => h _
  | _ + 3 => h

/-- A higher level asks more. -/
theorem mono {u u' : Nat} (h : UseAgree u' d c₁ c₂) (hu : u ≤ u') : UseAgree u d c₁ c₂ :=
  match u, u', hu, h with
  | 0, _, _, _ => trivial
  | 1, 1, _, h => h
  | 1, 2, _, h => AgreeLe.mono h (Nat.sub_le d 1)
  | 1, _ + 3, _, h => h _
  | 2, 2, _, h => h
  | 2, _ + 3, _, h => h _
  | _ + 3, _ + 3, _, h => h

/-- Under a container, a level asks one layer less of the elements. -/
theorem of_under {u w : Nat} (h : UseAgree (useUnder w) (d + 1) c₁ c₂) (hu : u ≤ w) :
    UseAgree u d c₁ c₂ := by
  refine mono ?_ hu
  unfold useUnder at h
  match w, h with
  | 0, _ => trivial
  | 1, h => exact AgreeLe.mono h (by omega)
  | 2, h => exact h
  | _ + 3, h => exact h

/-- Under a `held`, an occurring variable asks agreement everywhere, whatever the depth. -/
theorem of_held {u v d' : Nat} (h : UseAgree (useHeld (max u v)) d c₁ c₂) :
    UseAgree u d' c₁ c₂ := by
  match u, h with
  | 0, _ => trivial
  | _ + 1, h =>
    unfold useHeld at h
    rw [if_neg (by omega)] at h
    exact of_all h

end UseAgree

/-- Any two codecs agree below depth zero, because every input of a universe has a depth of at
    least one. -/
theorem agreeLe_zero (c₁ c₂ : S.C) : AgreeLe (Mean.d (B := S.sig)) 0 c₁ c₂ :=
  AgreeLe.zero Mean.d_pos c₁ c₂

variable {β : Table S.op}

mutual

/-- **Guarded congruence.** Two environments that give each variable the agreement its level asks
    give one answer below `d`. -/
theorem denote_agree : ∀ (t : Term S), t.guarded = true → ∀ (d : Nat) (ρ₁ ρ₂ : List S.C),
    (∀ i, UseAgree (t.use i) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    AgreeLe (Mean.d (B := S.sig)) d (denote α β t ρ₁) (denote α β t ρ₂)
  | .prim _, _, _, _, _, _ => .refl _ _
  | .opaq, _, _, _, _, _ => .refl _ _
  | .never, _, _, _, _, _ => .refl _ _
  | .var j, _, _, _, _, h => by
      have hj := h j
      simp only [Term.use] at hj
      exact hj
  | .mu b, hg, d, ρ₁, ρ₂, h => by
      simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      refine agreeLe_muCodec fun c₁ c₂ hc => denote_agree b hg.2 d (c₁ :: ρ₁) (c₂ :: ρ₂) ?_
      intro i
      match i with
      | 0 => exact UseAgree.mono (u' := 2) hc (by omega)
      | i + 1 => exact h i
  | .refine t p pA, hg, d, ρ₁, ρ₂, h =>
      agreeLe_refine2 (denote_agree t hg d ρ₁ ρ₂ h) (Mean.eval false p) (Mean.eval true pA)
  | .held s t P k₀ k, hg, _, ρ₁, ρ₂, h => by
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have ht := AgreeLe.eq_of_forall fun d' =>
        denote_agree t hg.1 d' ρ₁ ρ₂ fun i => UseAgree.of_held (h i)
      have hP := AgreeLe.eq_of_forall fun d' =>
        denote_agree P hg.2 d' ρ₁ ρ₂ fun i =>
          UseAgree.of_held (v := t.use i) (by rw [Nat.max_comm]; exact h i)
      refine AgreeLe.of_eq ?_ ?_
      · simp only [denote, denoteAbs, held1, refine2_e_def, adapt2_f, ht.1, hP.1, hP.2]
      · simp only [denote, denoteAbs, held1, refine2_p_def, adapt2_f, ht.2, hP.1, hP.2]
  | .list pre sp suf, hg, d, ρ₁, ρ₂, h => by
      simp only [Term.guarded, Bool.and_eq_true] at hg
      match d with
      | 0 => exact agreeLe_zero _ _
      | d + 1 =>
        simp only [denote, denoteAbs]
        cases Mean.list (B := S.sig) with
        | none => exact AgreeLe.refl _ _
        | some L =>
          exact agreeLe_listCodec L.d_lt
            (denoteList_agree pre hg.1.1 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (by omega))
            (denoteOpt_agree sp hg.1.2 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (by omega))
            (denoteList_agree suf hg.2 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (by omega))
  | .set t, hg, d, ρ₁, ρ₂, h => by
      match d with
      | 0 => exact agreeLe_zero _ _
      | d + 1 =>
        simp only [denote, denoteAbs]
        cases Mean.set (B := S.sig) with
        | none => exact AgreeLe.refl _ _
        | some L =>
          exact L.agree (denote_agree t hg d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) le_rfl)
  | .union opts, hg, d, ρ₁, ρ₂, h =>
      agreeLe_altCodec _ _ (denoteList_agree opts hg d ρ₁ ρ₂ h)
  | .object b, hg, d, ρ₁, ρ₂, h =>
      match d with
      | 0 => agreeLe_zero _ _
      | d + 1 => bodySem_agree b hg d ρ₁ ρ₂ h

/-- The payload's congruence: each slot and the open block read one layer below the map. -/
theorem bodySem_agree : ∀ (b : Body S), b.guarded = true → ∀ (d : Nat) (ρ₁ ρ₂ : List S.C),
    (∀ i, UseAgree (useUnder (b.use i)) (d + 1) (envAt ρ₁ i) (envAt ρ₂ i)) →
    AgreeLe (Mean.d (B := S.sig)) (d + 1) (bodySem α β b ρ₁) (bodySem α β b ρ₂)
  | .mk fields f wild, hg, d, ρ₁, ρ₂, h => by
      simp only [Body.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      simp only [bodySem, bodySemAbs]
      cases Mean.map (B := S.sig) with
      | none => exact AgreeLe.refl _ _
      | some F =>
        exact agreeLe_objectCodec F.d_lt
          (fun k => fieldSem_agree (f k) (hg.1 k) d ρ₁ ρ₂ fun i => UseAgree.of_under (h i)
            (le_max_of_le_left (Finset.le_sup (f := fun k => ObjectSlot.use i (f k))
              (Finset.mem_attach _ k))))
          (wildSem_agree wild hg.2 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (le_max_right _ _))

/-- A slot's congruence is its term's. -/
theorem fieldSem_agree : ∀ (s : ObjectSlot S), s.guarded = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List S.C),
    (∀ i, UseAgree (s.use i) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    FieldSem.Rel (AgreeLe (Mean.d (B := S.sig)) d) (fieldSem α β s ρ₁)
      (fieldSem α β s ρ₂)
  | .req t, hg, d, ρ₁, ρ₂, h => denote_agree t hg d ρ₁ ρ₂ h
  | .optional t, hg, d, ρ₁, ρ₂, h => denote_agree t hg d ρ₁ ρ₂ h

/-- The open block's congruence is its term's. -/
theorem wildSem_agree : ∀ (w : Option (Term S)), Term.guardedO w = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List S.C),
    (∀ i, UseAgree (Term.useO i w) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    RestSem.Rel (AgreeLe (Mean.d (B := S.sig)) d) (wildSem α β w ρ₁)
      (wildSem α β w ρ₂)
  | none, _, _, _, _, _ => trivial
  | some t, hg, d, ρ₁, ρ₂, h => denote_agree t hg d ρ₁ ρ₂ h

/-- The congruence of a list of terms, position by position. -/
theorem denoteList_agree : ∀ (ts : List (Term S)), Term.guardedL ts = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List S.C),
    (∀ i, UseAgree (Term.useL i ts) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    List.Forall₂ (AgreeLe (Mean.d (B := S.sig)) d) (denoteList α β ts ρ₁)
      (denoteList α β ts ρ₂)
  | [], _, _, _, _, _ => .nil
  | t :: ts, hg, d, ρ₁, ρ₂, h => by
      simp only [Term.guardedL, Bool.and_eq_true] at hg
      exact .cons (denote_agree t hg.1 d ρ₁ ρ₂ fun i => (h i).mono (le_max_left _ _))
        (denoteList_agree ts hg.2 d ρ₁ ρ₂ fun i => (h i).mono (le_max_right _ _))

/-- The congruence of an optional term. -/
theorem denoteOpt_agree : ∀ (sp : Option (Term S)), Term.guardedO sp = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List S.C),
    (∀ i, UseAgree (Term.useO i sp) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    Option.Rel (AgreeLe (Mean.d (B := S.sig)) d) (denoteOpt α β sp ρ₁)
      (denoteOpt α β sp ρ₂)
  | none, _, _, _, _, _ => .none
  | some t, hg, d, ρ₁, ρ₂, h => .some (denote_agree t hg d ρ₁ ρ₂ h)

end

/-- **The guard gives a contractive body.** At a guarded `mu b`, the body reads its variable one
    layer down, and every other variable is the same on both sides. -/
theorem contractive_body {b : Term S} (hg : (Term.mu b).guarded = true) (ρ : List S.C) :
    Contractive (Mean.d (B := S.sig)) fun c => denote α β b (c :: ρ) := by
  simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
  intro d c₁ c₂ hc
  refine denote_agree b hg.2 (d + 1) (c₁ :: ρ) (c₂ :: ρ) fun i => ?_
  match i with
  | 0 => exact UseAgree.mono (u' := 1) hc hg.1
  | i + 1 => exact UseAgree.refl _ _ _

end Calculus.Alg
