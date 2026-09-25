import Calculus.Denote

/-!
# The guard makes the body of a binder contractive

`Term.guarded` is a check on syntax, and `Contractive` is the premise that `Recursion.lean` asks
of a body. `contractive_body` connects the two: at a guarded `mu b`, the body
`fun c => denote b (c :: ρ)` reads `c` only one layer down.

The proof is one congruence, `denote_agree`, by one mutual induction over the term family. Its
hypothesis gives each variable the agreement that the variable's level asks (`UseAgree`). A
container passes its elements an input one layer shallower. A `held` passes its terms an input of
any depth, so it asks agreement everywhere. A nested `mu` keeps the depth, because its stages
agree stage by stage.
-/

namespace Calculus

/-- What a level of `Term.use` asks of the two codecs that stand for one variable: nothing where
    the variable does not occur, agreement one layer down under a container, agreement at the
    input's depth where it reads the input, and agreement everywhere under a `held`. -/
def UseAgree : Nat → Nat → Codec → Codec → Prop
  | 0, _, _, _ => True
  | 1, d, c₁, c₂ => AgreeLe (d - 1) c₁ c₂
  | 2, d, c₁, c₂ => AgreeLe d c₁ c₂
  | _ + 3, _, c₁, c₂ => ∀ d', AgreeLe d' c₁ c₂

namespace UseAgree

variable {d : Nat} {c₁ c₂ : Codec}

/-- A codec meets every level against itself. -/
theorem refl (u d : Nat) (c : Codec) : UseAgree u d c c :=
  match u with
  | 0 => trivial
  | 1 => AgreeLe.refl _ _
  | 2 => AgreeLe.refl _ _
  | _ + 3 => fun _ => AgreeLe.refl _ _

/-- Agreement everywhere meets every level. -/
theorem of_all {u : Nat} (h : ∀ d', AgreeLe d' c₁ c₂) : UseAgree u d c₁ c₂ :=
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

mutual

/-- **Guarded congruence.** Two environments that give each variable the agreement its level asks
    give one answer below `d`. -/
theorem denote_agree : ∀ (t : Term), t.guarded = true → ∀ (d : Nat) (ρ₁ ρ₂ : List Codec),
    (∀ i, UseAgree (t.use i) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    AgreeLe d (denote t ρ₁) (denote t ρ₂)
  | .string, _, _, _, _, _ => .refl _ _
  | .number, _, _, _, _, _ => .refl _ _
  | .boolean, _, _, _, _, _ => .refl _ _
  | .binary, _, _, _, _, _ => .refl _ _
  | .null, _, _, _, _, _ => .refl _ _
  | .literal _ _, _, _, _, _, _ => .refl _ _
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
  | .refine t p, hg, d, ρ₁, ρ₂, h => agreeLe_restrict (denote_agree t hg d ρ₁ ρ₂ h) p.eval
  | .held t P f g, hg, _, ρ₁, ρ₂, h => by
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have ht := AgreeLe.eq_of_forall fun d' =>
        denote_agree t hg.1 d' ρ₁ ρ₂ fun i => UseAgree.of_held (h i)
      have hP := AgreeLe.eq_of_forall fun d' =>
        denote_agree P hg.2 d' ρ₁ ρ₂ fun i =>
          UseAgree.of_held (v := t.use i) (by rw [Nat.max_comm]; exact h i)
      refine AgreeLe.of_eq ?_ ?_
      · simp only [denote, Alg.Codec.restrict, Alg.Codec.through, ht.1, hP.1]
      · simp only [denote, Alg.Codec.restrict, Alg.Codec.through, ht.2, hP.1]
  | .list pre sp suf, hg, d, ρ₁, ρ₂, h => by
      simp only [Term.guarded, Bool.and_eq_true] at hg
      match d with
      | 0 => exact AgreeLe.zero _ _
      | d + 1 =>
        exact agreeLe_listCodec
          (denoteList_agree pre hg.1.1 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (by omega))
          (denoteOpt_agree sp hg.1.2 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (by omega))
          (denoteList_agree suf hg.2 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (by omega))
  | .set t, hg, d, ρ₁, ρ₂, h =>
      match d with
      | 0 => AgreeLe.zero _ _
      | d + 1 => agreeLe_setCodec (denote_agree t hg d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) le_rfl)
  | .union opts, hg, d, ρ₁, ρ₂, h =>
      agreeLe_altCodec _ _ (denoteList_agree opts hg d ρ₁ ρ₂ h)
  | .object b, hg, d, ρ₁, ρ₂, h =>
      match d with
      | 0 => AgreeLe.zero _ _
      | d + 1 => bodySem_agree b hg d ρ₁ ρ₂ h

/-- The payload's congruence: each slot and the open block read one layer below the map. -/
theorem bodySem_agree : ∀ (b : Body), b.guarded = true → ∀ (d : Nat) (ρ₁ ρ₂ : List Codec),
    (∀ i, UseAgree (useUnder (b.use i)) (d + 1) (envAt ρ₁ i) (envAt ρ₂ i)) →
    AgreeLe (d + 1) (bodySem b ρ₁) (bodySem b ρ₂)
  | .mk fields f wild, hg, d, ρ₁, ρ₂, h => by
      simp only [Body.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact agreeLe_objectCodec
        (fun k => fieldSem_agree (f k) (hg.1 k) d ρ₁ ρ₂ fun i => UseAgree.of_under (h i)
          (le_max_of_le_left (Finset.le_sup (f := fun k => ObjectSlot.use i (f k))
            (Finset.mem_attach _ k))))
        (wildSem_agree wild hg.2 d ρ₁ ρ₂ fun i => UseAgree.of_under (h i) (le_max_right _ _))

/-- A slot's congruence is its term's. -/
theorem fieldSem_agree : ∀ (s : ObjectSlot), s.guarded = true → ∀ (d : Nat) (ρ₁ ρ₂ : List Codec),
    (∀ i, UseAgree (s.use i) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    FieldSem.Rel (AgreeLe d) (fieldSem s ρ₁) (fieldSem s ρ₂)
  | .req t, hg, d, ρ₁, ρ₂, h => denote_agree t hg d ρ₁ ρ₂ h
  | .optional t, hg, d, ρ₁, ρ₂, h => denote_agree t hg d ρ₁ ρ₂ h

/-- The open block's congruence is its term's. -/
theorem wildSem_agree : ∀ (w : Option Term), Term.guardedO w = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List Codec),
    (∀ i, UseAgree (Term.useO i w) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    RestSem.Rel (AgreeLe d) (wildSem w ρ₁) (wildSem w ρ₂)
  | none, _, _, _, _, _ => trivial
  | some t, hg, d, ρ₁, ρ₂, h => denote_agree t hg d ρ₁ ρ₂ h

/-- The congruence of a list of terms, position by position. -/
theorem denoteList_agree : ∀ (ts : List Term), Term.guardedL ts = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List Codec),
    (∀ i, UseAgree (Term.useL i ts) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    List.Forall₂ (AgreeLe d) (denoteList ts ρ₁) (denoteList ts ρ₂)
  | [], _, _, _, _, _ => .nil
  | t :: ts, hg, d, ρ₁, ρ₂, h => by
      simp only [Term.guardedL, Bool.and_eq_true] at hg
      exact .cons (denote_agree t hg.1 d ρ₁ ρ₂ fun i => (h i).mono (le_max_left _ _))
        (denoteList_agree ts hg.2 d ρ₁ ρ₂ fun i => (h i).mono (le_max_right _ _))

/-- The congruence of an optional term. -/
theorem denoteOpt_agree : ∀ (sp : Option Term), Term.guardedO sp = true →
    ∀ (d : Nat) (ρ₁ ρ₂ : List Codec),
    (∀ i, UseAgree (Term.useO i sp) d (envAt ρ₁ i) (envAt ρ₂ i)) →
    Option.Rel (AgreeLe d) (denoteOpt sp ρ₁) (denoteOpt sp ρ₂)
  | none, _, _, _, _, _ => .none
  | some t, hg, d, ρ₁, ρ₂, h => .some (denote_agree t hg d ρ₁ ρ₂ h)

end

/-- **The guard gives a contractive body.** At a guarded `mu b`, the body reads its variable one
    layer down, and every other variable is the same on both sides. -/
theorem contractive_body {b : Term} (hg : (Term.mu b).guarded = true) (ρ : List Codec) :
    Contractive fun c => denote b (c :: ρ) := by
  simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
  intro d c₁ c₂ hc
  refine denote_agree b hg.2 (d + 1) (c₁ :: ρ) (c₂ :: ρ) fun i => ?_
  match i with
  | 0 => exact UseAgree.mono (u' := 1) hc hg.1
  | i + 1 => exact UseAgree.refl _ _ _

end Calculus
