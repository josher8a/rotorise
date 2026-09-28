import Calculus.Lang.DisjointV
import Calculus.Lang.ExactA
import Calculus.Lang.HeldFree

/-!
# Disjointness on the read side, over a universe signature

`Alg.disjoint_soundA` states that `Term.disjoint` is sound on the read side: where the test
answers `true`, no attribute is read by both operands, under every two environments that keep
each paired binder pair apart (`ApartA`). `Alg.disjoint_orthogonal` joins the two sides: the two
operands are orthogonal.

A universe supplies the laws in two classes, as on the write side. `FormerAdmA` holds the set law,
and `LeafAdmA` holds the law of two primitives apart. The row of `refine` asks the predicate of
what the inner term reads. Two data predicates that hold together nowhere keep two refinements
apart only where both inner terms read one value, which holds over a held-free closed term: such
a term reads each attribute as the top reads it (`TopLaws`).
-/

namespace Calculus.Alg

open Calculus (alignPL alignP zipP anyP objAdmV entryP)

variable {S : Syn} [Sem S] [PrimAdmA S] {ρ ρ' ρ'' : List S.C}
  {α : Table S} {β : Table S.op}

noncomputable section

/-! ## The rows that the soundness proof reads -/

/-- The bottom reads nothing. -/
@[simp] theorem AdmA_never (a : Syn.A S) : AdmA α β (.never : Term S) ρ a = false := rfl

variable (α β) in
/-- `⋁` of `AdmA` over a union's options: `AdmAny` of the dual. -/
def AdmAAny (ts : List (Term S)) (ρ : List S.C) (a : Syn.A S) : Bool :=
  AdmAny β α ts (ρ.map convU) a

/-- An empty list of options reads no attribute. -/
@[simp] theorem AdmAAny_nil (a : Syn.A S) : AdmAAny α β ([] : List (Term S)) ρ a = false := rfl

/-- The options read where the first reads or the rest read. -/
@[simp] theorem AdmAAny_cons (t : Term S) (ts : List (Term S)) (a : Syn.A S) :
    AdmAAny α β (t :: ts) ρ a = (AdmA α β t ρ a || AdmAAny α β ts ρ a) := rfl

/-- A union reads where one of its options reads. -/
theorem AdmA_union (opts : List (Term S)) (a : Syn.A S) :
    AdmA α β (.union opts) ρ a = AdmAAny α β opts ρ a := rfl

omit [PrimAdmA S] in
/-- Every environment of the dual has the converse graph of the environment of its inverse
    converses. -/
theorem unconvEnv_R (ρ'' : List S.op.C) : List.Forall₂ R ρ'' (ρ''.map convU : List S.C) :=
  List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => ⟨rfl, rfl⟩)

/-- The dual admits one set under two environments with one converse graph. -/
theorem adm_op_env {ρ₁ ρ₂ : List S.op.C} {σ : List S.C} (h₁ : List.Forall₂ R ρ₁ σ)
    (h₂ : List.Forall₂ R ρ₂ σ) (y : Term S.op) (v : Syn.A S) :
    Adm (S := S.op) β α y ρ₁ v = Adm (S := S.op) β α y ρ₂ v := by
  rw [Bool.eq_iff_iff.mpr (Adm_exact (S := S.op) (α := β) (β := α) y ρ₁ v),
    Bool.eq_iff_iff.mpr (Adm_exact (S := S.op) (α := β) (β := α) y ρ₂ v),
    (denote_R α β y h₁).1, (denote_R α β y h₂).1]

/-- **A recursive term reads where its body reads over the stage below the attribute's depth**:
    the write-side unfolding of the dual. -/
theorem AdmA_mu_unfold (b : Term S) (ρ : List S.C) (a : Syn.A S) :
    AdmA α β (.mu b) ρ a
      = AdmA α β b (muStage (fun c => denote α β b (c :: ρ)) (Syn.dA a - 1) :: ρ) a := by
  have hR := muStage_R (fun c => denote α β b (c :: ρ))
    (fun c' => denote β α b (c' :: ρ.map convU))
    (fun _ _ h => denote_R α β b (.cons h (convEnv_R ρ))) (Syn.dA a - 1)
  exact (Adm_mu_unfold (S := S.op) (α := β) (β := α) b (ρ.map convU) a).trans
    (adm_op_env (.cons hR (convEnv_R ρ)) (convEnv_R (_ :: ρ)) _ a)

end

/-! ## The laws, on the read side -/

/-- **The read-side law of the set former.** The catch-all rows of the families read the
    disjointness of the former classes (`Shapes`). -/
class FormerAdmA (S : Syn) [Sem S] [PrimAdmA S] : Prop where
  /-- Two sets whose elements share no attribute share no set. -/
  set_never : ∀ {α : Table S} {β : Table S.op} (a y : Term S), (∀ u, (AdmA α β a [] u && AdmA α β y [] u) = false) →
    ∀ c, (AdmA α β (.set a) [] c && AdmA α β (.set y) [] c) = false

/-- **The read-side law of the leaves.** A primitive reads no variable, so the law is stated at
    the closed environment. -/
class LeafAdmA (S : Syn) [Sem S] [Leaf S] [PrimAdmA S] : Prop where
  /-- Two primitives met at the bottom share no attribute. -/
  prim_none : ∀ {α : Table S} {β : Table S.op} (g g' : S.Ground), Leaf.prim g g' = none →
    ∀ c, (AdmA α β (.prim g : Term S) [] c && AdmA α β (.prim g') [] c) = false

omit [PrimAdmA S] in
/-- **The leaves of the dual**: the primitives meet as the universe's do, and the test reads no
    stored-side predicate as data. -/
instance Leaf.op [Leaf S] : Leaf S.op where
  prim := Leaf.prim (S := S)
  isData _ := false
  pmeet _ _ := none

/-- The read-side law of the leaves is the write-side law of the dual. -/
instance LeafAdmA.op [Leaf S] [LeafAdmA S] : LeafAdm S.op where
  prim_none g g' h c := LeafAdmA.prim_none (S := S) g g' h c
  pmeet_none _ _ h := nomatch h

/-- The read-side law of the set former is the write-side law of the dual. -/
instance FormerAdmA.op [FormerAdmA S] : FormerAdm S.op where
  set_never {α' β'} a y h c := FormerAdmA.set_never (S := S) (α := β') (β := α') a y h c

/-! ## Soundness, on the read side -/

/-- The environments keep each paired binder pair apart: no attribute read by both. The
    environments of converses of the dual keep the binders apart on the write side. -/
def ApartA (p : Pairing) (ρ ρ' : List S.C) : Prop :=
  ApartV (S := S.op) p (ρ.map convU) (ρ'.map convU)

omit [PrimAdmA S] in
/-- Apart environments stay apart when the left operand unfolds: its new binder pairs with
    nothing. -/
theorem ApartA.left {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') (c : S.C) :
    ApartA (shiftL p) (c :: ρ) ρ' :=
  ApartV.left (S := S.op) h (convU c)

omit [PrimAdmA S] in
/-- …and when the right operand unfolds. -/
theorem ApartA.right {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') (c : S.C) :
    ApartA (shiftR p) ρ (c :: ρ') :=
  ApartV.right (S := S.op) h (convU c)

omit [PrimAdmA S] in
/-- Two new binders that read no attribute in common extend two apart environments at a paired
    binder. -/
theorem ApartA.mu {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') {c c' : S.C}
    (hc : ∀ v, ((c.p v).isSome && (c'.p v).isSome) = false) :
    ApartA (pairMu p) (c :: ρ) (c' :: ρ') :=
  ApartV.mu (S := S.op) h (c := convU c) (c' := convU c') hc

variable (α β) in
/-- A family is sound for `x` where every partner it accepts shares no value with `x`. -/
def DisjSoundA (ρ ρ' : List S.C) (x : Term S) (f : Term S → Bool) : Prop :=
  ∀ y, f y = true → ∀ v, (AdmA α β x ρ v && AdmA α β y ρ' v) = false

/-- **A read-side family is a write-side family of the dual**, at the same term and the same
    family. -/
theorem DisjSoundA_iff {x : Term S} {f : Term S → Bool} :
    DisjSoundA α β ρ ρ' x f ↔ DisjSound (S := S.op) β α (ρ.map convU) (ρ'.map convU) x f :=
  Iff.rfl

omit [PrimAdmA S] in
/-- A held-free closed term decodes an attribute as the top decodes it. -/
theorem top_of_HF_closed [TopLaws S] {t : Term S} (hh : hasHeld t = false) (hv : t.hasVar = false)
    (ρ : List S.C) {a : Syn.A S} {u : S.V} (h : (denote α β t ρ).p a = some u) :
    (Syn.top (S := S)).p a = some u := by
  rw [denote_closed t hv ρ []] at h
  exact (sub_denoteIn (S := S) t hh [] (fun i => by simp only [envAt, List.getD_nil]; exact sub_empty)).2 a u h

omit [PrimAdmA S] in
/-- A refinement over a held-free closed term reads only what the top reads to a value that
    satisfies the predicate. -/
theorem refineReads_top [TopLaws S] {t : Term S} (hh : hasHeld t = false) (hv : t.hasVar = false)
    {ρ : List S.C} {q : S.V → Bool} {a : Syn.A S} (h : refineReads α β t ρ q a = true) :
    ∃ u, (Syn.top (S := S)).p a = some u ∧ q u = true := by
  simp only [refineReads, gate, conv] at h
  split at h
  · next u hu => exact ⟨u, top_of_HF_closed hh hv ρ hu, h⟩
  · exact nomatch h

omit [PrimAdmA S] in
/-- **Two recursive terms read apart stage by stage.** Where the two bodies keep apart every
    two binders that read no attribute in common, each two stages of the same index read none
    in common. -/
theorem stage_apartA {B B' : S.C → S.C}
    (hB : ∀ c c', (∀ u, ((c.p u).isSome && (c'.p u).isSome) = false) →
      ∀ u, (((B c).p u).isSome && ((B' c').p u).isSome) = false) :
    ∀ n u, (((muStage B n).p u).isSome && ((muStage B' n).p u).isSome) = false
  | 0, _ => rfl
  | n + 1, u => hB _ _ (stage_apartA hB n) u

/-- **A read-side family sound at every apart pairing is a write-side family of the dual**, sound
    at every apart pairing of the dual. -/
theorem disjSoundA_op {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α β ρ ρ' x (fam q)) (q : Pairing)
    (ρ'' : List S.op.C) (hq : ApartV (S := S.op) q (ρ.map convU) ρ'') :
    DisjSound (S := S.op) β α (ρ.map convU) ρ'' x (fam q) := by
  intro y' hy u
  have hq' : ApartA q ρ (ρ''.map convU) := fun i j k hk w => by
    rw [(envAt_R (convEnv_R (ρ''.map convU)) j).1, ← (envAt_R (unconvEnv_R ρ'') j).1]
    exact hq i j k hk w
  have := hf q _ hq' y' hy u
  rwa [AdmA, AdmA, adm_op_env (convEnv_R (ρ''.map convU)) (unconvEnv_R ρ'')] at this

/-- **The rows of the right operand are sound**, given a sound family for every pairing that
    keeps the environments apart: the write-side rows of the dual. -/
theorem disjSRight_soundA {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α β ρ ρ' x (fam q))
    (y : Term S) (p : Pairing) (ρ' : List S.C) (hp : ApartA p ρ ρ')
    (h : disjSRight fam p y = true) (v : Syn.A S) :
    (AdmA α β x ρ v && AdmA α β y ρ' v) = false :=
  disjSRight_sound (S := S.op) (disjSoundA_op hf) y p (ρ'.map convU) hp h v

/-- …and over the options of a union. -/
theorem disjSRightL_soundA {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α β ρ ρ' x (fam q))
    (ys : List (Term S)) (p : Pairing) (ρ' : List S.C) (hp : ApartA p ρ ρ')
    (h : disjSRightL fam p ys = true) (v : Syn.A S) :
    (AdmA α β x ρ v && AdmAAny α β ys ρ' v) = false :=
  disjSRightL_sound (S := S.op) (disjSoundA_op hf) ys p (ρ'.map convU) hp h v

/-- **The split of the right operand is sound**, given a sound family at the pairing: the
    write-side law of the dual. -/
theorem splitR_soundA {ρ ρ' : List S.C} {x : Term S} {fam : Pairing → Term S → Bool} {p : Pairing}
    (hf : DisjSoundA α β ρ ρ' x (fam p)) (y : Term S) (h : splitR fam p y = true) (v : Syn.A S) :
    (AdmA α β x ρ v && AdmA α β y ρ' v) = false :=
  splitR_sound (S := S.op) (fam := fam) hf y h v

/-- **Two data predicates that meet at the empty predicate keep two refinements apart on the
    read side**, where both inner terms are closed and held-free: both then read one value, the
    value that the top reads. -/
theorem predApart_soundA [PrimAdm S] [Leaf S] [LeafAdm S] [TopLaws S] {q : S.Pred} {ρ' : List S.C} :
    ∀ (y : Term S), predApart q y = true → ∀ a u, (Syn.top (S := S)).p a = some u →
      Syn.eval q u = true → AdmA α β y ρ' a = false
  | .refine y q₁ q₂, h, a, u, htop, hq => by
      simp only [predApart, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rw [AdmA_refine_eq]
      set q' := half S.o.c q₁ q₂
      rcases h with ⟨⟨⟨-, hh⟩, hv⟩, hm⟩ | h
      · have hn : Leaf.pmeet q q' = some none := by
          revert hm; cases Leaf.pmeet q q' with
          | none => simp
          | some o => cases o <;> simp
        have hpm := LeafAdm.pmeet_none q q' hn u
        cases hr : refineReads α β y ρ' (Syn.eval q') a with
        | false => simp
        | true =>
          obtain ⟨u', hu', hq'⟩ := refineReads_top (α := α) (β := β) hh hv hr
          rw [htop] at hu'; cases hu'
          rw [hq, hq'] at hpm; exact absurd hpm (by simp)
      · rw [predApart_soundA (ρ' := ρ') y h a u htop hq, Bool.false_and]
  | .prim _, h, _, _, _, _ | .never, h, _, _, _, _ | .set _, h, _, _, _, _
  | .list _ _ _, h, _, _, _, _ | .held _ _ _ _ _, h, _, _, _, _
  | .opaq, h, _, _, _, _ | .object _, h, _, _, _, _ | .union _, h, _, _, _, _
  | .var _, h, _, _, _, _ | .mu _, h, _, _, _, _ => by
      simp [predApart] at h

/-- **The leaf family is sound on the read side**: the leaf family of the dual. -/
theorem famPrimD_soundA [Leaf S] [LeafAdmA S] [Shapes S] {ρ ρ' : List S.C} (g : S.Ground) :
    DisjSoundA α β ρ ρ' (.prim g) (famPrimD g) :=
  DisjSoundA_iff.mpr fun y hy => famPrimD_sound (S := S.op) g y (by cases y <;> exact hy)

/-- **The variable family is sound**: the variable family of the dual. -/
theorem famVarD_soundA {ρ ρ' : List S.C} {i : Nat} {q : Pairing} (hq : ApartA q ρ ρ') :
    DisjSoundA α β ρ ρ' (.var i) (famVarD i q) :=
  DisjSoundA_iff.mpr (famVarD_sound (S := S.op) hq)

/-- **The set family is sound**: the set family of the dual. -/
theorem famSetD_soundA [FormerAdmA S] [Shapes S] {ρ ρ' : List S.C} (a : Term S)
    {mt : Term S → Bool} (hmt : DisjSoundA α β ρ ρ' a mt) :
    DisjSoundA α β ρ ρ' (.set a) (famSetD a mt) :=
  DisjSoundA_iff.mpr (famSetD_sound (S := S.op) a hmt)

/-- **The list family is sound on the read side**: the list family of the dual. -/
theorem famListD_soundA [Shapes S] {ρ ρ' : List S.C} {pre suf : List (Term S)}
    {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Bool)} {fsp : Option (Term S → Bool)}
    (hp : List.Forall₂ (DisjSoundA α β ρ ρ') pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ DisjSoundA α β ρ ρ' t f)
    (hf : List.Forall₂ (DisjSoundA α β ρ ρ') suf fsuf) :
    DisjSoundA α β ρ ρ' (.list pre sp suf) (famListD fpre fsp fsuf) :=
  DisjSoundA_iff.mpr (famListD_sound (S := S.op) (sp := sp) hp hs hf)

/-- **The object family is sound**: the object family of the dual. -/
theorem famObjD_soundA [Shapes S] {ρ ρ' : List S.C} {fa : Finset String}
    {f : {k // k ∈ fa} → ObjectSlot S} {wa : Option (Term S)}
    {g : {k // k ∈ fa} → ObjectSlot S → Bool} {mw : Term S → Bool}
    (hg : ∀ k s, g k s = true → (ObjectSlot.isReq (f k) || ObjectSlot.isReq s) = true ∧
      ∀ w, (AdmAField α β (f k) ρ w && AdmAField α β s ρ' w) = false)
    (hmw : DisjSoundA α β ρ ρ' (Body.mk fa f wa).block mw) :
    DisjSoundA α β ρ ρ' (.object (.mk fa f wa)) (famObjD (.mk fa f wa) g mw) := by
  refine DisjSoundA_iff.mpr (famObjD_sound (S := S.op) (fun k s h => ?_) hmw)
  obtain ⟨hr, hs⟩ := hg k s h
  refine ⟨by simpa only [Body.at_mk] using hr, fun w => ?_⟩
  have := hs w
  cases s <;> simpa only [AdmAField, Body.at_mk] using this

mutual
/-- **Soundness of the zero test, on the write side.** Where `disjoint` answers `true`, no value
    is admitted by both operands, under every two environments that keep the paired binders
    apart. -/
theorem disjoint_soundA [PrimAdm S] [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (x y : Term S), Term.disjoint p x y = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' → ∀ v, (AdmA α β x ρ v && AdmA α β y ρ' v) = false
  | _, .never, _, _, _, _, _, _ => by simp
  | p, .held _ _ _ _ _, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fam := fun _ _ => false)
        (fun _ _ _ _ hh => nomatch hh) y p ρ' hp h v
  | p, .var i, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fun _ _ hq => famVarD_soundA hq) y p ρ' hp h v
  | p, .mu b, y, h, ρ, ρ', hp, v => by
      cases y with
      | mu b' =>
        simp only [Term.disjoint] at h
        have hB : ∀ c c', (∀ u, ((c.p u).isSome && (c'.p u).isSome) = false) →
            ∀ u, (((denote α β b (c :: ρ)).p u).isSome && ((denote α β b' (c' :: ρ')).p u).isSome)
              = false := fun c c' hc u => by
          have := disjoint_soundA (pairMu p) b b' h (c :: ρ) (c' :: ρ') (hp.mu hc) u
          rwa [AdmA_eq_isSome, AdmA_eq_isSome] at this
        have := stage_apartA hB (Syn.dA v) v
        rw [AdmA_eq_isSome, AdmA_eq_isSome]
        exact this
      | _ =>
        simp only [Term.disjoint] at h
        rw [AdmA_mu_unfold b ρ v]
        exact disjoint_soundA (shiftL p) b _ h _ ρ' (hp.left _) v
  | p, .refine x q qA, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjoint] at h
      refine splitR_soundA (ρ := ρ) (ρ' := ρ') (x := .refine x q qA) (p := p) ?_ y h v
      intro y' hy w
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hy
      rw [AdmA_refine_eq]
      rcases hy with hy | ⟨⟨⟨-, hh⟩, hv⟩, hy⟩
      · have := disjoint_soundA p x y' hy ρ ρ' hp w
        cases h1 : AdmA α β x ρ w <;> cases h2 : AdmA α β y' ρ' w <;> simp_all
      · cases hr : refineReads α β x ρ (Syn.eval (half S.o.c q qA)) w with
        | false => simp
        | true =>
          simp only [Bool.not_eq_true'] at hh hv
          obtain ⟨u, hu, hq⟩ := refineReads_top (α := α) (β := β) hh hv hr
          rw [predApart_soundA (ρ' := ρ') y' hy w u hu hq]; simp
  | p, .union os, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjoint] at h
      rw [AdmA_union]
      exact disjointL_soundA p os y h ρ ρ' hp v
  | p, .prim g, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fun _ _ _ => famPrimD_soundA g) y p ρ' hp h v
  | p, .set a, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ)
        (fun q ρ₁ hq => famSetD_soundA a (fun u hu w => disjoint_soundA q a u hu ρ ρ₁ hq w))
        y p ρ' hp h v
  | p, .opaq, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fam := fun _ _ => false)
        (fun _ _ _ _ hh => nomatch hh) y p ρ' hp h v
  | p, .list pre sp suf, y, h, ρ, ρ', hp, v => by
      cases sp with
      | none =>
        exact disjSRight_soundA (ρ := ρ) (fun q ρ₁ hq => famListD_soundA (sp := none)
          (disjointTs_soundA q pre ρ ρ₁ hq) (Or.inl ⟨rfl, rfl⟩) (disjointTs_soundA q suf ρ ρ₁ hq))
          y p ρ' hp h v
      | some t =>
        exact disjSRight_soundA (ρ := ρ) (fun q ρ₁ hq => famListD_soundA (sp := some t)
          (disjointTs_soundA q pre ρ ρ₁ hq)
          (Or.inr ⟨t, Term.disjoint q t, rfl, rfl,
            fun u hu w => disjoint_soundA q t u hu ρ ρ₁ hq w⟩)
          (disjointTs_soundA q suf ρ ρ₁ hq)) y p ρ' hp h v
  | p, .object (.mk fs f none), y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fun q ρ₁ hq => famObjD_soundA (wa := none)
        (fun k s hs => slot_soundA q (f k) s hs ρ ρ₁ hq)
        (fun _ _ w => by simp [Body.block])) y p ρ' hp h v
  | p, .object (.mk fs f (some t)), y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fun q ρ₁ hq => famObjD_soundA (wa := some t)
        (fun k s hs => slot_soundA q (f k) s hs ρ ρ₁ hq)
        (fun u hu w => disjoint_soundA q t u hu ρ ρ₁ hq w)) y p ρ' hp h v
termination_by structural _ x => x
/-- …and a union, option by option. -/
theorem disjointL_soundA [PrimAdm S] [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (os : List (Term S)) (y : Term S), Term.disjointL p os y = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' → ∀ v, (AdmAAny α β os ρ v && AdmA α β y ρ' v) = false
  | _, [], _, _, _, _, _, _ => by simp
  | p, x :: xs, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjointL, Bool.and_eq_true] at h
      have h1 := disjoint_soundA p x y h.1 ρ ρ' hp v
      have h2 := disjointL_soundA p xs y h.2 ρ ρ' hp v
      rw [AdmAAny_cons]
      cases a1 : AdmA α β x ρ v <;> cases a2 : AdmAAny α β xs ρ v <;> cases a3 : AdmA α β y ρ' v <;> simp_all
termination_by structural _ os => os
/-- …and each position of a row, partially applied. -/
theorem disjointTs_soundA [PrimAdm S] [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (ts : List (Term S)) (ρ ρ' : List S.C), ApartA p ρ ρ' →
      List.Forall₂ (DisjSoundA α β ρ ρ') ts (Term.disjointTs p ts)
  | _, [], _, _, _ => .nil
  | p, t :: ts, ρ, ρ', hp =>
      .cons (fun u hu w => disjoint_soundA p t u hu ρ ρ' hp w) (disjointTs_soundA p ts ρ ρ' hp)
termination_by structural _ ts => ts
/-- …and two slots, where one requires the name. -/
theorem slot_soundA [PrimAdm S] [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (s s' : ObjectSlot S), ObjectSlot.disjoint p s s' = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' →
        (ObjectSlot.isReq s || ObjectSlot.isReq s') = true ∧
          ∀ w, (AdmAField α β s ρ w && AdmAField α β s' ρ' w) = false
  | p, .req x, .req y, h, ρ, ρ', hp =>
      ⟨rfl, fun w => disjoint_soundA p x y h ρ ρ' hp w⟩
  | p, .req x, .optional y, h, ρ, ρ', hp =>
      ⟨rfl, fun w => disjoint_soundA p x y h ρ ρ' hp w⟩
  | p, .optional x, .req y, h, ρ, ρ', hp =>
      ⟨by simp [ObjectSlot.isReq], fun w => disjoint_soundA p x y h ρ ρ' hp w⟩
  | _, .optional _, .optional _, h, _, _, _ => by simp [ObjectSlot.disjoint] at h
termination_by structural _ s => s
end


/-- **Orthogonality, decided.** Where `disjoint` answers `true`, no value is written by both
    operands and no attribute is read by both, under environments that keep the paired binders
    apart on the matching side. -/
theorem disjoint_orthogonal [PrimAdm S] [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdm S] [FormerAdmA S]
    [Shapes S] [TopLaws S] {p : Pairing} {x y : Term S} (h : Term.disjoint p x y = true) :
    (∀ ρ ρ', ApartV p ρ ρ' → ∀ v, (Adm α β x ρ v && Adm α β y ρ' v) = false) ∧
    (∀ ρ ρ', ApartA p ρ ρ' → ∀ a, (AdmA α β x ρ a && AdmA α β y ρ' a) = false) :=
  ⟨fun ρ ρ' hp v => disjoint_sound p x y h ρ ρ' hp v,
   fun ρ ρ' hp a => disjoint_soundA p x y h ρ ρ' hp a⟩

end Calculus.Alg
