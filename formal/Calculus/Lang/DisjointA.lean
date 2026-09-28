import Calculus.Lang.DisjointV
import Calculus.Lang.ExactA
import Calculus.Lang.HeldFree

/-!
# Disjointness on the read side, over a universe signature

`Alg.disjoint_soundA` states that `Term.disjoint` is sound on the read side: where the test
answers `true`, no attribute is read by both operands, under every two environments that keep
each paired binder pair apart (`ApartA`). `Alg.disjoint_orthogonal` joins the two sides: the two
operands are orthogonal.

The test reads no orientation, so the read-side soundness is the write-side soundness at the dual,
and this module owns no induction. A universe supplies the read-side laws as the write-side laws of
the dual: `FormerAdmA` holds the set law, and `LeafAdmA` holds the primitive law. The write side at
the dual reads the top bound at the dual (`TopBound.op`). The graph of a held-free closed term lies
inside the graph of the top at either orientation, because the dual denotation and the dual top
are the converses of the denotation and the top (`TopLaws`).
-/

namespace Calculus.Alg

open Calculus (alignPL alignP zipP anyP objAdmV entryP)

variable {S : Syn} [Sem S] [PrimAdmA S] {ρ ρ' ρ'' : List S.C}
  {α : Table S} {β : Table S.op}

noncomputable section

/-! ## The rows of the read side -/

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

/-- **The read-side law of the set former is the write-side law of the dual**: two sets whose
    elements share no attribute share no set. -/
abbrev FormerAdmA (S : Syn) [Sem S] [PrimAdmA S] : Prop := FormerAdm S.op

/-- **The read-side laws of the leaves are the write-side laws of the dual.** The leaves are
    absolute, so the dual has the leaves of the universe, and the stored-side predicates meet
    as the universe states. -/
abbrev LeafAdmA (S : Syn) [Sem S] [Leaf S] [PrimAdmA S] : Prop := LeafAdm S.op

/-! ## The top bound, at both orientations -/

omit [PrimAdmA S] in
/-- **A held-free closed term lies below the top**, from the laws of the top. -/
instance TopBound.ofLaws [TopLaws S] : TopBound S where
  sub_top t hh hv ρ := by
    rw [denote_closed t hv ρ []]
    exact sub_denoteIn (S := S) t hh [] fun i => by
      simp only [envAt, List.getD_nil]; exact sub_empty

omit [PrimAdmA S] in
/-- **The graph of a term is absolute**: at the dual, a held-free closed term lies below the top,
    because the denotation and the top at the dual are the converses of those at the universe. -/
instance TopBound.op [TopLaws S] : TopBound S.op where
  sub_top {α' β'} t hh hv ρ := by
    rw [denote_closed (S := S.op) t hv ρ []]
    have hR := denote_R (S := S) β' α' t (ρ' := []) (ρ := []) .nil
    have hT := readC_R S.o (Mean.top (B := S.sig))
    have hs := TopBound.sub_top (S := S) (α := β') (β := α') t hh hv []
    exact ⟨fun v a h => by rw [hT.1]; rw [hR.1] at h; exact hs.2 v a h,
      fun a v h => by rw [hT.2]; rw [hR.2] at h; exact hs.1 a v h⟩

/-! ## Soundness, on the read side -/

/-- The environments keep each paired binder pair apart: no attribute read by both. The
    environments of converses of the dual keep the binders apart on the write side. -/
def ApartA (p : Pairing) (ρ ρ' : List S.C) : Prop :=
  ApartV (S := S.op) p (ρ.map convU) (ρ'.map convU)

/-- **Soundness of the zero test, on the read side**: the write-side soundness of the dual. The
    test reads no orientation, so the test at the dual is the test. Where `disjoint` answers
    `true`, no attribute is read by both operands, under every two environments that keep the
    paired binders apart. -/
theorem disjoint_soundA [Leaf S] [LeafAdmA S] [LeafMeet S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (x y : Term S), Term.disjoint p x y = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' → ∀ v, (AdmA α β x ρ v && AdmA α β y ρ' v) = false :=
  fun p x y h ρ ρ' hp v =>
    disjoint_sound (S := S.op) (α := β) (β := α) p x y h (ρ.map convU) (ρ'.map convU) hp v

/-- **Orthogonality, decided.** Where `disjoint` answers `true`, no value is written by both
    operands and no attribute is read by both, under environments that keep the paired binders
    apart on the matching side. -/
theorem disjoint_orthogonal [PrimAdm S] [Leaf S] [LeafAdm S] [LeafAdmA S] [LeafMeet S]
    [FormerAdm S] [FormerAdmA S] [Shapes S] [TopLaws S] {p : Pairing} {x y : Term S}
    (h : Term.disjoint p x y = true) :
    (∀ ρ ρ', ApartV p ρ ρ' → ∀ v, (Adm α β x ρ v && Adm α β y ρ' v) = false) ∧
    (∀ ρ ρ', ApartA p ρ ρ' → ∀ a, (AdmA α β x ρ a && AdmA α β y ρ' a) = false) :=
  ⟨fun ρ ρ' hp v => disjoint_sound p x y h ρ ρ' hp v,
   fun ρ ρ' hp a => disjoint_soundA p x y h ρ ρ' hp a⟩

end Calculus.Alg
