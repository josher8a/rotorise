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
inside the graph of the top at either orientation, because the dual denotes each term by the same
codec (`TopLaws`).
-/

namespace Calculus.Alg

open Calculus (alignPL alignP zipP anyP objAdmV entryP)

variable {S : Syn} [Sem S] [PrimAdmA S] {ρ ρ' ρ'' : List S.C}
  {α : Table S} {β : Table S.op}

section

/-! ## The rows of the read side -/

/-- **A recursive term reads where its body reads over the stage below the attribute's depth**:
    the write-side unfolding of the dual. -/
theorem AdmA_mu_unfold (b : Term S) (ρ : List S.C) (a : S.V) :
    AdmA α β (.mu b) ρ a
      = AdmA α β b (muStage (fun c => denote α β b (c :: ρ)) (Syn.d a - 1) :: ρ) a := by
  have hB : (fun c => denote (S := S.op) β α b (c :: ρ)) = fun c => denote α β b (c :: ρ) :=
    funext fun c => denote_op b (c :: ρ)
  have h := Adm_mu_unfold (S := S.op) (α := β) (β := α) b ρ a
  rw [hB] at h
  exact h

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
    rw [denote_of_closed t hv ρ []]
    exact sub_denoteIn (S := S) t hh [] fun i => by
      simp only [envAt, List.getD_nil]; exact sub_empty

omit [PrimAdmA S] in
/-- **The graph of a term is absolute**: at the dual, a held-free closed term lies below the top,
    because the dual denotes each term by the same codec, and the top is the top of the meaning. -/
instance TopBound.op [TopLaws S] : TopBound S.op where
  sub_top {α' β'} t hh hv ρ := by
    rw [denote_op]
    exact TopBound.sub_top (S := S) t hh hv ρ

/-! ## Soundness, on the read side -/

/-- The environments keep each paired binder pair apart: no attribute read by both. The
    environments keep the binders apart on the write side of the dual. -/
def ApartA (p : Pairing) (ρ ρ' : List S.C) : Prop :=
  ApartV (S := S.op) p ρ ρ'

/-- **Soundness of the zero test, on the read side**: the write-side soundness of the dual. The
    test reads no orientation, so the test at the dual is the test. Where `disjoint` answers
    `true`, no attribute is read by both operands, under every two environments that keep the
    paired binders apart. -/
theorem disjoint_soundA [Leaf S] [LeafAdmA S] [LeafMeet S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (x y : Term S), Term.disjoint p x y = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' → ∀ v, (AdmA α β x ρ v && AdmA α β y ρ' v) = false :=
  fun p x y h ρ ρ' hp v =>
    disjoint_sound (S := S.op) (α := β) (β := α) p x y h ρ ρ' hp v

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
