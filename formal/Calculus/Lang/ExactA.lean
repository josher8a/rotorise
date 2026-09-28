import Calculus.Lang.ExactV
import Calculus.Lang.Converse

/-!
# Exactness on the attribute side, over a universe signature

`AdmA` is the attribute half of `Adm`: a row per constructor that equals `dom(p)` of
`denote t`. The attribute row of a term is the value row of its converse in the dual universe,
under the environment of converses. So `AdmA_exact` is `Adm_exact` at the dual, composed with
`denote_tconv`, and the attribute side owns no induction. A universe supplies the value rows of
the primitives of its dual (`PrimAdmA`), and nothing else.
-/

namespace Calculus.Alg

/-- **The attribute-side row of each primitive**, and its exactness: the value-side rows of the
    dual universe. -/
abbrev PrimAdmA (S : Syn) [Sem S] [SynA S] [SemA S] := PrimAdm S.op

variable {S : Syn} [Sem S] [SynA S] [SemA S] {α : Table S} {β : Table S.op}

omit [SynA S] [SemA S] in
/-- The environment of converses is related to the environment by the converse graph. -/
theorem convEnv_R : ∀ ρ : List S.C, List.Forall₂ R (ρ.map conv) ρ
  | [] => .nil
  | c :: ρ => .cons (R_conv c) (convEnv_R ρ)

variable (α β) in
/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out. -/
noncomputable def refineReads (t : Term S) (ρ : List S.C) (q : S.V → Bool) (a : Sem.A S) :
    Bool :=
  gate (conv (denote α β t ρ)) q a

/-- `refineReads` is the gate of the converse term. -/
theorem refineReads_eq_gate (t : Term S) (ρ : List S.C) (q : S.V → Bool) (a : Sem.A S) :
    gate (denote β α (tconv t) (ρ.map conv)) q a = refineReads α β t ρ q a := by
  unfold refineReads gate
  rw [(denote_tconv α β t (convEnv_R ρ)).1]
  rfl

omit [SemA S] in
/-- The guard of the payload row reads the kind of each slot, and the converse keeps the kind. -/
theorem valPresentT_tconv (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) :
    valPresentT fields (fun k => tconvS (fld k)) keys = valPresentT fields fld keys := by
  simp only [valPresentT]
  congr 1
  refine propext (forall_congr' fun k => ?_)
  generalize fld k = s
  cases s <;> rfl

variable [PrimAdmA S]

noncomputable section

variable (α β) in
/-- **The joint admission predicate, attribute side**, under an environment `ρ`: the value row
    of the converse term in the dual universe, under the environment of converses. -/
def AdmA (t : Term S) (ρ : List S.C) : Sem.A S → Bool := Adm β α (tconv t) (ρ.map conv)

variable (α β) in
/-- The read side's payload row; `AdmBody`'s mirror. -/
def AdmABody (b : Body S) (ρ : List S.C) : Sem.A S → Bool := AdmBody β α (tconvB b) (ρ.map conv)

variable (α β) in
/-- A slot's read row is its term's. -/
def AdmAField (s : ObjectSlot S) (ρ : List S.C) : Sem.A S → Bool :=
  AdmField β α (tconvS s) (ρ.map conv)

variable (α β) in
/-- The open block's read row, where the body has one. -/
def AdmAWild (w : Option (Term S)) (ρ : List S.C) : Option (Sem.A S → Bool) :=
  AdmWild β α (tconvO w) (ρ.map conv)

variable (α β) in
/-- The options' read rows, in order. -/
def AdmAList (ts : List (Term S)) (ρ : List S.C) : List (Sem.A S → Bool) :=
  AdmList β α (tconvL ts) (ρ.map conv)

variable (α β) in
/-- The spread's read row, where there is one. -/
def AdmAOptT (o : Option (Term S)) (ρ : List S.C) : Option (Sem.A S → Bool) :=
  AdmOptT β α (tconvO o) (ρ.map conv)

@[simp] theorem AdmAList_eq (ρ : List S.C) :
    ∀ ts : List (Term S), AdmAList α β ts ρ = ts.map (AdmA α β · ρ)
  | [] => rfl
  | t :: ts => congrArg (AdmA α β t ρ :: ·) (AdmAList_eq ρ ts)

/-- A refinement reads what its inner term reads, its stored predicate holds on, and its
    predicate holds on the read. -/
theorem AdmA_refine_eq (t : Term S) (q : S.Pred) (qA : SynA.PredA S) (ρ : List S.C)
    (a : Sem.A S) :
    AdmA α β (.refine t q qA) ρ a =
      (AdmA α β t ρ a && (SemA.evalA qA a && refineReads α β t ρ (Sem.eval q) a)) := by
  rw [← refineReads_eq_gate]
  simp only [AdmA, tconv, Adm, Bool.and_assoc]
  rfl

/-- A held term reads what its stored outer reads, where the inner term reads the stored word's
    image, and the caller outer admits the caller word's image of the read. -/
theorem AdmA_held_eq [PrimAdm S] (t P PA : Term S) (k : Word S) (kA : Word S.op) (ρ : List S.C)
    (a : Sem.A S) :
    AdmA α β (.held t P PA k kA) ρ a =
      (AdmA α β PA ρ a && AdmA α β t ρ ((β.word kA).1 a) &&
        refineReads α β t ρ (fun w => Adm α β P ρ ((α.word k).2 w)) ((β.word kA).1 a)) := by
  have hP : (fun w => ((denote β α (tconv P) (ρ.map conv)).p ((α.word k).2 w)).isSome) =
      fun w => Adm α β P ρ ((α.word k).2 w) := by
    funext w
    rw [(denote_tconv α β P (convEnv_R ρ)).2, Adm_eq_isSome]
  rw [← hP, ← refineReads_eq_gate]
  simp only [AdmA, tconv, Adm]
  rw [Bool.and_comm (Adm β α (tconv t) _ _)]
  rfl

variable (α β) in
/-- The row is `dom(p)`, not a bound on it, under the environment `ρ`. -/
def ExactA (t : Term S) (ρ : List S.C) : Prop :=
  ∀ a, AdmA α β t ρ a = true ↔ ((denote α β t ρ).p a).isSome

/-- **Every attribute row is exact**, at every universe: the value law at the dual, through
    `denote_tconv`. -/
theorem AdmA_exact (t : Term S) (ρ : List S.C) : ExactA α β t ρ := fun a =>
  (Adm_exact (α := β) (β := α) (tconv t) (ρ.map conv) a).trans (by rw [(denote_tconv α β t (convEnv_R ρ)).1])

/-- The row, read as a Boolean: the read domain of the denotation. -/
theorem AdmA_eq_isSome (t : Term S) (ρ : List S.C) (a : Sem.A S) :
    AdmA α β t ρ a = ((denote α β t ρ).p a).isSome :=
  Bool.eq_iff_iff.mpr (AdmA_exact t ρ a)

/-- **A term with no variable reads one set of attributes under every environment.** -/
theorem AdmA_closed (t : Term S) (h : t.hasVar = false) (ρ ρ' : List S.C) :
    AdmA α β t ρ = AdmA α β t ρ' := by
  funext a
  rw [AdmA_eq_isSome, AdmA_eq_isSome, denote_closed t h ρ ρ']

end

end Calculus.Alg
