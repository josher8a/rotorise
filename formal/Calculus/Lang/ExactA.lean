import Calculus.Lang.ExactV
import Calculus.Lang.Converse

/-!
# Exactness on the attribute side, over a universe signature

`AdmA` is the attribute half of `Adm`: a row per constructor that equals the domain of `denote t` at
the dual orientation, `dom(p)` at the host. The attribute row of a term is the value row of the same
term in the dual universe, under the same environment. So `AdmA_exact` is `Adm_exact` at the dual,
composed with `denote_op`, and the attribute side owns no induction. A universe supplies the value
rows of the primitives of its dual (`PrimAdmA`), and nothing else.
-/

namespace Calculus.Alg

/-- **The attribute-side row of each primitive**, and its exactness: the value-side rows of the
    dual universe. -/
abbrev PrimAdmA (S : Syn) [Sem S] := PrimAdm S.op

variable {S : Syn} [Sem S] {α : Table S} {β : Table S.op}

variable (α β) in
/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out. -/
noncomputable def refineReads (t : Term S) (ρ : List S.C) (q : S.V → Bool) (a : Syn.A S) :
    Bool :=
  gate ((denote α β t ρ).f S.o.op) q a

/-- `refineReads` is the gate of the term at the dual orientation. -/
theorem refineReads_eq_gate (t : Term S) (ρ : List S.C) (q : S.V → Bool) (a : Syn.A S) :
    gate ((denote (S := S.op) β α t ρ).f S.o.op) q a = refineReads α β t ρ q a := by
  rw [denote_op]; rfl

variable [PrimAdmA S]

noncomputable section

variable (α β) in
/-- **The joint admission predicate, attribute side**, under an environment `ρ`: the value row
    of the term in the dual universe, under the same environment. -/
def AdmA (t : Term S) (ρ : List S.C) : Syn.A S → Bool := Adm (S := S.op) β α t ρ

variable (α β) in
/-- The read side's payload row; `AdmBody`'s mirror. -/
def AdmABody (b : Body S) (ρ : List S.C) : Syn.A S → Bool := AdmBody (S := S.op) β α b ρ

variable (α β) in
/-- A slot's read row is its term's. -/
def AdmAField (s : ObjectSlot S) (ρ : List S.C) : Syn.A S → Bool :=
  AdmField (S := S.op) β α s ρ

variable (α β) in
/-- The open block's read row, where the body has one. -/
def AdmAWild (w : Option (Term S)) (ρ : List S.C) : Option (Syn.A S → Bool) :=
  AdmWild (S := S.op) β α w ρ

variable (α β) in
/-- The options' read rows, in order. -/
def AdmAList (ts : List (Term S)) (ρ : List S.C) : List (Syn.A S → Bool) :=
  AdmList (S := S.op) β α ts ρ

variable (α β) in
/-- The spread's read row, where there is one. -/
def AdmAOptT (o : Option (Term S)) (ρ : List S.C) : Option (Syn.A S → Bool) :=
  AdmOptT (S := S.op) β α o ρ

@[simp] theorem AdmAList_eq (ρ : List S.C) :
    ∀ ts : List (Term S), AdmAList α β ts ρ = ts.map (AdmA α β · ρ)
  | [] => rfl
  | t :: ts => congrArg (AdmA α β t ρ :: ·) (AdmAList_eq ρ ts)

/-- A refinement reads what its inner term reads, its stored predicate holds on, and its
    predicate holds on the read. -/
theorem AdmA_refine_eq (t : Term S) (p : S.sig.P false) (pA : S.sig.P true) (ρ : List S.C)
    (a : Syn.A S) :
    AdmA α β (.refine t p pA) ρ a =
      (AdmA α β t ρ a && (Syn.evalA (half S.o.s p pA) a &&
        refineReads α β t ρ (Syn.eval (half S.o.c p pA)) a)) := by
  rw [← refineReads_eq_gate]
  simp only [AdmA, Adm, Bool.and_assoc]

/-- A held term reads what its stored outer reads, where the inner term reads the stored word's
    image, and the caller outer admits the caller word's image of the read. -/
theorem AdmA_held_eq [PrimAdm S] (t P PA : Term S) (k : List (S.sig.G false × Bool))
    (kA : List (S.sig.G true × Bool)) (ρ : List S.C) (a : Syn.A S) :
    AdmA α β (.held t P PA k kA) ρ a =
      (half2 S.o.s (AdmA α β P ρ a) (AdmA α β PA ρ a) &&
        AdmA α β t ρ ((β.word (halfK S.o.s k kA)).1 a) &&
        refineReads α β t ρ (fun w => half2 S.o.c (Adm α β P ρ ((α.word (halfK S.o.c k kA)).2 w))
          (Adm α β PA ρ ((α.word (halfK S.o.c k kA)).2 w))) ((β.word (halfK S.o.s k kA)).1 a)) := by
  have hP : (fun w => ((half2 S.o.c (denote (S := S.op) β α P ρ)
      (denote (S := S.op) β α PA ρ)).f S.o ((α.word (halfK S.o.c k kA)).2 w)).isSome) =
      fun w => half2 S.o.c (Adm α β P ρ ((α.word (halfK S.o.c k kA)).2 w))
        (Adm α β PA ρ ((α.word (halfK S.o.c k kA)).2 w)) := by
    funext w
    rw [denote_op, denote_op, half2_f, half2_apply Option.isSome, Adm_eq_isSome, Adm_eq_isSome]
  rw [← hP, ← refineReads_eq_gate]
  simp only [AdmA, Adm]
  rw [Bool.and_comm (Adm (S := S.op) β α t _ _)]

variable (α β) in
/-- The row is the domain at the dual orientation, not a bound on it, under the environment
    `ρ`. -/
def ExactA (t : Term S) (ρ : List S.C) : Prop :=
  ∀ a, AdmA α β t ρ a = true ↔ ((denote α β t ρ).f S.o.op a).isSome

/-- **Every attribute row is exact**, at every universe: the value law at the dual, through
    `denote_op`. -/
theorem AdmA_exact (t : Term S) (ρ : List S.C) : ExactA α β t ρ := fun a =>
  (Adm_exact (S := S.op) (α := β) (β := α) t ρ a).trans (by rw [denote_op])

/-- The row, read as a Boolean: the read domain of the denotation. -/
theorem AdmA_eq_isSome (t : Term S) (ρ : List S.C) (a : Syn.A S) :
    AdmA α β t ρ a = ((denote α β t ρ).f S.o.op a).isSome :=
  Bool.eq_iff_iff.mpr (AdmA_exact t ρ a)

/-- **A term with no variable reads one set of attributes under every environment.** -/
theorem AdmA_closed (t : Term S) (h : t.hasVar = false) (ρ ρ' : List S.C) :
    AdmA α β t ρ = AdmA α β t ρ' := by
  funext a
  rw [AdmA_eq_isSome, AdmA_eq_isSome, denote_closed t h ρ ρ']

end

end Calculus.Alg
