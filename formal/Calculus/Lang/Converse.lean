import Calculus.Lang.Term

/-!
# The converse of a term

The dual universe `S.op` reads the stored carrier as its caller carrier. Its caller-side
predicates and generators are the stored-side ones of `S`, and the reverse. Its codecs are the
converses of the codecs of `S`, and its formers are the formers of `S` with the two sides
swapped. So a universe has a dual with no new data.

`tconv` sends a term to the dual term: each two-sided row swaps its halves, and every other row
keeps its shape. `denote_tconv` says that the dual term denotes the converse codec, where the
dual reads the stored table as its caller table and the caller table as its stored table.
-/

namespace Calculus.Alg

variable {V A M : Type}

/-! ## The formers of the dual -/

/-- The list former with its two sides swapped. -/
def ListF.op {member : A → M} {dV : V → Nat} {dA : A → Nat} (L : ListF V A M member dV dA) :
    ListF A V Unit (fun _ => ()) dA dV :=
  { pV := L.pA, pA := L.pV, μ := (), hμ := fun _ => rfl, dV_lt := L.dA_lt, dA_lt := L.dV_lt }

/-- The keyed-map former with its two sides swapped. -/
def MapF.op {member : A → M} {dV : V → Nat} {dA : A → Nat} (F : MapF V A M member dV dA) :
    MapF A V Unit (fun _ => ()) dA dV :=
  { mV := F.mA, mA := F.mV, μ := (), hμ := fun _ => rfl, dV_lt := F.dA_lt, dA_lt := F.dV_lt }

/-- The set former, transported through the converse. The held set, the element obligation and
    the member are the trivial ones: the caller-side held set has no stored-side image. -/
def SetF.op {member : A → M} {dV : V → Nat} {dA : A → Nat} (L : SetF V A M member dV dA) :
    SetF A V Unit (fun _ => ()) dA dV :=
  { lift := fun c => conv (L.lift (unconv c))
    lawful := fun h => Lawful.conv (L.lawful (Lawful.unconv h))
    agree := fun h => ⟨(L.agree ⟨h.p, h.e⟩).p, (L.agree ⟨h.p, h.e⟩).e⟩
    agreeS := fun h => agreeS_conv (L.agreeS (agreeS_unconv h))
    elem := fun _ => True
    held := fun _ _ => True
    member := fun _ => some ()
    carrier := fun _ => carrier_conv _
    held_of := fun _ _ _ => trivial }

/-- The lift reads the graph of its element and nothing else. -/
theorem lift_graph {member : A → M} {dV : V → Nat} {dA : A → Nat} (L : SetF V A M member dV dA)
    (hV : ∀ v, 0 < dV v) (hA : ∀ a, 0 < dA a)
    {c₁ c₂ : Codec V A M} (he : c₁.e = c₂.e) (hp : c₁.p = c₂.p) :
    (L.lift c₁).e = (L.lift c₂).e ∧ (L.lift c₁).p = (L.lift c₂).p := by
  apply AgreeLe.eq_of_forall (dV := dV) (dA := dA)
  intro d
  cases d with
  | zero => exact AgreeLe.zero hV hA _ _
  | succ d => exact L.agree (AgreeLe.of_eq he hp)

/-- **The lift of the dual former over a converse element is the converse of the lift.** -/
theorem setOp_R {member : A → M} {dV : V → Nat} {dA : A → Nat} (L : SetF V A M member dV dA)
    (hV : ∀ v, 0 < dV v) (hA : ∀ a, 0 < dA a) {c' : Codec A V Unit} {c : Codec V A M}
    (h : R c' c) : R ((SetF.op L).lift c') (L.lift c) := by
  have := lift_graph L hV hA (c₁ := unconv c') (c₂ := c) h.2 h.1
  exact ⟨this.2, this.1⟩

/-- The codec an environment of converses gives a variable is the converse. -/
theorem envAt_R {N' : Type} : ∀ {ρ' : List (Codec A V N')} {ρ : List (Codec V A M)},
    List.Forall₂ R ρ' ρ → ∀ i, R (envAt ρ' i) (envAt ρ i)
  | [], [], .nil, _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, .cons h _, 0 => h
  | _ :: _, _ :: _, .cons _ hs, i + 1 => envAt_R hs i

/-! ## The dual universe -/

/-- The stored-side syntax of the dual: the caller-side syntax of the universe. -/
instance opSynA (S : Syn) [Sem S] [SynA S] : SynA S.op where
  PredA := S.Pred
  GenA := S.Gen
  decGenA := S.decGen

/-- **The meaning of the dual**: the converse of each codec, and each former with its sides
    swapped. -/
noncomputable instance opSem (S : Syn) [Sem S] [SynA S] [SemA S] : Sem S.op where
  A := S.V
  M := Unit
  member _ := ()
  decM := inferInstance
  ground g := conv (Sem.ground (S := S) g)
  lawful_ground g := Lawful.conv (Sem.lawful_ground (S := S) g)
  carrier_ground _ := carrier_conv _
  eval := SemA.evalA (S := S)
  dV := Sem.dA (S := S)
  dA := Sem.dV (S := S)
  dV_pos := Sem.dA_pos (S := S)
  dA_pos := Sem.dV_pos (S := S)
  list := (Sem.list (S := S)).map ListF.op
  map := (Sem.map (S := S)).map MapF.op
  set := (Sem.set (S := S)).map SetF.op
  groundμ g := (Sem.groundμ (S := S) g).map fun _ => ()
  top := conv (Sem.top (S := S))
  lawful_top := Lawful.conv (Sem.lawful_top (S := S))
  carrier_top := carrier_conv _
  topHeld _ := True
  top_held _ _ := trivial

/-- The stored-side meaning of the dual: the caller-side meaning of the universe, and the two
    truth predicates swapped. -/
instance opSemA (S : Syn) [Sem S] [SynA S] [SemA S] : SemA S.op where
  evalA := Sem.eval (S := S)
  truth := SemA.truthA (S := S)
  eval_truth := SemA.evalA_truthA (S := S)
  truthA := SemA.truth (S := S)
  evalA_truthA := SemA.eval_truth (S := S)

/-- **The dual of the dual is the syntax, on the nose.** -/
theorem Syn.op_op (S : Syn) [Sem S] [SynA S] [SemA S] : S.op.op = S := rfl

section Formers
variable {S : Syn} [Sem S] [SynA S] [SemA S]

/-- The list former of the dual. -/
theorem opSem_list : Sem.list (S := S.op) = (Sem.list (S := S)).map ListF.op := rfl

/-- The keyed-map former of the dual. -/
theorem opSem_map : Sem.map (S := S.op) = (Sem.map (S := S)).map MapF.op := rfl

/-- The set former of the dual. -/
theorem opSem_set : Sem.set (S := S.op) = (Sem.set (S := S)).map SetF.op := rfl

end Formers

/-! ## The converse of a term -/

section Tconv
variable {S : Syn} [Sem S] [SynA S]

mutual
/-- **The converse of a term swaps the halves of each two-sided row**, and changes nothing
    else. -/
def tconv : Term S → Term S.op
  | .prim g => .prim g
  | .set t => .set (tconv t)
  | .list pre sp suf => .list (tconvL pre) (tconvO sp) (tconvL suf)
  | .held t P PA k kA => .held (tconv t) (tconv PA) (tconv P) kA k
  | .refine t p pA => .refine (tconv t) pA p
  | .opaq => .opaq
  | .object b => .object (tconvB b)
  | .union ts => .union (tconvL ts)
  | .never => .never
  | .var i => .var i
  | .mu b => .mu (tconv b)

/-- The converse of a body: the converse of each slot and of the open block. -/
def tconvB : Body S → Body S.op
  | .mk fields f wild => .mk fields (fun k => tconvS (f k)) (tconvO wild)

/-- The converse of a slot keeps its shape. -/
def tconvS : ObjectSlot S → ObjectSlot S.op
  | .req t => .req (tconv t)
  | .optional t => .optional (tconv t)

/-- The converse of each term of a list. -/
def tconvL : List (Term S) → List (Term S.op)
  | [] => []
  | t :: ts => tconv t :: tconvL ts

/-- The converse of an optional term. -/
def tconvO : Option (Term S) → Option (Term S.op)
  | none => none
  | some t => some (tconv t)
end

variable [SemA S]

mutual
/-- **The converse is an involution** on terms, on the nose. -/
theorem tconv_tconv : ∀ t : Term S, tconv (tconv t) = t
  | .prim _ | .opaq | .never | .var _ => rfl
  | .set t => congrArg Term.set (tconv_tconv t)
  | .list pre sp suf => by
      simp only [tconv, tconvL_tconvL pre, tconvO_tconvO sp, tconvL_tconvL suf]
  | .held t P PA _ _ => by
      simp only [tconv, tconv_tconv t, tconv_tconv P, tconv_tconv PA]
  | .refine t _ _ => by simp only [tconv, tconv_tconv t]
  | .object b => congrArg Term.object (tconvB_tconvB b)
  | .union ts => congrArg Term.union (tconvL_tconvL ts)
  | .mu b => congrArg Term.mu (tconv_tconv b)

/-- …at a body. -/
theorem tconvB_tconvB : ∀ b : Body S, tconvB (tconvB b) = b
  | .mk fields f wild => by
      rw [tconvB, tconvB, tconvO_tconvO wild]
      congr 1
      funext k
      exact tconvS_tconvS (f k)

/-- …at a slot. -/
theorem tconvS_tconvS : ∀ s : ObjectSlot S, tconvS (tconvS s) = s
  | .req t => congrArg ObjectSlot.req (tconv_tconv t)
  | .optional t => congrArg ObjectSlot.optional (tconv_tconv t)

/-- …at a list. -/
theorem tconvL_tconvL : ∀ ts : List (Term S), tconvL (tconvL ts) = ts
  | [] => rfl
  | t :: ts => by simp only [tconvL, tconv_tconv t, tconvL_tconvL ts]

/-- …at an optional term. -/
theorem tconvO_tconvO : ∀ o : Option (Term S), tconvO (tconvO o) = o
  | none => rfl
  | some t => congrArg some (tconv_tconv t)
end

/-- **The converse is an involution on the terms of the dual**, where the outer converse reads
    the meaning of the universe. The converse of the dual is injective, because the converse of
    its dual inverts it. -/
theorem tconv_tconv_op (t : Term S.op) : tconv (S := S) (tconv (S := S.op) t) = t := by
  have inj : ∀ x y : Term S.op, tconv x = tconv y → x = y := fun x y h =>
    (tconv_tconv x).symm.trans ((congrArg (@tconv S.op.op (opSem S.op) _) h).trans (tconv_tconv y))
  exact inj _ _ (tconv_tconv (S := S) (tconv (S := S.op) t))

end Tconv

/-! ## The denotation of the converse -/

section DenoteTconv
variable {S : Syn} [Sem S] [SynA S] [SemA S] (α : Table S) (β : Table S.op)

mutual
/-- **The denotation of the converse is the converse of the denotation.** The dual reads the
    stored table as its caller table, and the caller table as its stored table, under an
    environment of converses. -/
theorem denote_tconv : ∀ (t : Term S) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → R (denote β α (tconv t) ρ') (denote α β t ρ)
  | .prim _, _, _, _ | .opaq, _, _, _ => R_conv _
  | .never, _, _, _ => ⟨rfl, rfl⟩
  | .var i, _, _, h => envAt_R h i
  | .set t, _, _, h => by
      simp only [tconv, denote, opSem_set]
      cases Sem.set (S := S) with
      | none => exact ⟨rfl, rfl⟩
      | some L => exact setOp_R L Sem.dV_pos Sem.dA_pos (denote_tconv t h)
  | .list pre sp suf, _, _, h => by
      simp only [tconv, denote, opSem_list]
      cases Sem.list (S := S) with
      | none => exact ⟨rfl, rfl⟩
      | some L =>
          exact listCodec_R L.pV L.pA L.μ () (denoteList_tconv pre h) (denoteOpt_tconv sp h)
            (denoteList_tconv suf h)
  | .held t P PA _ _, _, _, h =>
      R.held2 (denote_tconv t h) (denote_tconv PA h) (denote_tconv P h) _ _ _ _
  | .refine t _ _, _, _, h => R.refine2 (denote_tconv t h) _ _
  | .object b, _, _, h => bodySem_tconv b h
  | .union ts, _, _, h => altCodec_R _ _ (denoteList_tconv ts h)
  | .mu b, _, _, h => muCodec_R Sem.dV Sem.dA _ _ fun _ _ hc => denote_tconv b (.cons hc h)

/-- …at a body: the converse fields and the converse open block. -/
theorem bodySem_tconv : ∀ (b : Body S) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → R (bodySem β α (tconvB b) ρ') (bodySem α β b ρ)
  | .mk _ f wild, _, _, h => by
      simp only [tconvB, bodySem, opSem_map]
      cases Sem.map (S := S) with
      | none => exact ⟨rfl, rfl⟩
      | some F =>
          exact objectCodec_R F.mV F.mA () F.μ (fun k => fieldSem_tconv (f k) h)
            (wildSem_tconv wild h) (by cases wild <;> simp [wildSem])

/-- …at a slot. -/
theorem fieldSem_tconv : ∀ (s : ObjectSlot S) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → FieldR (fieldSem β α (tconvS s) ρ') (fieldSem α β s ρ)
  | .req t, _, _, h | .optional t, _, _, h => denote_tconv t h

/-- …at an open block. -/
theorem wildSem_tconv : ∀ (w : Option (Term S)) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → RestR (wildSem β α (tconvO w) ρ') (wildSem α β w ρ)
  | none, _, _, _ => trivial
  | some t, _, _, h => denote_tconv t h

/-- …at a list. -/
theorem denoteList_tconv : ∀ (ts : List (Term S)) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → List.Forall₂ R (denoteList β α (tconvL ts) ρ') (denoteList α β ts ρ)
  | [], _, _, _ => .nil
  | t :: ts, _, _, h => .cons (denote_tconv t h) (denoteList_tconv ts h)

/-- …at an optional term. -/
theorem denoteOpt_tconv : ∀ (o : Option (Term S)) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → Option.Rel R (denoteOpt β α (tconvO o) ρ') (denoteOpt α β o ρ)
  | none, _, _, _ => .none
  | some t, _, _, h => .some (denote_tconv t h)
end

end DenoteTconv

end Calculus.Alg
