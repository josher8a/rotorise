import Calculus.Lang.Term

/-!
# The converse of a term

The dual universe `S.op` keeps the signature and flips the orientation. So the dual reads the
stored carrier as its caller carrier, and the stored half of each two-sided row as its caller
half. The meaning is one absolute structure, and the dual reads that structure at the dual
orientation, with no new data.

A term of `S` is a term of `S.op`, because the term stores each half at its absolute side.
`denote_R` says that the term at the dual orientation denotes the converse codec, where the dual
reads the stored table as its caller table and the caller table as its stored table.
-/

namespace Calculus.Alg

variable {V A M : Type}

/-! ## The readings of the dual -/

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

section Readings
variable {Car : Bool → Type} {Mem : Type} {mem : Car true → Mem} {d : (s : Bool) → Car s → Nat}

/-- **The host codec read at the dual orientation is the converse of its reading.** -/
theorem readC_R : ∀ (o : Orient) (c : Codec (Car false) (Car true) Mem), R (readC o.op c) (readC o c)
  | ⟨(false, true), _⟩, c => R_conv c
  | ⟨(true, false), _⟩, c => (R_conv c).symm
  | ⟨(false, false), h⟩, _ => absurd rfl h
  | ⟨(true, true), h⟩, _ => absurd rfl h

/-- **The lift at the dual orientation is the converse of the lift**, at each orientation. -/
theorem setAt_R (L : SetF (Car false) (Car true) Mem mem (d false) (d true))
    (hpos : ∀ s x, 0 < d s x) :
    ∀ (o : Orient) {c' : Codec (Car o.s) (Car o.c) (MemAt Mem o.c)}
      {c : Codec (Car o.c) (Car o.s) (MemAt Mem o.s)},
      R c' c → R ((setAt L o.op).lift c') ((setAt L o).lift c)
  | ⟨(false, true), _⟩, _, _, h => setOp_R L (hpos false) (hpos true) h
  | ⟨(true, false), _⟩, _, _, h => (setOp_R L (hpos false) (hpos true) h.symm).symm
  | ⟨(false, false), h⟩, _, _, _ => absurd rfl h
  | ⟨(true, true), h⟩, _, _, _ => absurd rfl h

end Readings

/-- The half of the stored outer at the dual is the half of the caller outer. -/
theorem half2_R {X Y N N' : Type} (o : Orient) {a' b' : Codec Y X N'} {a b : Codec X Y N}
    (ha : R a' a) (hb : R b' b) :
    R (half2 o.c a' b') (half2 o.c a b) ∧ R (half2 o.s a' b') (half2 o.s a b) := by
  cases o.c <;> cases o.s <;> exact ⟨by assumption, by assumption⟩

/-! ## The converse of a codec at a universe -/

section ConvU
variable {S : Syn} [Sem S]

/-- **The converse of a codec of a universe**, as a codec of the dual. The converse names no
    member, so one map serves every orientation. -/
def convU (c : S.C) : S.op.C := Codec.ofEP (T := fun _ => True) (μ := none) (e := c.p) (p := c.e)

/-- The converse has the converse graph. -/
theorem R_convU (c : S.C) : R (convU c) c := ⟨rfl, rfl⟩

/-- **The converse keeps the law at every orientation**, with no case on the orientation. -/
theorem Lawful.convU {c : S.C} (h : Lawful Syn.member c) : Lawful Syn.member (convU c) :=
  .ofRC h.canon h.retract fun hμ => nomatch hμ

end ConvU

/-! ## The denotation of the converse -/

section DenoteR
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

mutual
/-- **The denotation at the dual orientation is the converse of the denotation.** The dual reads
    the stored table as its caller table, and the caller table as its stored table, under an
    environment of converses. -/
theorem denote_R : ∀ (t : Term S) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → R (denote β α t ρ') (denote α β t ρ)
  | .prim g, _, _, _ => readC_R S.o (Mean.ground g)
  | .opaq, _, _, _ => readC_R S.o Mean.top
  | .never, _, _, _ => ⟨rfl, rfl⟩
  | .var i, _, _, h => envAt_R h i
  | .set t, _, _, h => by
      simp only [denote, Syn.set]
      cases Mean.set (B := S.sig) with
      | none => exact ⟨rfl, rfl⟩
      | some L => exact setAt_R L Mean.d_pos S.o (denote_R t h)
  | .list pre sp suf, _, _, h => by
      simp only [denote, Syn.list]
      cases Mean.list (B := S.sig) with
      | none => exact ⟨rfl, rfl⟩
      | some L =>
          exact listCodec_R (L.p S.o.c) (L.p S.o.s) (μAt S.o.s L.μ) (μAt S.o.c L.μ)
            (denoteList_R pre h) (denoteOpt_R sp h) (denoteList_R suf h)
  | .held t P PA _ _, _, _, h =>
      let hh := half2_R S.o (denote_R P h) (denote_R PA h)
      R.held2 (denote_R t h) hh.2 hh.1 _ _ _ _
  | .refine t _ _, _, _, h => R.refine2 (denote_R t h) _ _
  | .object b, _, _, h => bodySem_R b h
  | .union ts, _, _, h => altCodec_R _ _ (denoteList_R ts h)
  | .mu b, _, _, h => muCodec_R Syn.dV Syn.dA _ _ fun _ _ hc => denote_R b (.cons hc h)

/-- …at a body: the converse fields and the converse open block. -/
theorem bodySem_R : ∀ (b : Body S) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → R (bodySem β α b ρ') (bodySem α β b ρ)
  | .mk _ f wild, _, _, h => by
      simp only [bodySem, Syn.map]
      cases Mean.map (B := S.sig) with
      | none => exact ⟨rfl, rfl⟩
      | some F =>
          exact objectCodec_R (F.m S.o.c) (F.m S.o.s) (μAt S.o.c F.μ) (μAt S.o.s F.μ)
            (fun k => fieldSem_R (f k) h) (wildSem_R wild h) (by cases wild <;> simp [wildSem])

/-- …at a slot. -/
theorem fieldSem_R : ∀ (s : ObjectSlot S) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → FieldR (fieldSem β α s ρ') (fieldSem α β s ρ)
  | .req t, _, _, h | .optional t, _, _, h => denote_R t h

/-- …at an open block. -/
theorem wildSem_R : ∀ (w : Option (Term S)) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → RestR (wildSem β α w ρ') (wildSem α β w ρ)
  | none, _, _, _ => trivial
  | some t, _, _, h => denote_R t h

/-- …at a list. -/
theorem denoteList_R : ∀ (ts : List (Term S)) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → List.Forall₂ R (denoteList β α ts ρ') (denoteList α β ts ρ)
  | [], _, _, _ => .nil
  | t :: ts, _, _, h => .cons (denote_R t h) (denoteList_R ts h)

/-- …at an optional term. -/
theorem denoteOpt_R : ∀ (o : Option (Term S)) {ρ' : List S.op.C} {ρ : List S.C},
    List.Forall₂ R ρ' ρ → Option.Rel R (denoteOpt β α o ρ') (denoteOpt α β o ρ)
  | none, _, _, _ => .none
  | some t, _, _, h => .some (denote_R t h)
end

end DenoteR

end Calculus.Alg
