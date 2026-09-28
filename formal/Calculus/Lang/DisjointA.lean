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

variable {S : Syn} [Sem S] [SynA S] [SemA S] [PrimAdmA S] {ρ ρ' ρ'' : List S.C}
  {α : Table S} {β : Table S.op}

/-! ## The converse of the syntax that the test reads -/

section Syntax
omit [SemA S] [PrimAdmA S]

/-- The converse of a list of terms is the list of the converses. -/
theorem tconvL_eq_map : ∀ ts : List (Term S), tconvL ts = ts.map tconv
  | [] => rfl
  | t :: ts => congrArg (tconv t :: ·) (tconvL_eq_map ts)

/-- The converse of an optional term is the optional converse. -/
theorem tconvO_eq_map : ∀ o : Option (Term S), tconvO o = o.map tconv
  | none => rfl
  | some _ => rfl

/-- The converse keeps the kind of a slot. -/
theorem isReq_tconvS : ∀ s : ObjectSlot S, (tconvS s).isReq = s.isReq
  | .req _ | .optional _ => rfl

/-- The converse of a body gives each name the converse slot. -/
theorem slotAt_tconvB (c : Body S) (k : String) : (tconvB c).slotAt k = tconvS (c.slotAt k) := by
  cases c with
  | mk fs f w =>
    rcases Decidable.em (k ∈ fs) with hk | hk
    · rw [Body.slotAt_pos (b := tconvB _) hk, Body.slotAt_pos (b := .mk fs f w) hk]; rfl
    · rw [Body.slotAt_neg (b := tconvB _) hk, Body.slotAt_neg (b := .mk fs f w) hk]
      cases w <;> rfl

mutual
/-- **The converse keeps the variables of a term.** -/
theorem hasVar_tconv : ∀ t : Term S, (tconv t).hasVar = t.hasVar
  | .var _ | .prim _ | .opaq | .never => rfl
  | .refine t _ _ | .mu t | .set t => hasVar_tconv t
  | .held t P PA _ _ => by
      simp only [tconv, Term.hasVar, hasVar_tconv t, hasVar_tconv P, hasVar_tconv PA,
        Bool.or_right_comm]
  | .list pre sp suf => by
      simp only [tconv, Term.hasVar, hasVarL_tconv pre, hasVarO_tconv sp, hasVarL_tconv suf]
  | .object b => hasVarB_tconv b
  | .union os => hasVarL_tconv os
/-- …of a body. -/
theorem hasVarB_tconv : ∀ b : Body S, (tconvB b).hasVar = b.hasVar
  | .mk fs f w => by
      simp only [tconvB, Body.hasVar, hasVarO_tconv w]
      congr 2
      exact propext (exists_congr fun k => by rw [hasVarS_tconv (f k)])
/-- …of a slot. -/
theorem hasVarS_tconv : ∀ s : ObjectSlot S, (tconvS s).hasVar = s.hasVar
  | .req t | .optional t => hasVar_tconv t
/-- …of a list. -/
theorem hasVarL_tconv : ∀ ts : List (Term S), Term.hasVarL (tconvL ts) = Term.hasVarL ts
  | [] => rfl
  | t :: ts => by simp only [tconvL, Term.hasVarL, hasVar_tconv t, hasVarL_tconv ts]
/-- …of an optional term. -/
theorem hasVarO_tconv : ∀ o : Option (Term S), Term.hasVarO (tconvO o) = Term.hasVarO o
  | none => rfl
  | some t => hasVar_tconv t
end

end Syntax

noncomputable section

/-! ## The rows that the soundness proof reads -/

/-- The bottom reads nothing. -/
@[simp] theorem AdmA_never (a : Sem.A S) : AdmA α β (.never : Term S) ρ a = false := rfl

variable (α β) in
/-- `⋁` of `AdmA` over a union's options: `AdmAny` of the dual. -/
def AdmAAny (ts : List (Term S)) (ρ : List S.C) (a : Sem.A S) : Bool :=
  AdmAny β α (tconvL ts) (ρ.map conv) a

/-- An empty list of options reads no attribute. -/
@[simp] theorem AdmAAny_nil (a : Sem.A S) : AdmAAny α β ([] : List (Term S)) ρ a = false := rfl

/-- The options read where the first reads or the rest read. -/
@[simp] theorem AdmAAny_cons (t : Term S) (ts : List (Term S)) (a : Sem.A S) :
    AdmAAny α β (t :: ts) ρ a = (AdmA α β t ρ a || AdmAAny α β ts ρ a) := rfl

/-- A union reads where one of its options reads. -/
theorem AdmA_union (opts : List (Term S)) (a : Sem.A S) :
    AdmA α β (.union opts) ρ a = AdmAAny α β opts ρ a := rfl

omit [PrimAdmA S] in
/-- **A recursive term reads as its body reads over the stage below the attribute's depth.** -/
theorem mu_p_unfold (b : Term S) (ρ : List S.C) (a : Sem.A S) :
    (denote α β (.mu b) ρ).p a
      = (denote α β b (muStage (fun c => denote α β b (c :: ρ)) (Sem.dA a - 1) :: ρ)).p a := by
  show (muStage (fun c => denote α β b (c :: ρ)) (Sem.dA a)).p a = _
  obtain ⟨n, hn⟩ : ∃ n, Sem.dA a = n + 1 := ⟨Sem.dA a - 1, by have := Sem.dA_pos a; omega⟩
  rw [hn, Nat.add_sub_cancel]
  rfl

/-- …and so it reads where its body reads over that stage. -/
theorem AdmA_mu_unfold (b : Term S) (ρ : List S.C) (a : Sem.A S) :
    AdmA α β (.mu b) ρ a
      = AdmA α β b (muStage (fun c => denote α β b (c :: ρ)) (Sem.dA a - 1) :: ρ) a := by
  rw [AdmA_eq_isSome, AdmA_eq_isSome, mu_p_unfold]

end

/-! ## The laws, on the read side -/

/-- **The read-side law of the set former.** The catch-all rows of the families read the
    disjointness of the former classes (`Shapes`). -/
class FormerAdmA (S : Syn) [Sem S] [SynA S] [SemA S] [PrimAdmA S] : Prop where
  /-- Two sets whose elements share no attribute share no set. -/
  set_never : ∀ {α : Table S} {β : Table S.op} (a y : Term S), (∀ u, (AdmA α β a [] u && AdmA α β y [] u) = false) →
    ∀ c, (AdmA α β (.set a) [] c && AdmA α β (.set y) [] c) = false

/-- **The read-side law of the leaves.** A primitive reads no variable, so the law is stated at
    the closed environment. -/
class LeafAdmA (S : Syn) [Sem S] [Leaf S] [SynA S] [SemA S] [PrimAdmA S] : Prop where
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
  set_never a y h c := by
    have := FormerAdmA.set_never (tconv a) (tconv y) (fun u => by
      simpa only [AdmA, tconv_tconv_op, List.map_nil] using h u) c
    simpa only [AdmA, tconv, tconv_tconv_op, List.map_nil] using this

/-! ## Soundness, on the read side -/

/-- The environments keep each paired binder pair apart: no attribute read by both. The
    environments of converses of the dual keep the binders apart on the write side. -/
def ApartA (p : Pairing) (ρ ρ' : List S.C) : Prop :=
  ApartV (S := S.op) p (ρ.map conv) (ρ'.map conv)

omit [PrimAdmA S] in
/-- Apart environments stay apart when the left operand unfolds: its new binder pairs with
    nothing. -/
theorem ApartA.left {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') (c : S.C) :
    ApartA (shiftL p) (c :: ρ) ρ' :=
  ApartV.left (S := S.op) h (conv c)

omit [PrimAdmA S] in
/-- …and when the right operand unfolds. -/
theorem ApartA.right {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') (c : S.C) :
    ApartA (shiftR p) ρ (c :: ρ') :=
  ApartV.right (S := S.op) h (conv c)

omit [PrimAdmA S] in
/-- Two new binders that read no attribute in common extend two apart environments at a paired
    binder. -/
theorem ApartA.mu {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') {c c' : S.C}
    (hc : ∀ v, ((c.p v).isSome && (c'.p v).isSome) = false) :
    ApartA (pairMu p) (c :: ρ) (c' :: ρ') :=
  ApartV.mu (S := S.op) h (c := conv c) (c' := conv c') hc

variable (α β) in
/-- A family is sound for `x` where every partner it accepts shares no value with `x`. -/
def DisjSoundA (ρ ρ' : List S.C) (x : Term S) (f : Term S → Bool) : Prop :=
  ∀ y, f y = true → ∀ v, (AdmA α β x ρ v && AdmA α β y ρ' v) = false

/-- **A read-side family is a write-side family of the dual**, where the dual family answers
    at each converse term what the family answers at the term. -/
theorem DisjSoundA_iff {x : Term S} {f : Term S → Bool} {f' : Term S.op → Bool}
    (hf : ∀ y, f' (tconv y) = f y) :
    DisjSoundA α β ρ ρ' x f ↔ DisjSound (S := S.op) β α (ρ.map conv) (ρ'.map conv) (tconv x) f' := by
  constructor
  · intro h y' hy v
    have := h (tconv y') (by rw [← hf, tconv_tconv_op]; exact hy) v
    simpa only [AdmA, tconv_tconv_op] using this
  · intro h y hy v
    exact h (tconv y) (by rw [hf]; exact hy) v

omit [PrimAdmA S] in
/-- A held-free closed term decodes an attribute as the top decodes it. -/
theorem top_of_HF_closed [TopLaws S] {t : Term S} (hh : hasHeld t = false) (hv : t.hasVar = false)
    (ρ : List S.C) {a : Sem.A S} {u : S.V} (h : (denote α β t ρ).p a = some u) :
    (Sem.top (S := S)).p a = some u := by
  rw [denote_closed t hv ρ []] at h
  exact (sub_denoteIn t hh [] (fun i => by simp only [envAt, List.getD_nil]; exact sub_empty)).2 a u h

omit [PrimAdmA S] in
/-- A refinement over a held-free closed term reads only what the top reads to a value that
    satisfies the predicate. -/
theorem refineReads_top [TopLaws S] {t : Term S} (hh : hasHeld t = false) (hv : t.hasVar = false)
    {ρ : List S.C} {q : S.V → Bool} {a : Sem.A S} (h : refineReads α β t ρ q a = true) :
    ∃ u, (Sem.top (S := S)).p a = some u ∧ q u = true := by
  simp only [refineReads, gate, conv] at h
  split at h
  · next u hu => exact ⟨u, top_of_HF_closed hh hv ρ hu, h⟩
  · exact nomatch h

omit [PrimAdmA S] [SynA S] [SemA S] in
/-- **Two recursive terms read apart stage by stage.** Where the two bodies keep apart every
    two binders that read no attribute in common, each two stages of the same index read none
    in common. -/
theorem stage_apartA {B B' : S.C → S.C}
    (hB : ∀ c c', (∀ u, ((c.p u).isSome && (c'.p u).isSome) = false) →
      ∀ u, (((B c).p u).isSome && ((B' c').p u).isSome) = false) :
    ∀ n u, (((muStage B n).p u).isSome && ((muStage B' n).p u).isSome) = false
  | 0, _ => rfl
  | n + 1, u => hB _ _ (stage_apartA hB n) u

mutual
/-- **The rows of the right operand are sound**, given a sound family for every pairing that
    keeps the environments apart. -/
theorem disjSRight_soundA {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α β ρ ρ' x (fam q)) :
    ∀ (y : Term S) (p : Pairing) (ρ' : List S.C), ApartA p ρ ρ' →
      disjSRight fam p y = true → ∀ v, (AdmA α β x ρ v && AdmA α β y ρ' v) = false
  | .never, _, _, _, _, v => by simp
  | .mu b, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [AdmA_mu_unfold b ρ' v]
      exact disjSRight_soundA hf b (shiftR p) _ (hp.right _) h v
  | .refine y q _, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [AdmA_refine_eq, ← Bool.and_assoc, disjSRight_soundA hf y p ρ' hp h v, Bool.false_and]
  | .union os, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [AdmA_union]
      exact disjSRightL_soundA hf os p ρ' hp h v
  | .prim g, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .set t, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .list a b c, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .held a b _ k _, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .opaq, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .object b, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .var j, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
/-- …and over the options of a union. -/
theorem disjSRightL_soundA {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α β ρ ρ' x (fam q)) :
    ∀ (ys : List (Term S)) (p : Pairing) (ρ' : List S.C), ApartA p ρ ρ' →
      disjSRightL fam p ys = true → ∀ v, (AdmA α β x ρ v && AdmAAny α β ys ρ' v) = false
  | [], _, _, _, _, v => by simp
  | y :: ys, p, ρ', hp, h, v => by
      simp only [disjSRightL, Bool.and_eq_true] at h
      rw [AdmAAny_cons, Bool.and_or_distrib_left, disjSRight_soundA hf y p ρ' hp h.1 v,
        disjSRightL_soundA hf ys p ρ' hp h.2 v, Bool.false_or]
end

omit [PrimAdmA S] in
mutual
/-- The split of the right operand of the dual reads the converse of each option. -/
theorem splitR_tconv (fam : Pairing → Term S → Bool) (p : Pairing) :
    ∀ y : Term S, splitR (fun q y' => fam q (tconv y')) p (tconv y) = splitR fam p y
  | .never => rfl
  | .union os => splitRL_tconv fam p os
  | .prim _ | .set _ | .list _ _ _ | .held _ _ _ _ _ | .refine _ _ _ | .opaq | .object _ | .var _
  | .mu _ => congrArg (fam p) (tconv_tconv _)
/-- …and each option of a union. -/
theorem splitRL_tconv (fam : Pairing → Term S → Bool) (p : Pairing) :
    ∀ ys : List (Term S), splitRL (fun q y' => fam q (tconv y')) p (tconvL ys) = splitRL fam p ys
  | [] => rfl
  | y :: ys => by simp only [tconvL, splitRL, splitR_tconv fam p y, splitRL_tconv fam p ys]
end

/-- **The split of the right operand is sound**, given a sound family at the pairing: the
    write-side law of the dual. -/
theorem splitR_soundA {ρ ρ' : List S.C} {x : Term S} {fam : Pairing → Term S → Bool} {p : Pairing}
    (hf : DisjSoundA α β ρ ρ' x (fam p)) (y : Term S) (h : splitR fam p y = true) (v : Sem.A S) :
    (AdmA α β x ρ v && AdmA α β y ρ' v) = false :=
  splitR_sound (S := S.op) (fam := fun q y' => fam q (tconv y'))
    ((DisjSoundA_iff fun y => congrArg (fam p) (tconv_tconv y)).mp hf) (tconv y)
    (by rw [splitR_tconv]; exact h) v

/-- **Two data predicates that meet at the empty predicate keep two refinements apart on the
    read side**, where both inner terms are closed and held-free: both then read one value, the
    value that the top reads. -/
theorem predApart_soundA [PrimAdm S] [Leaf S] [LeafAdm S] [TopLaws S] {q : S.Pred} {ρ' : List S.C} :
    ∀ (y : Term S), predApart q y = true → ∀ a u, (Sem.top (S := S)).p a = some u →
      Sem.eval q u = true → AdmA α β y ρ' a = false
  | .refine y q' _, h, a, u, htop, hq => by
      simp only [predApart, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rw [AdmA_refine_eq]
      rcases h with ⟨⟨⟨-, hh⟩, hv⟩, hm⟩ | h
      · have hn : Leaf.pmeet q q' = some none := by
          revert hm; cases Leaf.pmeet q q' with
          | none => simp
          | some o => cases o <;> simp
        have hpm := LeafAdm.pmeet_none q q' hn u
        cases hr : refineReads α β y ρ' (Sem.eval q') a with
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
  (DisjSoundA_iff (f' := famPrimD (S := S.op) g) fun y => by cases y <;> rfl).mpr
    (famPrimD_sound (S := S.op) g)

/-- **The variable family is sound**: the variable family of the dual. -/
theorem famVarD_soundA {ρ ρ' : List S.C} {i : Nat} {q : Pairing} (hq : ApartA q ρ ρ') :
    DisjSoundA α β ρ ρ' (.var i) (famVarD i q) :=
  (DisjSoundA_iff (f' := famVarD (S := S.op) i q) fun y => by cases y <;> rfl).mpr
    (famVarD_sound (S := S.op) hq)

/-- **The set family is sound**: the set family of the dual. -/
theorem famSetD_soundA [FormerAdmA S] [Shapes S] {ρ ρ' : List S.C} (a : Term S)
    {mt : Term S → Bool} (hmt : DisjSoundA α β ρ ρ' a mt) :
    DisjSoundA α β ρ ρ' (.set a) (famSetD a mt) := by
  refine (DisjSoundA_iff (f' := famSetD (tconv a) fun y' => mt (tconv y')) fun y => ?_).mpr
    (famSetD_sound (S := S.op) (tconv a) ((DisjSoundA_iff fun y => congrArg mt (tconv_tconv y)).mp hmt))
  cases y
  case set y => simp only [tconv, famSetD, hasVar_tconv, tconv_tconv]
  all_goals rfl

omit [PrimAdmA S] in
/-- One disjoint position of the dual rows is one disjoint position of the rows. -/
theorem anyZip_tconv : ∀ (fs : List (Term S → Bool)) (us : List (Term S)),
    anyZip (fs.map fun f y' => f (tconv y')) (us.map tconv) = anyZip fs us
  | f :: fs, u :: us => by simp only [List.map, anyZip, tconv_tconv, anyZip_tconv fs us]
  | [], _ => rfl
  | _ :: _, [] => rfl

omit [PrimAdmA S] in
/-- **The list test of the dual reads the converse rows.** -/
theorem famListD_tconv (fpre fsuf : List (Term S → Bool)) (fsp : Option (Term S → Bool))
    (y : Term S) :
    famListD (fpre.map fun f y' => f (tconv y')) (fsp.map fun f y' => f (tconv y'))
      (fsuf.map fun f y' => f (tconv y')) (tconv y) = famListD fpre fsp fsuf y := by
  cases y
  case list pre₂ sp₂ suf₂ =>
    have hr {α β : Type} (g : α → β) (pre suf : List α) (c : α) (n : Nat) :
        rowOfG (pre.map g) (some (g c)) (suf.map g) n = (rowOfG pre (some c) suf n).map (List.map g) :=
      rowOfG_map g pre (some c) suf n
    have hn {α β : Type} (g : α → β) (pre suf : List α) (n : Nat) :
        rowOfG (pre.map g) none (suf.map g) n = (rowOfG pre none suf n).map (List.map g) :=
      rowOfG_map g pre none suf n
    simp only [tconv, famListD, listDisjRow, tconvL_eq_map, tconvO_eq_map, List.length_map]
    cases fsp <;> cases sp₂ <;> simp only [Option.map_none, Option.map_some, hr, hn]
    · cases rowOfG pre₂ none suf₂ (fpre.length + fsuf.length) <;>
        simp only [Option.map_none, Option.map_some, ← List.map_append, anyZip_tconv]
    · cases rowOfG pre₂ (some _) suf₂ (fpre.length + fsuf.length) <;>
        simp only [Option.map_none, Option.map_some, ← List.map_append, anyZip_tconv]
    · cases rowOfG fpre (some _) fsuf (pre₂.length + suf₂.length) <;>
        simp only [Option.map_none, Option.map_some, ← List.map_append, anyZip_tconv]
    · split <;> try rfl
      cases rowOfG fpre (some _) fsuf _ <;> cases rowOfG pre₂ (some _) suf₂ _ <;>
        simp only [Option.map_none, Option.map_some, anyZip_tconv]
  all_goals rfl

/-- **The list family is sound on the read side**: the list family of the dual. -/
theorem famListD_soundA [Shapes S] {ρ ρ' : List S.C} {pre suf : List (Term S)}
    {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Bool)} {fsp : Option (Term S → Bool)}
    (hp : List.Forall₂ (DisjSoundA α β ρ ρ') pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ DisjSoundA α β ρ ρ' t f)
    (hf : List.Forall₂ (DisjSoundA α β ρ ρ') suf fsuf) :
    DisjSoundA α β ρ ρ' (.list pre sp suf) (famListD fpre fsp fsuf) := by
  have hd {t : Term S} {f : Term S → Bool} :=
    DisjSoundA_iff (α := α) (β := β) (ρ := ρ) (ρ' := ρ') (x := t) (f := f)
      (f' := fun y' => f (tconv y')) fun y => congrArg f (tconv_tconv y)
  have hl {ts : List (Term S)} {fs : List (Term S → Bool)} (h : List.Forall₂ (DisjSoundA α β ρ ρ') ts fs) :
      List.Forall₂ (DisjSound (S := S.op) β α (ρ.map conv) (ρ'.map conv)) (tconvL ts)
        (fs.map fun f y' => f (tconv y')) := by
    rw [tconvL_eq_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.imp fun _ _ h => hd.mp h
  refine (DisjSoundA_iff (famListD_tconv fpre fsuf fsp)).mpr
    (famListD_sound (S := S.op) (sp := tconvO sp) (hl hp) ?_ (hl hf))
  rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, htf⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨tconv t, _, rfl, rfl, hd.mp htf⟩

omit [PrimAdmA S] in
/-- **The object test of the dual reads the converse slots.** -/
theorem famObjD_tconv (fa : Finset String) (f : {k // k ∈ fa} → ObjectSlot S) (wa : Option (Term S))
    (g : {k // k ∈ fa} → ObjectSlot S → Bool) (mw : Term S → Bool) (y : Term S) :
    famObjD (tconvB (.mk fa f wa)) (fun k s => g k (tconvS s)) (fun y' => mw (tconv y')) (tconv y) =
      famObjD (.mk fa f wa) g mw y := by
  cases y
  case object b =>
    cases b with | mk fb h wb =>
    have hk : ∀ k : {k // k ∈ fa ∪ fb},
        slotD (tconvB (.mk fa f wa)) (tconvB (.mk fb h wb)) (fun k s => g k (tconvS s))
          (fun y' => mw (tconv y')) k = slotD (.mk fa f wa) (.mk fb h wb) g mw k := by
      intro k
      unfold slotD
      split
      · next ha =>
        rw [dif_pos (show k.1 ∈ (Body.mk fa f wa).fields from ha)]
        split
        · next hb => rw [dif_pos (show k.1 ∈ (Body.mk fb h wb).fields from hb)]; exact congrArg _ (tconvS_tconvS _)
        · next hb =>
          rw [dif_neg (show k.1 ∉ (Body.mk fb h wb).fields from hb)]
          cases wb
          · rfl
          · exact congrArg (g _) (congrArg ObjectSlot.optional (tconv_tconv _))
      · next ha =>
        rw [dif_neg (show k.1 ∉ (Body.mk fa f wa).fields from ha)]
        dsimp only [tconvB, Body.at_mk]
        split <;> split <;> simp_all [tconvS, eq_comm (a := tconv _), tconv_tconv]
    exact decide_eq_decide.mpr (exists_congr fun k => Eq.to_iff (congrArg (· = true) (hk k)))
  all_goals rfl

/-- **The object family is sound**: the object family of the dual. -/
theorem famObjD_soundA [Shapes S] {ρ ρ' : List S.C} {fa : Finset String}
    {f : {k // k ∈ fa} → ObjectSlot S} {wa : Option (Term S)}
    {g : {k // k ∈ fa} → ObjectSlot S → Bool} {mw : Term S → Bool}
    (hg : ∀ k s, g k s = true → (ObjectSlot.isReq (f k) || ObjectSlot.isReq s) = true ∧
      ∀ w, (AdmAField α β (f k) ρ w && AdmAField α β s ρ' w) = false)
    (hmw : DisjSoundA α β ρ ρ' (Body.mk fa f wa).block mw) :
    DisjSoundA α β ρ ρ' (.object (.mk fa f wa)) (famObjD (.mk fa f wa) g mw) := by
  refine (DisjSoundA_iff (famObjD_tconv fa f wa g mw)).mpr
    (famObjD_sound (S := S.op) (fun k s h => ?_) ?_)
  · obtain ⟨hr, hs⟩ := hg k (tconvS s) h
    refine ⟨by simpa only [tconvB, Body.at_mk, isReq_tconvS] using hr, fun w => ?_⟩
    have := hs w
    cases s <;> simpa only [AdmAField, tconvS, tconv_tconv_op, tconvB, Body.at_mk] using this
  · have hb : (tconvB (.mk fa f wa)).block = tconv (Body.mk fa f wa).block := by
      cases wa <;> rfl
    rw [hb]
    exact (DisjSoundA_iff fun y => congrArg mw (tconv_tconv y)).mp hmw

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
        have := stage_apartA hB (Sem.dA v) v
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
      · cases hr : refineReads α β x ρ (Sem.eval q) w with
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
