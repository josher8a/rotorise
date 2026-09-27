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

variable {S : Syn} [Sem S] [PrimAdm S] [PrimAdmA S] {ρ ρ' ρ'' : List S.C} {α : Table S}

noncomputable section

/-! ## Reading an attribute through a former -/

/-- The elements of an attribute, where the list former reads one. -/
def listOutA (a : Sem.A S) : Option (List (Sem.A S)) := (Sem.list (S := S)).bind (·.pA.out a)

/-- The entries of an attribute, where the map former reads one. -/
def mapOutA (a : Sem.A S) : Option (MapOf (Sem.A S)) := (Sem.map (S := S)).bind (·.mA.out a)

/-- A `list` reads an attribute that the list former reads by the row of its positions. -/
theorem AdmA_list_of_out {pre suf : List (Term S)} {sp : Option (Term S)} {a : Sem.A S}
    {as : List (Sem.A S)} (h : listOutA a = some as) :
    AdmA α (.list pre sp suf) ρ a = alignPL (AdmAList α pre ρ) (AdmAOptT α sp ρ) (AdmAList α suf ρ) as := by
  unfold listOutA at h
  rcases hL : Sem.list (S := S) with _ | L
  · rw [hL] at h; exact absurd h (by simp)
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmA, hL, h]

/-- A `list` reads no attribute that the list former does not read. -/
theorem AdmA_list_of_none {pre suf : List (Term S)} {sp : Option (Term S)} {a : Sem.A S}
    (h : listOutA a = none) : AdmA α (.list pre sp suf) ρ a = false := by
  unfold listOutA at h
  rcases hL : Sem.list (S := S) with _ | L
  · simp only [AdmA, hL]
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmA, hL, h]

/-- A body reads an attribute that the map former reads by two tests. -/
theorem AdmABody_of_out {b : Body S} {a : Sem.A S} {m : MapOf (Sem.A S)} (h : mapOutA a = some m) :
    AdmABody α b ρ a = (valPresentT b.fields b.at m.keys &&
      objAdmV ⟨b.fields, fun k => AdmAField α (b.at k) ρ⟩ (AdmAWild α b.wild ρ) m.keys m.get) := by
  unfold mapOutA at h
  cases b with
  | mk fields fld wild =>
  rcases hL : Sem.map (S := S) with _ | F
  · rw [hL] at h; exact absurd h (by simp)
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmABody, hL, h, Body.fields_mk, Body.at_mk, Body.wild_mk]

/-- A body reads no attribute that the map former does not read. -/
theorem AdmABody_of_none {b : Body S} {a : Sem.A S} (h : mapOutA a = none) :
    AdmABody α b ρ a = false := by
  unfold mapOutA at h
  cases b with
  | mk fields fld wild =>
  rcases hL : Sem.map (S := S) with _ | F
  · simp only [AdmABody, hL]
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmABody, hL, h]

/-- The bottom reads nothing. -/
@[simp] theorem AdmA_never (a : Sem.A S) : AdmA α (.never : Term S) ρ a = false := by simp [AdmA]

variable (α) in
/-- `⋁` of `AdmA` over a union's options. -/
def AdmAAny (ts : List (Term S)) (ρ : List S.C) (a : Sem.A S) : Bool := anyP (AdmAList α ts ρ) a

/-- An empty list of options reads no attribute. -/
@[simp] theorem AdmAAny_nil (a : Sem.A S) : AdmAAny α ([] : List (Term S)) ρ a = false := rfl

/-- The options read where the first reads or the rest read. -/
@[simp] theorem AdmAAny_cons (t : Term S) (ts : List (Term S)) (a : Sem.A S) :
    AdmAAny α (t :: ts) ρ a = (AdmA α t ρ a || AdmAAny α ts ρ a) := rfl

/-- A union reads where one of its options reads. -/
theorem AdmA_union (opts : List (Term S)) (a : Sem.A S) :
    AdmA α (.union opts) ρ a = AdmAAny α opts ρ a := by simp [AdmA, AdmAAny]

/-- The read-side rows of a term list are that list mapped. -/
theorem AdmAList_eq_map (ts : List (Term S)) : AdmAList α ts ρ = ts.map (AdmA α · ρ) :=
  AdmAList_eq ρ ts

/-- …and the same for the spread. -/
theorem AdmAOptT_eq_map (sp : Option (Term S)) : AdmAOptT α sp ρ = sp.map (AdmA α · ρ) := by
  cases sp <;> rfl

omit [PrimAdm S] [PrimAdmA S] in
/-- **A recursive term reads as its body reads over the stage below the attribute's depth.** -/
theorem mu_p_unfold (b : Term S) (ρ : List S.C) (a : Sem.A S) :
    (denote α (.mu b) ρ).p a
      = (denote α b (muStage (fun c => denote α b (c :: ρ)) (Sem.dA a - 1) :: ρ)).p a := by
  show (muStage (fun c => denote α b (c :: ρ)) (Sem.dA a)).p a = _
  obtain ⟨n, hn⟩ : ∃ n, Sem.dA a = n + 1 := ⟨Sem.dA a - 1, by have := Sem.dA_pos a; omega⟩
  rw [hn, Nat.add_sub_cancel]
  rfl

/-- …and so it reads where its body reads over that stage. -/
theorem AdmA_mu_unfold (b : Term S) (ρ : List S.C) (a : Sem.A S) :
    AdmA α (.mu b) ρ a
      = AdmA α b (muStage (fun c => denote α b (c :: ρ)) (Sem.dA a - 1) :: ρ) a := by
  rw [AdmA_eq_isSome b, ← mu_p_unfold]
  rfl

/-- **A body reads a map by its slots**, the read side's twin of `AdmBody_map_slots`. -/
theorem AdmABody_map_slots (c : Body S) {x : Sem.A S} {m : MapOf (Sem.A S)}
    (hm : mapOutA x = some m) :
    AdmABody α c ρ x = true ↔
      (∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ m.keys) ∧
      ∀ k : {k // k ∈ m.keys}, AdmAField α (c.slotAt k.1) ρ (m.get k) = true := by
  rw [AdmABody_of_out hm, valPresentT_req, Bool.and_eq_true, reqs_slotAt]
  apply and_congr Iff.rfl
  unfold objAdmV; rw [decide_eq_true_iff]
  refine forall_congr' fun k => ?_
  unfold entryP; simp only [MapOf.at]
  rcases Decidable.em (k.1 ∈ c.fields) with hk | hk
  · rw [dif_pos hk, Body.slotAt_pos hk]; rfl
  · rw [dif_neg hk, Body.slotAt_neg hk]
    cases hw : c.wild with
    | none => simp [AdmAWild, Body.block, hw, AdmAField]
    | some t => simp [AdmAWild, Body.block, hw, AdmAField]

end

/-! ## The laws, on the read side -/

/-- **The read-side law of the set former.** The catch-all rows of the families read the
    disjointness of the former classes (`Shapes`). -/
class FormerAdmA (S : Syn) [Sem S] [PrimAdm S] [PrimAdmA S] : Prop where
  /-- Two sets whose elements share no attribute share no set. -/
  set_never : ∀ {α : Table S} (a y : Term S), (∀ u, (AdmA α a [] u && AdmA α y [] u) = false) →
    ∀ c, (AdmA α (.set a) [] c && AdmA α (.set y) [] c) = false

/-- **The read-side law of the leaves.** A primitive reads no variable, so the law is stated at
    the closed environment. -/
class LeafAdmA (S : Syn) [Sem S] [PrimAdm S] [PrimAdmA S] [Leaf S] : Prop where
  /-- Two primitives met at the bottom share no attribute. -/
  prim_none : ∀ {α : Table S} (g g' : S.Ground), Leaf.prim g g' = none →
    ∀ c, (AdmA α (.prim g : Term S) [] c && AdmA α (.prim g') [] c) = false

/-! ## Soundness, on the read side -/

/-- The environments keep each paired binder pair apart: no value written by both. -/
def ApartA (p : Pairing) (ρ ρ' : List S.C) : Prop :=
  ∀ i j k, p i j = some k → ∀ v, (((envAt ρ i).p v).isSome && ((envAt ρ' j).p v).isSome) = false

omit [PrimAdm S] [PrimAdmA S] in
/-- Apart environments stay apart when the left operand unfolds: its new binder pairs with
    nothing. -/
theorem ApartA.left {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') (c : S.C) :
    ApartA (shiftL p) (c :: ρ) ρ' := by
  intro i j k hp v
  match i, hp with
  | 0, hp => exact nomatch hp
  | i + 1, hp => exact h i j k hp v

omit [PrimAdm S] [PrimAdmA S] in
/-- …and when the right operand unfolds. -/
theorem ApartA.right {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') (c : S.C) :
    ApartA (shiftR p) ρ (c :: ρ') := by
  intro i j k hp v
  match i, j, hp with
  | _, 0, hp => exact nomatch hp
  | i, j + 1, hp => exact h i j k hp v

omit [PrimAdm S] [PrimAdmA S] in
/-- Two new binders that read no attribute in common extend two apart environments at a paired
    binder. -/
theorem ApartA.mu {p : Pairing} {ρ ρ' : List S.C} (h : ApartA p ρ ρ') {c c' : S.C}
    (hc : ∀ v, ((c.p v).isSome && (c'.p v).isSome) = false) :
    ApartA (pairMu p) (c :: ρ) (c' :: ρ') := by
  intro i j k hp v
  match i, j, hp with
  | 0, 0, _ => exact hc v
  | i + 1, j + 1, hp =>
    simp only [pairMu, Option.map_eq_some_iff] at hp
    obtain ⟨k', hk, rfl⟩ := hp
    exact h i j k' hk v
  | 0, _ + 1, hp => exact nomatch hp
  | _ + 1, 0, hp => exact nomatch hp

variable (α) in
/-- A family is sound for `x` where every partner it accepts shares no value with `x`. -/
def DisjSoundA (ρ ρ' : List S.C) (x : Term S) (f : Term S → Bool) : Prop :=
  ∀ y, f y = true → ∀ v, (AdmA α x ρ v && AdmA α y ρ' v) = false

/-- A refinement reads what its inner term reads to a value that its predicate holds on. -/
theorem AdmA_refine_eq (t : Term S) (q : S.Pred) (ρ : List S.C) (v : Sem.A S) :
    AdmA α (.refine t q) ρ v = (AdmA α t ρ v && refineReads α t ρ (Sem.eval q) v) := rfl

omit [PrimAdm S] [PrimAdmA S] in
/-- A held-free closed term decodes an attribute as the top decodes it. -/
theorem top_of_HF_closed [TopLaws S] {t : Term S} (hh : hasHeld t = false) (hv : t.hasVar = false)
    (ρ : List S.C) {a : Sem.A S} {u : S.V} (h : (denote α t ρ).p a = some u) :
    (Sem.top (S := S)).p a = some u := by
  rw [denote_closed t hv ρ []] at h
  exact (sub_denoteIn t hh [] (fun i => by simp only [envAt, List.getD_nil]; exact sub_empty)).2 a u h

omit [PrimAdm S] [PrimAdmA S] in
/-- A refinement over a held-free closed term reads only what the top reads to a value that
    satisfies the predicate. -/
theorem refineReads_top [TopLaws S] {t : Term S} (hh : hasHeld t = false) (hv : t.hasVar = false)
    {ρ : List S.C} {q : S.V → Bool} {a : Sem.A S} (h : refineReads α t ρ q a = true) :
    ∃ u, (Sem.top (S := S)).p a = some u ∧ q u = true := by
  unfold refineReads at h
  split at h
  · next u hu => exact ⟨u, top_of_HF_closed hh hv ρ hu, h⟩
  · exact nomatch h

omit [PrimAdm S] [PrimAdmA S] in
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
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α ρ ρ' x (fam q)) :
    ∀ (y : Term S) (p : Pairing) (ρ' : List S.C), ApartA p ρ ρ' →
      disjSRight fam p y = true → ∀ v, (AdmA α x ρ v && AdmA α y ρ' v) = false
  | .never, _, _, _, _, v => by simp
  | .mu b, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [AdmA_mu_unfold b ρ' v]
      exact disjSRight_soundA hf b (shiftR p) _ (hp.right _) h v
  | .refine y q, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [AdmA_refine_eq, ← Bool.and_assoc, disjSRight_soundA hf y p ρ' hp h v, Bool.false_and]
  | .union os, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [AdmA_union]
      exact disjSRightL_soundA hf os p ρ' hp h v
  | .prim g, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .set t, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .list a b c, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .held a b k, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .opaq, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .object b, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .var j, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
/-- …and over the options of a union. -/
theorem disjSRightL_soundA {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartA q ρ ρ' → DisjSoundA α ρ ρ' x (fam q)) :
    ∀ (ys : List (Term S)) (p : Pairing) (ρ' : List S.C), ApartA p ρ ρ' →
      disjSRightL fam p ys = true → ∀ v, (AdmA α x ρ v && AdmAAny α ys ρ' v) = false
  | [], _, _, _, _, v => by simp
  | y :: ys, p, ρ', hp, h, v => by
      simp only [disjSRightL, Bool.and_eq_true] at h
      rw [AdmAAny_cons, Bool.and_or_distrib_left, disjSRight_soundA hf y p ρ' hp h.1 v,
        disjSRightL_soundA hf ys p ρ' hp h.2 v, Bool.false_or]
end

mutual
/-- **The split of the right operand is sound**, given a sound family at the pairing. -/
theorem splitR_soundA {ρ ρ' : List S.C} {x : Term S} {fam : Pairing → Term S → Bool} {p : Pairing}
    (hf : DisjSoundA α ρ ρ' x (fam p)) :
    ∀ (y : Term S), splitR fam p y = true → ∀ v, (AdmA α x ρ v && AdmA α y ρ' v) = false
  | .never, _, v => by simp
  | .union os, h, v => by
      simp only [splitR] at h
      rw [AdmA_union]
      exact splitRL_soundA hf os h v
  | .mu b, h, v => hf _ (by simpa only [splitR] using h) v
  | .refine y q, h, v => hf _ (by simpa only [splitR] using h) v
  | .prim g, h, v => hf _ (by simpa only [splitR] using h) v
  | .set t, h, v => hf _ (by simpa only [splitR] using h) v
  | .list a b c, h, v => hf _ (by simpa only [splitR] using h) v
  | .held a b k, h, v => hf _ (by simpa only [splitR] using h) v
  | .opaq, h, v => hf _ (by simpa only [splitR] using h) v
  | .object b, h, v => hf _ (by simpa only [splitR] using h) v
  | .var j, h, v => hf _ (by simpa only [splitR] using h) v
/-- …and over the options of a union. -/
theorem splitRL_soundA {ρ ρ' : List S.C} {x : Term S} {fam : Pairing → Term S → Bool} {p : Pairing}
    (hf : DisjSoundA α ρ ρ' x (fam p)) :
    ∀ (ys : List (Term S)), splitRL fam p ys = true → ∀ v, (AdmA α x ρ v && AdmAAny α ys ρ' v) = false
  | [], _, v => by simp
  | y :: ys, h, v => by
      simp only [splitRL, Bool.and_eq_true] at h
      rw [AdmAAny_cons, Bool.and_or_distrib_left, splitR_soundA hf y h.1 v,
        splitRL_soundA hf ys h.2 v, Bool.false_or]
end

/-- **Two data predicates that meet at the empty predicate keep two refinements apart on the
    read side**, where both inner terms are closed and held-free: both then read one value, the
    value that the top reads. -/
theorem predApart_soundA [Leaf S] [LeafAdm S] [TopLaws S] {q : S.Pred} {ρ' : List S.C} :
    ∀ (y : Term S), predApart q y = true → ∀ a u, (Sem.top (S := S)).p a = some u →
      Sem.eval q u = true → AdmA α y ρ' a = false
  | .refine y q', h, a, u, htop, hq => by
      simp only [predApart, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rw [AdmA_refine_eq]
      rcases h with ⟨⟨⟨-, hh⟩, hv⟩, hm⟩ | h
      · have hn : Leaf.pmeet q q' = some none := by
          revert hm; cases Leaf.pmeet q q' with
          | none => simp
          | some o => cases o <;> simp
        have hpm := LeafAdm.pmeet_none q q' hn u
        cases hr : refineReads α y ρ' (Sem.eval q') a with
        | false => simp
        | true =>
          obtain ⟨u', hu', hq'⟩ := refineReads_top (α := α) hh hv hr
          rw [htop] at hu'; cases hu'
          rw [hq, hq'] at hpm; exact absurd hpm (by simp)
      · rw [predApart_soundA (ρ' := ρ') y h a u htop hq, Bool.false_and]
  | .prim _, h, _, _, _, _ | .never, h, _, _, _, _ | .set _, h, _, _, _, _
  | .list _ _ _, h, _, _, _, _ | .held _ _ _, h, _, _, _, _
  | .opaq, h, _, _, _, _ | .object _, h, _, _, _, _ | .union _, h, _, _, _, _
  | .var _, h, _, _, _, _ | .mu _, h, _, _, _, _ => by
      simp [predApart] at h

/-- **The leaf family is sound on the read side**: the leaf law, and the shape classes at every
    former. -/
theorem famPrimD_soundA [Leaf S] [LeafAdmA S] [Shapes S] {ρ ρ' : List S.C} (g : S.Ground) :
    DisjSoundA α ρ ρ' (.prim g) (famPrimD g) := by
  intro y h v
  cases y with
  | prim g' =>
      simp only [famPrimD, Option.isNone_iff_eq_none] at h
      exact LeafAdmA.prim_none (α := α) g g' h v
  | set t => exact Shapes.prim_setA g t v
  | list a b c => exact Shapes.prim_listA g a b c v
  | object b => exact Shapes.prim_objA g b v
  | _ => simp [famPrimD] at h

/-- **The variable family is sound**: a paired binder pair reads no attribute in common. -/
theorem famVarD_soundA {ρ ρ' : List S.C} {i : Nat} {q : Pairing} (hq : ApartA q ρ ρ') :
    DisjSoundA α ρ ρ' (.var i) (famVarD i q) := by
  intro y h v
  cases y with
  | var j =>
      simp only [famVarD, Option.isSome_iff_exists] at h
      obtain ⟨k, hk⟩ := h
      exact hq i j k hk v
  | _ => simp [famVarD] at h

/-- **The set family is sound**: the set law over closed elements, and the shape classes at
    every other former. -/
theorem famSetD_soundA [FormerAdmA S] [Shapes S] {ρ ρ' : List S.C} (a : Term S)
    {mt : Term S → Bool} (hmt : DisjSoundA α ρ ρ' a mt) :
    DisjSoundA α ρ ρ' (.set a) (famSetD a mt) := by
  intro y h v
  cases y with
  | set y' =>
      simp only [famSetD, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨ha, hy⟩, hm⟩ := h
      have hc := FormerAdmA.set_never a y' (fun u => by
        rw [← AdmA_closed a ha ρ [], ← AdmA_closed y' hy ρ' []]; exact hmt y' hm u) v
      rwa [AdmA_closed (.set a) ha ρ [], AdmA_closed (.set y') hy ρ' []]
  | prim g =>
      have := Shapes.prim_setA (α := α) (ρ := ρ') (ρ' := ρ) g a v
      rw [Bool.and_comm]; exact this
  | list x y z => exact Shapes.set_listA a x y z v
  | object b => exact Shapes.set_objA a b v
  | _ => simp [famSetD] at h



variable (α) in
/-- Two rows of terms share no row of values. -/
def RowsApartA (ρ ρ' : List S.C) (r₁ r₂ : List (Term S)) : Prop :=
  ∀ ws : List (Sem.A S), (zipP (AdmAList α r₁ ρ) ws && zipP (AdmAList α r₂ ρ') ws) = false

/-- One disjoint position keeps two rows of one length apart. -/
theorem rowsApartA_of_anyZip {ρ ρ' : List S.C} :
    ∀ {r₁ : List (Term S)} {fs : List (Term S → Bool)}, List.Forall₂ (DisjSoundA α ρ ρ') r₁ fs →
      ∀ {r₂ : List (Term S)}, anyZip fs r₂ = true → RowsApartA α ρ ρ' r₁ r₂
  | _, _, .nil, _, h, _ => by simp [anyZip] at h
  | t :: r₁, f :: fs, .cons ht hr, r₂, h, ws => by
      cases r₂ with
      | nil => simp [anyZip] at h
      | cons u r₂ =>
        cases ws with
        | nil => simp [AdmAList, zipP]
        | cons w ws =>
          simp only [anyZip, Bool.or_eq_true] at h
          simp only [AdmAList, zipP]
          rcases h with h | h
          · have := ht u h w
            cases h1 : AdmA α t ρ w <;> cases h2 : AdmA α u ρ' w <;> simp_all
          · have := rowsApartA_of_anyZip hr h ws
            cases h1 : zipP (AdmAList α r₁ ρ) ws <;> cases h2 : zipP (AdmAList α r₂ ρ') ws <;>
              simp_all

/-- Two rows stay apart when a common prefix of equal length goes in front. -/
theorem RowsApartA.append_left {ρ ρ' : List S.C} {A₁ A₂ X₁ X₂ : List (Term S)}
    (hA : A₁.length = A₂.length) (h : RowsApartA α ρ ρ' A₁ A₂) :
    RowsApartA α ρ ρ' (A₁ ++ X₁) (A₂ ++ X₂) := by
  intro ws
  rcases Nat.lt_or_ge ws.length A₁.length with hl | hl
  · rw [zipP_false_of_length_ne _ _ (by simp [AdmAList_eq]; omega), Bool.false_and]
  · rw [← List.take_append_drop A₁.length ws, AdmAList_eq, AdmAList_eq, List.map_append,
      List.map_append, zipP_append _ _ _ _ (by simp; omega),
      zipP_append _ _ _ _ (by simp; omega)]
    have := h (ws.take A₁.length)
    rw [AdmAList_eq, AdmAList_eq] at this
    cases h1 : zipP (A₁.map (AdmA α · ρ)) (ws.take A₁.length) <;>
      cases h2 : zipP (A₂.map (AdmA α · ρ')) (ws.take A₁.length) <;> simp_all

/-- …and when a common suffix of equal length goes behind. -/
theorem RowsApartA.append_right {ρ ρ' : List S.C} {B₁ B₂ X₁ X₂ : List (Term S)}
    (hX : X₁.length = X₂.length) (h : RowsApartA α ρ ρ' B₁ B₂) :
    RowsApartA α ρ ρ' (X₁ ++ B₁) (X₂ ++ B₂) := by
  intro ws
  rcases Nat.lt_or_ge ws.length X₁.length with hl | hl
  · rw [zipP_false_of_length_ne _ _ (by simp [AdmAList_eq]; omega), Bool.false_and]
  · rw [← List.take_append_drop X₁.length ws, AdmAList_eq, AdmAList_eq, List.map_append,
      List.map_append, zipP_append _ _ _ _ (by simp; omega),
      zipP_append _ _ _ _ (by simp; omega)]
    have := h (ws.drop X₁.length)
    rw [AdmAList_eq, AdmAList_eq] at this
    cases h1 : zipP (B₁.map (AdmA α · ρ)) (ws.drop X₁.length) <;>
      cases h2 : zipP (B₂.map (AdmA α · ρ')) (ws.drop X₁.length) <;> simp_all

/-- Two `list` shapes whose rows are apart at every common length share no value. -/
theorem AdmA_list_apart {ρ ρ' : List S.C} {p₁ s₁ p₂ s₂ : List (Term S)} {q₁ q₂ : Option (Term S)}
    (h : ∀ n r₁ r₂, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      RowsApartA α ρ ρ' r₁ r₂) (v : Sem.A S) :
    (AdmA α (.list p₁ q₁ s₁) ρ v && AdmA α (.list p₂ q₂ s₂) ρ' v) = false := by
  cases hv : listOutA v with
  | none => simp [AdmA_list_of_none hv]
  | some ws =>
      rw [AdmA_list_of_out hv, AdmA_list_of_out hv, AdmAList_eq_map, AdmAOptT_eq_map, AdmAList_eq_map,
        AdmAList_eq_map, AdmAOptT_eq_map, AdmAList_eq_map, alignPL_eq_rowOfG, alignPL_eq_rowOfG,
        rowOfG_map, rowOfG_map]
      cases h₁ : rowOfG p₁ q₁ s₁ ws.length with
      | none => simp
      | some r₁ =>
        cases h₂ : rowOfG p₂ q₂ s₂ ws.length with
        | none => simp
        | some r₂ =>
          have := h _ _ _ h₁ h₂ ws
          simpa only [Option.map_some, AdmAList_eq] using this

/-- **The list family is sound on the read side.** Two attributes of different lengths differ,
    so each common length needs one disjoint position. -/
theorem famListD_soundA [Shapes S] {ρ ρ' : List S.C} {pre suf : List (Term S)}
    {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Bool)} {fsp : Option (Term S → Bool)}
    (hp : List.Forall₂ (DisjSoundA α ρ ρ') pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ DisjSoundA α ρ ρ' t f)
    (hf : List.Forall₂ (DisjSoundA α ρ ρ') suf fsuf) :
    DisjSoundA α ρ ρ' (.list pre sp suf) (famListD fpre fsp fsuf) := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro y h v
  cases y with
  | prim g => rw [Bool.and_comm]; exact Shapes.prim_listA g pre sp suf v
  | set t => rw [Bool.and_comm]; exact Shapes.set_listA t pre sp suf v
  | object b => exact Shapes.list_objA pre sp suf b v
  | list pre₂ sp₂ suf₂ =>
    simp only [famListD] at h
    refine AdmA_list_apart (fun n r₁ r₂ h₁ h₂ => ?_) v
    rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, htf⟩
    · -- the left states one arity
      simp only [listDisjRow] at h
      rw [rowOfG_none_eq] at h₁
      split at h₁
      · next hn =>
        simp only [Option.some.injEq] at h₁; subst h₁
        rw [show fpre.length + fsuf.length = n by omega, h₂] at h
        exact rowsApartA_of_anyZip (forall₂_append hp hf) h
      · exact nomatch h₁
    · cases sp₂ with
      | none =>
        simp only [listDisjRow] at h
        rw [rowOfG_none_eq] at h₂
        split at h₂
        · next hn =>
          simp only [Option.some.injEq] at h₂; subst h₂
          subst hn
          cases hfs : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
          | none =>
            have := rowOfG_isSome_len h₁
            rw [rowOfG_some_eq, if_neg (by omega)] at hfs
            exact nomatch hfs
          | some fs =>
            rw [hfs] at h
            have hF := rowOfG_forall₂ (R := DisjSoundA α ρ ρ') hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf
              h₁ hfs
            exact rowsApartA_of_anyZip hF h
        · exact nomatch h₂
      | some c =>
        simp only [listDisjRow] at h
        split at h
        · next hdom =>
          have hdm := dominates_max hdom
          have hn₁ := rowOfG_isSome_len h₁
          have hn₂ := rowOfG_isSome_len h₂
          generalize hP : max fpre.length pre₂.length = P at h hdm
          generalize hS : max fsuf.length suf₂.length = S' at h hdm
          split at h
          · next fs us hfs hus =>
            obtain ⟨rN, hrN⟩ := rowOfG_total (pre := pre) (suf := suf) (c := t) (n := P + S')
              (by omega)
            have hF := rowOfG_forall₂ (R := DisjSoundA α ρ ρ') hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf
              hrN hfs
            have hr₁ := rowOfG_respread (P := P) (S := S') (n := n) (by omega) (by omega)
              (by omega) hrN h₁
            have hr₂ := rowOfG_respread (P := P) (S := S') (n := n) (by omega) (by omega)
              (by omega) hus h₂
            have hlN := rowOfG_length hrN
            have hlu := rowOfG_length hus
            have hlf' := hF.length_eq
            subst hr₁ hr₂
            rcases anyZip_take_drop P h with ha | ha
            · rw [List.append_assoc, List.append_assoc]
              exact RowsApartA.append_left (by simp; omega)
                (rowsApartA_of_anyZip (List.forall₂_take P hF) ha)
            · exact RowsApartA.append_right (by simp; omega)
                (rowsApartA_of_anyZip (List.forall₂_drop P hF) ha)
          · exact nomatch h
        · exact nomatch h
  | _ => simp [famListD] at h



/-- **Two bodies apart at one name** share no map: the name is required on one side, so a
    common map holds the name, and the two slots share no value there. -/
theorem AdmABody_apart_at {ρ ρ' : List S.C} {a b : Body S} {k : String}
    (hr : (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)) = true)
    (hs : ∀ w, (AdmAField α (a.slotAt k) ρ w && AdmAField α (b.slotAt k) ρ' w) = false) (v : Sem.A S) :
    (AdmABody α a ρ v && AdmABody α b ρ' v) = false := by
  refine Bool.eq_false_iff.mpr (fun hab => ?_)
  rw [Bool.and_eq_true] at hab
  obtain ⟨hA, hB⟩ := hab
  cases hv : mapOutA v with
  | none => rw [AdmABody_of_none hv] at hA; exact absurd hA (by simp)
  | some m =>
    rw [AdmABody_map_slots _ hv] at hA hB
    rw [Bool.or_eq_true] at hr
    have hk : k ∈ m.keys := hr.elim (hA.1 k) (hB.1 k)
    have h1 := hs (m.get ⟨k, hk⟩)
    rw [hA.2 ⟨k, hk⟩, hB.2 ⟨k, hk⟩] at h1
    exact absurd h1 (by simp)

/-- **The object family is sound**: two bodies read no map in common where one name holds two
    disjoint slots, one of them required. -/
theorem famObjD_soundA [Shapes S] {ρ ρ' : List S.C} {a : Body S}
    {g : {k // k ∈ a.fields} → ObjectSlot S → Bool} {mw : Term S → Bool}
    (hg : ∀ k s, g k s = true → (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq s) = true ∧
      ∀ w, (AdmAField α (a.at k) ρ w && AdmAField α s ρ' w) = false)
    (hmw : DisjSoundA α ρ ρ' a.block mw) :
    DisjSoundA α ρ ρ' (.object a) (famObjD a g mw) := by
  intro y h v
  cases y with
  | prim g' => rw [Bool.and_comm]; exact Shapes.prim_objA g' a v
  | set t => rw [Bool.and_comm]; exact Shapes.set_objA t a v
  | list p q s => rw [Bool.and_comm]; exact Shapes.list_objA p q s a v
  | object b =>
    simp only [famObjD, decide_eq_true_eq] at h
    obtain ⟨⟨k, hk⟩, hd⟩ := h
    show (AdmABody α a ρ v && AdmABody α b ρ' v) = false
    unfold slotD at hd
    split at hd
    · next ha =>
      have hb : (if h' : k ∈ b.fields then b.at ⟨k, h'⟩ else .optional b.block) = b.slotAt k := rfl
      rw [hb] at hd
      obtain ⟨hr, hs⟩ := hg _ _ hd
      rw [← Body.slotAt_pos ha] at hr hs
      exact AdmABody_apart_at hr hs v
    · next ha =>
      have hkb : k ∈ b.fields := (Finset.mem_union.mp hk).resolve_left ha
      split at hd
      · next y hy =>
        have hbs : b.slotAt k = .req y := by rw [Body.slotAt_pos hkb]; exact hy
        refine AdmABody_apart_at (k := k) (by rw [hbs]; simp [ObjectSlot.isReq]) (fun w => ?_) v
        rw [hbs, Body.slotAt_neg ha]
        exact hmw y hd w
      · exact nomatch hd
  | _ => simp [famObjD] at h

mutual
/-- **Soundness of the zero test, on the write side.** Where `disjoint` answers `true`, no value
    is admitted by both operands, under every two environments that keep the paired binders
    apart. -/
theorem disjoint_soundA [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (x y : Term S), Term.disjoint p x y = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' → ∀ v, (AdmA α x ρ v && AdmA α y ρ' v) = false
  | _, .never, _, _, _, _, _, _ => by simp
  | p, .held _ _ _, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fam := fun _ _ => false)
        (fun _ _ _ _ hh => nomatch hh) y p ρ' hp h v
  | p, .var i, y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fun _ _ hq => famVarD_soundA hq) y p ρ' hp h v
  | p, .mu b, y, h, ρ, ρ', hp, v => by
      cases y with
      | mu b' =>
        simp only [Term.disjoint] at h
        have hB : ∀ c c', (∀ u, ((c.p u).isSome && (c'.p u).isSome) = false) →
            ∀ u, (((denote α b (c :: ρ)).p u).isSome && ((denote α b' (c' :: ρ')).p u).isSome)
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
  | p, .refine x q, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjoint] at h
      refine splitR_soundA (ρ := ρ) (ρ' := ρ') (x := .refine x q) (p := p) ?_ y h v
      intro y' hy w
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hy
      rw [AdmA_refine_eq]
      rcases hy with hy | ⟨⟨⟨-, hh⟩, hv⟩, hy⟩
      · have := disjoint_soundA p x y' hy ρ ρ' hp w
        cases h1 : AdmA α x ρ w <;> cases h2 : AdmA α y' ρ' w <;> simp_all
      · cases hr : refineReads α x ρ (Sem.eval q) w with
        | false => simp
        | true =>
          simp only [Bool.not_eq_true'] at hh hv
          obtain ⟨u, hu, hq⟩ := refineReads_top (α := α) hh hv hr
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
      disjSRight_soundA (ρ := ρ) (fun q ρ₁ hq => famObjD_soundA (a := .mk fs f none)
        (fun k s hs => slot_soundA q (f k) s hs ρ ρ₁ hq)
        (fun _ _ w => by simp [Body.block])) y p ρ' hp h v
  | p, .object (.mk fs f (some t)), y, h, ρ, ρ', hp, v =>
      disjSRight_soundA (ρ := ρ) (fun q ρ₁ hq => famObjD_soundA (a := .mk fs f (some t))
        (fun k s hs => slot_soundA q (f k) s hs ρ ρ₁ hq)
        (fun u hu w => disjoint_soundA q t u hu ρ ρ₁ hq w)) y p ρ' hp h v
termination_by structural _ x => x
/-- …and a union, option by option. -/
theorem disjointL_soundA [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (os : List (Term S)) (y : Term S), Term.disjointL p os y = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' → ∀ v, (AdmAAny α os ρ v && AdmA α y ρ' v) = false
  | _, [], _, _, _, _, _, _ => by simp
  | p, x :: xs, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjointL, Bool.and_eq_true] at h
      have h1 := disjoint_soundA p x y h.1 ρ ρ' hp v
      have h2 := disjointL_soundA p xs y h.2 ρ ρ' hp v
      rw [AdmAAny_cons]
      cases a1 : AdmA α x ρ v <;> cases a2 : AdmAAny α xs ρ v <;> cases a3 : AdmA α y ρ' v <;> simp_all
termination_by structural _ os => os
/-- …and each position of a row, partially applied. -/
theorem disjointTs_soundA [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (ts : List (Term S)) (ρ ρ' : List S.C), ApartA p ρ ρ' →
      List.Forall₂ (DisjSoundA α ρ ρ') ts (Term.disjointTs p ts)
  | _, [], _, _, _ => .nil
  | p, t :: ts, ρ, ρ', hp =>
      .cons (fun u hu w => disjoint_soundA p t u hu ρ ρ' hp w) (disjointTs_soundA p ts ρ ρ' hp)
termination_by structural _ ts => ts
/-- …and two slots, where one requires the name. -/
theorem slot_soundA [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] :
    ∀ (p : Pairing) (s s' : ObjectSlot S), ObjectSlot.disjoint p s s' = true →
      ∀ (ρ ρ' : List S.C), ApartA p ρ ρ' →
        (ObjectSlot.isReq s || ObjectSlot.isReq s') = true ∧
          ∀ w, (AdmAField α s ρ w && AdmAField α s' ρ' w) = false
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
theorem disjoint_orthogonal [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdm S] [FormerAdmA S]
    [Shapes S] [TopLaws S] {p : Pairing} {x y : Term S} (h : Term.disjoint p x y = true) :
    (∀ ρ ρ', ApartV p ρ ρ' → ∀ v, (Adm α x ρ v && Adm α y ρ' v) = false) ∧
    (∀ ρ ρ', ApartA p ρ ρ' → ∀ a, (AdmA α x ρ a && AdmA α y ρ' a) = false) :=
  ⟨fun ρ ρ' hp v => disjoint_sound p x y h ρ ρ' hp v,
   fun ρ ρ' hp a => disjoint_soundA p x y h ρ ρ' hp a⟩

end Calculus.Alg
