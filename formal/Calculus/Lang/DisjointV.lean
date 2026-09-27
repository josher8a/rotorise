import Calculus.Lang.Disjoint
import Calculus.Lang.ExactV
import Calculus.Lang.Shapes

/-!
# Disjointness on the write side, over a universe signature

`Alg.disjoint_sound` states that `Term.disjoint` is sound on the write side: where the test
answers `true`, no value is admitted by both operands, under every two environments that keep
each paired binder pair apart (`ApartV`). The proof recurses on the left operand, as the test
does, and every row is structure except the leaves.

A universe supplies the laws in two classes. `FormerAdm` holds the set law: two sets whose
elements share no value share no set. `LeafAdm` holds the laws of the leaves: two primitives
that the leaf keeps apart share no value, and two predicates that meet at the empty predicate
hold together nowhere. Both classes are outside `Sem` and outside `Leaf`, because only the
soundness theorems read the laws. Two formers in different classes share no value, and that
fact is a theorem of the shape classes (`Shapes`).
-/

namespace Calculus.Alg

open Calculus (alignPL alignP zipP anyP objAdmV entryP)

variable {S : Syn} [Sem S] [PrimAdm S] {ρ ρ' ρ'' : List S.C}

noncomputable section

/-! ## Reading a value through a former -/

/-- The elements of a value, where the list former reads one. -/
def listOut (v : S.V) : Option (List S.V) := (Sem.list (S := S)).bind (·.pV.out v)

/-- The entries of a value, where the map former reads one. -/
def mapOut (v : S.V) : Option (MapOf S.V) := (Sem.map (S := S)).bind (·.mV.out v)

/-- A `list` admits a value that the list former reads by the row of its positions. -/
theorem Adm_list_of_out {pre suf : List (Term S)} {sp : Option (Term S)} {v : S.V}
    {vs : List S.V} (h : listOut v = some vs) :
    Adm (.list pre sp suf) ρ v = alignPL (AdmList pre ρ) (AdmOptT sp ρ) (AdmList suf ρ) vs := by
  unfold listOut at h
  rcases hL : Sem.list (S := S) with _ | L
  · rw [hL] at h; exact absurd h (by simp)
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [Adm, hL, h]

/-- A `list` admits no value that the list former does not read. -/
theorem Adm_list_of_none {pre suf : List (Term S)} {sp : Option (Term S)} {v : S.V}
    (h : listOut v = none) : Adm (.list pre sp suf) ρ v = false := by
  unfold listOut at h
  rcases hL : Sem.list (S := S) with _ | L
  · simp only [Adm, hL]
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [Adm, hL, h]

/-- A body admits a value that the map former reads by two tests: the required names are
    present, and each present name passes its row. -/
theorem AdmBody_of_out {b : Body S} {v : S.V} {m : MapOf S.V} (h : mapOut v = some m) :
    AdmBody b ρ v = (valPresentT b.fields b.at m.keys &&
      objAdmV ⟨b.fields, fun k => AdmField (b.at k) ρ⟩ (AdmWild b.wild ρ) m.keys m.get) := by
  unfold mapOut at h
  cases b with
  | mk fields fld wild =>
  rcases hL : Sem.map (S := S) with _ | F
  · rw [hL] at h; exact absurd h (by simp)
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmBody, hL, h, Body.fields_mk, Body.at_mk, Body.wild_mk]

/-- A body admits no value that the map former does not read. -/
theorem AdmBody_of_none {b : Body S} {v : S.V} (h : mapOut v = none) :
    AdmBody b ρ v = false := by
  unfold mapOut at h
  cases b with
  | mk fields fld wild =>
  rcases hL : Sem.map (S := S) with _ | F
  · simp only [AdmBody, hL]
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmBody, hL, h]

omit [Sem S] [PrimAdm S] in
/-- `valPresentT` in the form the object row uses: a declared name that must be present is
    present. -/
theorem valPresentT_req (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) :
    valPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (fld k) = true → k.1 ∈ keys) := by
  unfold valPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [ObjectSlot.isReq])
  · cases hf : fld k with
    | optional t => rfl
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))

/-- The bottom admits nothing. -/
@[simp] theorem Adm_never (v : S.V) : Adm (.never : Term S) ρ v = false := by simp [Adm]

/-- `⋁` of `Adm` over a union's options. -/
def AdmAny (ts : List (Term S)) (ρ : List S.C) (v : S.V) : Bool := anyP (AdmList ts ρ) v

/-- An empty list of options admits no value. -/
@[simp] theorem AdmAny_nil (v : S.V) : AdmAny ([] : List (Term S)) ρ v = false := rfl

/-- The options admit where the first admits or the rest admit. -/
@[simp] theorem AdmAny_cons (t : Term S) (ts : List (Term S)) (v : S.V) :
    AdmAny (t :: ts) ρ v = (Adm t ρ v || AdmAny ts ρ v) := rfl

/-- A union admits where one of its options admits. -/
theorem Adm_union (opts : List (Term S)) (v : S.V) :
    Adm (.union opts) ρ v = AdmAny opts ρ v := by simp [Adm, AdmAny]

/-- The rows of a term list are that list mapped, so `rowOfG_map` carries a row of terms
    onto the row of rows the admission reads. -/
theorem AdmList_eq_map (ts : List (Term S)) : AdmList ts ρ = ts.map (Adm · ρ) :=
  AdmList_eq ρ ts

/-- …and the same for the spread. -/
theorem AdmOptT_eq_map (sp : Option (Term S)) : AdmOptT sp ρ = sp.map (Adm · ρ) := by
  cases sp <;> rfl

omit [Sem S] [PrimAdm S] in
/-- The required names, read over the whole key space: an undeclared name is `optional`. -/
theorem reqs_slotAt (c : Body S) (keys : Finset String) :
    decide (∀ k : {k // k ∈ c.fields}, ObjectSlot.isReq (c.at k) = true → k.1 ∈ keys) = true ↔
    ∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ keys := by
  rw [decide_eq_true_iff]
  constructor
  · intro h k hr
    rcases Decidable.em (k ∈ c.fields) with hk | hk
    · rw [Body.slotAt_pos hk] at hr; exact h ⟨k, hk⟩ hr
    · rw [Body.slotAt_neg hk] at hr; exact absurd hr (by simp [ObjectSlot.isReq])
  · intro h k hr; exact h k.1 (by rw [Body.slotAt_pos k.2]; exact hr)

/-- **A body admits a map by its slots**: every name whose slot is required is present, and
    every present name passes its slot. -/
theorem AdmBody_map_slots (c : Body S) {v : S.V} {m : MapOf S.V} (hm : mapOut v = some m) :
    AdmBody c ρ v = true ↔
      (∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ m.keys) ∧
      ∀ k : {k // k ∈ m.keys}, AdmField (c.slotAt k.1) ρ (m.get k) = true := by
  rw [AdmBody_of_out hm, valPresentT_req, Bool.and_eq_true, reqs_slotAt]
  apply and_congr Iff.rfl
  unfold objAdmV; rw [decide_eq_true_iff]
  refine forall_congr' fun k => ?_
  unfold entryP; simp only [MapOf.at]
  rcases Decidable.em (k.1 ∈ c.fields) with hk | hk
  · rw [dif_pos hk, Body.slotAt_pos hk]; rfl
  · rw [dif_neg hk, Body.slotAt_neg hk]
    cases hw : c.wild with
    | none => simp [AdmWild, Body.block, hw, AdmField]
    | some t => simp [AdmWild, Body.block, hw, AdmField]

/-- **A recursive term admits what its body admits over the stage below the value's depth.** The
    limit reads a value at the stage that the value's depth names, and that stage is the body over
    the stage below. So the unfolding needs no guard. -/
theorem Adm_mu_unfold (b : Term S) (ρ : List S.C) (v : S.V) :
    Adm (.mu b) ρ v = Adm b (muStage (fun c => denote b (c :: ρ)) (Sem.dV v - 1) :: ρ) v := by
  rw [Adm_eq_isSome b]
  show ((muStage (fun c => denote b (c :: ρ)) (Sem.dV v)).e v).isSome = _
  obtain ⟨n, hn⟩ : ∃ n, Sem.dV v = n + 1 := ⟨Sem.dV v - 1, by have := Sem.dV_pos v; omega⟩
  rw [hn, Nat.add_sub_cancel]
  rfl

end

/-! ## The laws, on the write side -/

/-- **The write-side law of the set former.** The catch-all rows of the families read the
    disjointness of the former classes (`Shapes`). -/
class FormerAdm (S : Syn) [Sem S] [PrimAdm S] : Prop where
  /-- Two sets whose elements share no value share no set. -/
  set_never : ∀ a y : Term S, (∀ u, (Adm a [] u && Adm y [] u) = false) →
    ∀ v, (Adm (.set a) [] v && Adm (.set y) [] v) = false

/-- **The write-side laws of the leaves.** A primitive reads no variable, so the laws are
    stated at the closed environment. -/
class LeafAdm (S : Syn) [Sem S] [PrimAdm S] [Leaf S] : Prop where
  /-- Two primitives met at the bottom share no value. -/
  prim_none : ∀ g g' : S.Ground, Leaf.prim g g' = none →
    ∀ v, (Adm (.prim g : Term S) [] v && Adm (.prim g') [] v) = false
  /-- Two predicates met at the empty predicate hold together nowhere. -/
  pmeet_none : ∀ q p : S.Pred, Leaf.pmeet q p = some none →
    ∀ v, (Sem.eval q v && Sem.eval p v) = false


/-! ## Soundness, on the write side -/

/-- The environments keep each paired binder pair apart: no value written by both. -/
def ApartV (p : Pairing) (ρ ρ' : List S.C) : Prop :=
  ∀ i j k, p i j = some k → ∀ v, (((envAt ρ i).e v).isSome && ((envAt ρ' j).e v).isSome) = false

omit [PrimAdm S] in
/-- Apart environments stay apart when the left operand unfolds: its new binder pairs with
    nothing. -/
theorem ApartV.left {p : Pairing} {ρ ρ' : List S.C} (h : ApartV p ρ ρ') (c : S.C) :
    ApartV (shiftL p) (c :: ρ) ρ' := by
  intro i j k hp v
  match i, hp with
  | 0, hp => exact nomatch hp
  | i + 1, hp => exact h i j k hp v

omit [PrimAdm S] in
/-- …and when the right operand unfolds. -/
theorem ApartV.right {p : Pairing} {ρ ρ' : List S.C} (h : ApartV p ρ ρ') (c : S.C) :
    ApartV (shiftR p) ρ (c :: ρ') := by
  intro i j k hp v
  match i, j, hp with
  | _, 0, hp => exact nomatch hp
  | i, j + 1, hp => exact h i j k hp v

omit [PrimAdm S] in
/-- Two new binders that share no value extend two apart environments at a paired binder. -/
theorem ApartV.mu {p : Pairing} {ρ ρ' : List S.C} (h : ApartV p ρ ρ') {c c' : S.C}
    (hc : ∀ v, ((c.e v).isSome && (c'.e v).isSome) = false) :
    ApartV (pairMu p) (c :: ρ) (c' :: ρ') := by
  intro i j k hp v
  match i, j, hp with
  | 0, 0, _ => exact hc v
  | i + 1, j + 1, hp =>
    simp only [pairMu, Option.map_eq_some_iff] at hp
    obtain ⟨k', hk, rfl⟩ := hp
    exact h i j k' hk v
  | 0, _ + 1, hp => exact nomatch hp
  | _ + 1, 0, hp => exact nomatch hp

/-- A family is sound for `x` where every partner it accepts shares no value with `x`. -/
def DisjSound (ρ ρ' : List S.C) (x : Term S) (f : Term S → Bool) : Prop :=
  ∀ y, f y = true → ∀ v, (Adm x ρ v && Adm y ρ' v) = false

/-- A refinement admits what its inner term admits and its predicate holds on. -/
theorem Adm_refine_eq (t : Term S) (q : S.Pred) (ρ : List S.C) (v : S.V) :
    Adm (.refine t q) ρ v = (Adm t ρ v && Sem.eval q v) := rfl

omit [PrimAdm S] in
/-- **Two recursive terms are disjoint stage by stage.** Where the two bodies keep apart every
    two binders that share no value, each two stages of the same index share no value. -/
theorem stage_apart {B B' : S.C → S.C}
    (hB : ∀ c c', (∀ u, ((c.e u).isSome && (c'.e u).isSome) = false) →
      ∀ u, (((B c).e u).isSome && ((B' c').e u).isSome) = false) :
    ∀ n u, (((muStage B n).e u).isSome && ((muStage B' n).e u).isSome) = false
  | 0, _ => rfl
  | n + 1, u => hB _ _ (stage_apart hB n) u

mutual
/-- **The rows of the right operand are sound**, given a sound family for every pairing that
    keeps the environments apart. -/
theorem disjSRight_sound {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartV q ρ ρ' → DisjSound ρ ρ' x (fam q)) :
    ∀ (y : Term S) (p : Pairing) (ρ' : List S.C), ApartV p ρ ρ' →
      disjSRight fam p y = true → ∀ v, (Adm x ρ v && Adm y ρ' v) = false
  | .never, _, _, _, _, v => by simp
  | .mu b, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [Adm_mu_unfold b ρ' v]
      exact disjSRight_sound hf b (shiftR p) _ (hp.right _) h v
  | .refine y q, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [Adm_refine_eq, ← Bool.and_assoc, disjSRight_sound hf y p ρ' hp h v, Bool.false_and]
  | .union os, p, ρ', hp, h, v => by
      simp only [disjSRight] at h
      rw [Adm_union]
      exact disjSRightL_sound hf os p ρ' hp h v
  | .prim g, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .set t, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .list a b c, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .held a b c d, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .opaq, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .object b, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
  | .var j, p, ρ', hp, h, v => hf p ρ' hp _ (by simpa only [disjSRight] using h) v
/-- …and over the options of a union. -/
theorem disjSRightL_sound {ρ : List S.C} {x : Term S} {fam : Pairing → Term S → Bool}
    (hf : ∀ q ρ', ApartV q ρ ρ' → DisjSound ρ ρ' x (fam q)) :
    ∀ (ys : List (Term S)) (p : Pairing) (ρ' : List S.C), ApartV p ρ ρ' →
      disjSRightL fam p ys = true → ∀ v, (Adm x ρ v && AdmAny ys ρ' v) = false
  | [], _, _, _, _, v => by simp
  | y :: ys, p, ρ', hp, h, v => by
      simp only [disjSRightL, Bool.and_eq_true] at h
      rw [AdmAny_cons, Bool.and_or_distrib_left, disjSRight_sound hf y p ρ' hp h.1 v,
        disjSRightL_sound hf ys p ρ' hp h.2 v, Bool.false_or]
end

mutual
/-- **The split of the right operand is sound**, given a sound family at the pairing. -/
theorem splitR_sound {ρ ρ' : List S.C} {x : Term S} {fam : Pairing → Term S → Bool} {p : Pairing}
    (hf : DisjSound ρ ρ' x (fam p)) :
    ∀ (y : Term S), splitR fam p y = true → ∀ v, (Adm x ρ v && Adm y ρ' v) = false
  | .never, _, v => by simp
  | .union os, h, v => by
      simp only [splitR] at h
      rw [Adm_union]
      exact splitRL_sound hf os h v
  | .mu b, h, v => hf _ (by simpa only [splitR] using h) v
  | .refine y q, h, v => hf _ (by simpa only [splitR] using h) v
  | .prim g, h, v => hf _ (by simpa only [splitR] using h) v
  | .set t, h, v => hf _ (by simpa only [splitR] using h) v
  | .list a b c, h, v => hf _ (by simpa only [splitR] using h) v
  | .held a b c d, h, v => hf _ (by simpa only [splitR] using h) v
  | .opaq, h, v => hf _ (by simpa only [splitR] using h) v
  | .object b, h, v => hf _ (by simpa only [splitR] using h) v
  | .var j, h, v => hf _ (by simpa only [splitR] using h) v
/-- …and over the options of a union. -/
theorem splitRL_sound {ρ ρ' : List S.C} {x : Term S} {fam : Pairing → Term S → Bool} {p : Pairing}
    (hf : DisjSound ρ ρ' x (fam p)) :
    ∀ (ys : List (Term S)), splitRL fam p ys = true → ∀ v, (Adm x ρ v && AdmAny ys ρ' v) = false
  | [], _, v => by simp
  | y :: ys, h, v => by
      simp only [splitRL, Bool.and_eq_true] at h
      rw [AdmAny_cons, Bool.and_or_distrib_left, splitR_sound hf y h.1 v,
        splitRL_sound hf ys h.2 v, Bool.false_or]
end

/-- **Two data predicates that meet at the empty predicate keep a refinement chain apart**: no
    value satisfies `q` and a refinement of the chain. -/
theorem predApart_sound [Leaf S] [LeafAdm S] {q : S.Pred} {ρ' : List S.C} :
    ∀ (y : Term S), predApart q y = true → ∀ v, (Sem.eval q v && Adm y ρ' v) = false
  | .refine y q', h, v => by
      simp only [predApart, Bool.or_eq_true, Bool.and_eq_true] at h
      rw [Adm_refine_eq]
      rcases h with ⟨-, hm⟩ | h
      · have hn : Leaf.pmeet q q' = some none := by
          revert hm; cases Leaf.pmeet q q' with
          | none => simp
          | some o => cases o <;> simp
        have := LeafAdm.pmeet_none q q' hn v
        cases hq : Sem.eval q v <;> cases hq' : Sem.eval q' v <;> simp_all
      · have := predApart_sound (ρ' := ρ') y h v
        cases hq : Sem.eval q v <;> cases ha : Adm y ρ' v <;> simp_all
  | .prim _, h, _ | .never, h, _ | .set _, h, _ | .list _ _ _, h, _ | .held _ _ _ _, h, _
  | .opaq, h, _ | .object _, h, _ | .union _, h, _ | .var _, h, _ | .mu _, h, _ => by
      simp [predApart] at h

/-- **The leaf family is sound**: the leaf law, and the shape classes at every former. -/
theorem famPrimD_sound [Leaf S] [LeafAdm S] [Shapes S] {ρ ρ' : List S.C} (g : S.Ground) :
    DisjSound ρ ρ' (.prim g) (famPrimD g) := by
  intro y h v
  cases y with
  | prim g' =>
      simp only [famPrimD, Option.isNone_iff_eq_none] at h
      exact LeafAdm.prim_none g g' h v
  | set t => exact Shapes.prim_set g t v
  | list a b c => exact Shapes.prim_list g a b c v
  | object b => exact Shapes.prim_obj g b v
  | _ => simp [famPrimD] at h

/-- **The variable family is sound**: a paired binder pair shares no value. -/
theorem famVarD_sound {ρ ρ' : List S.C} {i : Nat} {q : Pairing} (hq : ApartV q ρ ρ') :
    DisjSound ρ ρ' (.var i) (famVarD i q) := by
  intro y h v
  cases y with
  | var j =>
      simp only [famVarD, Option.isSome_iff_exists] at h
      obtain ⟨k, hk⟩ := h
      exact hq i j k hk v
  | _ => simp [famVarD] at h

/-- **The set family is sound**: the set law over closed elements, and the shape classes at
    every other former. -/
theorem famSetD_sound [FormerAdm S] [Shapes S] {ρ ρ' : List S.C} (a : Term S)
    {mt : Term S → Bool} (hmt : DisjSound ρ ρ' a mt) :
    DisjSound ρ ρ' (.set a) (famSetD a mt) := by
  intro y h v
  cases y with
  | set y' =>
      simp only [famSetD, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨ha, hy⟩, hm⟩ := h
      have hc := FormerAdm.set_never a y' (fun u => by
        rw [← Adm_closed a ha ρ [], ← Adm_closed y' hy ρ' []]; exact hmt y' hm u) v
      rwa [Adm_closed (.set a) ha ρ [], Adm_closed (.set y') hy ρ' []]
  | prim g =>
      have := Shapes.prim_set (ρ := ρ') (ρ' := ρ) g a v
      rw [Bool.and_comm]; exact this
  | list x y z => exact Shapes.set_list a x y z v
  | object b => exact Shapes.set_obj a b v
  | _ => simp [famSetD] at h



/-- Two rows of terms share no row of values. -/
def RowsApart (ρ ρ' : List S.C) (r₁ r₂ : List (Term S)) : Prop :=
  ∀ ws : List S.V, (zipP (AdmList r₁ ρ) ws && zipP (AdmList r₂ ρ') ws) = false

/-- One disjoint position keeps two rows of one length apart. -/
theorem rowsApart_of_anyZip {ρ ρ' : List S.C} :
    ∀ {r₁ : List (Term S)} {fs : List (Term S → Bool)}, List.Forall₂ (DisjSound ρ ρ') r₁ fs →
      ∀ {r₂ : List (Term S)}, anyZip fs r₂ = true → RowsApart ρ ρ' r₁ r₂
  | _, _, .nil, _, h, _ => by simp [anyZip] at h
  | t :: r₁, f :: fs, .cons ht hr, r₂, h, ws => by
      cases r₂ with
      | nil => simp [anyZip] at h
      | cons u r₂ =>
        cases ws with
        | nil => simp [AdmList, zipP]
        | cons w ws =>
          simp only [anyZip, Bool.or_eq_true] at h
          simp only [AdmList, zipP]
          rcases h with h | h
          · have := ht u h w
            cases h1 : Adm t ρ w <;> cases h2 : Adm u ρ' w <;> simp_all
          · have := rowsApart_of_anyZip hr h ws
            cases h1 : zipP (AdmList r₁ ρ) ws <;> cases h2 : zipP (AdmList r₂ ρ') ws <;>
              simp_all

/-- Two rows stay apart when a common prefix of equal length goes in front. -/
theorem RowsApart.append_left {ρ ρ' : List S.C} {A₁ A₂ X₁ X₂ : List (Term S)}
    (hA : A₁.length = A₂.length) (h : RowsApart ρ ρ' A₁ A₂) :
    RowsApart ρ ρ' (A₁ ++ X₁) (A₂ ++ X₂) := by
  intro ws
  rcases Nat.lt_or_ge ws.length A₁.length with hl | hl
  · rw [zipP_false_of_length_ne _ _ (by simp [AdmList_eq]; omega), Bool.false_and]
  · rw [← List.take_append_drop A₁.length ws, AdmList_eq, AdmList_eq, List.map_append,
      List.map_append, zipP_append _ _ _ _ (by simp; omega),
      zipP_append _ _ _ _ (by simp; omega)]
    have := h (ws.take A₁.length)
    rw [AdmList_eq, AdmList_eq] at this
    cases h1 : zipP (A₁.map (Adm · ρ)) (ws.take A₁.length) <;>
      cases h2 : zipP (A₂.map (Adm · ρ')) (ws.take A₁.length) <;> simp_all

/-- …and when a common suffix of equal length goes behind. -/
theorem RowsApart.append_right {ρ ρ' : List S.C} {B₁ B₂ X₁ X₂ : List (Term S)}
    (hX : X₁.length = X₂.length) (h : RowsApart ρ ρ' B₁ B₂) :
    RowsApart ρ ρ' (X₁ ++ B₁) (X₂ ++ B₂) := by
  intro ws
  rcases Nat.lt_or_ge ws.length X₁.length with hl | hl
  · rw [zipP_false_of_length_ne _ _ (by simp [AdmList_eq]; omega), Bool.false_and]
  · rw [← List.take_append_drop X₁.length ws, AdmList_eq, AdmList_eq, List.map_append,
      List.map_append, zipP_append _ _ _ _ (by simp; omega),
      zipP_append _ _ _ _ (by simp; omega)]
    have := h (ws.drop X₁.length)
    rw [AdmList_eq, AdmList_eq] at this
    cases h1 : zipP (B₁.map (Adm · ρ)) (ws.drop X₁.length) <;>
      cases h2 : zipP (B₂.map (Adm · ρ')) (ws.drop X₁.length) <;> simp_all

/-- Two `list` shapes whose rows are apart at every common length share no value. -/
theorem Adm_list_apart {ρ ρ' : List S.C} {p₁ s₁ p₂ s₂ : List (Term S)} {q₁ q₂ : Option (Term S)}
    (h : ∀ n r₁ r₂, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      RowsApart ρ ρ' r₁ r₂) (v : S.V) :
    (Adm (.list p₁ q₁ s₁) ρ v && Adm (.list p₂ q₂ s₂) ρ' v) = false := by
  cases hv : listOut v with
  | none => simp [Adm_list_of_none hv]
  | some ws =>
      rw [Adm_list_of_out hv, Adm_list_of_out hv, AdmList_eq_map, AdmOptT_eq_map, AdmList_eq_map,
        AdmList_eq_map, AdmOptT_eq_map, AdmList_eq_map, alignPL_eq_rowOfG, alignPL_eq_rowOfG,
        rowOfG_map, rowOfG_map]
      cases h₁ : rowOfG p₁ q₁ s₁ ws.length with
      | none => simp
      | some r₁ =>
        cases h₂ : rowOfG p₂ q₂ s₂ ws.length with
        | none => simp
        | some r₂ =>
          have := h _ _ _ h₁ h₂ ws
          simpa only [Option.map_some, AdmList_eq] using this

omit [Sem S] [PrimAdm S] in
/-- A disjoint position of a row cut in two lies in one of the two parts. -/
theorem anyZip_take_drop : ∀ (P : Nat) {fs : List (Term S → Bool)} {us : List (Term S)},
    anyZip fs us = true →
      anyZip (fs.take P) (us.take P) = true ∨ anyZip (fs.drop P) (us.drop P) = true
  | 0, _, _, h => Or.inr (by simpa using h)
  | _ + 1, [], _, h => by simp [anyZip] at h
  | _ + 1, _ :: _, [], h => by simp [anyZip] at h
  | P + 1, f :: fs, u :: us, h => by
      simp only [anyZip, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl (by simp [anyZip, h])
      · rcases anyZip_take_drop P h with h' | h'
        · exact Or.inl (by simp [anyZip, h'])
        · exact Or.inr (by simpa using h')

/-- A row that the shape assigns has the length the shape was asked for. -/
theorem rowOfG_isSome_len {α : Type} {pre suf : List α} {sp : Option α} {n : Nat} {r : List α}
    (h : rowOfG pre sp suf n = some r) : pre.length + suf.length ≤ n := by
  have := rowOfG_length h
  cases sp with
  | none => rw [rowOfG_none_eq] at h; split at h <;> simp_all
  | some c => rw [rowOfG_some_eq] at h; split at h <;> simp_all

/-- **The list family is sound.** Two values of different lengths differ, so each common length
    needs one disjoint position, which `listDisjRow` finds. -/
theorem famListD_sound [Shapes S] {ρ ρ' : List S.C} {pre suf : List (Term S)}
    {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Bool)} {fsp : Option (Term S → Bool)}
    (hp : List.Forall₂ (DisjSound ρ ρ') pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ DisjSound ρ ρ' t f)
    (hf : List.Forall₂ (DisjSound ρ ρ') suf fsuf) :
    DisjSound ρ ρ' (.list pre sp suf) (famListD fpre fsp fsuf) := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro y h v
  cases y with
  | prim g => rw [Bool.and_comm]; exact Shapes.prim_list g pre sp suf v
  | set t => rw [Bool.and_comm]; exact Shapes.set_list t pre sp suf v
  | object b => exact Shapes.list_obj pre sp suf b v
  | list pre₂ sp₂ suf₂ =>
    simp only [famListD] at h
    refine Adm_list_apart (fun n r₁ r₂ h₁ h₂ => ?_) v
    rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, htf⟩
    · -- the left states one arity
      simp only [listDisjRow] at h
      rw [rowOfG_none_eq] at h₁
      split at h₁
      · next hn =>
        simp only [Option.some.injEq] at h₁; subst h₁
        rw [show fpre.length + fsuf.length = n by omega, h₂] at h
        exact rowsApart_of_anyZip (forall₂_append hp hf) h
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
            have hF := rowOfG_forall₂ (R := DisjSound ρ ρ') hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf
              h₁ hfs
            exact rowsApart_of_anyZip hF h
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
            have hF := rowOfG_forall₂ (R := DisjSound ρ ρ') hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf
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
              exact RowsApart.append_left (by simp; omega)
                (rowsApart_of_anyZip (List.forall₂_take P hF) ha)
            · exact RowsApart.append_right (by simp; omega)
                (rowsApart_of_anyZip (List.forall₂_drop P hF) ha)
          · exact nomatch h
        · exact nomatch h
  | _ => simp [famListD] at h



/-- **Two bodies apart at one name** share no map: the name is required on one side, so a
    common map holds the name, and the two slots share no value there. -/
theorem AdmBody_apart_at {ρ ρ' : List S.C} {a b : Body S} {k : String}
    (hr : (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)) = true)
    (hs : ∀ w, (AdmField (a.slotAt k) ρ w && AdmField (b.slotAt k) ρ' w) = false) (v : S.V) :
    (AdmBody a ρ v && AdmBody b ρ' v) = false := by
  refine Bool.eq_false_iff.mpr (fun hab => ?_)
  rw [Bool.and_eq_true] at hab
  obtain ⟨hA, hB⟩ := hab
  cases hv : mapOut v with
  | none => rw [AdmBody_of_none hv] at hA; exact absurd hA (by simp)
  | some m =>
    rw [AdmBody_map_slots _ hv] at hA hB
    rw [Bool.or_eq_true] at hr
    have hk : k ∈ m.keys := hr.elim (hA.1 k) (hB.1 k)
    have h1 := hs (m.get ⟨k, hk⟩)
    rw [hA.2 ⟨k, hk⟩, hB.2 ⟨k, hk⟩] at h1
    exact absurd h1 (by simp)

/-- **The object family is sound**: two bodies share no map where one name holds two disjoint
    slots, one of them required. -/
theorem famObjD_sound [Shapes S] {ρ ρ' : List S.C} {a : Body S}
    {g : {k // k ∈ a.fields} → ObjectSlot S → Bool} {mw : Term S → Bool}
    (hg : ∀ k s, g k s = true → (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq s) = true ∧
      ∀ w, (AdmField (a.at k) ρ w && AdmField s ρ' w) = false)
    (hmw : DisjSound ρ ρ' a.block mw) :
    DisjSound ρ ρ' (.object a) (famObjD a g mw) := by
  intro y h v
  cases y with
  | prim g' => rw [Bool.and_comm]; exact Shapes.prim_obj g' a v
  | set t => rw [Bool.and_comm]; exact Shapes.set_obj t a v
  | list p q s => rw [Bool.and_comm]; exact Shapes.list_obj p q s a v
  | object b =>
    simp only [famObjD, decide_eq_true_eq] at h
    obtain ⟨⟨k, hk⟩, hd⟩ := h
    show (AdmBody a ρ v && AdmBody b ρ' v) = false
    unfold slotD at hd
    split at hd
    · next ha =>
      have hb : (if h' : k ∈ b.fields then b.at ⟨k, h'⟩ else .optional b.block) = b.slotAt k := rfl
      rw [hb] at hd
      obtain ⟨hr, hs⟩ := hg _ _ hd
      rw [← Body.slotAt_pos ha] at hr hs
      exact AdmBody_apart_at hr hs v
    · next ha =>
      have hkb : k ∈ b.fields := (Finset.mem_union.mp hk).resolve_left ha
      split at hd
      · next y hy =>
        have hbs : b.slotAt k = .req y := by rw [Body.slotAt_pos hkb]; exact hy
        refine AdmBody_apart_at (k := k) (by rw [hbs]; simp [ObjectSlot.isReq]) (fun w => ?_) v
        rw [hbs, Body.slotAt_neg ha]
        exact hmw y hd w
      · exact nomatch hd
  | _ => simp [famObjD] at h

mutual
/-- **Soundness of the zero test, on the write side.** Where `disjoint` answers `true`, no value
    is admitted by both operands, under every two environments that keep the paired binders
    apart. -/
theorem disjoint_sound [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (x y : Term S), Term.disjoint p x y = true →
      ∀ (ρ ρ' : List S.C), ApartV p ρ ρ' → ∀ v, (Adm x ρ v && Adm y ρ' v) = false
  | _, .never, _, _, _, _, _, _ => by simp
  | p, .held _ _ _ _, y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ) (fam := fun _ _ => false)
        (fun _ _ _ _ hh => nomatch hh) y p ρ' hp h v
  | p, .var i, y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ) (fun _ _ hq => famVarD_sound hq) y p ρ' hp h v
  | p, .mu b, y, h, ρ, ρ', hp, v => by
      cases y with
      | mu b' =>
        simp only [Term.disjoint] at h
        have hB : ∀ c c', (∀ u, ((c.e u).isSome && (c'.e u).isSome) = false) →
            ∀ u, (((denote b (c :: ρ)).e u).isSome && ((denote b' (c' :: ρ')).e u).isSome)
              = false := fun c c' hc u => by
          have := disjoint_sound (pairMu p) b b' h (c :: ρ) (c' :: ρ') (hp.mu hc) u
          rwa [Adm_eq_isSome, Adm_eq_isSome] at this
        have := stage_apart hB (Sem.dV v) v
        rw [Adm_eq_isSome, Adm_eq_isSome]
        exact this
      | _ =>
        simp only [Term.disjoint] at h
        rw [Adm_mu_unfold b ρ v]
        exact disjoint_sound (shiftL p) b _ h _ ρ' (hp.left _) v
  | p, .refine x q, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjoint] at h
      refine splitR_sound (ρ := ρ) (ρ' := ρ') (x := .refine x q) (p := p) ?_ y h v
      intro y' hy w
      rw [Bool.or_eq_true, Bool.and_eq_true] at hy
      rw [Adm_refine_eq]
      rcases hy with hy | ⟨-, hy⟩
      · have := disjoint_sound p x y' hy ρ ρ' hp w
        cases h1 : Adm x ρ w <;> cases h2 : Adm y' ρ' w <;> simp_all
      · have := predApart_sound (ρ' := ρ') y' hy w
        cases h1 : Sem.eval q w <;> cases h2 : Adm y' ρ' w <;> simp_all
  | p, .union os, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjoint] at h
      rw [Adm_union]
      exact disjointL_sound p os y h ρ ρ' hp v
  | p, .prim g, y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ) (fun _ _ _ => famPrimD_sound g) y p ρ' hp h v
  | p, .set a, y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ)
        (fun q ρ₁ hq => famSetD_sound a (fun u hu w => disjoint_sound q a u hu ρ ρ₁ hq w))
        y p ρ' hp h v
  | p, .opaq, y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ) (fam := fun _ _ => false)
        (fun _ _ _ _ hh => nomatch hh) y p ρ' hp h v
  | p, .list pre sp suf, y, h, ρ, ρ', hp, v => by
      cases sp with
      | none =>
        exact disjSRight_sound (ρ := ρ) (fun q ρ₁ hq => famListD_sound (sp := none)
          (disjointTs_sound q pre ρ ρ₁ hq) (Or.inl ⟨rfl, rfl⟩) (disjointTs_sound q suf ρ ρ₁ hq))
          y p ρ' hp h v
      | some t =>
        exact disjSRight_sound (ρ := ρ) (fun q ρ₁ hq => famListD_sound (sp := some t)
          (disjointTs_sound q pre ρ ρ₁ hq)
          (Or.inr ⟨t, Term.disjoint q t, rfl, rfl,
            fun u hu w => disjoint_sound q t u hu ρ ρ₁ hq w⟩)
          (disjointTs_sound q suf ρ ρ₁ hq)) y p ρ' hp h v
  | p, .object (.mk fs f none), y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ) (fun q ρ₁ hq => famObjD_sound (a := .mk fs f none)
        (fun k s hs => slot_sound q (f k) s hs ρ ρ₁ hq)
        (fun _ _ w => by simp [Body.block])) y p ρ' hp h v
  | p, .object (.mk fs f (some t)), y, h, ρ, ρ', hp, v =>
      disjSRight_sound (ρ := ρ) (fun q ρ₁ hq => famObjD_sound (a := .mk fs f (some t))
        (fun k s hs => slot_sound q (f k) s hs ρ ρ₁ hq)
        (fun u hu w => disjoint_sound q t u hu ρ ρ₁ hq w)) y p ρ' hp h v
termination_by structural _ x => x
/-- …and a union, option by option. -/
theorem disjointL_sound [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (os : List (Term S)) (y : Term S), Term.disjointL p os y = true →
      ∀ (ρ ρ' : List S.C), ApartV p ρ ρ' → ∀ v, (AdmAny os ρ v && Adm y ρ' v) = false
  | _, [], _, _, _, _, _, _ => by simp
  | p, x :: xs, y, h, ρ, ρ', hp, v => by
      simp only [Term.disjointL, Bool.and_eq_true] at h
      have h1 := disjoint_sound p x y h.1 ρ ρ' hp v
      have h2 := disjointL_sound p xs y h.2 ρ ρ' hp v
      rw [AdmAny_cons]
      cases a1 : Adm x ρ v <;> cases a2 : AdmAny xs ρ v <;> cases a3 : Adm y ρ' v <;> simp_all
termination_by structural _ os => os
/-- …and each position of a row, partially applied. -/
theorem disjointTs_sound [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (ts : List (Term S)) (ρ ρ' : List S.C), ApartV p ρ ρ' →
      List.Forall₂ (DisjSound ρ ρ') ts (Term.disjointTs p ts)
  | _, [], _, _, _ => .nil
  | p, t :: ts, ρ, ρ', hp =>
      .cons (fun u hu w => disjoint_sound p t u hu ρ ρ' hp w) (disjointTs_sound p ts ρ ρ' hp)
termination_by structural _ ts => ts
/-- …and two slots, where one requires the name. -/
theorem slot_sound [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (s s' : ObjectSlot S), ObjectSlot.disjoint p s s' = true →
      ∀ (ρ ρ' : List S.C), ApartV p ρ ρ' →
        (ObjectSlot.isReq s || ObjectSlot.isReq s') = true ∧
          ∀ w, (AdmField s ρ w && AdmField s' ρ' w) = false
  | p, .req x, .req y, h, ρ, ρ', hp =>
      ⟨rfl, fun w => disjoint_sound p x y h ρ ρ' hp w⟩
  | p, .req x, .optional y, h, ρ, ρ', hp =>
      ⟨rfl, fun w => disjoint_sound p x y h ρ ρ' hp w⟩
  | p, .optional x, .req y, h, ρ, ρ', hp =>
      ⟨by simp [ObjectSlot.isReq], fun w => disjoint_sound p x y h ρ ρ' hp w⟩
  | _, .optional _, .optional _, h, _, _, _ => by simp [ObjectSlot.disjoint] at h
termination_by structural _ s => s
end

end Calculus.Alg
