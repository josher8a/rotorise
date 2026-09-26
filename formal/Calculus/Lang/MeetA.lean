import Calculus.Lang.MeetV
import Calculus.Lang.ExactA

/-!
# The meet on the read side, over a universe signature

`Alg.AdmA_meet_both` states the read-side homomorphism and its reading agreement together: where
two terms have a meet `z`, `z` reads exactly the attributes that both terms read, and where both
terms read an attribute, `z` reads it to the same value as each. The pairing is forced: the row of
`refine` asks the predicate of what the inner term reads, so the refinement rows reduce to the
reading agreement.

A universe supplies the laws in two classes, as on the write side. `FormerAdmA` holds the laws of
the formers, and `LeafAdmA` holds the laws of the leaf meet.
-/

namespace Calculus.Alg

open Calculus (alignPL alignP zipP anyP objAdmV entryP)

variable {S : Syn} [Sem S] [PrimAdm S] [PrimAdmA S]

noncomputable section

/-! ## Reading an attribute through a former -/

/-- The elements of an attribute, where the list former reads one. -/
def listOutA (a : Sem.A S) : Option (List (Sem.A S)) := (Sem.list (S := S)).bind (·.pA.out a)

/-- The entries of an attribute, where the map former reads one. -/
def mapOutA (a : Sem.A S) : Option (MapOf (Sem.A S)) := (Sem.map (S := S)).bind (·.mA.out a)

/-- A `list` reads an attribute that the list former reads by the row of its positions. -/
theorem AdmA_list_of_out {pre suf : List (Term S)} {sp : Option (Term S)} {a : Sem.A S}
    {as : List (Sem.A S)} (h : listOutA a = some as) :
    AdmA (.list pre sp suf) a = alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as := by
  unfold listOutA at h
  rcases hL : Sem.list (S := S) with _ | L
  · rw [hL] at h; exact absurd h (by simp)
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmA, hL, h]

/-- A `list` reads no attribute that the list former does not read. -/
theorem AdmA_list_of_none {pre suf : List (Term S)} {sp : Option (Term S)} {a : Sem.A S}
    (h : listOutA a = none) : AdmA (.list pre sp suf) a = false := by
  unfold listOutA at h
  rcases hL : Sem.list (S := S) with _ | L
  · simp only [AdmA, hL]
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmA, hL, h]

/-- A body reads an attribute that the map former reads by two tests. -/
theorem AdmABody_of_out {b : Body S} {a : Sem.A S} {m : MapOf (Sem.A S)} (h : mapOutA a = some m) :
    AdmABody b a = (reqPresentT b.fields b.at m.keys &&
      objAdmV ⟨b.fields, fun k => AdmAField (b.at k)⟩ (AdmAWild b.wild) m.keys m.get) := by
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
    AdmABody b a = false := by
  unfold mapOutA at h
  cases b with
  | mk fields fld wild =>
  rcases hL : Sem.map (S := S) with _ | F
  · simp only [AdmABody, hL]
  · rw [hL] at h
    simp only [Option.bind_some] at h
    simp only [AdmABody, hL, h]

/-- The bottom reads nothing. -/
@[simp] theorem AdmA_never (a : Sem.A S) : AdmA (.never : Term S) a = false := by simp [AdmA]

/-- `⋁` of `AdmA` over a union's options. -/
def AdmAAny (ts : List (Term S)) (a : Sem.A S) : Bool := anyP (AdmAList ts) a

/-- An empty list of options reads no attribute. -/
@[simp] theorem AdmAAny_nil (a : Sem.A S) : AdmAAny ([] : List (Term S)) a = false := rfl

/-- The options read where the first reads or the rest read. -/
@[simp] theorem AdmAAny_cons (t : Term S) (ts : List (Term S)) (a : Sem.A S) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

/-- A union reads where one of its options reads. -/
theorem AdmA_union (opts : List (Term S)) (a : Sem.A S) :
    AdmA (.union opts) a = AdmAAny opts a := by simp [AdmA, AdmAAny]

/-- The options read exactly where one of them reads. -/
theorem AdmAAny_iff : ∀ {os : List (Term S)} {a : Sem.A S},
    AdmAAny os a = true ↔ ∃ t ∈ os, AdmA t a = true
  | [], a => by simp
  | t :: ts, a => by
      rw [AdmAAny_cons, Bool.or_eq_true, AdmAAny_iff]
      simp

omit [PrimAdm S] [PrimAdmA S] in
/-- `refine`'s gate at a successful read asks the predicate of the value. -/
theorem refineReads_some {t : Term S} {q : S.V → Bool} {a : Sem.A S} {v : S.V}
    (h : (denote t).p a = some v) : refineReads t q a = q v := by
  simp [refineReads, h]

omit [PrimAdm S] [PrimAdmA S] in
/-- …and at a failed one refuses. -/
theorem refineReads_none {t : Term S} {q : S.V → Bool} {a : Sem.A S}
    (h : (denote t).p a = none) : refineReads t q a = false := by
  simp [refineReads, h]

/-- A term reads an attribute exactly where its codec reads it. -/
theorem isSome_p_eq_AdmA (t : Term S) (a : Sem.A S) : ((denote t).p a).isSome = AdmA t a :=
  Bool.coe_iff_coe.mp (by simpa using (AdmA_exact t a).symm)

omit [Sem S] [PrimAdm S] [PrimAdmA S] in
/-- `reqPresentT` in the form the object row uses: a declared name that must be read is
    present. -/
theorem reqPresentT_req (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) :
    reqPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (fld k) = true → k.1 ∈ keys) := by
  unfold reqPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [ObjectSlot.isReq])
  · cases hf : fld k with
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))
    | optional t => rfl

/-- Every row that answers the bottom owes only its first half: the second is vacuous, because
    the first says no attribute is read by both factors. -/
theorem bottom_row {x y : Term S}
    (h1 : ∀ a : Sem.A S, AdmA (.never : Term S) a = (AdmA x a && AdmA y a)) :
    (∀ a : Sem.A S, AdmA (.never : Term S) a = (AdmA x a && AdmA y a)) ∧
    (∀ a : Sem.A S, AdmA x a = true → AdmA y a = true →
      (denote (.never : Term S)).p a = (denote x).p a ∧
      (denote (.never : Term S)).p a = (denote y).p a) :=
  ⟨h1, fun a ha hb => absurd (h1 a) (by rw [ha, hb]; simp [AdmA])⟩

/-- A declared position that holds nothing empties the tuple: every wire list the tuple
    reads fills each declared position. -/
theorem alignPA_never_false : ∀ {ts : List (Term S)} {tail : Option (Term S)} {ws : List (Sem.A S)},
    ts.any Term.isNever = true → alignP (AdmAList ts) (AdmAOptT tail) ws = false := by
  intro ts
  induction ts with
  | nil => intro _ _ h; simp at h
  | cons t ts' ih =>
    intro tail ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmAList, alignP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht, show AdmA .never _ = false from rfl, Bool.false_and]
      · rw [ih (tail := tail) (ws := ws') hrest, Bool.and_false]

/-- A suffix holding the bottom reads nothing, on the read side. -/
theorem zipPA_never_false : ∀ {suf : List (Term S)} {as : List (Sem.A S)},
    suf.any Term.isNever = true → zipP (AdmAList suf) as = false := by
  intro suf
  induction suf with
  | nil => intro _ h; simp at h
  | cons t ts' ih =>
    intro as h
    cases as with
    | nil => rfl
    | cons w as' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmAList, zipP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht,
          show AdmA .never w = false from rfl, Bool.false_and]
      · rw [ih (as := as') hrest, Bool.and_false]

/-- Normalising a list keeps what it reads. -/
theorem AdmA_listOf (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S)) (a : Sem.A S) :
    AdmA (Term.listOf pre sp suf) a = AdmA (.list pre sp suf) a := by
  unfold Term.listOf
  split
  next hany =>
    rw [AdmA_never]
    cases ha : listOutA a with
    | none => rw [AdmA_list_of_none ha]
    | some as =>
      rw [AdmA_list_of_out ha]
      refine Eq.symm ?_
      simp only [alignPL]
      rcases Bool.or_eq_true .. |>.mp hany with hp | hs
      · rw [alignPA_never_false hp, Bool.false_and]
      · rw [zipPA_never_false hs, Bool.and_false]
  next => rfl

/-- The read-side rows of a term list are that list mapped. -/
theorem AdmAList_eq_map (ts : List (Term S)) : AdmAList ts = ts.map AdmA := AdmAList_eq ts

/-- …and the same for the spread. -/
theorem AdmAOptT_eq_map (sp : Option (Term S)) : AdmAOptT sp = sp.map AdmA := by
  cases sp <;> rfl

/-- **The suffix row meets position by position**, on the read side. -/
theorem zipPA_meet {r₁ r₂ rz : List (Term S)} (hlen : r₁.length = r₂.length)
    (hF : List.Forall₂ (fun (pq : Term S × Term S) w => ∀ b, AdmA w b = (AdmA pq.1 b && AdmA pq.2 b))
      (r₁.zip r₂) rz) :
    ∀ as, zipP (AdmAList rz) as = (zipP (AdmAList r₁) as && zipP (AdmAList r₂) as) := by
  intro as
  induction as generalizing r₁ r₂ rz with
  | nil =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipP, AdmAList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons _ _ => simp [zipP, AdmAList]
  | cons b as ihb =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipP, AdmAList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons hr hrest =>
                  simp only [AdmAList, zipP, hr, ihb (by simpa using hlen) hrest]
                  simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- **The `list` meet's read-side admission obligation, read off the three rows.** The twin
    of `Adm_list_rows`. -/
theorem AdmA_list_rows {p₁ s₁ p₂ s₂ pz sz : List (Term S)} {q₁ q₂ qz : Option (Term S)}
    (hsome : ∀ n, (rowOfG pz qz sz n).isSome
      = ((rowOfG p₁ q₁ s₁ n).isSome && (rowOfG p₂ q₂ s₂ n).isSome))
    (hrel : ∀ n r₁ r₂ rz, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      rowOfG pz qz sz n = some rz →
      r₁.length = r₂.length ∧
        List.Forall₂ (fun (pq : Term S × Term S) w => ∀ b, AdmA w b = (AdmA pq.1 b && AdmA pq.2 b))
          (r₁.zip r₂) rz)
    (a : Sem.A S) :
    AdmA (.list pz qz sz) a = (AdmA (.list p₁ q₁ s₁) a && AdmA (.list p₂ q₂ s₂) a) := by
  cases ha : listOutA a with
  | none => simp [AdmA_list_of_none ha]
  | some as =>
      have hb := hsome as.length
      simp only [AdmA_list_of_out ha, AdmAList_eq_map, AdmAOptT_eq_map, alignPL_eq_rowOfG,
        rowOfG_map]
      cases h₁ : rowOfG p₁ q₁ s₁ as.length with
      | none =>
          rw [h₁] at hb
          simp only [Option.isSome_none, Bool.false_and] at hb
          cases hz : rowOfG pz qz sz as.length with
          | none => simp
          | some rz => rw [hz] at hb; simp at hb
      | some r₁ =>
          cases h₂ : rowOfG p₂ q₂ s₂ as.length with
          | none =>
              rw [h₁, h₂] at hb
              simp only [Option.isSome_some, Option.isSome_none, Bool.and_false] at hb
              cases hz : rowOfG pz qz sz as.length with
              | none => simp
              | some rz => rw [hz] at hb; simp at hb
          | some r₂ =>
              cases hz : rowOfG pz qz sz as.length with
              | none => rw [h₁, h₂, hz] at hb; simp at hb
              | some rz =>
                  obtain ⟨hlen, hF⟩ := hrel _ _ _ _ h₁ h₂ hz
                  simp only [Option.map_some]
                  simpa only [← AdmAList_eq_map] using zipPA_meet hlen hF as

omit [PrimAdm S] [PrimAdmA S] in
/-- **`slots` is `rowOfG` with no suffix.** The codec-side row and the term-side row are one
    definition seen twice, which is what lets the reading agreement be stated over `rowOfG`
    like the admission. -/
theorem slots_eq_rowOfG : ∀ (cs : List S.C) (sp : Option S.C) (m : Nat),
    slots cs sp m = rowOfG cs sp [] m := by
  intro cs
  induction cs with
  | nil =>
      intro sp m
      cases sp with
      | none =>
          cases m with
          | zero =>
              rw [rowOfG_none_eq, if_pos (by simp only [List.length_nil]),
                List.append_nil]
              rfl
          | succ n =>
              rw [rowOfG_none_eq,
                if_neg (by simp only [List.length_nil, Nat.add_zero]; omega)]
              rfl
      | some c =>
          rw [slots_spread, rowOfG_some_eq,
            if_neg (by simp only [List.length_nil, Nat.add_zero]; omega)]
          simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.append_nil]
  | cons c cs ih =>
      intro sp m
      cases m with
      | zero =>
          cases sp with
          | none =>
              rw [rowOfG_none_eq,
                if_neg (by simp only [List.length_cons, List.length_nil]; omega)]
              rfl
          | some d =>
              rw [rowOfG_some_eq,
                if_pos (by simp only [List.length_cons, List.length_nil]; omega)]
              rfl
      | succ n =>
          simp only [slots, ih]
          cases sp with
          | none =>
              simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, List.length_cons,
                List.append_nil]
              split
              · next he =>
                  rw [if_pos (by omega)]
                  simp only [Option.map_some, List.cons_append]
              · next he => rw [if_neg (by omega)]; rfl
          | some d =>
              simp only [rowOfG_some_eq, List.length_nil, Nat.add_zero, List.length_cons,
                List.append_nil]
              split
              · next he => rw [if_pos (by omega)]; rfl
              · next he =>
                  rw [if_neg (by omega),
                    show n + 1 - (cs.length + 1) = n - cs.length by omega]
                  simp only [Option.map_some, List.cons_append]

omit [PrimAdm S] [PrimAdmA S] in
/-- …and `slotsL` is `rowOfG`. -/
theorem slotsL_eq_rowOfG (pre : List S.C) (sp : Option S.C) (suf : List S.C) (n : Nat) :
    slotsL pre sp suf n = rowOfG pre sp suf n := by
  unfold slotsL
  rw [slots_eq_rowOfG]
  cases sp with
  | none =>
      simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, List.append_nil]
      split
      · next hlt => rw [if_neg (by omega)]
      · next hge =>
          split
          · next he => rw [if_pos (by omega)]; simp
          · next he => rw [if_neg (by omega)]; simp
  | some c =>
      simp only [rowOfG_some_eq, List.length_nil, Nat.add_zero, List.append_nil]
      split
      · next hlt => rw [if_pos (by omega)]
      · next hge =>
          split
          · next hlt2 => rw [if_pos (by omega)]; simp
          · next hge2 =>
              rw [if_neg (by omega),
                show n - suf.length - pre.length = n - pre.length - suf.length by omega]
              simp

/-- Every position of an admitted row is admitted. -/
theorem zipPA_forall₂ : ∀ {r : List (Term S)} {as : List (Sem.A S)}, zipP (AdmAList r) as = true →
    List.Forall₂ (fun t b => AdmA t b = true) r as := by
  intro r
  induction r with
  | nil =>
      intro as h
      cases as with
      | nil => exact .nil
      | cons => simp [zipP, AdmAList] at h
  | cons t r' ih =>
      intro as h
      cases as with
      | nil => simp [zipP, AdmAList] at h
      | cons b as' =>
          simp only [AdmAList, zipP, Bool.and_eq_true] at h
          exact .cons h.1 (ih h.2)

omit [PrimAdm S] [PrimAdmA S] in
/-- The spread a container denotes is the spread's own codec. -/
theorem denoteOpt_eq_map (sp : Option (Term S)) : denoteOpt sp = sp.map denote := by
  cases sp <;> rfl

/-- **Two `list` shapes with no common length read nothing together.** -/
theorem AdmA_list_disjoint {p₁ s₁ p₂ s₂ : List (Term S)} {q₁ q₂ : Option (Term S)}
    (h : ∀ n, rowOfG p₁ q₁ s₁ n = none ∨ rowOfG p₂ q₂ s₂ n = none) (a : Sem.A S) :
    (AdmA (.list p₁ q₁ s₁) a && AdmA (.list p₂ q₂ s₂) a) = false := by
  cases ha : listOutA a with
  | none => simp [AdmA_list_of_none ha]
  | some as =>
      simp only [AdmA_list_of_out ha, AdmAList_eq_map, AdmAOptT_eq_map, alignPL_eq_rowOfG,
        rowOfG_map]
      rcases h as.length with hn | hn <;> simp [hn]

/-- A term that admits an attribute is not the bottom. -/
theorem not_isNever_of_admA {t : Term S} {b : Sem.A S} (hh : AdmA t b = true) : t.isNever = false := by
  cases t <;> first | rfl | exact absurd hh (by simp [AdmA])

/-- The conclusion of the read-side homomorphism, at one pair. -/
abbrev AdmAAt (x y z : Term S) : Prop :=
  (∀ a : Sem.A S, AdmA z a = (AdmA x a && AdmA y a)) ∧
  (∀ a : Sem.A S, AdmA x a = true → AdmA y a = true →
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a)


/-- The base row: the same constructor on both sides is reflexive on both halves. -/
theorem admA_same (x : Term S) : AdmAAt x x x :=
  ⟨fun a => (Bool.and_self _).symm, fun a _ _ => ⟨rfl, rfl⟩⟩


/-! ## The laws, on the read side -/

/-- **The read-side laws of the formers.** The set laws carry an element meet to a set meet. The
    six disjointness laws close the catch-all rows of the families: two formers in different
    attribute slots share no attribute. -/
class FormerAdmA (S : Syn) [Sem S] [PrimAdm S] [PrimAdmA S] : Prop where
  /-- Over held-free terms, the set of an element meet reads what both sets read, as each. -/
  set_meet : ∀ a y z : Term S, HF a → HF y → HF z → (∀ u, AdmA z u = (AdmA a u && AdmA y u)) →
    AdmAAt (.set a) (.set y) (.set z)
  /-- Two sets whose elements share no attribute share no set. -/
  set_never : ∀ a y : Term S, (∀ u, (AdmA a u && AdmA y u) = false) →
    ∀ c, (AdmA (.set a) c && AdmA (.set y) c) = false
  /-- A primitive and a set share no attribute. -/
  prim_set : ∀ (g : S.Ground) (t : Term S) c, (AdmA (.prim g) c && AdmA (.set t) c) = false
  /-- A primitive and a list share no attribute. -/
  prim_list : ∀ (g : S.Ground) (pre : List (Term S)) sp suf c,
    (AdmA (.prim g) c && AdmA (.list pre sp suf) c) = false
  /-- A primitive and an object share no attribute. -/
  prim_obj : ∀ (g : S.Ground) (b : Body S) c, (AdmA (.prim g) c && AdmA (.object b) c) = false
  /-- A set and a list share no attribute. -/
  set_list : ∀ (t : Term S) pre sp suf c, (AdmA (.set t) c && AdmA (.list pre sp suf) c) = false
  /-- A set and an object share no attribute. -/
  set_obj : ∀ (t : Term S) b c, (AdmA (.set t) c && AdmA (.object b) c) = false
  /-- A list and an object share no attribute. -/
  list_obj : ∀ (pre : List (Term S)) sp suf b c,
    (AdmA (.list pre sp suf) c && AdmA (.object b) c) = false

/-- **The read-side laws of a leaf meet**: each leaf answer reads what both factors read, and
    reads it as each of them does. -/
class LeafAdmA (S : Syn) [Sem S] [PrimAdm S] [PrimAdmA S] [Leaf S] : Prop where
  /-- Two primitives met at a primitive. -/
  prim_some : ∀ g g' h : S.Ground, Leaf.prim g g' = some h →
    AdmAAt (.prim g) (.prim g') (.prim h : Term S)
  /-- Two primitives met at the bottom share no attribute. -/
  prim_none : ∀ g g' : S.Ground, Leaf.prim g g' = none →
    ∀ c, (AdmA (.prim g : Term S) c && AdmA (.prim g') c) = false
  /-- A primitive that meets the top at itself reads as the top does. -/
  prim_top : ∀ g : S.Ground, Leaf.primTop g = true → AdmAAt (.prim g) (.opaq : Term S) (.prim g)

/-- The conclusion is symmetric in the two factors. -/
theorem AdmAAt.swap {x y z : Term S} (h : AdmAAt x y z) : AdmAAt y x z :=
  ⟨fun a => by rw [h.1 a, Bool.and_comm], fun a hy hx => ⟨(h.2 a hx hy).2, (h.2 a hx hy).1⟩⟩

/-- Two terms that share no attribute meet at the bottom. -/
theorem bottom_of_and_falseA {x y : Term S} (h : ∀ c, (AdmA x c && AdmA y c) = false) :
    AdmAAt x y .never := bottom_row (fun c => by rw [h c, AdmA_never])

/-- …in either order. -/
theorem bottom_of_and_falseA' {x y : Term S} (h : ∀ c, (AdmA y c && AdmA x c) = false) :
    AdmAAt x y .never := bottom_row (fun c => by rw [Bool.and_comm, h c, AdmA_never])

/-- The catch-all of every family: two formers in different attribute slots meet at the
    bottom. -/
local macro "fam_bottomA" fam:ident : tactic => `(tactic|
  (simp only [$fam:ident, Option.some.injEq] at *
   subst_vars
   first
     | exact bottom_of_and_falseA (fun c => FormerAdmA.prim_set _ _ c)
     | exact bottom_of_and_falseA' (fun c => FormerAdmA.prim_set _ _ c)
     | exact bottom_of_and_falseA (fun c => FormerAdmA.prim_list _ _ _ _ c)
     | exact bottom_of_and_falseA' (fun c => FormerAdmA.prim_list _ _ _ _ c)
     | exact bottom_of_and_falseA (fun c => FormerAdmA.prim_obj _ _ c)
     | exact bottom_of_and_falseA' (fun c => FormerAdmA.prim_obj _ _ c)
     | exact bottom_of_and_falseA (fun c => FormerAdmA.set_list _ _ _ _ c)
     | exact bottom_of_and_falseA' (fun c => FormerAdmA.set_list _ _ _ _ c)
     | exact bottom_of_and_falseA (fun c => FormerAdmA.set_obj _ _ c)
     | exact bottom_of_and_falseA' (fun c => FormerAdmA.set_obj _ _ c)
     | exact bottom_of_and_falseA (fun c => FormerAdmA.list_obj _ _ _ _ c)
     | exact bottom_of_and_falseA' (fun c => FormerAdmA.list_obj _ _ _ _ c)))

/-- Normalising a refinement keeps what it reads. -/
theorem AdmA_refineOf [Leaf S] [LeafAdm S] (z : Term S) (p : S.Pred) (a : Sem.A S) :
    AdmA (Term.refineOf z p) a = AdmA (.refine z p) a := by
  cases z <;>
    first
      | rfl
      | (simp only [Term.refineOf]
         rename_i z' q
         split
         · rename_i r hr
           show (AdmA z' a && refineReads z' (Sem.eval r) a)
               = ((AdmA z' a && refineReads z' (Sem.eval q) a) && refineReads (.refine z' q) (Sem.eval p) a)
           simp only [refineReads, denote, Codec.restrict]
           cases hv : (denote z').p a with
           | none => simp
           | some v0 =>
               simp only [Option.bind_some]
               rw [LeafAdm.pmeet_some _ _ _ hr v0]
               cases hq : (Sem.eval q) v0 <;> simp [hq]
         · rename_i hr
           show false = ((AdmA z' a && refineReads z' (Sem.eval q) a) && refineReads (.refine z' q) (Sem.eval p) a)
           simp only [refineReads, denote, Codec.restrict]
           cases hv : (denote z').p a with
           | none => simp
           | some v0 =>
               simp only [Option.bind_some]
               have he := LeafAdm.pmeet_none _ _ hr v0
               cases hq : (Sem.eval q) v0 <;> simp [hq] at he ⊢
               simp [he]
         · rfl)

/-- Normalising a refinement changes no reading at an attribute the inner term admits. -/
theorem refineOf_p [Leaf S] [LeafAdm S] {w : Term S} {p : S.Pred} {a : Sem.A S} (hw : AdmA w a = true) :
    (denote (Term.refineOf w p)).p a
      = ((denote w).p a).bind (fun v => if (Sem.eval p) v then some v else none) := by
  cases w with
  | never => simp [AdmA] at hw
  | refine z' q =>
      obtain ⟨_, hq⟩ := Bool.and_eq_true_iff.mp
        (show (AdmA z' a && refineReads z' (Sem.eval q) a) = true from hw)
      cases hv : (denote z').p a with
      | none => exact absurd ((refineReads_none hv).symm.trans hq) (by simp)
      | some v0 =>
        have hqv : (Sem.eval q) v0 = true := (refineReads_some hv).symm.trans hq
        have hwv : (denote (.refine z' q)).p a = some v0 := by
          show ((denote z').p a).bind (fun v => if (Sem.eval q) v then some v else none) = some v0
          rw [hv]; simp [hqv]
        rw [hwv]
        simp only [Option.bind_some]
        simp only [Term.refineOf]
        split
        · rename_i r hr
          show ((denote z').p a).bind (fun v => if (Sem.eval r) v then some v else none) = _
          rw [hv]
          simp only [Option.bind_some]
          rw [LeafAdm.pmeet_some _ _ _ hr v0, hqv, Bool.true_and]
        · rename_i hr
          have hp0 : (Sem.eval p) v0 = false := by
            have he := LeafAdm.pmeet_none _ _ hr v0
            rwa [hqv, Bool.true_and] at he
          rw [hp0]; rfl
        · show (((denote z').p a).bind (fun v => if (Sem.eval q) v then some v else none)).bind
              (fun v => if (Sem.eval p) v then some v else none) = _
          rw [hv]; simp [hqv]
  | _ => rfl

omit [PrimAdm S] [PrimAdmA S] in
/-- A refinement's gate reads the inner term, so terms that read alike gate alike. -/
theorem refineReads_congr {t u : Term S} {q : S.V → Bool} {a : Sem.A S}
    (hh : (denote t).p a = (denote u).p a) : refineReads t q a = refineReads u q a := by
  simp only [refineReads, hh]

/-- **The refinement row, with the refinement on the left.** The predicate is data, so it rides
    on the meet of the inner terms; the reading agreement is what makes the gate agree. -/
theorem refine_row_l [Leaf S] [LeafAdm S] {x y w : Term S} {p : S.Pred}
    (ih1 : ∀ b, AdmA w b = (AdmA x b && AdmA y b))
    (ih2 : ∀ b, AdmA x b = true → AdmA y b = true →
      (denote w).p b = (denote x).p b ∧ (denote w).p b = (denote y).p b) :
    (∀ a, AdmA (Term.refineOf w p) a = (AdmA (.refine x p) a && AdmA y a)) ∧
    (∀ a, AdmA (.refine x p) a = true → AdmA y a = true →
      (denote (Term.refineOf w p)).p a = (denote (.refine x p)).p a ∧
      (denote (Term.refineOf w p)).p a = (denote y).p a) := by
  constructor
  · intro a
    rw [AdmA_refineOf]
    show (AdmA w a && refineReads w (Sem.eval p) a) = ((AdmA x a && refineReads x (Sem.eval p) a) && AdmA y a)
    cases hw : AdmA w a with
    | false =>
        rw [ih1 a, Bool.and_eq_false_iff] at hw
        rcases hw with hx | hy
        · rw [hx]; simp
        · rw [hy]; simp
    | true =>
        have hxy := ih1 a
        rw [hw] at hxy
        have hx : AdmA x a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).1
        have hy : AdmA y a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).2
        rw [refineReads_congr (ih2 a hx hy).1, hx, hy]
        simp
  · intro a ha hb
    rw [show AdmA (.refine x p) a = (AdmA x a && refineReads x (Sem.eval p) a) from rfl,
      Bool.and_eq_true] at ha
    obtain ⟨hx, hr⟩ := ha
    have hw : AdmA w a = true := by rw [ih1 a, hx, hb]; rfl
    obtain ⟨hd1, hd2⟩ := ih2 a hx hb
    cases hp : (denote x).p a with
    | none => rw [refineReads_none hp] at hr; exact absurd hr (by simp)
    | some v =>
        rw [refineReads_some hp] at hr
        have hwv : (denote w).p a = some v := hd1.trans hp
        have hyv : (denote y).p a = some v := hd2.symm.trans hwv
        refine ⟨?_, ?_⟩
        · rw [refineOf_p hw, hwv,
            show (denote (.refine x p)).p a
              = ((denote x).p a).bind (fun u => if (Sem.eval p) u then some u else none) from rfl, hp]
        · simp [refineOf_p hw, hwv, hyv, hr]

/-- …and with the refinement on the right. -/
theorem refine_row_r [Leaf S] [LeafAdm S] {x y w : Term S} {p : S.Pred}
    (ih1 : ∀ b, AdmA w b = (AdmA x b && AdmA y b))
    (ih2 : ∀ b, AdmA x b = true → AdmA y b = true →
      (denote w).p b = (denote x).p b ∧ (denote w).p b = (denote y).p b) :
    (∀ a, AdmA (Term.refineOf w p) a = (AdmA x a && AdmA (.refine y p) a)) ∧
    (∀ a, AdmA x a = true → AdmA (.refine y p) a = true →
      (denote (Term.refineOf w p)).p a = (denote x).p a ∧
      (denote (Term.refineOf w p)).p a = (denote (.refine y p)).p a) := by
  constructor
  · intro a
    rw [AdmA_refineOf]
    show (AdmA w a && refineReads w (Sem.eval p) a) = (AdmA x a && (AdmA y a && refineReads y (Sem.eval p) a))
    cases hw : AdmA w a with
    | false =>
        rw [ih1 a, Bool.and_eq_false_iff] at hw
        rcases hw with hx | hy
        · rw [hx]; simp
        · rw [hy]; simp
    | true =>
        have hxy := ih1 a
        rw [hw] at hxy
        have hx : AdmA x a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).1
        have hy : AdmA y a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).2
        rw [refineReads_congr (ih2 a hx hy).2, hx, hy]
        simp
  · intro a ha hb
    rw [show AdmA (.refine y p) a = (AdmA y a && refineReads y (Sem.eval p) a) from rfl,
      Bool.and_eq_true] at hb
    obtain ⟨hy, hr⟩ := hb
    have hw : AdmA w a = true := by rw [ih1 a, ha, hy]; rfl
    obtain ⟨hd1, hd2⟩ := ih2 a ha hy
    cases hp : (denote y).p a with
    | none => rw [refineReads_none hp] at hr; exact absurd hr (by simp)
    | some v =>
        rw [refineReads_some hp] at hr
        have hwv : (denote w).p a = some v := hd2.trans hp
        have hxv : (denote x).p a = some v := hd1.symm.trans hwv
        refine ⟨?_, ?_⟩
        · simp [refineOf_p hw, hwv, hxv, hr]
        · rw [refineOf_p hw, hwv,
            show (denote (.refine y p)).p a
              = ((denote y).p a).bind (fun u => if (Sem.eval p) u then some u else none) from rfl, hp]

/-- The options that survive are the ones that read; the bottoms read nothing. -/
theorem AdmAAny_filter_never : ∀ (ts : List (Term S)) (v : Sem.A S),
    AdmAAny (ts.filter (fun z => !z.isNever)) v = AdmAAny ts v
  | [], _ => rfl
  | t :: ts, v => by
      cases ht : t.isNever with
      | true =>
        have htn : t = Term.never := eq_never_of_isNever ht
        subst htn
        rw [List.filter_cons, if_neg (by simp [Term.isNever]), AdmAAny_cons,
          AdmAAny_filter_never ts v]
        rfl
      | false =>
        rw [List.filter_cons, if_pos (by simp [ht]), AdmAAny_cons, AdmAAny_cons,
          AdmAAny_filter_never ts v]

/-- The join over the met options is the join over the options, met with the partner. -/
theorem AdmAAny_meet {y : Term S} (v : Sem.A S) : ∀ {os zs : List (Term S)},
    List.Forall₂ (fun t w => ∀ u, AdmA w u = (AdmA t u && AdmA y u)) os zs →
    AdmAAny zs v = (AdmAAny os v && AdmA y v) := by
  intro os zs h
  induction h with
  | nil => simp
  | cons hh _ ihx =>
    rw [AdmAAny_cons, AdmAAny_cons, hh v, ihx]
    cases AdmA _ v <;> cases AdmA y v <;> simp

/-- **`ofOptions` reads what its options read**, and no certificate is spent. -/
theorem AdmA_ofOptions (ts : List (Term S)) (a : Sem.A S) :
    AdmA (Term.ofOptions ts) a = AdmAAny ts a := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAAny_cons, AdmAAny_nil, Bool.or_false]
  | _ :: _ :: _ => rfl

/-- **The coproduct row of the meet needs no certificate, on the read side either.** -/
theorem union_meet_freeA {os zs : List (Term S)} {y : Term S} (a : Sem.A S)
    (hR : List.Forall₂ (fun t w => ∀ b, AdmA w b = (AdmA t b && AdmA y b)) os zs) :
    AdmA (Term.ofOptions (zs.filter (fun z => !z.isNever))) a
      = (AdmA (.union os) a && AdmA y a) := by
  rw [AdmA_ofOptions, AdmAAny_filter_never, AdmAAny_meet a hR, AdmA_union]

/-- A `Forall₂` relates every left element to some right one. -/
theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {x}, x ∈ as → ∃ y ∈ bs, R x y
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons hr hrest, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨y, hy, hry⟩ := forall₂_mem_left hrest hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

/-- **A union reads through its first reader.** -/
theorem union_p_find (ts : List (Term S)) (a : Sem.A S) :
    (denote (.union ts)).p a = (ts.find? (fun u => AdmA u a)).bind (fun t => (denote t).p a) := by
  show select (denoteList ts) (·.p) a = _
  unfold select
  rw [denoteList_eq, List.find?_map]
  have hq : ((fun c : S.C => (c.p a).isSome) ∘ denote) = fun u => AdmA u a := by
    funext u
    show ((denote u).p a).isSome = AdmA u a
    rw [isSome_p_eq_AdmA u a]
  rw [hq]
  cases ts.find? (fun u => AdmA u a) <;> simp

/-- …and so does a list of survivors, whatever its length. -/
theorem ofOptions_p_find (ts : List (Term S)) (a : Sem.A S) :
    (denote (Term.ofOptions ts)).p a
      = (ts.find? (fun u => AdmA u a)).bind (fun t => (denote t).p a) := by
  match ts with
  | [] => rfl
  | [s] =>
      show (denote s).p a = _
      cases h : AdmA s a with
      | true => simp [List.find?, h]
      | false =>
        have : (denote s).p a = none := by
          cases hp : (denote s).p a with
          | none => rfl
          | some _ => rw [(AdmA_exact s a).mpr (by rw [hp]; rfl)] at h; exact nomatch h
        simp [List.find?, h, this]
  | _ :: _ :: _ => exact union_p_find _ a

/-- **The first reader crosses a `Forall₂`** whose relation keeps the reading test. -/
theorem find?_forall₂ {α β : Type} {P : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ t w, P t w → q w = p t) :
    ∀ {os : List α} {zs : List β}, List.Forall₂ P os zs →
      ∀ {t}, os.find? p = some t → ∃ w, zs.find? q = some w ∧ P t w
  | _, _, .nil, _, h => nomatch h
  | _, _, @List.Forall₂.cons _ _ _ t0 w0 _ _ hr hrest, t, h => by
      cases hp : p t0 with
      | true =>
        rw [List.find?_cons_of_pos hp] at h; cases h
        exact ⟨w0, List.find?_cons_of_pos (by rw [hpq _ _ hr, hp]), hr⟩
      | false =>
        rw [List.find?_cons_of_neg (by simp [hp])] at h
        obtain ⟨w, hw, hP⟩ := find?_forall₂ hpq hrest h
        exact ⟨w, by rw [List.find?_cons_of_neg (by simp [hpq _ _ hr, hp])]; exact hw, hP⟩

/-- Filtering out what cannot pass the test leaves the first passer. -/
theorem find?_filter_of {β : Type} {q keep : β → Bool} (h : ∀ w, q w = true → keep w = true) :
    ∀ zs : List β, (zs.filter keep).find? q = zs.find? q
  | [] => rfl
  | w :: zs => by
      cases hq : q w with
      | true => rw [List.filter_cons_of_pos (h w hq), List.find?_cons_of_pos hq,
          List.find?_cons_of_pos hq]
      | false =>
        rw [List.find?_cons_of_neg (by simp [hq])]
        cases hk : keep w with
        | true => rw [List.filter_cons_of_pos hk, List.find?_cons_of_neg (by simp [hq]),
            find?_filter_of h zs]
        | false => rw [List.filter_cons_of_neg (by simp [hk]), find?_filter_of h zs]

/-- A union that reads has a first reader. -/
theorem find?_of_AdmA_union {os : List (Term S)} {a : Sem.A S} (h : AdmA (.union os) a = true) :
    ∃ t, os.find? (fun u => AdmA u a) = some t := by
  rw [AdmA_union] at h
  obtain ⟨t, ht, hta⟩ := AdmAAny_iff.mp h
  cases hf : os.find? (fun u => AdmA u a) with
  | some t' => exact ⟨t', rfl⟩
  | none => exact absurd hta (by simpa using List.find?_eq_none.mp hf t ht)

/-! ## The read side's homomorphism and its reading agreement, structurally -/

/-- `f` answers the read side with one term fixed on the left, at every right operand. -/
def AdmASound (x : Term S) (f : Term S → Option (Term S)) : Prop :=
  ∀ y z, f y = some z → AdmAAt x y z

/-- …and over the operands the shared inner hands a family. -/
def AdmAFam (x : Term S) (fam : Term S → Option (Term S)) : Prop :=
  ∀ y z, Delegated y → fam y = some z → AdmAAt x y z

/-- **Three rows that read every position alike read the whole list alike.** The answer's row
    and the two factors' rows agree at every position that both factors admit, so the three
    traversals agree. -/
theorem traverse_p_agree : ∀ {r₁ r₂ rz : List (Term S)} {as : List (Sem.A S)},
    List.Forall₂ (fun (pq : Term S × Term S) w => AdmAAt pq.1 pq.2 w) (r₁.zip r₂) rz →
    r₁.length = r₂.length →
    List.Forall₂ (fun t b => AdmA t b = true) r₁ as →
    List.Forall₂ (fun t b => AdmA t b = true) r₂ as →
    traverse (fun ca : S.C × Sem.A S => ca.1.p ca.2) ((rz.map denote).zip as)
        = traverse (fun ca : S.C × Sem.A S => ca.1.p ca.2) ((r₁.map denote).zip as) ∧
      traverse (fun ca : S.C × Sem.A S => ca.1.p ca.2) ((rz.map denote).zip as)
        = traverse (fun ca : S.C × Sem.A S => ca.1.p ca.2) ((r₂.map denote).zip as) := by
  intro r₁
  induction r₁ with
  | nil =>
      intro r₂ rz as hF hl ha hb
      cases r₂ with
      | nil => cases hF; cases ha; exact ⟨rfl, rfl⟩
      | cons => exact absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
  | cons t r₁' ih =>
      intro r₂ rz as hF hl ha hb
      cases r₂ with
      | nil => exact absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
      | cons u r₂' =>
          rw [List.zip_cons_cons] at hF
          cases hF with
          | cons hh ht =>
              cases ha with
              | cons hat hat' =>
                  cases hb with
                  | cons hbt hbt' =>
                      obtain ⟨hz1, hz2⟩ :=
                        ih ht (by simp only [List.length_cons] at hl; omega) hat' hbt'
                      obtain ⟨hp1, hp2⟩ := hh.2 _ hat hbt
                      refine ⟨?_, ?_⟩
                      · simp only [List.map_cons, List.zip_cons_cons, traverse_cons, hp1, hz1]
                      · simp only [List.map_cons, List.zip_cons_cons, traverse_cons, hp2, hz2]

/-- **The whole read-side obligation of the `list` meet, read off the three rows.** The
    admission half is `AdmA_list_rows`; the reading half is `traverse_p_agree` through
    `slotsL_eq_rowOfG`, which says the codec-side row and the term-side row are one row. -/
theorem AdmA_list_at {p₁ s₁ p₂ s₂ pz sz : List (Term S)} {q₁ q₂ qz : Option (Term S)}
    (hsome : ∀ n, (rowOfG pz qz sz n).isSome
      = ((rowOfG p₁ q₁ s₁ n).isSome && (rowOfG p₂ q₂ s₂ n).isSome))
    (hrel : ∀ n r₁ r₂ rz, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      rowOfG pz qz sz n = some rz →
      r₁.length = r₂.length ∧
        List.Forall₂ (fun (pq : Term S × Term S) w => AdmAAt pq.1 pq.2 w) (r₁.zip r₂) rz) :
    AdmAAt (.list p₁ q₁ s₁) (.list p₂ q₂ s₂) (.list pz qz sz) := by
  refine ⟨AdmA_list_rows hsome (fun n r₁ r₂ rz h1 h2 h3 => ?_), ?_⟩
  · obtain ⟨hlen, hF⟩ := hrel n r₁ r₂ rz h1 h2 h3
    exact ⟨hlen, hF.imp (fun _ _ h => h.1)⟩
  · intro a ha hb
    cases hla : listOutA a with
    | none => rw [AdmA_list_of_none hla] at ha; exact absurd ha (by simp)
    | some as =>
        simp only [AdmA_list_of_out hla, AdmAList_eq_map, AdmAOptT_eq_map, alignPL_eq_rowOfG,
          rowOfG_map] at ha hb
        cases h₁ : rowOfG p₁ q₁ s₁ as.length with
        | none => rw [h₁] at ha; simp at ha
        | some r₁ =>
            cases h₂ : rowOfG p₂ q₂ s₂ as.length with
            | none => rw [h₂] at hb; simp at hb
            | some r₂ =>
                have hzs := hsome as.length
                rw [h₁, h₂] at hzs
                cases hz : rowOfG pz qz sz as.length with
                | none => rw [hz] at hzs; simp at hzs
                | some rz =>
                    obtain ⟨hlen, hF⟩ := hrel _ _ _ _ h₁ h₂ hz
                    rw [h₁] at ha
                    rw [h₂] at hb
                    simp only [Option.map_some, ← AdmAList_eq_map] at ha hb
                    obtain ⟨hq1, hq2⟩ :=
                      traverse_p_agree hF hlen (zipPA_forall₂ ha) (zipPA_forall₂ hb)
                    unfold listOutA at hla
                    rcases hL : Sem.list (S := S) with _ | Lf
                    · rw [hL] at hla; exact absurd hla (by simp)
                    · rw [hL, Option.bind_some] at hla
                      simp only [denote, hL, listCodec, carriedCodec, alignL, denoteList_eq,
                        denoteOpt_eq_map, slotsL_eq_rowOfG, rowOfG_map, h₁, h₂, hz,
                        Option.map_some, Option.bind_some, hla]
                      exact ⟨congrArg (Option.map Lf.pV.into) hq1,
                        congrArg (Option.map Lf.pV.into) hq2⟩

mutual
/-- Every row that reads the right operand alone reads what the family reads. -/
theorem admA_meetSRight [Leaf S] [LeafAdm S] {x : Term S} {fam : Term S → Option (Term S)} (hf : AdmAFam x fam) :
    ∀ (y : Term S) z, meetSRight fam y = some z → AdmAAt x y z
  | .never, _, h => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
  | .var _, _, h => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
  | .held _ _ _ _, _, h => by simp [meetSRight] at h
  | .refine y p, _, h => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ih1, ih2⟩ := admA_meetSRight hf y w hw
        exact refine_row_r ih1 ih2
      · exact absurd h (by simp)
  | .union os, _, h => by
      obtain ⟨zs, hF, rfl⟩ := meetSRight_union h
      have hB := admA_meetSRightL hf os zs hF
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · rw [Bool.and_comm]
        exact union_meet_freeA a (List.Forall₂.imp (fun _ _ hh => hh.1) hB)
      · obtain ⟨t, hft⟩ := find?_of_AdmA_union hb
        have hta : AdmA t a = true := List.find?_some (p := fun u => AdmA u a) hft
        obtain ⟨w, hfw, hwA, hwP⟩ :=
          find?_forall₂ (q := fun u => AdmA u a) (fun _ _ hh => by rw [hh.1 a, ha, Bool.and_true])
            hB hft
        rw [ofOptions_p_find, find?_filter_of (fun w hw => by rw [not_isNever_of_admA hw]; rfl),
          hfw, union_p_find, hft]
        exact ⟨(hwP a hta ha).2, (hwP a hta ha).1⟩
  | .prim g, _, h => hf (.prim g) _ trivial h
  | .set b, _, h => hf (.set b) _ trivial h
  | .opaq, _, h => hf .opaq _ trivial h
  | .list p q s, _, h => hf (.list p q s) _ trivial h
  | .object b, _, h => hf (.object b) _ trivial h
termination_by structural y => y

/-- The union row's options, lifted pointwise. -/
theorem admA_meetSRightL [Leaf S] [LeafAdm S] {x : Term S} {fam : Term S → Option (Term S)} (hf : AdmAFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w =>
        (∀ b, AdmA w b = (AdmA t b && AdmA x b)) ∧
        (∀ b, AdmA t b = true → AdmA x b = true →
          (denote w).p b = (denote t).p b ∧ (denote w).p b = (denote x).p b)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          obtain ⟨h1, h2⟩ := admA_meetSRight hf t _ hh
          exact .cons ⟨fun b => by rw [h1 b, Bool.and_comm],
            fun b hbt hbx => ⟨(h2 b hbx hbt).2, (h2 b hbx hbt).1⟩⟩ (admA_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-! ### The leaf families -/

/-- **The one leaf family reads exactly wherever the leaf laws hold.** -/
theorem admA_famPrim [Leaf S] [LeafAdmA S] [FormerAdmA S] (g : S.Ground) :
    AdmAFam (.prim g) (famPrim g) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case prim g' =>
      simp only [famPrim, Option.some.injEq] at h
      subst h
      cases hp : Leaf.prim g g' with
      | some k => exact LeafAdmA.prim_some g g' k hp
      | none => exact bottom_of_and_falseA (LeafAdmA.prim_none g g' hp)
  case opaq =>
      simp only [famPrim] at h
      cases ht : Leaf.primTop g with
      | false => simp [ht] at h
      | true =>
          simp only [ht, if_true, Option.some.injEq] at h
          subst h
          exact LeafAdmA.prim_top g ht
  all_goals fam_bottomA famPrim

/-- The top meets itself, and a primitive where the leaf says so. -/
theorem admA_famOpaq [Leaf S] [LeafAdmA S] : AdmAFam (.opaq : Term S) famOpaq := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case prim g =>
      simp only [famOpaq] at h
      cases ht : Leaf.primTop g with
      | false => simp [ht] at h
      | true =>
          simp only [ht, if_true, Option.some.injEq] at h
          subst h
          exact (LeafAdmA.prim_top g ht).swap
  case opaq =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      exact admA_same _
  all_goals simp [famOpaq] at h

/-- **Two sets read together at their elements**, and a set reads nothing that another former
    reads. -/
theorem admA_famSet [FormerAdmA S] (a : Term S) {mt : Term S → Option (Term S)}
    (ih : AdmASound a mt) : AdmAFam (.set a) (famSet a mt) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case set y =>
      simp only [famSet] at h
      split at h
      · next z' hz =>
        have hm := (ih y z' hz).1
        split at h
        · next hn =>
          simp only [Option.some.injEq] at h; subst h
          have hz' : z' = .never := eq_never_of_isNever hn
          subst hz'
          exact bottom_of_and_falseA
            (FormerAdmA.set_never a y (fun u => by rw [← hm u, AdmA_never]))
        · next hn =>
          split at h
          · exact nomatch h
          · next hh =>
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hh
            simp only [Option.some.injEq] at h; subst h
            exact FormerAdmA.set_meet a y z' (HF_of_hasHeld a hh.1.1) (HF_of_hasHeld y hh.1.2)
              (HF_of_hasHeld z' hh.2) hm
      · exact nomatch h
  case opaq => simp [famSet] at h
  all_goals fam_bottomA famSet

/-! ### The container families -/

/-- Two tuples' positions, zipped and lifted pointwise. -/
theorem admAList_zip_lift :
    ∀ {ts us : List (Term S)} {fs : List (Term S → Option (Term S))} {vs : List (Term S)},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun (p : (Term S → Option (Term S)) × Term S) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : (Sem.A S → Bool) × (Sem.A S → Bool)) r => ∀ w, r w = (pq.1 w && pq.2 w))
        ((AdmAList ts).zip (AdmAList us)) (AdmAList vs) := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hF; cases hfs; rw [List.zip_nil_left] at hF; cases hF; exact .nil
  | cons t ts' ihx =>
      intro us fs vs hfs hF
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => rw [List.zip_nil_right] at hF; cases hF; exact .nil
          | cons u us' =>
              cases hF with
              | cons hh ht => exact .cons (fun w => (hf u _ hh).1 w) (ihx hfs' ht)

/-- **Normalisation keeps the read-side obligation.** Where a declared position is the bottom
    the answer admits no attribute, so the reading half is vacuous and the bottom stands. -/
theorem AdmAAt_listOf {x y : Term S} {pre suf : List (Term S)} {sp : Option (Term S)}
    (h : AdmAAt x y (.list pre sp suf)) : AdmAAt x y (Term.listOf pre sp suf) := by
  rcases listOf_cases pre sp suf with hc | hc
  · rw [hc]
    refine bottom_row (fun a => ?_)
    rw [← h.1 a, ← AdmA_listOf, hc]
  · rw [hc]; exact h

/-- Two rows of terms, the left as partially applied meets, met position by position on the
    read side. The term-level twin of `admAList_zip_lift`. -/
theorem zipF_lift_termsA :
    ∀ {ts us : List (Term S)} {fs : List (Term S → Option (Term S))} {vs : List (Term S)},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun (p : (Term S → Option (Term S)) × Term S) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : Term S × Term S) w => AdmAAt pq.1 pq.2 w) (ts.zip us) vs := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts ihs =>
      intro us fs vs hfs hv
      cases hfs with
      | cons hsound hfs' =>
          cases us with
          | nil => cases hv; exact .nil
          | cons u us =>
              cases hv with
              | cons hh ht => exact .cons (hsound u _ hh) (ihs hfs' ht)

/-- **The one positional container's family, on the read side.** The same three branches the
    value side takes, with `AdmA_list_at` in place of `Adm_list_rows`. -/
theorem admA_famList [FormerAdmA S] {pre suf : List (Term S)} {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Option (Term S))} {fsp : Option (Term S → Option (Term S))}
    (hp : List.Forall₂ AdmASound pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ AdmASound t f)
    (hf : List.Forall₂ AdmASound suf fsuf) :
    AdmAFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case list pre₂ sp₂ suf₂ =>
      simp only [famList] at h
      rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, hsound⟩
      · simp only [listMeetRow] at h
        rw [show rowOfG fpre none fsuf (fpre.length + fsuf.length) = some (fpre ++ fsuf) from
          by rw [rowOfG_none_eq, if_pos rfl]] at h
        have hlen0 : fpre.length + fsuf.length = pre.length + suf.length := by omega
        rw [hlen0] at h
        cases hR : rowOfG pre₂ sp₂ suf₂ (pre.length + suf.length) with
        | none =>
            rw [hR] at h
            simp only [Option.some.injEq] at h
            subst h
            have hdis : ∀ n, rowOfG pre none suf n = none ∨ rowOfG pre₂ sp₂ suf₂ n = none := by
              intro n
              cases hd2 : decide (n = pre.length + suf.length) with
              | true => simp only [decide_eq_true_eq] at hd2; subst hd2; exact Or.inr hR
              | false =>
                  simp only [decide_eq_false_iff_not] at hd2
                  exact Or.inl (by rw [rowOfG_none_eq, if_neg hd2])
            exact bottom_row (fun a => (AdmA_list_disjoint hdis a).symm)
        | some us =>
            rw [hR] at h
            obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
            have hus : us.length = pre.length + suf.length := rowOfG_length hR
            have hFz : List.Forall₂
                (fun (p : (Term S → Option (Term S)) × Term S) w => p.1 p.2 = some w)
                ((fpre ++ fsuf).zip us) row :=
              allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
            have hrowlen : row.length = pre.length + suf.length := by
              have hz := hFz.length_eq
              simp only [List.length_zip, List.length_append, hus] at hz
              omega
            have hrel₀ := zipF_lift_termsA (forall₂_append hp hf) hFz
            refine AdmAAt_listOf ?_
            refine AdmA_list_at (p₁ := pre) (q₁ := none) (s₁ := suf) ?_ ?_
            · intro n
              simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, hrowlen]
              cases hd2 : decide (n = pre.length + suf.length) with
              | true =>
                  simp only [decide_eq_true_eq] at hd2
                  subst hd2
                  rw [if_pos rfl, if_pos rfl, hR]
                  simp
              | false =>
                  simp only [decide_eq_false_iff_not] at hd2
                  rw [if_neg hd2, if_neg hd2]
                  simp
            · intro n r₁ r₂ rz h1 h2 h3
              rw [rowOfG_none_eq] at h1 h3
              simp only [List.length_nil, Nat.add_zero, hrowlen] at h3
              split at h1
              · next he =>
                  simp only [Option.some.injEq] at h1
                  subst h1
                  subst he
                  rw [if_pos rfl] at h3
                  simp only [Option.some.injEq] at h3
                  subst h3
                  rw [hR] at h2
                  simp only [Option.some.injEq] at h2
                  subst h2
                  exact ⟨by simp only [List.length_append]; omega, by simpa using hrel₀⟩
              · exact absurd h1 (by simp)
      · cases sp₂ with
        | none =>
            simp only [listMeetRow] at h
            rw [show rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length)
                = some (pre₂ ++ suf₂) from by rw [rowOfG_none_eq, if_pos rfl]] at h
            cases hL : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
            | none =>
                rw [hL] at h
                simp only [Option.some.injEq] at h
                subst h
                have hshort : pre₂.length + suf₂.length < fpre.length + fsuf.length := by
                  rw [rowOfG_some_eq] at hL
                  split at hL
                  · omega
                  · exact absurd hL (by simp)
                have hdis : ∀ n,
                    rowOfG pre (some t) suf n = none ∨ rowOfG pre₂ none suf₂ n = none := by
                  intro n
                  cases hd2 : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd2
                      subst hd2
                      exact Or.inl (by rw [rowOfG_some_eq, if_pos (by omega)])
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd2
                      exact Or.inr (by rw [rowOfG_none_eq, if_neg hd2])
                exact bottom_row (fun a => (AdmA_list_disjoint hdis a).symm)
            | some fs =>
                rw [hL] at h
                obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨ts, hts, htsF⟩ :=
                  rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hL
                have hmin : pre.length + suf.length ≤ pre₂.length + suf₂.length := by
                  rw [rowOfG_some_eq] at hL
                  split at hL
                  · exact absurd hL (by simp)
                  · omega
                have hfs : fs.length = pre₂.length + suf₂.length := rowOfG_length hL
                have hFz : List.Forall₂
                    (fun (p : (Term S → Option (Term S)) × Term S) w => p.1 p.2 = some w)
                    (fs.zip (pre₂ ++ suf₂)) row :=
                  allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
                have hrowlen : row.length = pre₂.length + suf₂.length := by
                  have hz := hFz.length_eq
                  simp only [List.length_zip, List.length_append, hfs] at hz
                  omega
                have hrel₀ := zipF_lift_termsA htsF hFz
                refine AdmAAt_listOf ?_
                refine AdmA_list_at (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_
                · intro n
                  simp only [rowOfG_none_eq, rowOfG_some_eq, List.length_nil, Nat.add_zero,
                    hrowlen]
                  cases hd2 : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd2
                      subst hd2
                      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
                      simp
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd2
                      rw [if_neg hd2, if_neg hd2]
                      simp
                · intro n r₁ r₂ rz h1 h2 h3
                  rw [rowOfG_none_eq] at h2 h3
                  simp only [List.length_nil, Nat.add_zero, hrowlen] at h3
                  split at h2
                  · next he =>
                      simp only [Option.some.injEq] at h2
                      subst h2
                      subst he
                      rw [if_pos rfl] at h3
                      simp only [Option.some.injEq] at h3
                      subst h3
                      rw [hts] at h1
                      simp only [Option.some.injEq] at h1
                      subst h1
                      refine ⟨?_, by simpa using hrel₀⟩
                      have hl := rowOfG_length hts
                      simp only [List.length_append]
                      omega
                  · exact absurd h2 (by simp)
        | some c =>
            simp only [listMeetRow] at h
            split at h
            · next hdom =>
                obtain ⟨fs, hfs⟩ :=
                  rowOfG_total (pre := fpre) (suf := fsuf) (c := f)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                obtain ⟨us, hus⟩ :=
                  rowOfG_total (pre := pre₂) (suf := suf₂) (c := c)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                rw [hfs, hus] at h
                cases hfc : f c with
                | none => rw [hfc] at h; exact absurd h (by simp)
                | some spz =>
                    rw [hfc] at h
                    obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                    have hfsl : fs.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hfs
                    have husl : us.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hus
                    have hFz : List.Forall₂
                        (fun (p : (Term S → Option (Term S)) × Term S) w => p.1 p.2 = some w)
                        (fs.zip us) row :=
                      allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
                    have hrowlen : row.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length := by
                      have hz := hFz.length_eq
                      simp only [List.length_zip, hfsl, husl] at hz
                      omega
                    have htk : (row.take (max fpre.length pre₂.length)).length
                        = max fpre.length pre₂.length := by
                      rw [List.length_take, hrowlen]; omega
                    have hdp : (row.drop (max fpre.length pre₂.length)).length
                        = max fsuf.length suf₂.length := by
                      rw [List.length_drop, hrowlen]; omega
                    obtain ⟨ts, hts, htsF⟩ :=
                      rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hfs
                    have htsl : ts.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hts
                    have hrel₀ := zipF_lift_termsA htsF hFz
                    have hspz : AdmAAt t c spz := hsound c spz hfc
                    have hdm := dominates_max hdom
                    refine AdmAAt_listOf ?_
                    refine AdmA_list_at (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_
                    · intro n
                      simp only [rowOfG_some_isSome, htk, hdp]
                      rcases Nat.lt_or_ge n (pre.length + suf.length) with h1 | h1
                      · rw [decide_eq_false (by omega : ¬ (max fpre.length pre₂.length
                          + max fsuf.length suf₂.length ≤ n)),
                          decide_eq_false (by omega : ¬ (pre.length + suf.length ≤ n)),
                          Bool.false_and]
                      · rcases Nat.lt_or_ge n (pre₂.length + suf₂.length) with h2 | h2
                        · rw [decide_eq_false (by omega : ¬ (max fpre.length pre₂.length
                            + max fsuf.length suf₂.length ≤ n)),
                            decide_eq_true (by omega : pre.length + suf.length ≤ n),
                            decide_eq_false (by omega : ¬ (pre₂.length + suf₂.length ≤ n)),
                            Bool.and_false]
                        · rw [decide_eq_true (by omega : max fpre.length pre₂.length
                            + max fsuf.length suf₂.length ≤ n),
                            decide_eq_true (by omega : pre.length + suf.length ≤ n),
                            decide_eq_true (by omega : pre₂.length + suf₂.length ≤ n),
                            Bool.and_self]
                    · intro n r₁ r₂ rz h1 h2 h3
                      rw [rowOfG_some_eq, htk, hdp] at h3
                      split at h3
                      · exact absurd h3 (by simp)
                      · next hge =>
                          simp only [Option.some.injEq] at h3
                          subst h3
                          have hr₁ := rowOfG_respread (P := max fpre.length pre₂.length)
                            (S := max fsuf.length suf₂.length)
                            (by omega) (by omega) (by omega) hts h1
                          have hr₂ := rowOfG_respread (P := max fpre.length pre₂.length)
                            (S := max fsuf.length suf₂.length)
                            (by omega) (by omega) (by omega) hus h2
                          subst hr₁; subst hr₂
                          refine ⟨?_, ?_⟩
                          · simp only [List.length_append, List.length_take, List.length_drop,
                              List.length_replicate, htsl, husl]
                          · refine forall₂_zip_append ?_
                              (forall₂_zip_append ?_ (forall₂_zip_take _ hrel₀)
                                (forall₂_zip_replicate hspz _))
                              (forall₂_zip_drop _ hrel₀)
                            · simp only [List.length_append, List.length_take,
                                List.length_replicate, htsl, husl]
                            · simp only [List.length_take, htsl, husl]
            · exact absurd h (by simp)
  case opaq => simp [famList] at h
  all_goals fam_bottomA famList

/-! ### The object families -/

/-- **A body reads a map by its slots**, the read side's twin of `AdmBody_map_slots`. -/
theorem AdmABody_map_slots (c : Body S) {x : Sem.A S} {m : MapOf (Sem.A S)}
    (hm : mapOutA x = some m) :
    AdmABody c x = true ↔
      (∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ m.keys) ∧
      ∀ k : {k // k ∈ m.keys}, AdmAField (c.slotAt k.1) (m.get k) = true := by
  rw [AdmABody_of_out hm, reqPresentT_req, Bool.and_eq_true, reqs_slotAt]
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

/-- **Two bodies conjoined at every name are conjoined as bodies**, read side. -/
theorem AdmABody_of_slots {a b z : Body S}
    (hS : ∀ k c, AdmAField (z.slotAt k) c = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c))
    (hR : ∀ k, ObjectSlot.isReq (z.slotAt k)
      = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (c : Sem.A S) : AdmABody z c = (AdmABody a c && AdmABody b c) := by
  cases hc : mapOutA c with
  | none => rw [AdmABody_of_none hc, AdmABody_of_none hc, AdmABody_of_none hc]; rfl
  | some m =>
    rw [Bool.eq_iff_iff, Bool.and_eq_true, AdmABody_map_slots _ hc, AdmABody_map_slots _ hc,
      AdmABody_map_slots _ hc]
    constructor
    · rintro ⟨hr, hs⟩
      refine ⟨⟨fun k h => hr k (by rw [hR, h, Bool.true_or]), fun k => ?_⟩,
        ⟨fun k h => hr k (by rw [hR, h, Bool.or_true]), fun k => ?_⟩⟩
      · have h1 := hs k; rw [hS, Bool.and_eq_true] at h1; exact h1.1
      · have h1 := hs k; rw [hS, Bool.and_eq_true] at h1; exact h1.2
    · rintro ⟨⟨hra, hsa⟩, ⟨hrb, hsb⟩⟩
      refine ⟨fun k h => ?_, fun k => by rw [hS, hsa k, hsb k]; rfl⟩
      rw [hR, Bool.or_eq_true] at h
      exact h.elim (hra k) (hrb k)

omit [PrimAdm S] [PrimAdmA S] in
/-- A present name reads through its slot's codec, the block `never` standing in for a
    closed body: `Codec.empty` reads nothing, and neither does a missing rest codec. -/
theorem entryCodec_slotAt (c : Body S) (k : String) (x : Sem.A S) :
    (entryCodec ⟨c.fields, fun k => fieldSem (c.at k)⟩ (rcOf (wildSem c.wild)) k).bind
        (fun cd => cd.p x)
      = (fieldSem (c.slotAt k)).codec.p x := by
  unfold entryCodec; simp only [MapOf.at]
  rcases Decidable.em (k ∈ c.fields) with hk | hk
  · rw [dif_pos hk, Body.slotAt_pos hk]; rfl
  · rw [dif_neg hk, Body.slotAt_neg hk]
    cases hw : c.wild with
    | none => simp [wildSem, rcOf, Body.block, hw, fieldSem, FieldSem.codec, denote, Codec.empty]
    | some t => simp [wildSem, rcOf, Body.block, hw, fieldSem, FieldSem.codec]

omit [PrimAdm S] [PrimAdmA S] in
/-- **Two bodies that read every present name alike read the map alike.** -/
theorem bodySem_p_congr {c d : Body S} {x : Sem.A S} {m : MapOf (Sem.A S)}
    (hm : mapOutA x = some m)
    (hc : reqPresentB ⟨c.fields, fun k => fieldSem (c.at k)⟩ m.keys = true)
    (hd : reqPresentB ⟨d.fields, fun k => fieldSem (d.at k)⟩ m.keys = true)
    (he : ∀ k (hk : k ∈ m.keys), (fieldSem (c.slotAt k)).codec.p (m.get ⟨k, hk⟩)
      = (fieldSem (d.slotAt k)).codec.p (m.get ⟨k, hk⟩)) :
    (bodySem c).p x = (bodySem d).p x := by
  have hkc : ∀ w : Option (Term S), ∀ sems : MapOf (FieldSem S.V (Sem.A S) (Sem.M S)),
      keepB (wildSem w) sems = fun _ => true := by
    intro w sems; cases w <;> rfl
  unfold mapOutA at hm
  rcases hF : Sem.map (S := S) with _ | F
  · rw [hF] at hm; exact absurd hm (by simp)
  · rw [hF, Option.bind_some] at hm
    cases c with
    | mk fc Fc wc =>
      cases d with
      | mk fd Fd wd =>
        simp only [bodySem, hF, objectCodec, objectCodecCore, carriedCodec, hkc, hm,
          Option.bind_some]
        simp only [objRead]
        simp only [Body.fields_mk, Body.at_mk] at hc hd
        rw [if_pos hc, if_pos hd, Option.map_map, Option.map_map]
        refine congrArg (Option.map _) (congrArg funImage (funext fun kk => ?_))
        have hk' := (Finset.mem_filter.mp kk.2).1
        have h1 := entryCodec_slotAt (.mk fc Fc wc) kk.1 (m.get ⟨kk.1, hk'⟩)
        have h2 := entryCodec_slotAt (.mk fd Fd wd) kk.1 (m.get ⟨kk.1, hk'⟩)
        simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at h1 h2
        exact (h1.trans (he kk.1 hk')).trans h2.symm

/-- A body that reads a map finds every required name present. -/
theorem reqPresentB_of_AdmABody {c : Body S} {x : Sem.A S} {m : MapOf (Sem.A S)}
    (hm : mapOutA x = some m) (h : AdmABody c x = true) :
    reqPresentB ⟨c.fields, fun k => fieldSem (c.at k)⟩ m.keys = true := by
  rw [AdmABody_of_out hm, Bool.and_eq_true] at h
  rw [← reqPresentT_eq]; exact h.1

/-- **Two objects conjoined at every name, read side**: the rows conjoin, and where both
    factors read a map the meet reads it as each of them does. -/
theorem AdmA_object_of_slots {a b z : Body S}
    (hS : ∀ k c, AdmAField (z.slotAt k) c = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c))
    (hR : ∀ k, ObjectSlot.isReq (z.slotAt k)
      = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (hP : ∀ k c, AdmAField (a.slotAt k) c = true → AdmAField (b.slotAt k) c = true →
      (fieldSem (z.slotAt k)).codec.p c = (fieldSem (a.slotAt k)).codec.p c
        ∧ (fieldSem (z.slotAt k)).codec.p c = (fieldSem (b.slotAt k)).codec.p c) :
    (∀ c, AdmA (.object z) c = (AdmA (.object a) c && AdmA (.object b) c)) ∧
    (∀ c, AdmA (.object a) c = true → AdmA (.object b) c = true →
      (denote (.object z)).p c = (denote (.object a)).p c
        ∧ (denote (.object z)).p c = (denote (.object b)).p c) := by
  have half1 : ∀ c, AdmA (.object z) c = (AdmA (.object a) c && AdmA (.object b) c) :=
    AdmABody_of_slots hS hR
  refine ⟨half1, fun c hA hB => ?_⟩
  have hZ : AdmA (.object z) c = true := by rw [half1, hA, hB]; rfl
  cases hc : mapOutA c with
  | none =>
    exact absurd hA (by
      show ¬ AdmABody a _ = true
      rw [AdmABody_of_none hc]; simp)
  | some m =>
    have hA' : AdmABody a c = true := hA
    have hB' : AdmABody b c = true := hB
    have hZ' : AdmABody z c = true := hZ
    have hsa := ((AdmABody_map_slots a hc).mp hA').2
    have hsb := ((AdmABody_map_slots b hc).mp hB').2
    exact ⟨bodySem_p_congr hc (reqPresentB_of_AdmABody hc hZ') (reqPresentB_of_AdmABody hc hA')
        (fun k hk => (hP k _ (hsa ⟨k, hk⟩) (hsb ⟨k, hk⟩)).1),
      bodySem_p_congr hc (reqPresentB_of_AdmABody hc hZ') (reqPresentB_of_AdmABody hc hB')
        (fun k hk => (hP k _ (hsa ⟨k, hk⟩) (hsb ⟨k, hk⟩)).2)⟩

/-- **A slot at the bottom empties the product, read side.** -/
theorem AdmABody_false_of_bottom {a b : Body S} {s : ObjectSlot S} {k : String}
    (hs : ∀ c, AdmAField s c = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c))
    (hr : ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (hbot : ObjectSlot.isBottom s = true) (c : Sem.A S) :
    (AdmABody a c && AdmABody b c) = false := by
  refine Bool.eq_false_iff.mpr (fun hab => ?_)
  rw [Bool.and_eq_true] at hab
  obtain ⟨hA, hB⟩ := hab
  cases hc : mapOutA c with
  | none => rw [AdmABody_of_none hc] at hA; exact absurd hA (by simp)
  | some m =>
    rw [AdmABody_map_slots _ hc] at hA hB
    have hreq := isReq_of_isBottom hbot
    rw [hr, Bool.or_eq_true] at hreq
    have hk : k ∈ m.keys := hreq.elim (hA.1 k) (hB.1 k)
    have h1 := hs (m.get ⟨k, hk⟩)
    rw [hA.2 ⟨k, hk⟩, hB.2 ⟨k, hk⟩] at h1
    cases s with
    | req t =>
      have ht : t = .never := by
        cases t <;> simp_all [ObjectSlot.isBottom, Term.isNever]
      subst ht; exact absurd h1 (by simp [AdmAField])
    | optional t => exact absurd hbot (by simp [ObjectSlot.isBottom])

/-- **One name of the met body, on the read side**: the slot reads exactly what both bodies'
    slots at that name read, is required where either is, and reads a stored attribute both
    admit as each of them does. -/
theorem objSlot_soundA {a b : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      (∀ c, AdmAField fm c = (AdmAField (a.at k) c && AdmAField fl c))
      ∧ (∀ c, AdmAField (a.at k) c = true → AdmAField fl c = true →
          (fieldSem fm).codec.p c = (fieldSem (a.at k)).codec.p c
            ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → AdmAAt a.block y z)
    {k : {k // k ∈ a.fields ∪ b.fields}} {s : ObjectSlot S} (h : objSlot a b g mw k = some s) :
    (∀ c, AdmAField s c = (AdmAField (a.slotAt k.1) c && AdmAField (b.slotAt k.1) c)) ∧
    ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k.1) || ObjectSlot.isReq (b.slotAt k.1)) ∧
    (∀ c, AdmAField (a.slotAt k.1) c = true → AdmAField (b.slotAt k.1) c = true →
      (fieldSem s).codec.p c = (fieldSem (a.slotAt k.1)).codec.p c
        ∧ (fieldSem s).codec.p c = (fieldSem (b.slotAt k.1)).codec.p c) := by
  unfold objSlot at h
  split at h
  next ha =>
    have hb : (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
        = b.slotAt k.1 := rfl
    rw [hb] at h
    rw [Body.slotAt_pos ha]
    exact ⟨(hg _ _ _ h).1, hgreq _ _ _ h, (hg _ _ _ h).2⟩
  next ha =>
    have hb := (Finset.mem_union.mp k.2).resolve_left ha
    rw [Body.slotAt_neg ha, Body.slotAt_pos hb]
    cases hf : b.at ⟨k.1, hb⟩ with
    | req y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun c => (hw _ _ hz).1 c, rfl, fun c h1 h2 => (hw _ _ hz).2 c h1 h2⟩
    | optional y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun c => (hw _ _ hz).1 c, rfl, fun c h1 h2 => (hw _ _ hz).2 c h1 h2⟩

/-- **Two objects meet pointwise, and the meet is exact on the read side.** -/
theorem admA_famObj [FormerAdmA S] {a : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      (∀ c, AdmAField fm c = (AdmAField (a.at k) c && AdmAField fl c))
      ∧ (∀ c, AdmAField (a.at k) c = true → AdmAField fl c = true →
          (fieldSem fm).codec.p c = (fieldSem (a.at k)).codec.p c
            ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → AdmAAt a.block y z) :
    AdmAFam (.object a) (famObj a g mw) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      unfold objObj at h
      split at h
      next hbot =>
        obtain ⟨k, hk⟩ := of_decide_eq_true hbot
        obtain ⟨s, hs, hsb⟩ := Option.map_eq_some_iff.mp hk
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hS, hR, -⟩ := objSlot_soundA hg hgreq hw hs
        have hf := AdmABody_false_of_bottom hS hR hsb
        refine ⟨fun c => (hf c).symm, fun c hA hB => ?_⟩
        have hA' : AdmABody a c = true := hA
        have hB' : AdmABody b c = true := hB
        have := hf c
        rw [hA', hB'] at this; exact absurd this (by simp)
      next =>
        split at h
        next => exact absurd h (by simp)
        next zb hwz =>
          split at h
          next hall =>
            simp only [Option.some.injEq] at h; subst h
            have hbw := hw _ _ hwz
            have hblk : ∀ k, k ∉ a.fields → k ∉ b.fields →
                (∀ c, AdmAField (.optional (if zb.isNever then .never else zb)) c
                  = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c)) ∧
                ObjectSlot.isReq (.optional (if zb.isNever then .never else zb))
                  = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)) ∧
                (∀ c, AdmAField (a.slotAt k) c = true → AdmAField (b.slotAt k) c = true →
                  (fieldSem (.optional (if zb.isNever then .never else zb))).codec.p c
                    = (fieldSem (a.slotAt k)).codec.p c
                  ∧ (fieldSem (.optional (if zb.isNever then .never else zb))).codec.p c
                    = (fieldSem (b.slotAt k)).codec.p c) := by
              intro k ha hb
              rw [Body.slotAt_neg ha, Body.slotAt_neg hb]
              cases hn : zb.isNever
              · exact ⟨fun c => hbw.1 c, rfl, fun c h1 h2 => hbw.2 c h1 h2⟩
              · rw [if_pos rfl]
                have hz := eq_never_of_isNever hn
                subst hz
                exact ⟨fun c => hbw.1 c, rfl, fun c h1 h2 => hbw.2 c h1 h2⟩
            have hall' := of_decide_eq_true hall
            refine AdmA_object_of_slots (fun k c => ?_) (fun k => ?_) (fun k c => ?_)
            · exact objObj_slots (P := fun k s => AdmAField s c
                  = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c)) hall'
                (fun k' s hs => (objSlot_soundA hg hgreq hw hs).1 c)
                (fun k' ha hb => (hblk k' ha hb).1 c) k
            · exact objObj_slots (P := fun k s => ObjectSlot.isReq s
                  = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k))) hall'
                (fun k' s hs => (objSlot_soundA hg hgreq hw hs).2.1)
                (fun k' ha hb => (hblk k' ha hb).2.1) k
            · exact objObj_slots (P := fun k s => AdmAField (a.slotAt k) c = true →
                  AdmAField (b.slotAt k) c = true →
                  (fieldSem s).codec.p c = (fieldSem (a.slotAt k)).codec.p c
                    ∧ (fieldSem s).codec.p c = (fieldSem (b.slotAt k)).codec.p c) hall'
                (fun k' s hs => (objSlot_soundA hg hgreq hw hs).2.2 c)
                (fun k' ha hb => (hblk k' ha hb).2.2 c) k
          next => exact absurd h (by simp)
  case opaq => simp [famObj] at h
  all_goals fam_bottomA famObj

/-! ### The outer theorem -/

mutual
/-- **The read side's homomorphism and its reading agreement, together.** Both halves are
    proved at once because a refinement row needs the agreement against whichever factor the
    wrapper sits on. -/
theorem AdmA_meet_both [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] : ∀ (x y : Term S) z, Term.meet x y = some z → AdmAAt x y z
  | .never, _, _, h => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact ⟨fun a => rfl, fun a ha _ => absurd ha (by simp [AdmA])⟩
  | .held _ _ _ _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .var _, _, _, h => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact ⟨fun a => by simp [AdmA], fun a ha _ => absurd ha (by simp [AdmA])⟩
  | .mu _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .refine x p, y, _, h => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨ih1, ih2⟩ := AdmA_meet_both x _ w hw
          exact refine_row_l ih1 ih2
        · exact absurd h (by simp)
  | .union os, y, _, h => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
      | _ =>
        obtain ⟨zs, hF, rfl⟩ := meet_union_of h (by simp)
        have hB := admA_meetL os _ zs hF
        refine ⟨fun a => ?_, fun a ha hb => ?_⟩
        · exact union_meet_freeA a (List.Forall₂.imp (fun _ _ hh => hh.1) hB)
        · obtain ⟨t, hft⟩ := find?_of_AdmA_union ha
          have hta : AdmA t a = true := List.find?_some (p := fun u => AdmA u a) hft
          obtain ⟨w, hfw, hwA, hwP⟩ :=
            find?_forall₂ (q := fun u => AdmA u a) (fun _ _ hh => by rw [hh.1 a, hb, Bool.and_true])
              hB hft
          rw [ofOptions_p_find, find?_filter_of (fun w hw => by rw [not_isNever_of_admA hw]; rfl),
            hfw, union_p_find, hft]
          exact hwP a hta hb
  | .prim g, y, z, h => admA_meetSRight (admA_famPrim g) y z h
  | .set a, y, z, h => admA_meetSRight (admA_famSet a (fun u w hw => AdmA_meet_both a u w hw)) y z h
  | .opaq, y, z, h => admA_meetSRight (admA_famOpaq) y z h
  | .list pre sp suf, y, z, h => by
      cases sp with
      | none =>
          exact admA_meetSRight (admA_famList (pre := pre) (sp := none) (suf := suf)
            (admA_meetSTs pre) (Or.inl ⟨rfl, rfl⟩) (admA_meetSTs suf)) y z h
      | some t =>
          exact admA_meetSRight (admA_famList (pre := pre) (sp := some t) (suf := suf)
            (admA_meetSTs pre)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => AdmA_meet_both t u w hw⟩)
            (admA_meetSTs suf)) y z h
  | .object (.mk fs f none), y, z, h =>
      admA_meetSRight (admA_famObj (a := .mk fs f none)
        (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun _ _ hz => by
          simp only [Option.some.injEq] at hz; subst hz
          exact ⟨fun _ => rfl, fun _ ha _ => absurd ha (by simp [Body.block])⟩)) y z h
  | .object (.mk fs f (some t)), y, z, h =>
      admA_meetSRight (admA_famObj (a := .mk fs f (some t))
        (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun u w hw => AdmA_meet_both t u w hw)) y z h
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem admA_meetL [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] : ∀ (os : List (Term S)) (y : Term S) (zs : List (Term S)),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w =>
      (∀ b, AdmA w b = (AdmA t b && AdmA y b)) ∧
      (∀ b, AdmA t b = true → AdmA y b = true →
        (denote w).p b = (denote t).p b ∧ (denote w).p b = (denote y).p b)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht => exact .cons (AdmA_meet_both t y _ hh) (admA_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem admA_meetSTs [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] : ∀ ts : List (Term S), List.Forall₂ AdmASound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => AdmA_meet_both t u w hw) (admA_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name read what both read, and read it to the same value. -/
theorem admA_Field_meet [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] : ∀ (f fl : ObjectSlot S) (fm : ObjectSlot S), ObjectSlot.meet f fl = some fm →
    (∀ c, AdmAField fm c = (AdmAField f c && AdmAField fl c))
    ∧ (∀ c, AdmAField f c = true → AdmAField fl c = true →
        (fieldSem fm).codec.p c = (fieldSem f).codec.p c
          ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c)
  | .req x, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .req x, .optional y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, .optional y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
termination_by structural f => f
end

/-- **`AdmA` is a homomorphism from the meet to conjunction.** Where two terms have a meet, the
    attributes it reads are exactly the attributes both read. -/
theorem AdmA_meet [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] {x y z : Term S} (h : Term.meet x y = some z) (a : Sem.A S) :
    AdmA z a = (AdmA x a && AdmA y a) :=
  (AdmA_meet_both x y z h).1 a

/-- **…and it reads them to the same value.** The read agreement is proved with the homomorphism
    and not after it: `AdmA (.refine t p) a` asks the predicate of what `t` decodes `a` to. -/
theorem denote_meet_p [Leaf S] [LeafAdm S] [LeafAdmA S] [FormerAdmA S] {x y z : Term S} (h : Term.meet x y = some z) {a : Sem.A S}
    (hx : AdmA x a = true) (hy : AdmA y a = true) :
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a :=
  (AdmA_meet_both x y z h).2 a hx hy

end

end Calculus.Alg
