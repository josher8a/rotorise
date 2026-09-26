import Calculus.Lang.MeetRows
import Calculus.Lang.ExactV
import Calculus.Lang.Shapes

/-!
# The meet on the write side, over a universe signature

`Alg.Adm_meet` states that `Adm` is a homomorphism from the meet to conjunction: where two terms
have a meet `z`, `z` admits exactly the values that both terms admit. The proof recurses on the
left operand, as the meet does, and every row is structure except the leaves.

A universe supplies the laws in two classes. `FormerAdm` holds the set laws: the set former
carries an element meet to a set meet. `LeafAdm` holds the laws of the leaf meet: each leaf answer
is exact. Both classes are outside `Sem` and outside `Leaf`, because only the theorems of the meet
read the laws. Two formers in different classes share no value, and that fact is a theorem of
the shape classes (`Shapes`).
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

/-! ## The rows that the families read -/

/-- The rows of a term list are that list mapped, so `rowOfG_map` carries a row of terms
    onto the row of rows the admission reads. -/
theorem AdmList_eq_map (ts : List (Term S)) : AdmList ts ρ = ts.map (Adm · ρ) :=
  AdmList_eq ρ ts

/-- …and the same for the spread. -/
theorem AdmOptT_eq_map (sp : Option (Term S)) : AdmOptT sp ρ = sp.map (Adm · ρ) := by
  cases sp <;> rfl

/-- **The suffix row meets position by position**, which is `alignP_meet_zip` for the half
    that carries no spread. Stated over terms, because the three rows the `list` meet
    compares are rows of terms. -/
theorem zipP_meet {r₁ r₂ rz : List (Term S)} (hlen : r₁.length = r₂.length)
    (hF : List.Forall₂
      (fun (pq : Term S × Term S) w => ∀ u, Adm w ρ'' u = (Adm pq.1 ρ u && Adm pq.2 ρ' u))
      (r₁.zip r₂) rz) :
    ∀ ws, zipP (AdmList rz ρ'') ws = (zipP (AdmList r₁ ρ) ws && zipP (AdmList r₂ ρ') ws) := by
  intro ws
  induction ws generalizing r₁ r₂ rz with
  | nil =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipP, AdmList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons _ _ => simp [zipP, AdmList]
  | cons w ws ihw =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipP, AdmList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons hr hrest =>
                  simp only [AdmList, zipP, hr,
                    ihw (by simpa using hlen) hrest]
                  simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- A declared position that holds nothing empties the tuple: every list the tuple admits fills
    each declared position. -/
theorem alignP_never_false : ∀ {ts : List (Term S)} {tail : Option (Term S)} {ws : List S.V},
    ts.any Term.isNever = true → alignP (AdmList ts ρ) (AdmOptT tail ρ) ws = false := by
  intro ts
  induction ts with
  | nil => intro _ _ h; simp at h
  | cons t ts' ih =>
    intro tail ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmList, alignP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht, show Adm .never ρ _ = false from rfl, Bool.false_and]
      · rw [ih (tail := tail) (ws := ws') hrest, Bool.and_false]

/-- A declared SUFFIX position that holds nothing empties the list, for the same reason:
    every value the list admits fills each suffix position too. -/
theorem zipP_never_false : ∀ {suf : List (Term S)} {ws : List S.V},
    suf.any Term.isNever = true → zipP (AdmList suf ρ) ws = false := by
  intro suf
  induction suf with
  | nil => intro _ h; simp at h
  | cons t ts' ih =>
    intro ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmList, zipP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht,
          show Adm .never ρ w = false from rfl, Bool.false_and]
      · rw [ih (ws := ws') hrest, Bool.and_false]

/-- Normalising a list keeps what it admits. -/
theorem Adm_listOf (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S)) (v : S.V) :
    Adm (Term.listOf pre sp suf) ρ v = Adm (.list pre sp suf) ρ v := by
  unfold Term.listOf
  split
  next hany =>
    rw [Adm_never]
    cases hv : listOut v with
    | none => rw [Adm_list_of_none hv]
    | some ws =>
      rw [Adm_list_of_out hv]
      refine Eq.symm ?_
      simp only [alignPL]
      rcases Bool.or_eq_true .. |>.mp hany with hp | hs
      · rw [alignP_never_false hp, Bool.false_and]
      · rw [zipP_never_false hs, Bool.and_false]
  next => rfl

/-- **The `list` meet's whole admission obligation, read off the three rows.** A `list`
    admits an array exactly where its row at that length does, so an answer whose row exists
    exactly where both factors' rows exist, and is their pointwise meet there, admits exactly
    what both factors admit. Each of `listMeetRow`'s three branches supplies these two facts
    and nothing else. -/
theorem Adm_list_rows {p₁ s₁ p₂ s₂ pz sz : List (Term S)} {q₁ q₂ qz : Option (Term S)}
    (hsome : ∀ n, (rowOfG pz qz sz n).isSome
      = ((rowOfG p₁ q₁ s₁ n).isSome && (rowOfG p₂ q₂ s₂ n).isSome))
    (hrel : ∀ n r₁ r₂ rz, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      rowOfG pz qz sz n = some rz →
      r₁.length = r₂.length ∧
        List.Forall₂
          (fun (pq : Term S × Term S) w => ∀ u, Adm w ρ'' u = (Adm pq.1 ρ u && Adm pq.2 ρ' u))
          (r₁.zip r₂) rz)
    (v : S.V) :
    Adm (.list pz qz sz) ρ'' v = (Adm (.list p₁ q₁ s₁) ρ v && Adm (.list p₂ q₂ s₂) ρ' v) := by
  cases hv : listOut v with
  | none => simp [Adm_list_of_none hv]
  | some ws =>
      have hb := hsome ws.length
      simp only [Adm_list_of_out hv, AdmList_eq_map, AdmOptT_eq_map, alignPL_eq_rowOfG, rowOfG_map]
      cases h₁ : rowOfG p₁ q₁ s₁ ws.length with
      | none =>
          rw [h₁] at hb
          simp only [Option.isSome_none, Bool.false_and] at hb
          cases hz : rowOfG pz qz sz ws.length with
          | none => simp
          | some rz => rw [hz] at hb; simp at hb
      | some r₁ =>
          cases h₂ : rowOfG p₂ q₂ s₂ ws.length with
          | none =>
              rw [h₁, h₂] at hb
              simp only [Option.isSome_some, Option.isSome_none, Bool.and_false] at hb
              cases hz : rowOfG pz qz sz ws.length with
              | none => simp
              | some rz => rw [hz] at hb; simp at hb
          | some r₂ =>
              cases hz : rowOfG pz qz sz ws.length with
              | none => rw [h₁, h₂, hz] at hb; simp at hb
              | some rz =>
                  obtain ⟨hlen, hF⟩ := hrel _ _ _ _ h₁ h₂ hz
                  simp only [Option.map_some]
                  simpa only [← AdmList_eq_map] using zipP_meet hlen hF ws

/-- **Two `list` shapes with no common length share no value.** The bottom is the right
    answer exactly there, and `listMeetRow` reaches it from both flattening branches. -/
theorem Adm_list_disjoint {p₁ s₁ p₂ s₂ : List (Term S)} {q₁ q₂ : Option (Term S)}
    (h : ∀ n, rowOfG p₁ q₁ s₁ n = none ∨ rowOfG p₂ q₂ s₂ n = none) (v : S.V) :
    (Adm (.list p₁ q₁ s₁) ρ v && Adm (.list p₂ q₂ s₂) ρ' v) = false := by
  cases hv : listOut v with
  | none => simp [Adm_list_of_none hv]
  | some ws =>
      simp only [Adm_list_of_out hv, AdmList_eq_map, AdmOptT_eq_map, alignPL_eq_rowOfG,
        rowOfG_map]
      rcases h ws.length with hn | hn <;> simp [hn]

/-! ### The count, and what the meet does to it

These are what let the coproduct row of the meet stand without a certificate. What the row needs is
that the meet scales the number of admitting options by whether the partner admits, and that is a
fact about counting rather than about separation. -/

/-- The options that survive are the ones that admit; the bottoms admit nothing. -/
theorem AdmAny_filter_never : ∀ (ts : List (Term S)) (v : S.V),
    AdmAny (ts.filter (fun z => !z.isNever)) ρ v = AdmAny ts ρ v
  | [], _ => rfl
  | t :: ts, v => by
      cases ht : t.isNever with
      | true =>
        have htn : t = Term.never := eq_never_of_isNever ht
        subst htn
        rw [List.filter_cons, if_neg (by simp [Term.isNever]), AdmAny_cons,
          AdmAny_filter_never ts v]
        rfl
      | false =>
        rw [List.filter_cons, if_pos (by simp [ht]), AdmAny_cons, AdmAny_cons,
          AdmAny_filter_never ts v]

/-- The join over the met options is the join over the options, met with the partner. -/
theorem AdmAny_meet {y : Term S} (v : S.V) : ∀ {os zs : List (Term S)},
    List.Forall₂ (fun t w => ∀ u, Adm w ρ'' u = (Adm t ρ u && Adm y ρ' u)) os zs →
    AdmAny zs ρ'' v = (AdmAny os ρ v && Adm y ρ' v) := by
  intro os zs h
  induction h with
  | nil => simp
  | cons hh _ ihx =>
    rw [AdmAny_cons, AdmAny_cons, hh v, ihx]
    cases Adm _ ρ v <;> cases Adm y ρ' v <;> simp

/-- **`ofOptions` admits what its options admit**, and no certificate is spent. -/
theorem Adm_ofOptions (ts : List (Term S)) (v : S.V) :
    Adm (Term.ofOptions ts) ρ v = AdmAny ts ρ v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAny_cons, AdmAny_nil, Bool.or_false]
  | _ :: _ :: _ => rfl

/-- **The coproduct row of the meet needs no certificate.** The bottoms admit nothing, and `&&`
    distributes over the options' disjunction. -/
theorem union_meet_free {os zs : List (Term S)} {y : Term S} (v : S.V)
    (hR : List.Forall₂ (fun t w => ∀ u, Adm w ρ'' u = (Adm t ρ u && Adm y ρ' u)) os zs) :
    Adm (Term.ofOptions (zs.filter (fun z => !z.isNever))) ρ'' v
      = (Adm (.union os) ρ v && Adm y ρ' v) := by
  rw [Adm_ofOptions, AdmAny_filter_never, AdmAny_meet v hR, Adm_union]


-- the object rows put the whole field table to `decide` under a binder, which is where the
-- default budget goes

/-! ## `Adm` is a homomorphism from the meet to conjunction, structurally

The definition recurses on the left operand, so the theorem does too: one shared lemma for every
row that reads the right operand alone, one flat lemma per left constructor, and an outer
recursion that feeds the induction hypothesis at the subterm into the two. -/

/-- `f` answers the meet with one term fixed on the left, at EVERY right operand. The container
    families need this of the call they carry, because they apply it to a subterm of any shape. -/
def AdmSound (ρ ρ' ρ'' : List S.C) (x : Term S) (f : Term S → Option (Term S)) : Prop :=
  ∀ y z, f y = some z → ∀ v, Adm z ρ'' v = (Adm x ρ v && Adm y ρ' v)

/-- `fam` answers the meet with one term fixed on the left, over the operands it is handed. -/
def AdmFam (ρ ρ' ρ'' : List S.C) (x : Term S) (fam : Term S → Option (Term S)) : Prop :=
  ∀ y z, Delegated y → fam y = some z → ∀ v, Adm z ρ'' v = (Adm x ρ v && Adm y ρ' v)

/-- Two terms that share no value meet at the bottom. -/
theorem bottom_of_and_false {x y : Term S} {v : S.V} (h : (Adm x ρ v && Adm y ρ' v) = false) :
    Adm .never ρ'' v = (Adm x ρ v && Adm y ρ' v) := by rw [h, Adm_never]

/-- …in either order. -/
theorem bottom_of_and_false' {x y : Term S} {v : S.V} (h : (Adm y ρ' v && Adm x ρ v) = false) :
    Adm .never ρ'' v = (Adm x ρ v && Adm y ρ' v) := by rw [Bool.and_comm, h, Adm_never]

/-- Two rows of terms, the left as partially applied meets, met position by position. -/
theorem zipF_lift_terms :
    ∀ {ts us : List (Term S)} {fs : List (Term S → Option (Term S))} {vs : List (Term S)},
      List.Forall₂ (AdmSound ρ ρ' ρ'') ts fs →
      List.Forall₂ (fun (p : (Term S → Option (Term S)) × Term S) v => p.1 p.2 = some v)
        (fs.zip us) vs →
      List.Forall₂
        (fun (pq : Term S × Term S) w => ∀ u, Adm w ρ'' u = (Adm pq.1 ρ u && Adm pq.2 ρ' u))
        (ts.zip us) vs := by
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
              | cons hh ht =>
                  exact .cons (fun w => hsound u _ hh w) (ihs hfs' ht)

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

/-- **Two bodies conjoined at every name are conjoined as bodies.** -/
theorem AdmBody_of_slots {a b z : Body S}
    (hS : ∀ k w, AdmField (z.slotAt k) ρ'' w
      = (AdmField (a.slotAt k) ρ w && AdmField (b.slotAt k) ρ' w))
    (hR : ∀ k, ObjectSlot.isReq (z.slotAt k)
      = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (v : S.V) : AdmBody z ρ'' v = (AdmBody a ρ v && AdmBody b ρ' v) := by
  cases hv : mapOut v with
  | none => rw [AdmBody_of_none hv, AdmBody_of_none hv, AdmBody_of_none hv]; rfl
  | some m =>
    rw [Bool.eq_iff_iff, Bool.and_eq_true, AdmBody_map_slots _ hv, AdmBody_map_slots _ hv,
      AdmBody_map_slots _ hv]
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

/-- **A slot at the bottom empties the product**, at a name either body requires. -/
theorem AdmBody_false_of_bottom {a b : Body S} {s : ObjectSlot S} {k : String}
    (hs : ∀ w, AdmField s ρ'' w = (AdmField (a.slotAt k) ρ w && AdmField (b.slotAt k) ρ' w))
    (hr : ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (hbot : ObjectSlot.isBottom s = true) (v : S.V) :
    (AdmBody a ρ v && AdmBody b ρ' v) = false := by
  refine Bool.eq_false_iff.mpr (fun hab => ?_)
  rw [Bool.and_eq_true] at hab
  obtain ⟨hA, hB⟩ := hab
  cases hv : mapOut v with
  | none => rw [AdmBody_of_none hv] at hA; exact absurd hA (by simp)
  | some m =>
    rw [AdmBody_map_slots _ hv] at hA hB
    have hreq := isReq_of_isBottom hbot
    rw [hr, Bool.or_eq_true] at hreq
    have hk : k ∈ m.keys := hreq.elim (hA.1 k) (hB.1 k)
    have h1 := hs (m.get ⟨k, hk⟩)
    rw [hA.2 ⟨k, hk⟩, hB.2 ⟨k, hk⟩] at h1
    cases s with
    | req t =>
      have ht : t = .never := by
        cases t <;> simp_all [ObjectSlot.isBottom, Term.isNever]
      subst ht; exact absurd h1 (by simp [AdmField])
    | optional t => exact absurd hbot (by simp [ObjectSlot.isBottom])

/-- **One name of the met body, on the write side**: the slot the meet gives a name admits
    exactly what both bodies' slots at that name admit, and is required where either is. -/
theorem objSlot_sound {a b : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      ∀ w, AdmField fm ρ'' w = (AdmField (a.at k) ρ w && AdmField fl ρ' w))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → ∀ w, Adm z ρ'' w = (Adm a.block ρ w && Adm y ρ' w))
    {k : {k // k ∈ a.fields ∪ b.fields}} {s : ObjectSlot S} (h : objSlot a b g mw k = some s) :
    (∀ w, AdmField s ρ'' w = (AdmField (a.slotAt k.1) ρ w && AdmField (b.slotAt k.1) ρ' w)) ∧
    ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k.1) || ObjectSlot.isReq (b.slotAt k.1)) := by
  unfold objSlot at h
  split at h
  next ha =>
    have hb : (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
        = b.slotAt k.1 := rfl
    rw [hb] at h
    rw [Body.slotAt_pos ha]
    exact ⟨hg _ _ _ h, hgreq _ _ _ h⟩
  next ha =>
    have hb := (Finset.mem_union.mp k.2).resolve_left ha
    rw [Body.slotAt_neg ha, Body.slotAt_pos hb]
    cases hf : b.at ⟨k.1, hb⟩ with
    | req y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun w => hw _ _ hz w, rfl⟩
    | optional y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun w => hw _ _ hz w, rfl⟩

end

/-! ## The laws, on the write side -/

/-- **The write-side laws of the formers.** The set laws carry an element meet to a set meet. The
    catch-all rows of the families read the disjointness of the former classes (`Shapes`). -/
class FormerAdm (S : Syn) [Sem S] [PrimAdm S] : Prop where
  /-- Over held-free terms, the set of an element meet is the meet of the sets. -/
  set_meet : ∀ a y z : Term S, HF a → HF y → HF z →
    (∀ u, Adm z [] u = (Adm a [] u && Adm y [] u)) →
    ∀ v, Adm (.set z) [] v = (Adm (.set a) [] v && Adm (.set y) [] v)
  /-- Two sets whose elements share no value share no set. -/
  set_never : ∀ a y : Term S, (∀ u, (Adm a [] u && Adm y [] u) = false) →
    ∀ v, (Adm (.set a) [] v && Adm (.set y) [] v) = false

/-- **The write-side laws of a leaf meet**: each leaf answer is exact. A primitive and the top
    read no variable, so the laws are stated at the closed environment. -/
class LeafAdm (S : Syn) [Sem S] [PrimAdm S] [Leaf S] : Prop where
  /-- Two primitives met at a primitive admit what both admit. -/
  prim_some : ∀ g g' h : S.Ground, Leaf.prim g g' = some h →
    ∀ v, Adm (.prim h : Term S) [] v = (Adm (.prim g : Term S) [] v && Adm (.prim g') [] v)
  /-- Two primitives met at the bottom share no value. -/
  prim_none : ∀ g g' : S.Ground, Leaf.prim g g' = none →
    ∀ v, (Adm (.prim g : Term S) [] v && Adm (.prim g') [] v) = false
  /-- A primitive that meets the top at itself is inside the top. -/
  prim_top : ∀ g : S.Ground, Leaf.primTop g = true →
    ∀ v, Adm (.prim g : Term S) [] v = true → Adm (.opaq : Term S) [] v = true
  /-- Two predicates met at a predicate hold where both hold. -/
  pmeet_some : ∀ q p r : S.Pred, Leaf.pmeet q p = some (some r) →
    ∀ v, Sem.eval r v = (Sem.eval q v && Sem.eval p v)
  /-- Two predicates met at the empty predicate hold together nowhere. -/
  pmeet_none : ∀ q p : S.Pred, Leaf.pmeet q p = some none →
    ∀ v, (Sem.eval q v && Sem.eval p v) = false

/-- The catch-all of every family: two formers in different value slots meet at the bottom. -/
local macro "fam_bottom" fam:ident : tactic => `(tactic|
  (simp only [$fam:ident, Option.some.injEq] at *
   subst_vars
   first
     | exact bottom_of_and_false (Shapes.prim_set ..)
     | exact bottom_of_and_false' (Shapes.prim_set ..)
     | exact bottom_of_and_false (Shapes.prim_list ..)
     | exact bottom_of_and_false' (Shapes.prim_list ..)
     | exact bottom_of_and_false (Shapes.prim_obj ..)
     | exact bottom_of_and_false' (Shapes.prim_obj ..)
     | exact bottom_of_and_false (Shapes.set_list ..)
     | exact bottom_of_and_false' (Shapes.set_list ..)
     | exact bottom_of_and_false (Shapes.set_obj ..)
     | exact bottom_of_and_false' (Shapes.set_obj ..)
     | exact bottom_of_and_false (Shapes.list_obj ..)
     | exact bottom_of_and_false' (Shapes.list_obj ..)))

-- the object rows put the whole field table to `decide` under a binder
set_option maxHeartbeats 1000000

noncomputable section

/-! ### The container families -/

/-- **The one positional container's family.** Two `list` shapes meet through their rows, and
    `Adm_list_rows` states the whole obligation over those rows. -/
theorem Adm_famList [Shapes S] {pre suf : List (Term S)} {sp : Option (Term S)}
    {fpre fsuf : List (Term S → Option (Term S))} {fsp : Option (Term S → Option (Term S))}
    (hp : List.Forall₂ (AdmSound ρ ρ' ρ'') pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ AdmSound ρ ρ' ρ'' t f)
    (hf : List.Forall₂ (AdmSound ρ ρ' ρ'') suf fsuf) :
    AdmFam ρ ρ' ρ'' (.list pre sp suf) (famList fpre fsp fsuf) := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case list pre₂ sp₂ suf₂ =>
      simp only [famList] at h
      rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, hsound⟩
      · -- The left states a fixed arity, so the answer is that one row, flattened.
        simp only [listMeetRow] at h
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
              cases hd : decide (n = pre.length + suf.length) with
              | true => simp only [decide_eq_true_eq] at hd; subst hd; exact Or.inr hR
              | false =>
                  simp only [decide_eq_false_iff_not] at hd
                  exact Or.inl (by rw [rowOfG_none_eq, if_neg hd])
            exact (Adm_list_disjoint hdis v).symm
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
            have hrel₀ := zipF_lift_terms (forall₂_append hp hf) hFz
            rw [Adm_listOf]
            refine Adm_list_rows (p₁ := pre) (q₁ := none) (s₁ := suf) ?_ ?_ v
            · intro n
              simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, hrowlen]
              cases hd : decide (n = pre.length + suf.length) with
              | true =>
                  simp only [decide_eq_true_eq] at hd
                  subst hd
                  rw [if_pos rfl, if_pos rfl, hR]
                  simp
              | false =>
                  simp only [decide_eq_false_iff_not] at hd
                  rw [if_neg hd, if_neg hd]
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
            -- The right states a fixed arity: the answer flattens to that length.
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
                  cases hd : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd
                      subst hd
                      exact Or.inl (by rw [rowOfG_some_eq, if_pos (by omega)])
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd
                      exact Or.inr (by rw [rowOfG_none_eq, if_neg hd])
                exact (Adm_list_disjoint hdis v).symm
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
                have hrel₀ := zipF_lift_terms htsF hFz
                rw [Adm_listOf]
                refine Adm_list_rows (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_ v
                · intro n
                  simp only [rowOfG_none_eq, rowOfG_some_eq, List.length_nil, Nat.add_zero,
                    hrowlen]
                  cases hd : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd
                      subst hd
                      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
                      simp
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd
                      rw [if_neg hd, if_neg hd]
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
            -- Both sides spread. The answer is the row at one length, re-spread at every
            -- other, and `dominates` is what makes the answer refuse exactly where a
            -- factor does.
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
                    have hrel₀ := zipF_lift_terms htsF hFz
                    have hspz : ∀ u, Adm spz ρ'' u = (Adm t ρ u && Adm c ρ' u) :=
                      hsound c spz hfc
                    have hdm := dominates_max hdom
                    rw [Adm_listOf]
                    refine Adm_list_rows (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_ v
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
  all_goals fam_bottom famList

/-- **Two objects meet pointwise, and the meet is exact on the write side.** -/
theorem Adm_famObj [Shapes S] {a : Body S} {g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S)}
    {mw : Term S → Option (Term S)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      ∀ w, AdmField fm ρ'' w = (AdmField (a.at k) ρ w && AdmField fl ρ' w))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot S), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → ∀ w, Adm z ρ'' w = (Adm a.block ρ w && Adm y ρ' w)) :
    AdmFam ρ ρ' ρ'' (.object a) (famObj a g mw) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      unfold objObj at h
      split at h
      next hbot =>
        obtain ⟨k, hk⟩ := of_decide_eq_true hbot
        obtain ⟨s, hs, hsb⟩ := Option.map_eq_some_iff.mp hk
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hS, hR⟩ := objSlot_sound hg hgreq hw hs
        exact (AdmBody_false_of_bottom hS hR hsb v).symm
      next =>
        split at h
        next => exact absurd h (by simp)
        next zb hwz =>
          split at h
          next hall =>
            simp only [Option.some.injEq] at h; subst h
            have hblkA : ∀ w, Adm (if zb.isNever then .never else zb) ρ'' w
                = (Adm a.block ρ w && Adm b.block ρ' w) := by
              intro w
              cases hn : zb.isNever
              · exact hw _ _ hwz w
              · rw [if_pos rfl, ← hw _ _ hwz w, eq_never_of_isNever hn]
            refine AdmBody_of_slots (fun k w => ?_) (fun k => ?_) v
            · exact objObj_slots (P := fun k s => AdmField s ρ'' w
                  = (AdmField (a.slotAt k) ρ w && AdmField (b.slotAt k) ρ' w))
                (of_decide_eq_true hall) (fun k' s hs => (objSlot_sound hg hgreq hw hs).1 w)
                (fun k' ha hb => by
                  rw [Body.slotAt_neg ha, Body.slotAt_neg hb]; exact hblkA w) k
            · exact objObj_slots (P := fun k s => ObjectSlot.isReq s
                  = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
                (of_decide_eq_true hall) (fun k' s hs => (objSlot_sound hg hgreq hw hs).2)
                (fun k' ha hb => by rw [Body.slotAt_neg ha, Body.slotAt_neg hb]; rfl) k
          next => exact absurd h (by simp)
  case opaq => simp [famObj] at h
  all_goals fam_bottom famObj

/-- **Two sets meet at their elements**, and a set is at the bottom beside every other former. -/
theorem Adm_famSet [FormerAdm S] [Shapes S] (a : Term S) {mt : Term S → Option (Term S)}
    (ih : AdmSound ρ ρ' ρ'' a mt) : AdmFam ρ ρ' ρ'' (.set a) (famSet a mt) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case set y =>
      simp only [famSet] at h
      split at h
      · exact nomatch h
      next hv =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hv
      -- the elements read no variable, so the closed laws of the universe apply
      have ha := Adm_closed a hv.1 ρ []
      have hy := Adm_closed y hv.2 ρ' []
      have hsa := Adm_closed (.set a) hv.1 ρ []
      have hsy := Adm_closed (.set y) hv.2 ρ' []
      split at h
      · next z' hz =>
        have hm := ih y z' hz
        split at h
        · next hn =>
          simp only [Option.some.injEq] at h; subst h
          have hz' : z' = .never := eq_never_of_isNever hn
          subst hz'
          rw [hsa, hsy]
          exact bottom_of_and_false
            (FormerAdm.set_never a y (fun u => by rw [← ha, ← hy, ← hm u, Adm_never]) v)
        · next hn =>
          split at h
          · exact nomatch h
          · next hh =>
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hh
            simp only [Option.some.injEq] at h; subst h
            rw [Adm_closed (.set z') hh.2 ρ'' [], hsa, hsy]
            exact FormerAdm.set_meet a y z' (HF_of_hasHeld a hh.1.1.1) (HF_of_hasHeld y hh.1.1.2)
              (HF_of_hasHeld z' hh.1.2)
              (fun u => by rw [← Adm_closed z' hh.2 ρ'' [], ← ha, ← hy]; exact hm u) v
      · exact nomatch h
  case opaq => simp [famSet] at h
  all_goals fam_bottom famSet

/-! ### The leaf rows -/

/-- …and normalising a refinement keeps what it admits. -/
theorem Adm_refineOf [Leaf S] [LeafAdm S] (z : Term S) (p : S.Pred) (v : S.V) :
    Adm (Term.refineOf z p) ρ v = Adm (.refine z p) ρ v := by
  cases z <;>
    first
      | rfl
      | (simp only [Term.refineOf]
         rename_i z' q
         split
         · rename_i r hr
           show (Adm z' ρ v && Sem.eval r v) = ((Adm z' ρ v && Sem.eval q v) && Sem.eval p v)
           rw [LeafAdm.pmeet_some q p r hr v, Bool.and_assoc]
         · rename_i hr
           show Adm .never ρ v = ((Adm z' ρ v && Sem.eval q v) && Sem.eval p v)
           rw [Bool.and_assoc, LeafAdm.pmeet_none q p hr v, Bool.and_false, Adm_never]
         · rfl)

/-! ### The environments of a pairing, and the recursive rows -/

/-- **The environments agree with the pairing on the write side**: the binder of the answer that
    a pairing names writes where both binders it pairs write. -/
def PairedV (p : Pairing) (ρ ρ' ρ'' : List S.C) : Prop :=
  ∀ i j k, p i j = some k → ∀ v,
    ((envAt ρ'' k).e v).isSome = (((envAt ρ i).e v).isSome && ((envAt ρ' j).e v).isSome)

omit [PrimAdm S] in
/-- Two closed terms pair no binder, so every three environments agree with the pairing. -/
theorem PairedV.pair0 (ρ ρ' ρ'' : List S.C) : PairedV pair0 ρ ρ' ρ'' := fun _ _ _ h => nomatch h

omit [PrimAdm S] in
/-- An unfolding of the left operand binds a codec that pairs with nothing. -/
theorem PairedV.left {p : Pairing} (h : PairedV p ρ ρ' ρ'') (c : S.C) :
    PairedV (shiftL p) (c :: ρ) ρ' ρ'' := by
  intro i j k hp v
  match i, hp with
  | 0, hp => exact nomatch hp
  | i + 1, hp => exact h i j k hp v

omit [PrimAdm S] in
/-- An unfolding of the right operand binds a codec that pairs with nothing. -/
theorem PairedV.right {p : Pairing} (h : PairedV p ρ ρ' ρ'') (c : S.C) :
    PairedV (shiftR p) ρ (c :: ρ') ρ'' := by
  intro i j k hp v
  match i, j, hp with
  | _, 0, hp => exact nomatch hp
  | i, j + 1, hp => exact h i j k hp v

omit [PrimAdm S] in
/-- Under a `mu ∧ mu`, the two new binders pair at a codec that writes where both write. -/
theorem PairedV.mu {p : Pairing} (h : PairedV p ρ ρ' ρ'') {c c' c'' : S.C}
    (hc : ∀ v, (c''.e v).isSome = ((c.e v).isSome && (c'.e v).isSome)) :
    PairedV (pairMu p) (c :: ρ) (c' :: ρ') (c'' :: ρ'') := by
  intro i j k hp v
  match i, j, hp with
  | 0, 0, hp => cases hp; exact hc v
  | i + 1, j + 1, hp =>
    simp only [pairMu, Option.map_eq_some_iff] at hp
    obtain ⟨k', hk, rfl⟩ := hp
    exact h i j k' hk v
  | 0, _ + 1, hp => exact nomatch hp
  | _ + 1, 0, hp => exact nomatch hp

omit [PrimAdm S] in
/-- **The stage-wise meet, on the write side.** A body meet that meets the write domains carries
    the meet to every stage. No guard and no chain: each stage is the body over the stage below. -/
theorem stage_meetV {B B' B'' : S.C → S.C}
    (hB : ∀ c c' c'', (∀ v, (c''.e v).isSome = ((c.e v).isSome && (c'.e v).isSome)) →
      ∀ v, ((B'' c'').e v).isSome = (((B c).e v).isSome && ((B' c').e v).isSome)) :
    ∀ n v, ((muStage B'' n).e v).isSome
      = (((muStage B n).e v).isSome && ((muStage B' n).e v).isSome)
  | 0, _ => rfl
  | n + 1, v => hB _ _ _ (stage_meetV hB n) v

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

/-- A recursive term over the bottom admits nothing: every stage is the bottom. -/
theorem Adm_mu_never (ρ : List S.C) (v : S.V) : Adm (.mu (.never : Term S)) ρ v = false := by
  show ((muStage (fun c => denote (.never : Term S) (c :: ρ)) (Sem.dV v)).e v).isSome = false
  generalize Sem.dV v = n
  cases n <;> rfl

/-- **The `mu ∧ mu` row on the write side**: a body meet under every three environments that meet
    at the new binders is a meet of the two recursive terms. -/
theorem Adm_mu_meet {b b' w : Term S}
    (hB : ∀ c c' c'', (∀ v, (c''.e v).isSome = ((c.e v).isSome && (c'.e v).isSome)) →
      ∀ v, Adm w (c'' :: ρ'') v = (Adm b (c :: ρ) v && Adm b' (c' :: ρ') v)) (v : S.V) :
    Adm (.mu w) ρ'' v = (Adm (.mu b) ρ v && Adm (.mu b') ρ' v) :=
  stage_meetV (B := fun c => denote b (c :: ρ)) (B' := fun c => denote b' (c :: ρ'))
    (B'' := fun c => denote w (c :: ρ''))
    (fun c c' c'' hc u => by simpa only [Adm_eq_isSome] using hB c c' c'' hc u) (Sem.dV v) v

mutual
/-- Every row that reads the right operand alone is sound wherever the family is. A right
    recursive term unfolds at the stage below the value's depth. -/
theorem Adm_meetSRight [Leaf S] [LeafAdm S] {x : Term S}
    {fam : Pairing → Term S → Option (Term S)}
    (hf : ∀ q ρ' ρ'', PairedV q ρ ρ' ρ'' → AdmFam ρ ρ' ρ'' x (fam q)) :
    ∀ (y : Term S) (p : Pairing) (ρ' ρ'' : List S.C) z, PairedV p ρ ρ' ρ'' →
      meetSRight fam p y = some z → ∀ v, Adm z ρ'' v = (Adm x ρ v && Adm y ρ' v)
  | .never, _, _, _, _, _, h, _ => by
      simp only [meetSRight, Option.some.injEq] at h; subst h; simp [Adm]
  | .held _ _ _ _, _, _, _, _, _, h, _ => by simp [meetSRight] at h
  | .var _, _, _, _, _, _, h, _ => by simp [meetSRight] at h
  | .mu b, p, ρ', ρ'', _, hp, h, v => by
      simp only [meetSRight] at h
      rw [Adm_mu_unfold b ρ' v]
      exact Adm_meetSRight hf b (shiftR p) _ ρ'' _ (hp.right _) h v
  | .refine y q, p, ρ', ρ'', _, hp, h, v => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        have ihw := Adm_meetSRight hf y p ρ' ρ'' w hp hw v
        rw [Adm_refineOf]
        simp only [Adm, ihw]
        simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      · obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.mp h
        split at hz
        · next hn =>
            cases hz
            have ihw := Adm_meetSRight hf y p ρ' ρ'' w hp hw v
            rw [eq_never_of_isNever hn, Adm_never] at ihw
            have hr : Adm (.refine y q) ρ' v = (Adm y ρ' v && Sem.eval q v) := by simp [Adm]
            rw [Adm_never, hr, ← Bool.and_assoc, ← ihw, Bool.false_and]
        · exact nomatch hz
  | .union os, p, ρ', ρ'', _, hp, h, v => by
      obtain ⟨zs, hF, rfl⟩ := meetSRight_union h
      rw [Bool.and_comm]
      exact union_meet_free v (Adm_meetSRightL hf os p ρ' ρ'' _ hp hF)
  | .prim g, p, _, _, _, hp, h, v => hf p _ _ hp (.prim g) _ trivial h v
  | .set b, p, _, _, _, hp, h, v => hf p _ _ hp (.set b) _ trivial h v
  | .opaq, p, _, _, _, hp, h, v => hf p _ _ hp .opaq _ trivial h v
  | .list pr q s, p, _, _, _, hp, h, v => hf p _ _ hp (.list pr q s) _ trivial h v
  | .object b, p, _, _, _, hp, h, v => hf p _ _ hp (.object b) _ trivial h v
termination_by structural y => y

/-- The list companion: the union row's options, lifted pointwise. It recurses on the list and
    `Adm_meetSRight` on the term, as the definition's own pair does. -/
theorem Adm_meetSRightL [Leaf S] [LeafAdm S] {x : Term S}
    {fam : Pairing → Term S → Option (Term S)}
    (hf : ∀ q ρ' ρ'', PairedV q ρ ρ' ρ'' → AdmFam ρ ρ' ρ'' x (fam q)) :
    ∀ os (p : Pairing) (ρ' ρ'' : List S.C) zs, PairedV p ρ ρ' ρ'' →
      List.Forall₂ (fun t w => meetSRight fam p t = some w) os zs →
      List.Forall₂ (fun t w => ∀ u, Adm w ρ'' u = (Adm t ρ' u && Adm x ρ u)) os zs
  | [], _, _, _, _, _, h => by cases h; exact .nil
  | t :: ts, p, ρ', ρ'', _, hp, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun u => by rw [Adm_meetSRight hf t p ρ' ρ'' _ hp hh u, Bool.and_comm])
            (Adm_meetSRightL hf ts p ρ' ρ'' _ hp ht)
termination_by structural os => os
end

/-- **The one leaf family is exact wherever the leaf laws hold.** A primitive and the top read
    no variable, so each row is the closed one. -/
theorem Adm_famPrim [Leaf S] [LeafAdm S] [Shapes S] (g : S.Ground) :
    AdmFam ρ ρ' ρ'' (.prim g) (famPrim g) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case prim g' =>
      simp only [famPrim, Option.some.injEq] at h
      subst h
      cases hp : Leaf.prim g g' with
      | some k => exact LeafAdm.prim_some g g' k hp v
      | none => exact bottom_of_and_false (LeafAdm.prim_none g g' hp v)
  case opaq =>
      simp only [famPrim] at h
      cases ht : Leaf.primTop g with
      | false => simp [ht] at h
      | true =>
          simp only [ht, if_true, Option.some.injEq] at h
          subst h
          change Adm (.prim g) [] v = (Adm (.prim g) [] v && Adm .opaq [] v)
          cases hg : Adm (.prim g : Term S) [] v
          · simp
          · simp [LeafAdm.prim_top g ht v hg]
  all_goals fam_bottom famPrim

/-- The top meets itself, and a primitive where the leaf says so. -/
theorem Adm_famOpaq [Leaf S] [LeafAdm S] : AdmFam ρ ρ' ρ'' (.opaq : Term S) famOpaq := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case prim g =>
      simp only [famOpaq] at h
      cases ht : Leaf.primTop g with
      | false => simp [ht] at h
      | true =>
          simp only [ht, if_true, Option.some.injEq] at h
          subst h
          change Adm (.prim g) [] v = (Adm .opaq [] v && Adm (.prim g) [] v)
          cases hg : Adm (.prim g : Term S) [] v
          · simp
          · simp [LeafAdm.prim_top g ht v hg]
  case opaq =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      exact (Bool.and_self _).symm
  all_goals simp [famOpaq] at h

/-! ### The outer theorem -/

mutual
/-- **`Adm` is a homomorphism from the meet to conjunction.** Where two terms have a meet at a
    pairing, the values it admits are exactly the values both admit, under every three
    environments that agree with the pairing. -/
theorem Adm_meet [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (x y z : Term S), Term.meet p x y = some z →
      ∀ (ρ ρ' ρ'' : List S.C), PairedV p ρ ρ' ρ'' → ∀ v, Adm z ρ'' v = (Adm x ρ v && Adm y ρ' v)
  | _, .never, _, _, h, _, _, _, _, _ => by
      simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
  | _, .held _ _ _ _, y, _, h, _, _, _, _, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | exact absurd h (by simp [Term.meet])
  -- two variables meet at the binder the pairing names, which writes where both write
  | _, .var i, y, _, h, _, _, _, hp, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | (simp only [Term.meet, Option.map_eq_some_iff] at h
             obtain ⟨k, hk, rfl⟩ := h
             exact hp i _ k hk v)
          | exact absurd h (by simp [Term.meet])
  -- two recursive terms meet stage by stage, and an unfolding meets the body
  | p, .mu b, y, _, h, ρ, ρ', ρ'', hp, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | (simp only [Term.meet, Option.bind_eq_some_iff] at h
             obtain ⟨w, hw, hz⟩ := h
             have hmu := Adm_mu_meet (ρ := ρ) (ρ' := ρ') (ρ'' := ρ'') (fun c c' c'' hc u =>
               Adm_meet (pairMu p) b _ w hw (c :: ρ) (c' :: ρ') (c'' :: ρ'') (hp.mu hc) u) v
             split at hz
             · next hn =>
                 cases hz
                 rw [← hmu, eq_never_of_isNever hn, Adm_mu_never, Adm_never]
             · split at hz
               · next hu =>
                   cases hz
                   rw [Adm_eq_isSome _ ρ'' v, ← (denote_mu_vacuous hu ρ'').1,
                     ← Adm_eq_isSome (.mu w) ρ'' v]
                   exact hmu
               · split at hz
                 · cases hz; exact hmu
                 · exact nomatch hz)
          | (simp only [Term.meet] at h
             rw [Adm_mu_unfold b ρ v]
             exact Adm_meet (shiftL p) b _ _ h _ ρ' ρ'' (hp.left _) v)
  | p, .refine x q, y, _, h, ρ, ρ', ρ'', hp, v => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          have ihw := Adm_meet p x _ w hw ρ ρ' ρ'' hp v
          rw [Adm_refineOf]
          simp only [Adm, ihw]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        · obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.mp h
          split at hz
          · next hn =>
              cases hz
              have ihw := Adm_meet p x _ w hw ρ ρ' ρ'' hp v
              rw [eq_never_of_isNever hn, Adm_never] at ihw
              have hr : Adm (.refine x q) ρ v = (Adm x ρ v && Sem.eval q v) := by simp [Adm]
              rw [Adm_never, hr, Bool.and_right_comm, ← ihw, Bool.false_and]
          · exact nomatch hz
  | p, .union os, y, _, h, ρ, ρ', ρ'', hp, v => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      | _ =>
        obtain ⟨zs, hF, rfl⟩ := meet_union_of h (by simp)
        exact union_meet_free v (Adm_meetL p os _ _ hF ρ ρ' ρ'' hp)
  | p, .prim g, y, z, h, ρ, ρ', ρ'', hp, v =>
      Adm_meetSRight (ρ := ρ) (fun _ _ _ _ => Adm_famPrim g) y p ρ' ρ'' z hp h v
  | p, .set a, y, z, h, ρ, ρ', ρ'', hp, v =>
      Adm_meetSRight (ρ := ρ)
        (fun q ρ₁ ρ₂ hq => Adm_famSet a (fun u w hw => Adm_meet q a u w hw ρ ρ₁ ρ₂ hq))
        y p ρ' ρ'' z hp h v
  | p, .opaq, y, z, h, ρ, ρ', ρ'', hp, v =>
      Adm_meetSRight (ρ := ρ) (fun _ _ _ _ => Adm_famOpaq) y p ρ' ρ'' z hp h v
  | p, .list pre sp suf, y, z, h, ρ, ρ', ρ'', hp, v => by
      cases sp with
      | none =>
          exact Adm_meetSRight (ρ := ρ) (fun q ρ₁ ρ₂ hq => Adm_famList (pre := pre) (sp := none)
            (suf := suf) (Adm_meetSTs q pre ρ ρ₁ ρ₂ hq) (Or.inl ⟨rfl, rfl⟩)
            (Adm_meetSTs q suf ρ ρ₁ ρ₂ hq)) y p ρ' ρ'' z hp h v
      | some t =>
          exact Adm_meetSRight (ρ := ρ) (fun q ρ₁ ρ₂ hq => Adm_famList (pre := pre)
            (sp := some t) (suf := suf) (Adm_meetSTs q pre ρ ρ₁ ρ₂ hq)
            (Or.inr ⟨t, Term.meet q t, rfl, rfl, fun u w hw => Adm_meet q t u w hw ρ ρ₁ ρ₂ hq⟩)
            (Adm_meetSTs q suf ρ ρ₁ ρ₂ hq)) y p ρ' ρ'' z hp h v
  | p, .object (.mk fs f none), y, z, h, ρ, ρ', ρ'', hp, v =>
      Adm_meetSRight (ρ := ρ) (fun q ρ₁ ρ₂ hq => Adm_famObj (a := .mk fs f none)
        (fun k fl fm hm w => Adm_Field_meet q (f k) fl fm hm ρ ρ₁ ρ₂ hq w)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun _ _ hz _ => by simp only [Option.some.injEq] at hz; subst hz; rfl))
        y p ρ' ρ'' z hp h v
  | p, .object (.mk fs f (some t)), y, z, h, ρ, ρ', ρ'', hp, v =>
      Adm_meetSRight (ρ := ρ) (fun q ρ₁ ρ₂ hq => Adm_famObj (a := .mk fs f (some t))
        (fun k fl fm hm w => Adm_Field_meet q (f k) fl fm hm ρ ρ₁ ρ₂ hq w)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun u w hw => Adm_meet q t u w hw ρ ρ₁ ρ₂ hq)) y p ρ' ρ'' z hp h v
termination_by structural _ x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem Adm_meetL [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (os : List (Term S)) (y : Term S) (zs : List (Term S)),
    List.Forall₂ (fun t w => Term.meet p t y = some w) os zs →
    ∀ (ρ ρ' ρ'' : List S.C), PairedV p ρ ρ' ρ'' →
    List.Forall₂ (fun t w => ∀ u, Adm w ρ'' u = (Adm t ρ u && Adm y ρ' u)) os zs
  | _, [], _, _, h, _, _, _, _ => by cases h; exact .nil
  | p, t :: ts, y, _, h, ρ, ρ', ρ'', hp => by
      cases h with
      | cons hh ht =>
          exact .cons (fun u => Adm_meet p t y _ hh ρ ρ' ρ'' hp u)
            (Adm_meetL p ts y _ ht ρ ρ' ρ'' hp)
termination_by structural _ os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem Adm_meetSTs [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (ts : List (Term S)) (ρ ρ' ρ'' : List S.C), PairedV p ρ ρ' ρ'' →
      List.Forall₂ (AdmSound ρ ρ' ρ'') ts (Term.meetSTs p ts)
  | _, [], _, _, _, _ => .nil
  | p, t :: ts, ρ, ρ', ρ'', hp =>
      .cons (fun u w hw => Adm_meet p t u w hw ρ ρ' ρ'' hp) (Adm_meetSTs p ts ρ ρ' ρ'' hp)
termination_by structural _ ts => ts

/-- Two fields at one name admit what both admit, at the stronger mark. -/
theorem Adm_Field_meet [Leaf S] [LeafAdm S] [FormerAdm S] [Shapes S] :
    ∀ (p : Pairing) (f fl : ObjectSlot S) (fm : ObjectSlot S), ObjectSlot.meet p f fl = some fm →
    ∀ (ρ ρ' ρ'' : List S.C), PairedV p ρ ρ' ρ'' →
    ∀ w, AdmField fm ρ'' w = (AdmField f ρ w && AdmField fl ρ' w)
  | p, .req x, .req y, _, h, ρ, ρ', ρ'', hp, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet p x y tz hz ρ ρ' ρ'' hp w
  | p, .req x, .optional y, _, h, ρ, ρ', ρ'', hp, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet p x y tz hz ρ ρ' ρ'' hp w
  | p, .optional x, .req y, _, h, ρ, ρ', ρ'', hp, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet p x y tz hz ρ ρ' ρ'' hp w
  | p, .optional x, .optional y, _, h, ρ, ρ', ρ'', hp, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet p x y tz hz ρ ρ' ρ'' hp w
termination_by structural _ f => f
end

end

end Calculus.Alg
