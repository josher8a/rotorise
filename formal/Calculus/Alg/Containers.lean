import Calculus.Alg.Positions
import Calculus.Alg.Maps

/-!
# The list and the object, over any carriers

A container reads a universe through one summand onto a canonical carrier: a list summand onto
`List`, and a keyed-map summand onto `MapOf`. Each container is `carriedCodec` at its summand. So
the laws of the payload map are proved one time here, and a universe supplies only its summands.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M}

/-! ## `list` (§3): one prefix, at most one spread, one suffix -/

section List
variable (sL : Summand (List V) V M member)

/-- §3 `(list)`: the positional product over a prefix, a spread and a suffix, carried by the
    list prism. Each position goes through its own codec at the orientation. -/
abbrev listCodec (pre : List (Codec V M)) (spread : Option (Codec V M))
    (suf : List (Codec V M)) : Codec V M :=
  carriedCodec sL
    (fun vs => ∃ ps, alignL pre spread suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
    (fun o vs => (alignL pre spread suf vs).bind (traverse fun cv => cv.1.f o cv.2))

variable {sL} {pre : List (Codec V M)} {sp : Option (Codec V M)}
  {suf : List (Codec V M)}

/-- A list is lawful: the alignment puts each position on its own codec. -/
theorem lawful_listCodec
    (hpre : ∀ c ∈ pre, Lawful member c) (hsp : ∀ c ∈ sp, Lawful member c)
    (hsuf : ∀ c ∈ suf, Lawful member c) : Lawful member (listCodec sL pre sp suf) := by
  refine lawful_carried (Orient.both
    (P := fun o => ∀ x y, (alignL pre sp suf x).bind (traverse fun cv => cv.1.f o cv.2) = some y →
      (alignL pre sp suf y).bind (traverse fun cv => cv.1.f o.op cv.2) = some x)
    (list_retract (fun c h => (hpre c h).core) (fun c h => (hsp c h).core)
      (fun c h => (hsuf c h).core)) ?_)
  intro as vs hD
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  rw [alignL_of_slotsL hs hn]
  exact zip_canonS ds as vs (slotsL_all hpre hsp hsuf hs) hlen htr

/-- Writing and reading a `list` puts every position on its own carrier. -/
theorem carrier_listCodec (hpre : ∀ c ∈ pre, Carrier c) (hsp : ∀ c ∈ sp, Carrier c)
    (hsuf : ∀ c ∈ suf, Carrier c) : Carrier (listCodec sL pre sp suf) := by
  refine carrier_carried ?_ ?_
  · intro vs as hE
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    exact ⟨_, hal, zip_domE ds vs as (slotsL_all hpre hsp hsuf hs) htr⟩
  · intro as vs hD
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    have hn : vs.length = as.length := by
      rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
    exact ⟨_, alignL_of_slotsL hs hn, zip_ranP ds as vs (slotsL_all hpre hsp hsuf hs) htr⟩

end List

/-! ## Objects (§4)

An object is the product of its slots over the names. A slot reads the lookup `p.at k`, so a
slot is a codec on the presence lift `Option V`: a present value goes through the entry's codec,
and absence takes the slot's behavior (`absentOf`). The product runs over the declared names and
the present names; every other name is absent and stays absent. `objectCodecCore` is
`carriedCodec` at the keyed-map prism, so §2's prism halves are the ones already discharged. -/

section Product
variable {L : String → Orient → Option V → Option (Option V)} {F : Finset String}

/-- **The product of slots** over the names `F` and the present names. -/
def objP (L : String → Orient → Option V → Option (Option V)) (F : Finset String)
    (o : Orient) (p : MapOf V) : Option (MapOf V) :=
  if ∀ k ∈ F ∪ p.keys, (L k o (p.at k)).isSome then
    some (MapOf.ofFun (F ∪ p.keys) fun k => if k ∈ F ∪ p.keys then (L k o (p.at k)).join else none)
  else none

/-- **What the product sends**: each slot sends its lookup, and nothing outside the names. -/
theorem objP_eq {o p q} :
    objP L F o p = some q ↔
      (∀ k ∈ F ∪ p.keys, L k o (p.at k) = some (q.at k)) ∧ q.keys ⊆ F ∪ p.keys := by
  have hout : ∀ g : String → Option V, ∀ k, k ∉ F ∪ p.keys →
      (fun k => if k ∈ F ∪ p.keys then g k else none) k = none :=
    fun g k hk => by simp only [hk, if_false]
  unfold objP
  constructor
  · intro h
    split at h
    · next hall =>
      cases h
      refine ⟨fun k hk => ?_, fun k hk => (Finset.mem_filter.mp hk).1⟩
      rw [MapOf.at_ofFun (hout _)]
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hall k hk)
      simp only [hk, if_true, hy, Option.join_some]
    · exact nomatch h
  · rintro ⟨hq, hsub⟩
    rw [if_pos fun k hk => by rw [hq k hk]; rfl]
    refine congrArg some (MapOf.ext_at fun k => ?_)
    rw [MapOf.at_ofFun (hout _)]
    rcases Decidable.em (k ∈ F ∪ p.keys) with hk | hk
    · simp only [hk, if_true, hq k hk, Option.join_some]
    · simp only [hk, if_false]
      exact (MapOf.at_none fun h' => hk (hsub h')).symm

/-- **The inverse law of the product**, from each slot's: a name outside `F` keeps absence. -/
theorem objP_inv (hL : ∀ k o x y, L k o x = some y → L k o.op y = some x)
    (hA : ∀ k o, k ∉ F → L k o none = some none) :
    ∀ o p q, objP L F o p = some q → objP L F o.op q = some p := by
  intro o p q h
  obtain ⟨hq, hsub⟩ := objP_eq.mp h
  have back : ∀ k, L k o.op (q.at k) = some (p.at k) := by
    intro k
    rcases Decidable.em (k ∈ F ∪ p.keys) with hk | hk
    · exact hL k o _ _ (hq k hk)
    · rw [MapOf.at_none fun h' => hk (hsub h'),
        MapOf.at_none fun h' => hk (Finset.mem_union.mpr (Or.inr h'))]
      exact hA k o.op fun h' => hk (Finset.mem_union.mpr (Or.inl h'))
  refine objP_eq.mpr ⟨fun k _ => back k, fun k hk => ?_⟩
  refine Finset.mem_union.mpr (Decidable.byContradiction fun hn => ?_)
  have hqk : q.at k = none := MapOf.at_none fun h' => hn (Or.inr h')
  have := back k
  rw [hqk, hA k o.op fun h' => hn (Or.inl h'), MapOf.at_of_mem ⟨k, hk⟩] at this
  exact nomatch this

/-- Two products whose slots agree on the names send one map alike. -/
theorem objP_congr {L₁ L₂ : String → Orient → Option V → Option (Option V)} {o p}
    (h : ∀ k ∈ F ∪ p.keys, L₁ k o (p.at k) = L₂ k o (p.at k)) :
    objP L₁ F o p = objP L₂ F o p := by
  have hf : (fun k => if k ∈ F ∪ p.keys then (L₁ k o (p.at k)).join else none) =
      fun k => if k ∈ F ∪ p.keys then (L₂ k o (p.at k)).join else none := funext fun k => by
    rcases Decidable.em (k ∈ F ∪ p.keys) with hk | hk
    · simp only [hk, if_true, h k hk]
    · simp only [hk, if_false]
  unfold objP
  rw [hf]
  exact if_congr (forall₂_congr fun k hk => by rw [h k hk]) rfl rfl

end Product

section Object

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    String × V → Prop := fun kv =>
  match sems.at kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The codec one entry goes through: the field its name declares, or else the rest
    policy's. `none` is an undeclared name under `refuse`. -/
def entryCodec (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) (k : String) :
    Option (Codec V M) :=
  match sems.at k with
  | some fs => some fs.codec
  | none => rc?

/-- **The slot of a name** on the presence lift: a present value goes through the entry's
    codec, and absence takes the slot's behavior at the orientation. -/
def liftTable (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    String → Orient → Option V → Option (Option V)
  | k, o, some v => ((entryCodec sems rc? k).bind fun c => c.f o v).map some
  | k, o, none => absentOf o (sems.at k)

/-- The held set of a slot: a present value is in its entry's set, and an absent name is one
    the slot lets be absent on the write. -/
def slotT (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) (k : String) :
    Option V → Prop
  | some v => objEntryT sems rc? (k, v)
  | none => (absentOf .host (sems.at k)).isSome

/-- Whether no field of a table fills an absent name. -/
def noFill (sems : MapOf (FieldSem V M)) : Bool :=
  decide (∀ k : {k // k ∈ sems.keys}, (sems.2 k).isFill = false)

variable {sems : MapOf (FieldSem V M)} {rc? : Option (Codec V M)}

/-- A property of every field and of the rest codec is a property of every entry's
    codec — which is how the object's per-entry laws are discharged, once each. -/
theorem entryCodec_of {Q : Codec V M → Prop} (hf : ∀ k, Q (sems.2 k).codec)
    (hrc : ∀ c ∈ rc?, Q c) {k c} (h : entryCodec sems rc? k = some c) : Q c := by
  simp only [entryCodec] at h
  cases hsp : sems.at k with
  | some fs => rw [hsp] at h; cases h; exact MapOf.at_forall (Q := fun fs => Q fs.codec) hf hsp
  | none => rw [hsp] at h; exact hrc c h

/-- §4's held set, per entry, in the same vocabulary. -/
theorem objEntryT_eq {kv} :
    objEntryT sems rc? kv ↔ ∃ c, entryCodec sems rc? kv.1 = some c ∧ c.T kv.2 := by
  simp only [objEntryT, entryCodec]
  cases sems.at kv.1 <;> simp

/-- A table with no fill holds no fill at any name. -/
theorem noFill_at (h : noFill sems = true) : ∀ k fs, sems.at k = some fs → fs.isFill = false :=
  fun k _ hs => by obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hs; exact of_decide_eq_true h ⟨k, hk⟩

/-- An undeclared name keeps absence at every orientation. -/
theorem liftTable_absent {k : String} (hk : k ∉ sems.keys) (o : Orient) :
    liftTable sems rc? k o none = some none := by
  simp only [liftTable, MapOf.at_none hk, absentOf]

/-- At absence a slot that is not a fill answers absence or refuses. -/
theorem liftTable_none {k : String} {o : Orient} {y : Option V}
    (hk : ∀ fs, sems.at k = some fs → fs.isFill = false)
    (h : liftTable sems rc? k o none = some y) : y = none := by
  revert h
  simp only [liftTable]
  match hs : sems.at k with
  | none => intro h; exact (Option.some.inj h).symm
  | some (.req _) => intro h; cases h
  | some (.opt _) => intro h; cases h; rfl
  | some (.fill _ _) => exact absurd (hk _ hs) (by simp [FieldSem.isFill])

/-- A slot that is not a fill acts alike at absence at every orientation. -/
theorem absentOf_of_notFill {o o' : Orient} {x : Option (FieldSem V M)}
    (hx : ∀ fs, x = some fs → fs.isFill = false) : absentOf o x = absentOf o' x := by
  match x, hx with
  | none, _ => rfl
  | some (.req _), _ => rfl
  | some (.opt _), _ => rfl
  | some (.fill _ _), hx => exact absurd (hx _ rfl) (by simp [FieldSem.isFill])

/-- At absence a slot that is not a fill and answers answers absence. -/
theorem absentOf_isSome {o : Orient} {x : Option (FieldSem V M)}
    (hx : ∀ fs, x = some fs → fs.isFill = false) (h : (absentOf o x).isSome) :
    absentOf o x = some none := by
  match x, hx, h with
  | none, _, _ => rfl
  | some (.opt _), _, _ => rfl
  | some (.fill _ _), hx, _ => exact absurd (hx _ rfl) (by simp [FieldSem.isFill])

/-- **The object's payload map at an orientation**: the product of the slots (`objAt_eq_objP`).
    A table with no fill takes the form that walks the present keys and looks no name up, because
    the vectors reduce it by `rfl` under a bound key, where a lookup does not reduce. A fill adds
    the names it reads, so its table takes the product itself. -/
noncomputable def objAt (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) (o : Orient) :
    MapOf V → Option (MapOf V) := fun p =>
  if noFill sems then
    if ∀ k ∈ sems.keys, k ∉ p.keys → (absentOf o (sems.at k)).isSome then
      (funImage fun k => (entryCodec sems rc? k.1).bind fun c => c.f o (p.2 k)).map
        fun g => ⟨p.1, g⟩
    else none
  else objP (liftTable sems rc?) sems.keys o p

/-- **The payload map is the product of the slots** over the declared names and the present names. -/
theorem objAt_eq_objP (o : Orient) (p : MapOf V) :
    objAt sems rc? o p = objP (liftTable sems rc?) sems.keys o p := by
  unfold objAt
  split
  · next hnf =>
    have hnf := noFill_at hnf
    refine Option.ext fun q => ?_
    rw [objP_eq]
    refine Iff.symm ?_
    split
    · next hg =>
      constructor
      · rintro ⟨hq, hsub⟩
        -- a present name: the entry sends the value to `q`'s
        have hpres : ∀ k : {k // k ∈ p.keys}, ∃ w, (entryCodec sems rc? k.1).bind
            (fun c => c.f o (p.2 k)) = some w ∧ q.at k.1 = some w := by
          intro k
          have := hq k.1 (Finset.mem_union.mpr (Or.inr k.2))
          rw [MapOf.at_of_mem k] at this
          simp only [liftTable, Option.map_eq_some_iff] at this
          obtain ⟨w, hw, he⟩ := this
          exact ⟨w, hw, he.symm⟩
        have hsome : ∀ k : {k // k ∈ p.keys},
            ((entryCodec sems rc? k.1).bind fun c => c.f o (p.2 k)).isSome := fun k => by
          obtain ⟨w, hw, _⟩ := hpres k; rw [hw]; rfl
        rw [funImage_eq (f := fun k => (_ : Option V).get (hsome k)) fun k => (Option.some_get _).symm]
        refine congrArg some (MapOf.ext_at fun k => ?_)
        rcases Decidable.em (k ∈ p.keys) with hkp | hkp
        · obtain ⟨w, hw, hqk⟩ := hpres ⟨k, hkp⟩
          rw [hqk]
          simp only [MapOf.at, dif_pos hkp, hw, Option.get_some]
        · refine (MapOf.at_none (m := ⟨p.keys, fun k =>
            ((entryCodec sems rc? k.1).bind fun c => c.f o (p.get k)).get (hsome k)⟩) hkp).trans ?_
          rcases Decidable.em (k ∈ sems.keys) with hkF | hkF
          · have := hq k (Finset.mem_union.mpr (Or.inl hkF))
            rw [MapOf.at_none hkp] at this
            exact (liftTable_none (hnf k) this).symm
          · exact (MapOf.at_none fun h' => (Finset.mem_union.mp (hsub h')).elim hkF hkp).symm
      · intro h
        obtain ⟨g, hg', rfl⟩ := Option.map_eq_some_iff.mp h
        have hent := funImage_some hg'
        refine ⟨fun k hk => ?_, fun k hk => Finset.mem_union.mpr (Or.inr hk)⟩
        rcases Decidable.em (k ∈ p.keys) with hkp | hkp
        · rw [MapOf.at_of_mem ⟨k, hkp⟩, MapOf.at_of_mem (m := (⟨p.1, g⟩ : MapOf V)) ⟨k, hkp⟩]
          simp only [liftTable, hent ⟨k, hkp⟩, Option.map_some]
        · rw [MapOf.at_none hkp, MapOf.at_none (m := (⟨p.1, g⟩ : MapOf V)) hkp]
          exact absentOf_isSome (hnf k) (hg k ((Finset.mem_union.mp hk).resolve_right hkp) hkp)
    · next hg =>
      refine ⟨fun ⟨hq, _⟩ => absurd (fun k hkF hkp => ?_) hg, fun h => (nomatch h)⟩
      have := hq k (Finset.mem_union.mpr (Or.inl hkF))
      rw [MapOf.at_none hkp] at this
      simp only [liftTable] at this
      rw [this]; rfl

  · rfl

/-- What the payload map sends at an orientation: each slot sends its lookup, and nothing
    outside the names. -/
theorem objAt_eq {o : Orient} {p q : MapOf V} :
    objAt sems rc? o p = some q ↔
      (∀ k ∈ sems.keys ∪ p.keys, liftTable sems rc? k o (p.at k) = some (q.at k)) ∧
        q.keys ⊆ sems.keys ∪ p.keys := by
  rw [objAt_eq_objP]; exact objP_eq

/-- **The domain of the payload map**: every absent declared name answers at absence, and every
    present entry goes through its codec. -/
theorem objAt_isSome {o : Orient} {p : MapOf V} :
    (objAt sems rc? o p).isSome ↔
      (∀ k ∈ sems.keys, k ∉ p.keys → (absentOf o (sems.at k)).isSome) ∧
        ∀ k : {k // k ∈ p.keys}, ((entryCodec sems rc? k.1).bind fun c => c.f o (p.get k)).isSome := by
  rw [objAt_eq_objP]
  unfold objP
  split
  · next hall =>
    simp only [Option.isSome_some, true_iff]
    refine ⟨fun k hk hkp => ?_, fun k => ?_⟩
    · have := hall k (Finset.mem_union.mpr (Or.inl hk))
      rwa [MapOf.at_none hkp] at this
    · have := hall k.1 (Finset.mem_union.mpr (Or.inr k.2))
      rw [MapOf.at_of_mem k] at this
      simpa only [liftTable, Option.isSome_map] using this
  · next hall =>
    refine ⟨fun h => (nomatch h), fun ⟨ha, he⟩ => absurd (fun k hk => ?_) hall⟩
    rcases Decidable.em (k ∈ p.keys) with hkp | hkp
    · rw [MapOf.at_of_mem ⟨k, hkp⟩]
      simpa only [liftTable, Option.isSome_map] using he ⟨k, hkp⟩
    · rw [MapOf.at_none hkp]
      exact ha k ((Finset.mem_union.mp hk).resolve_right hkp) hkp

/-- **The held set of the slot product**: every absent declared name lets absence be on the
    write, and every present entry is in its entry's set. -/
theorem slotT_all_iff {p : MapOf V} :
    (∀ k, slotT sems rc? k (p.at k)) ↔
      (∀ k ∈ sems.keys, k ∉ p.keys → (absentOf .host (sems.at k)).isSome) ∧
        ∀ k : {k // k ∈ p.keys}, objEntryT sems rc? (k.1, p.get k) := by
  constructor
  · intro h
    refine ⟨fun k _ hkp => ?_, fun k => ?_⟩
    · have := h k; rwa [MapOf.at_none hkp] at this
    · have := h k.1; rwa [MapOf.at_of_mem k] at this
  · rintro ⟨ha, he⟩ k
    rcases Decidable.em (k ∈ p.keys) with hkp | hkp
    · rw [MapOf.at_of_mem ⟨k, hkp⟩]; exact he ⟨k, hkp⟩
    · rw [MapOf.at_none hkp]
      rcases Decidable.em (k ∈ sems.keys) with hk | hk
      · exact ha k hk hkp
      · simp only [slotT, MapOf.at_none hk, absentOf, Option.isSome_some]

/-- Every name, declared or not, sends its lookup. -/
theorem objAt_at {o : Orient} {p q : MapOf V} (h : objAt sems rc? o p = some q) (k : String) :
    liftTable sems rc? k o (p.at k) = some (q.at k) := by
  obtain ⟨hq, hsub⟩ := objAt_eq.mp h
  rcases Decidable.em (k ∈ sems.keys ∪ p.keys) with hk | hk
  · exact hq k hk
  · rw [MapOf.at_none fun h' => hk (hsub h'),
      MapOf.at_none fun h' => hk (Finset.mem_union.mpr (Or.inr h'))]
    exact liftTable_absent (fun h' => hk (Finset.mem_union.mpr (Or.inl h'))) o

variable (sM : Summand (MapOf V) V M member)

/-- The object is `carriedCodec` at the keyed-map prism, with the payload map `objAt`. -/
noncomputable abbrev objectCodecCore (sems : MapOf (FieldSem V M)) (rc? : Option (Codec V M)) :
    Codec V M :=
  carriedCodec sM (fun p => ∀ k, slotT sems rc? k (p.at k)) (objAt sems rc?)

/-- §4's `object`: the core at the rest policy's codec. -/
noncomputable abbrev objectCodec (sems : MapOf (FieldSem V M)) (rest : RestSem V M) :
    Codec V M :=
  objectCodecCore sM sems (rcOf rest)

variable {sM}

/-! ### §2's clauses for the object's payload map -/

/-- §4's held set follows from the entry carriers, slot by slot, where every fill's constant is
    in its codec's held set. The host refuses at construction a constant that its codec cannot
    write. -/
theorem carrier_objectCodec {rest : RestSem V M}
    (hsems : ∀ k, Carrier (sems.2 k).codec)
    (hrc : ∀ rc, rcOf rest = some rc → Carrier rc)
    (hfill : ∀ k c v, sems.2 k = .fill c v → c.T v) :
    Carrier (objectCodec sM sems rest) := by
  -- presence: the entry's codec holds the value it writes, and the value it reads
  have present : ∀ {k o v w}, liftTable sems (rcOf rest) k o (some v) = some w →
      ∃ c a, entryCodec sems (rcOf rest) k = some c ∧ c.f o v = some a ∧ w = some a ∧
        Carrier c := fun h => by
    simp only [liftTable, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨c, hc, hca⟩ := Option.bind_eq_some_iff.mp ha
    exact ⟨c, a, hc, hca, rfl, entryCodec_of hsems hrc hc⟩
  -- absence on the read: the slot answers absence, or a fill answers its constant
  have absentRead : ∀ {k y}, liftTable sems (rcOf rest) k .dual none = some y →
      slotT sems (rcOf rest) k y := by
    intro k y h
    simp only [liftTable] at h
    match hs : sems.at k with
    | none => rw [hs] at h; cases h; simp only [slotT, hs, absentOf, Option.isSome_some]
    | some (.req c) => rw [hs] at h; exact nomatch h
    | some (.opt c) => rw [hs] at h; cases h; simp only [slotT, hs, absentOf, Option.isSome_some]
    | some (.fill c v) =>
      rw [hs] at h
      simp only [absentOf, Orient.c, cond_true] at h
      cases h
      obtain ⟨hk, hget⟩ := MapOf.at_eq_some.mp hs
      exact objEntryT_eq.mpr ⟨c, by simp only [entryCodec, hs, FieldSem.codec], hfill ⟨k, hk⟩ c v hget⟩
  refine carrier_carried (fun {p _} h k => ?_) (fun {q _} h k => ?_)
  · have hk := objAt_at h k
    rcases (p.at k).eq_none_or_eq_some with hx | ⟨v, hx⟩ <;> rw [hx] at hk ⊢
    · simp only [liftTable] at hk
      simp only [slotT, hk, Option.isSome_some]
    · obtain ⟨c, a, hc, hca, -, hC⟩ := present hk
      exact objEntryT_eq.mpr ⟨c, hc, hC.domE hca⟩
  · have hk := objAt_at h k
    rcases (q.at k).eq_none_or_eq_some with hx | ⟨a, hx⟩ <;> rw [hx] at hk
    · exact absentRead hk
    · obtain ⟨c, v, hc, hcv, hv, hC⟩ := present hk
      rw [hv]
      exact objEntryT_eq.mpr ⟨c, hc, hC.ranP hcv⟩

/-- **The inverse law of the payload map**, at every orientation, for a table with no fill:
    each slot inverts its own map, and an undeclared name keeps absence. A fill reads an absent
    name as a value that the write sends to a present name, so a fill is not an inverse. -/
theorem object_inv {rest : RestSem V M} (hnf : noFill sems = true)
    (hf : ∀ k, Lawful member (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, Lawful member c) (o : Orient) :
    ∀ p q, objAt sems (rcOf rest) o p = some q → objAt sems (rcOf rest) o.op q = some p := by
  intro p q h
  rw [objAt_eq_objP] at h ⊢
  refine objP_inv (L := liftTable sems (rcOf rest)) (fun k o x y h => ?_)
    (fun k o hk => liftTable_absent hk o) o p q h
  cases x with
  | none =>
    obtain rfl := liftTable_none (noFill_at hnf k) h
    simp only [liftTable] at h ⊢
    rwa [absentOf_of_notFill (o' := o) (noFill_at hnf k)]
  | some v =>
    simp only [liftTable, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨c, hc, hcw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [liftTable, hc, Option.bind_some, (entryCodec_of hf hrc hc).inv hcw, Option.map_some]

/-- The keyed product: the doc's current-schema `object`, for a table with no fill. -/
theorem lawful_objectCodec {rest : RestSem V M} (hnf : noFill sems = true)
    (hf : ∀ k, Lawful member (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful member c) :
    Lawful member (objectCodec sM sems rest) :=
  lawful_carried (object_inv hnf hf (rcOf_forall hrest))

end Object

end Calculus.Alg
