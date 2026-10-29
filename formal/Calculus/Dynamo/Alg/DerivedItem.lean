import Calculus.Alg.Derive
import Calculus.Dynamo.Alg.Frontier

/-!
# The item with derived keys, at the DynamoDB row

A row of an item is the top-level map that an object codec writes: an attribute `M`. The key names
are a finite set `KS`. The key part of a row is the string at each key name, or no string where the
row lacks the name. A row that holds an attribute other than `S` at a key name has no key part, so
`keep` gives `none` there, and the strict read of the graph refuses the row. The read that deletes
the keys still reads the row, because `drop` removes each key name whatever attribute the name holds.

The key part `{k // k ∈ KS} → Option String` has decidable equality, because `KS` is finite. The
carrier `Attr` has none, because `.m` holds a function. So the lens needs no equality on the carrier.
-/

namespace Calculus

namespace DerivedItem

open Alg

variable (KS : Finset String)

/-- The key part of a row: at each key name, the string, or no string where the row lacks the name. -/
abbrev KeyPart := {k // k ∈ KS} → Option String

/-- **Two key parts are equal where they agree at each key name.** The decision runs over the finite
    key names, with a route that the classical gateways already list. -/
instance : DecidableEq (KeyPart KS) := fun y y' =>
  decidable_of_iff (∀ k, y k = y' k) ⟨funext, fun h _ => h ▸ rfl⟩

/-- What an attribute gives to a key part: no attribute gives no string, an `S` gives its string, and
    any other attribute gives no key part. -/
def keyAt : Option Attr → Option (Option String)
  | none => some none
  | some (.s v) => some (some v)
  | some _ => none

/-- The map without the key names. -/
def dropMap (m : MapOf Attr) : MapOf Attr := m.keep fun nm => decide (nm ∉ KS)

/-- The map that holds the strings of a key part at the key names. -/
def keysMap (y : KeyPart KS) : MapOf Attr :=
  MapOf.ofFun KS fun nm => if h : nm ∈ KS then (y ⟨nm, h⟩).map Attr.s else none

/-- The map with a key part: the strings of the key part, and the other names of the map. -/
def joinMap (x : MapOf Attr) (y : KeyPart KS) : MapOf Attr := (keysMap KS y).union (dropMap KS x)

/-- The key part of a map, or none where a key name holds an attribute other than `S`. -/
def keepMap (m : MapOf Attr) : Option (KeyPart KS) :=
  if h : ∀ k : {k // k ∈ KS}, (keyAt (m.at k.1)).isSome then
    some fun k => (keyAt (m.at k.1)).get (h k)
  else none

variable {KS}

/-- A key name has no value in a map without the key names. -/
theorem at_dropMap_mem (m : MapOf Attr) {nm : String} (h : nm ∈ KS) : (dropMap KS m).at nm = none :=
  MapOf.at_keep_neg m (by simp [h])

/-- A name that is no key name keeps its value in a map without the key names. -/
theorem at_dropMap_nmem (m : MapOf Attr) {nm : String} (h : nm ∉ KS) :
    (dropMap KS m).at nm = m.at nm :=
  MapOf.at_keep_pos m (by simp [h])

/-- The map of a key part holds the string of the key part at a key name. -/
theorem at_keysMap_mem (y : KeyPart KS) {nm : String} (h : nm ∈ KS) :
    (keysMap KS y).at nm = (y ⟨nm, h⟩).map Attr.s := by
  unfold keysMap
  rw [MapOf.at_ofFun (fun k hk => by simp [hk]), dif_pos h]

/-- The map of a key part holds nothing at a name that is no key name. -/
theorem at_keysMap_nmem (y : KeyPart KS) {nm : String} (h : nm ∉ KS) : (keysMap KS y).at nm = none := by
  unfold keysMap
  rw [MapOf.at_ofFun (fun k hk => by simp [hk]), dif_neg h]

/-- A joined map holds the string of the key part at a key name. -/
theorem at_joinMap_mem (x : MapOf Attr) (y : KeyPart KS) {nm : String} (h : nm ∈ KS) :
    (joinMap KS x y).at nm = (y ⟨nm, h⟩).map Attr.s := by
  rw [joinMap, MapOf.at_union, at_keysMap_mem y h, at_dropMap_mem x h]
  cases y ⟨nm, h⟩ <;> rfl

/-- A joined map keeps the value of the first map at a name that is no key name. -/
theorem at_joinMap_nmem (x : MapOf Attr) (y : KeyPart KS) {nm : String} (h : nm ∉ KS) :
    (joinMap KS x y).at nm = x.at nm := by
  rw [joinMap, MapOf.at_union, at_keysMap_nmem y h, at_dropMap_nmem x h]
  rfl

/-- **PutGet at the map.** The key part of a joined map is the part that the join put. -/
theorem keepMap_joinMap (x : MapOf Attr) (y : KeyPart KS) : keepMap KS (joinMap KS x y) = some y := by
  have key : ∀ k : {k // k ∈ KS}, keyAt ((joinMap KS x y).at k.1) = some (y k) := fun k => by
    rw [at_joinMap_mem x y k.2]
    cases y k <;> rfl
  unfold keepMap
  rw [dif_pos (fun k => by rw [key k]; rfl)]
  exact congrArg some (funext fun k => by simp [key k])

/-- **The complement is unchanged by a join.** -/
theorem dropMap_joinMap (x : MapOf Attr) (y : KeyPart KS) :
    dropMap KS (joinMap KS x y) = dropMap KS x :=
  MapOf.ext_at fun nm => by
    cases h : decide (nm ∈ KS) with
    | true =>
        have hm : nm ∈ KS := of_decide_eq_true h
        rw [at_dropMap_mem _ hm, at_dropMap_mem _ hm]
    | false =>
        have hm : nm ∉ KS := of_decide_eq_false h
        rw [at_dropMap_nmem _ hm, at_dropMap_nmem _ hm, at_joinMap_nmem _ _ hm]

/-- A key part of a map is the string of the map at each key name. -/
theorem keepMap_spec {m : MapOf Attr} {y : KeyPart KS} (h : keepMap KS m = some y) :
    ∀ k : {k // k ∈ KS}, keyAt (m.at k.1) = some (y k) := by
  unfold keepMap at h
  split at h
  · next hall =>
      cases h
      intro k
      exact (Option.some_get (hall k)).symm
  · exact nomatch h

/-- **GetPut at the map.** A map with a key part is its complement joined to the key part. -/
theorem joinMap_keepMap {m : MapOf Attr} {y : KeyPart KS} (h : keepMap KS m = some y) :
    joinMap KS (dropMap KS m) y = m :=
  MapOf.ext_at fun nm => by
    cases hd : decide (nm ∈ KS) with
    | true =>
        have hm : nm ∈ KS := of_decide_eq_true hd
        rw [at_joinMap_mem _ _ hm]
        have hk := keepMap_spec h ⟨nm, hm⟩
        cases hv : m.at nm with
        | none =>
            rw [hv] at hk
            rw [← Option.some.inj hk]
            rfl
        | some a =>
            rw [hv] at hk
            cases a <;> first
              | (cases hk) | (simp only [keyAt, Option.some.injEq] at hk; rw [← hk]; rfl)
    | false =>
        have hm : nm ∉ KS := of_decide_eq_false hd
        rw [at_joinMap_nmem _ _ hm, at_dropMap_nmem _ hm]

variable (KS)

/-- **The split of a row at the key names.** The rows are the `M` attributes. A value that is no
    map has no key part. -/
def split : Split Attr (KeyPart KS) where
  rows a := ∃ m, a = mA.into m
  drop a := match mA.out a with
    | some m => mA.into (dropMap KS m)
    | none => a
  keep a := (mA.out a).bind (keepMap KS)
  join x y := match mA.out x with
    | some m => mA.into (joinMap KS m y)
    | none => x
  keep_join := by
    rintro x ⟨m, rfl⟩ y
    simp [mA.out_into, keepMap_joinMap]
  drop_join := by
    rintro x ⟨m, rfl⟩ y
    simp [mA.out_into, dropMap_joinMap]
  join_keep := by
    intro a y h
    cases hm : mA.out a with
    | none => simp [hm] at h
    | some m =>
        rw [hm] at h
        have hk : keepMap KS m = some y := h
        simp only [mA.out_into, joinMap_keepMap hk]
        exact (mA.into_out hm).symm

variable {KS}

/-- **A key name that holds an attribute other than `S` gives no key part.** -/
theorem keepMap_none_of_num (m : MapOf Attr) {nm : String} (h : nm ∈ KS) {v : WFNumeral}
    (hv : m.at nm = some (.n v)) : keepMap KS m = none := by
  unfold keepMap
  rw [dif_neg]
  intro hall
  have := hall ⟨nm, h⟩
  simp only [hv, keyAt] at this
  exact nomatch this

/-- **An object that declares no key name writes a row with no key name.** A row of the object is an
    `M` attribute, and the complement of the row is the row. The rest policy refuses an undeclared
    name, so the row holds declared names only. -/
theorem write_row {sems : MapOf FieldSem} (hdisj : ∀ nm ∈ sems.keys, nm ∉ KS) {t r : Value}
    (h : (objectCodec sems Alg.RestSem.refuse).e t = some r) :
    (split KS).rows r ∧ (split KS).drop r = r := by
  obtain ⟨x, y, -, hy, rfl⟩ := Alg.carried_e.mp h
  have hq := Alg.objAt_eq.mp hy
  have hx : ∀ k ∈ x.keys, k ∈ sems.keys := fun k hk =>
    Decidable.byContradiction fun hn => by
      have := hq.1 k (Finset.mem_union.mpr (Or.inr hk))
      rw [MapOf.at_of_mem (m := x) ⟨k, hk⟩] at this
      simp only [Alg.liftTable, Alg.entryCodec, MapOf.at_none hn, Alg.rcOf] at this
      exact nomatch this
  have hyk : ∀ k ∈ y.keys, k ∈ sems.keys := fun k hk =>
    (Finset.mem_union.mp (hq.2 hk)).elim id (hx k)
  refine ⟨⟨y, rfl⟩, ?_⟩
  show mA.into (dropMap KS y) = mA.into y
  congr 1
  exact MapOf.ext_at fun nm => by
    cases hd : decide (nm ∈ KS) with
    | true =>
        have hm : nm ∈ KS := of_decide_eq_true hd
        rw [at_dropMap_mem _ hm, MapOf.at_none fun hk => hdisj nm (hyk nm hk) hm]
    | false => rw [at_dropMap_nmem _ (of_decide_eq_false hd)]

/-- **The derived item of an object codec meets the core laws.** The object has no fill, each field
    is lawful, the rest policy refuses, and no declared name is a key name. The key function is
    free. -/
theorem derive_core_object {sems : MapOf FieldSem} (hnf : Alg.noFill sems = true)
    (hf : ∀ k, Lawful (sems.2 k).codec) (hdisj : ∀ nm ∈ sems.keys, nm ∉ KS)
    (k : Value → KeyPart KS) :
    LawfulCore ((split KS).derive (objectCodec sems Alg.RestSem.refuse) k) :=
  (split KS).derive_core (lawful_objectCodec hnf hf fun _ h => nomatch h) (write_row hdisj)

/-- A pet record with one required string field `name`. The corpus codec of the anchor. -/
def petRecord : Codec :=
  objectCodec ⟨{"name"}, fun _ => Alg.FieldSem.req (baseCodec .string)⟩ Alg.RestSem.refuse

/-- **The derived item of the pet record meets the core laws.** The key names are `PK`, and the
    key function is any function of the pet. -/
theorem petRecord_derive_core (k : Value → KeyPart {"PK"}) :
    LawfulCore ((split {"PK"}).derive petRecord k) :=
  derive_core_object (sems := ⟨{"name"}, fun _ => Alg.FieldSem.req (baseCodec .string)⟩)
    (by decide) (fun _ => lawful_baseCodec _) (by decide) k

end DerivedItem

end Calculus
