import Calculus.Alg.Derive
import Calculus.Dynamo.Alg.Frontier

/-!
# The item with derived keys, at the DynamoDB row

A row of an item is the top-level map that an object codec writes: an attribute `M`. The key names
are a finite set `KS`. A key attribute of DynamoDB is `S`, `N` or `B`. The member of a key is a fact
of the key name, so the model takes the member as data: a function `mem` from a key name to `S`, `N`
or `B`. The key part of a row is the value at each key name, or no value where the row lacks the
name. The value is a string at an `S` key, a numeral at an `N` key, and bytes at a `B` key, so a key
part holds no value that the member refuses. A row that holds another member at a key name has no
key part, so `keep` gives `none` there, and the strict read of the graph refuses the row. The read
that deletes the keys still reads the row, because `drop` removes each key name whatever attribute
the name holds. A stale row has the member of its key name and the value of another item, and the
strict read accepts it.

The key part has decidable equality, because `KS` is finite and each carrier has decidable equality.
The carrier `Attr` has none, because `.m` holds a function. So the lens needs no equality on `Attr`.
-/

namespace Calculus

namespace DerivedItem

open Alg

/-- The member of a key attribute: a string, a number, or bytes. -/
inductive Member where
  | s
  | n
  | b
  deriving DecidableEq

/-- The value of a key at a member: a string at `S`, a well-formed numeral at `N`, and bytes at
    `B`. -/
abbrev Member.Carrier : Member → Type
  | .s => String
  | .n => WFNumeral
  | .b => Bytes

instance (m : Member) : DecidableEq m.Carrier :=
  match m with
  | .s => inferInstanceAs (DecidableEq String)
  | .n => inferInstanceAs (DecidableEq WFNumeral)
  | .b => inferInstanceAs (DecidableEq Bytes)

/-- The attribute that carries a key value at its member. -/
def Member.attr : (m : Member) → m.Carrier → Attr
  | .s, v => .s v
  | .n, v => .n v
  | .b, v => .b v

variable (KS : Finset String) (mem : {k // k ∈ KS} → Member)

/-- The key part of a row: at each key name, the value at the member of the name, or no value where
    the row lacks the name. -/
abbrev KeyPart := (k : {k // k ∈ KS}) → Option (mem k).Carrier

/-- **Two key parts are equal where they agree at each key name.** The decision runs over the finite
    key names, with a route that the classical gateways already list. -/
instance : DecidableEq (KeyPart KS mem) := fun y y' =>
  decidable_of_iff (∀ k, y k = y' k) ⟨funext, fun h _ => h ▸ rfl⟩

/-- What an attribute gives to a key part at a member: no attribute gives no value, the attribute of
    the member gives its value, and any other attribute gives no key part. -/
def keyAt : (m : Member) → Option Attr → Option (Option m.Carrier)
  | _, none => some none
  | .s, some (.s v) => some (some v)
  | .n, some (.n v) => some (some v)
  | .b, some (.b v) => some (some v)
  | _, some _ => none

/-- **A key value written at its member reads back.** -/
theorem keyAt_attr (m : Member) (v : Option m.Carrier) : keyAt m (v.map m.attr) = some v := by
  cases m <;> cases v <;> rfl

/-- **An attribute that gives a key value is the attribute of that value.** -/
theorem attr_of_keyAt {m : Member} {a : Option Attr} {v : Option m.Carrier}
    (h : keyAt m a = some v) : v.map m.attr = a := by
  cases m <;> cases a with
  | none => cases h; rfl
  | some a => cases a <;> first | (cases h; rfl) | (cases h)

/-- The map without the key names. -/
def dropMap (m : MapOf Attr) : MapOf Attr := m.keep fun nm => decide (nm ∉ KS)

/-- The map that holds the values of a key part at the key names, each at its member. -/
def keysMap (y : KeyPart KS mem) : MapOf Attr :=
  MapOf.ofFun KS fun nm => if h : nm ∈ KS then (y ⟨nm, h⟩).map (mem ⟨nm, h⟩).attr else none

/-- The map with a key part: the values of the key part, and the other names of the map. -/
def joinMap (x : MapOf Attr) (y : KeyPart KS mem) : MapOf Attr :=
  (keysMap KS mem y).union (dropMap KS x)

/-- The key part of a map, or none where a key name holds a member other than its own. -/
def keepMap (m : MapOf Attr) : Option (KeyPart KS mem) :=
  if h : ∀ k : {k // k ∈ KS}, (keyAt (mem k) (m.at k.1)).isSome then
    some fun k => (keyAt (mem k) (m.at k.1)).get (h k)
  else none

variable {KS} {mem}

/-- A key name has no value in a map without the key names. -/
theorem at_dropMap_mem (m : MapOf Attr) {nm : String} (h : nm ∈ KS) : (dropMap KS m).at nm = none :=
  MapOf.at_keep_neg m (by simp [h])

/-- A name that is no key name keeps its value in a map without the key names. -/
theorem at_dropMap_nmem (m : MapOf Attr) {nm : String} (h : nm ∉ KS) :
    (dropMap KS m).at nm = m.at nm :=
  MapOf.at_keep_pos m (by simp [h])

/-- The map of a key part holds the value of the key part at a key name, at the member of the name. -/
theorem at_keysMap_mem (y : KeyPart KS mem) {nm : String} (h : nm ∈ KS) :
    (keysMap KS mem y).at nm = (y ⟨nm, h⟩).map (mem ⟨nm, h⟩).attr := by
  unfold keysMap
  rw [MapOf.at_ofFun (fun k hk => by simp [hk]), dif_pos h]

/-- The map of a key part holds nothing at a name that is no key name. -/
theorem at_keysMap_nmem (y : KeyPart KS mem) {nm : String} (h : nm ∉ KS) :
    (keysMap KS mem y).at nm = none := by
  unfold keysMap
  rw [MapOf.at_ofFun (fun k hk => by simp [hk]), dif_neg h]

/-- A joined map holds the value of the key part at a key name, at the member of the name. -/
theorem at_joinMap_mem (x : MapOf Attr) (y : KeyPart KS mem) {nm : String} (h : nm ∈ KS) :
    (joinMap KS mem x y).at nm = (y ⟨nm, h⟩).map (mem ⟨nm, h⟩).attr := by
  rw [joinMap, MapOf.at_union, at_keysMap_mem y h, at_dropMap_mem x h]
  cases y ⟨nm, h⟩ <;> rfl

/-- A joined map keeps the value of the first map at a name that is no key name. -/
theorem at_joinMap_nmem (x : MapOf Attr) (y : KeyPart KS mem) {nm : String} (h : nm ∉ KS) :
    (joinMap KS mem x y).at nm = x.at nm := by
  rw [joinMap, MapOf.at_union, at_keysMap_nmem y h, at_dropMap_nmem x h]
  rfl

/-- **PutGet at the map.** The key part of a joined map is the part that the join put. -/
theorem keepMap_joinMap (x : MapOf Attr) (y : KeyPart KS mem) :
    keepMap KS mem (joinMap KS mem x y) = some y := by
  have key : ∀ k : {k // k ∈ KS}, keyAt (mem k) ((joinMap KS mem x y).at k.1) = some (y k) :=
    fun k => by
      rw [at_joinMap_mem x y k.2]
      exact keyAt_attr (mem k) (y k)
  unfold keepMap
  rw [dif_pos (fun k => by rw [key k]; rfl)]
  exact congrArg some (funext fun k => by simp [key k])

/-- **The complement is unchanged by a join.** -/
theorem dropMap_joinMap (x : MapOf Attr) (y : KeyPart KS mem) :
    dropMap KS (joinMap KS mem x y) = dropMap KS x :=
  MapOf.ext_at fun nm => by
    cases h : decide (nm ∈ KS) with
    | true =>
        have hm : nm ∈ KS := of_decide_eq_true h
        rw [at_dropMap_mem _ hm, at_dropMap_mem _ hm]
    | false =>
        have hm : nm ∉ KS := of_decide_eq_false h
        rw [at_dropMap_nmem _ hm, at_dropMap_nmem _ hm, at_joinMap_nmem _ _ hm]

/-- A key part of a map is the value of the map at each key name, at the member of the name. -/
theorem keepMap_spec {m : MapOf Attr} {y : KeyPart KS mem} (h : keepMap KS mem m = some y) :
    ∀ k : {k // k ∈ KS}, keyAt (mem k) (m.at k.1) = some (y k) := by
  unfold keepMap at h
  split at h
  · next hall =>
      cases h
      intro k
      exact (Option.some_get (hall k)).symm
  · exact nomatch h

/-- **GetPut at the map.** A map with a key part is its complement joined to the key part. -/
theorem joinMap_keepMap {m : MapOf Attr} {y : KeyPart KS mem} (h : keepMap KS mem m = some y) :
    joinMap KS mem (dropMap KS m) y = m :=
  MapOf.ext_at fun nm => by
    cases hd : decide (nm ∈ KS) with
    | true =>
        have hm : nm ∈ KS := of_decide_eq_true hd
        rw [at_joinMap_mem _ _ hm]
        exact attr_of_keyAt (keepMap_spec h ⟨nm, hm⟩)
    | false =>
        have hm : nm ∉ KS := of_decide_eq_false hd
        rw [at_joinMap_nmem _ _ hm, at_dropMap_nmem _ hm]

variable (KS) (mem)

/-- **The split of a row at the key names.** The rows are the `M` attributes. A value that is no
    map has no key part. -/
def split : Split Attr (KeyPart KS mem) where
  rows a := ∃ m, a = mA.into m
  drop a := match mA.out a with
    | some m => mA.into (dropMap KS m)
    | none => a
  keep a := (mA.out a).bind (keepMap KS mem)
  join x y := match mA.out x with
    | some m => mA.into (joinMap KS mem m y)
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
        have hk : keepMap KS mem m = some y := h
        simp only [mA.out_into, joinMap_keepMap hk]
        exact (mA.into_out hm).symm

variable {KS} {mem}

/-- **A key name that holds another member than its own gives no key part.** The row is stale in the
    member, so the strict read refuses it, and the read that deletes the key part reads it. -/
theorem keepMap_none_of_mismatch (m : MapOf Attr) {nm : String} (h : nm ∈ KS) {a : Attr}
    (hv : m.at nm = some a) (hk : keyAt (mem ⟨nm, h⟩) (some a) = none) :
    keepMap KS mem m = none := by
  unfold keepMap
  rw [dif_neg]
  intro hall
  have := hall ⟨nm, h⟩
  simp only [hv, hk] at this
  exact nomatch this

/-- **An `S` key name that holds a number gives no key part.** -/
theorem keepMap_none_of_num (m : MapOf Attr) {nm : String} (h : nm ∈ KS)
    (hs : mem ⟨nm, h⟩ = .s) {v : WFNumeral} (hv : m.at nm = some (.n v)) :
    keepMap KS mem m = none :=
  keepMap_none_of_mismatch m h hv (by rw [hs]; rfl)

/-- **An `N` key name that holds a string gives no key part.** -/
theorem keepMap_none_of_str (m : MapOf Attr) {nm : String} (h : nm ∈ KS)
    (hn : mem ⟨nm, h⟩ = .n) {v : String} (hv : m.at nm = some (.s v)) :
    keepMap KS mem m = none :=
  keepMap_none_of_mismatch m h hv (by rw [hn]; rfl)

/-- **An object that declares no key name writes a row with no key name.** A row of the object is an
    `M` attribute, and the complement of the row is the row. The rest policy refuses an undeclared
    name, so the row holds declared names only. -/
theorem write_row {sems : MapOf FieldSem} (hdisj : ∀ nm ∈ sems.keys, nm ∉ KS) {t r : Value}
    (h : (objectCodec sems Alg.RestSem.refuse).e t = some r) :
    (split KS mem).rows r ∧ (split KS mem).drop r = r := by
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
    (k : Value → KeyPart KS mem) :
    LawfulCore ((split KS mem).derive (objectCodec sems Alg.RestSem.refuse) k) :=
  (split KS mem).derive_core (lawful_objectCodec hnf hf fun _ h => nomatch h) (write_row hdisj)

/-- **A row of an item with a stale key part reads as the item, at any member.** The row joins the row
    of the item to any key part, and the key part holds the member of each key name. -/
theorem derive_object_stale {sems : MapOf FieldSem} (hnf : Alg.noFill sems = true)
    (hf : ∀ k, Lawful (sems.2 k).codec) (hdisj : ∀ nm ∈ sems.keys, nm ∉ KS)
    (k : Value → KeyPart KS mem) {t r : Value}
    (he : (objectCodec sems Alg.RestSem.refuse).e t = some r) (y : KeyPart KS mem) :
    ((split KS mem).derive (objectCodec sems Alg.RestSem.refuse) k).p ((split KS mem).join r y) =
      some t :=
  Alg.Split.derive_p_stale (s := split KS mem) (c := objectCodec sems Alg.RestSem.refuse) (k := k)
    (lawful_objectCodec (rest := Alg.RestSem.refuse) hnf hf fun _ h => nomatch h) (write_row hdisj)
    he y

/-- **A row that holds another member at a key name reads through the complement.** The row has no key
    part, so the strict read of the graph refuses it, and the read that deletes the key names reads
    the outside part. -/
theorem derive_p_mismatch {c : Codec} {k : Value → KeyPart KS mem} {m : MapOf Attr} {v : Value}
    (h : keepMap KS mem m = none) :
    ((split KS mem).derive c k).p (mA.into m) = some v ↔
      c.p (mA.into (dropMap KS m)) = some v ∧ (((split KS mem).graph c k).e v).isSome := by
  have hk : (split KS mem).keep (mA.into m) = none := by simp [split, mA.out_into, h]
  have := Alg.Split.derive_p_no_keypart (s := split KS mem) (c := c) (k := k) (v := v) hk
  simpa [split, mA.out_into] using this

/-- A pet record with one required string field `name`. The corpus codec of the anchor. -/
def petRecord : Codec :=
  objectCodec ⟨{"name"}, fun _ => Alg.FieldSem.req (baseCodec .string)⟩ Alg.RestSem.refuse

/-- The members of a pet row: `PK` is a string, and `SK`, the number that orders the pets of one
    partition, is a number. -/
def petMember : {k // k ∈ ({"PK", "SK"} : Finset String)} → Member := fun k =>
  if k.1 = "SK" then .n else .s

/-- **The derived item of the pet record meets the core laws.** The key names are `PK`, a string key,
    and `SK`, a number key, and the key function is any function of the pet. The theorem holds a row
    with an `N` key. -/
theorem petRecord_derive_core (k : Value → KeyPart {"PK", "SK"} petMember) :
    LawfulCore ((split {"PK", "SK"} petMember).derive petRecord k) :=
  derive_core_object (sems := ⟨{"name"}, fun _ => Alg.FieldSem.req (baseCodec .string)⟩)
    (by decide) (fun _ => lawful_baseCodec _) (by decide) k

/-- **A pet row with a number sort key reads back its key part.** The key part holds a string at `PK`
    and a numeral at `SK`, and the row that joins the part to a row reads back the part. -/
theorem petRecord_keepMap_joinMap (x : MapOf Attr) (y : KeyPart {"PK", "SK"} petMember) :
    keepMap {"PK", "SK"} petMember (joinMap {"PK", "SK"} petMember x y) = some y :=
  keepMap_joinMap x y

end DerivedItem

end Calculus
