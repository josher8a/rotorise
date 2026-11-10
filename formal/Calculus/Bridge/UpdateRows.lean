import Calculus.Bridge.Verdicts
import Calculus.Dynamo.Alg.KeyUpdate
import Calculus.Bridge.ItemRows

/-!
# The rows of a key update

The emitter runs keyUpdates and keyComponents of `src/` on the keys of a schema, the values that
the codec decides, and a change. A row holds the keys as trees with the member of each key (a string
or a number) and the footprint that the host read at the given item, the decided values, the change,
the separator, and what the host gave: a refusal of one of three kinds, or a patch of the touched
keys, where each written key is the attribute at a member with a text, and a removed key has no
value. The comparator reads the footprint of each key at the given item (`Tree.foot`), and states
that the update of the model (`update`) gives the result of the host. The update prints each key at
the member of the key, as `DerivedItem.keyPartOf` does, so a row with a number key holds the host
to the member that the item writer of `src/` writes. The update and the item agree on the key
part: where `update` gives a patch, each entry is the rendered component of the key part of the
changed item (`update_keyPart`), at the member of the key name.

A part of a row names the attribute that it reads, and prints the value as the plain component of
the host does: the upper case name, then the value. A change writes a value or removes the attribute.
A part with a transform or a tag is outside the rows. A name is a path of names joined by `.`, and
the model reads it through `PathName`: a write to a path reaches the paths above it and the paths
below it, as the host reads it.
-/

namespace Calculus

namespace DerivedKey

/-- **The order of the names of a row.** A name is a path of names joined by `.`. A path is above
    another where the characters of the first, and one `.`, begin the characters of the second. The
    host refuses an empty name, so the prefix at a `.` is the prefix of the lists of names. A row
    reads the characters of a string, so this instance is in the host bridge, and the key update
    reads no string. -/
instance : PathName String where
  pre m n := decide (m.toList = n.toList) || (m.toList ++ ['.']).isPrefixOf n.toList
  pre_refl n := by
    rw [show decide (n.toList = n.toList) = true from decide_eq_true rfl]
    rfl

/-- The key of an item as the host gives it to a patch: a printed key at the member of the key
    (`false` for a string, `true` for a number), no key, or a throw. The host throws where a segment
    holds the separator, where the spec selects nothing, and where the text of a number key is no
    numeral. -/
def Out.written (c : Char) (numeric : Bool) (o : Out) : Option (Option (Bool × String)) :=
  (DerivedItem.carrierOf libraryView c (memberOfNumeric numeric) (memberOfNumeric_ne_b numeric) o).map
    (renderKey (memberOfNumeric numeric))

/-- A key of the schema, as the host read it: the name, whether the member is a number, the tree of
    the spec, whether the key addresses the table, and the footprint that the host read at the given
    item. -/
structure UpdateKey where
  name : String
  numeric : Bool
  tree : Tree String
  ofTable : Bool
  footprint : List String

/-- What the host did with an update. A refusal is of one kind: the change writes a decided
    attribute at another value, the change touches a key that it cannot rewrite, or the build of a
    key throws. A patch holds, for a key that it writes, the attribute at a member (`false` for a
    string, `true` for a number) with a text, or none where the key is removed. -/
inductive HostUpdate where
  | decided
  | rewrite
  | unbuilt
  | patch (entries : List (String × Option (Bool × String)))
  deriving DecidableEq

/-- A row of the key update. -/
structure UpdateRow where
  name : String
  keys : List UpdateKey
  decided : List (String × String)
  changed : List (String × Option String)
  sep : Char
  host : HostUpdate

/-- The keys of a row, as the model reads them. -/
def UpdateRow.keyDefs (r : UpdateRow) : List (KeyDef String Bool) :=
  r.keys.map fun k => KeyDef.ofTree k.name k.numeric k.tree k.ofTable

/-- What the model gives for a row. -/
def UpdateRow.model (r : UpdateRow) : HostUpdate :=
  match update (Out.written r.sep) r.keyDefs r.decided r.changed with
  | .refused .decided => .decided
  | .refused (.rewrite _) => .rewrite
  | .refused (.unbuilt _) => .unbuilt
  | .patch p => .patch p

/-- The names of two lists are the same set. -/
def sameNames (a b : List String) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-- The footprint that the host read at the given item, against the footprint of the model. -/
def UpdateRow.footOk (r : UpdateRow) : Bool :=
  let g : Item String := given (fun n => r.decided.lookup n) ⟨r.changed⟩
  r.keys.all fun k => sameNames k.footprint (k.tree.foot g)

/-- The comparator of a row: the footprints are the host's, and the result is the host's. -/
def updateRowOk (r : UpdateRow) : Bool := r.footOk && decide (r.model = r.host)

/-- **A row that passes states what the host did.** The footprint of each key at the given item is
    the set that the host read, and the update of the model gives the result of the host. -/
theorem updateRowOk_iff (r : UpdateRow) : updateRowOk r = true ↔
    r.footOk = true ∧ r.model = r.host := by
  simp [updateRowOk]

/-- The names of the rows that fail. -/
def failingUpdates (rows : List UpdateRow) : List String :=
  (rows.filter fun r => !updateRowOk r).map UpdateRow.name

/-- **A list with no failing row passes at each row.** -/
theorem updateRowOk_of_failing {rows : List UpdateRow} (h : failingUpdates rows = []) :
    ∀ r ∈ rows, updateRowOk r = true := fun r hr =>
  Bool.eq_false_imp_eq_true.mp fun hq => absurd
    ((congrArg (r.name ∈ ·) h).mp
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, by rw [hq]; rfl⟩)))
    List.not_mem_nil

section Connect

variable {KS : Finset String} {mem : {k // k ∈ KS} → DerivedItem.Member}
  (hb : ∀ k, mem k ≠ DerivedItem.Member.b) (c : Char) (specs : {k // k ∈ KS} → KeySpec String)

/-- **A key of the schema is at a key name of the key part.** The name is a key name, the spec of
    the name is the spec of the key, and the member of the name is the member of the key. -/
def KeyDef.AtKeyName (k : KeyDef String Bool) : Prop :=
  ∃ h : k.name ∈ KS, specs ⟨k.name, h⟩ = k.spec ∧ mem ⟨k.name, h⟩ = memberOfNumeric k.mem

/-- **Two reads at one member are one read.** The printed key at the member `m`, and the component
    of the key part at the member `m'`, agree where `m = m'`. -/
theorem render_get_eq {m m' : DerivedItem.Member} (e : m = m') (hm : m ≠ DerivedItem.Member.b)
    (hm' : m' ≠ DerivedItem.Member.b) (o : Out) {w : Option (Bool × String)}
    (hh : (DerivedItem.carrierOf libraryView c m' hm' o).isSome = true)
    (h : (DerivedItem.carrierOf libraryView c m hm o).map (renderKey m) = some w) :
    renderKey m' ((DerivedItem.carrierOf libraryView c m' hm' o).get hh) = w := by
  subst e
  have e' : hm' = hm := rfl
  subst e'
  revert hh
  cases hc : DerivedItem.carrierOf libraryView c m hm' o with
  | none => rw [hc] at h; cases h
  | some z =>
      rw [hc] at h
      intro hh
      simpa [Option.map] using Option.some.inj h

/-- **The patch is the key part of the changed item.** Where `update` gives the patch `P`, and the
    key part of the changed item exists, each entry of `P` is the rendered component of the key part at
    the name of its key. A key outside `P` has the component of the key part of the first item. The
    premises are the three of `update_commute`, and that each key of the schema is at a key name of
    the key part (`KeyDef.AtKeyName`). -/
theorem update_keyPart {keys : List (KeyDef String Bool)} {dec : List (String × String)}
    {ch : List (String × Option String)} {P : List (String × Option (Bool × String))}
    (hnd : (keys.map KeyDef.name).Nodup) (hP : update (Out.written c) keys dec ch = .patch P)
    {x : Item String} (hx : ∀ n v, dec.lookup n = some v → x n = some v)
    (ht : ∀ k ∈ keys, KeyDef.AtKeyName (mem := mem) specs k)
    {kp : DerivedItem.KeyPart KS mem}
    (hk : DerivedItem.keyPartOf libraryView hb c specs
      (applied (fun n => dec.lookup n) ⟨ch⟩ x) = some kp) :
    ∀ k ∈ keys, ∀ h : k.name ∈ KS,
      (∀ v, (k.name, v) ∈ P → v = renderKey (mem ⟨k.name, h⟩) (kp ⟨k.name, h⟩)) ∧
      ((∀ v, (k.name, v) ∉ P) → ∀ kx, DerivedItem.keyPartOf libraryView hb c specs x = some kx →
        kp ⟨k.name, h⟩ = kx ⟨k.name, h⟩) := by
  intro k hkk h
  obtain ⟨h', hsp, hmem⟩ := ht k hkk
  have e0 : h' = h := rfl
  subst e0
  have hcom := update_commute hnd hP hx k hkk
  unfold DerivedItem.keyPartOf at hk
  split at hk
  next hall =>
    have hkp := congrFun (Option.some.inj hk) ⟨k.name, h'⟩
    refine ⟨fun v hv => ?_, fun hnot kx hkx => ?_⟩
    · have this := hcom.1 v hv
      rw [← hsp] at this
      unfold Out.written at this
      rw [← hkp]
      exact (render_get_eq c hmem.symm (memberOfNumeric_ne_b _) (hb _) _ (hall _) this).symm
    · unfold DerivedItem.keyPartOf at hkx
      split at hkx
      next hall' =>
        have hkx' := congrFun (Option.some.inj hkx) ⟨k.name, h'⟩
        have e : keyOf false false (applied (fun n => dec.lookup n) ⟨ch⟩ x) (specs ⟨k.name, h'⟩) =
            keyOf false false x (specs ⟨k.name, h'⟩) := by
          rw [hsp]; exact hcom.2 hnot
        rw [← hkp, ← hkx']
        have key : ∀ o o' : Out, o = o' →
            ∀ (h1 : (DerivedItem.carrierOf libraryView c (mem ⟨k.name, h'⟩) (hb _) o).isSome = true)
              (h2 : (DerivedItem.carrierOf libraryView c (mem ⟨k.name, h'⟩) (hb _) o').isSome = true),
            (DerivedItem.carrierOf libraryView c (mem ⟨k.name, h'⟩) (hb _) o).get h1 =
              (DerivedItem.carrierOf libraryView c (mem ⟨k.name, h'⟩) (hb _) o').get h2 := by
          intro o o' e'; subst e'; intros; rfl
        exact key _ _ e _ _
      next => cases hkx
  next => cases hk

end Connect

end DerivedKey

end Calculus
