import Calculus.Bridge.Verdicts
import Calculus.Dynamo.Alg.KeyUpdate

/-!
# The rows of a key update

The emitter runs keyUpdates and keyComponents of `src/` on the keys of a schema, the values that
the codec decides, and a change. A row holds the keys as trees with the footprint that the host read
at the given item, the decided values, the change, the separator, and what the host gave: a refusal
of one of three kinds, or a patch of the touched keys, where a removed key has no value. The
comparator reads the footprint of each key at the given item (`Tree.foot`), and states that the
update of the model (`update`) gives the result of the host.

A part of a row names the attribute that it reads, and prints the value as the plain component of
the host does: the upper case name, then the value. A part with a transform, a tag or a path of
names is outside the rows. The host reads a path by a prefix of names, and the model reads a name as
one opaque symbol.
-/

namespace Calculus

namespace DerivedKey

/-- The key of an item as the host gives it to a patch: a printed key, no key, or a throw. The host
    throws where a segment holds the separator, and where the spec selects nothing. -/
def Out.written (c : Char) : Out → Option (Option String)
  | .refused => none
  | .nothing => some none
  | .raw k => some (some k)
  | .segs ss =>
      if ss.any (fun s => s.toList.contains c) then none
      else some (some (String.ofList (join c (charSegs ss))))

/-- A plain component of a leaf: the attribute that it reads, and the label that it prints. -/
def Part.named (n label : String) : Part String := ⟨some n, fun v => v.map (Comp.named label)⟩

/-- A key of the schema, as the host read it: the name, the tree of the spec, whether the key
    addresses the table, and the footprint that the host read at the given item. -/
structure UpdateKey where
  name : String
  tree : Tree String
  ofTable : Bool
  footprint : List String

/-- What the host did with an update. A refusal is of one kind: the change writes a decided
    attribute at another value, the change touches a key that it cannot rewrite, or the build of a
    key throws. -/
inductive HostUpdate where
  | decided
  | rewrite
  | unbuilt
  | patch (entries : List (String × Option String))
  deriving DecidableEq

/-- A row of the key update. -/
structure UpdateRow where
  name : String
  keys : List UpdateKey
  decided : List (String × String)
  changed : List (String × String)
  sep : Char
  host : HostUpdate

/-- The keys of a row, as the model reads them. -/
def UpdateRow.keyDefs (r : UpdateRow) : List (KeyDef String) :=
  r.keys.map fun k => KeyDef.ofTree k.name k.tree k.ofTable

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
  let g : Item String := given (fun n => r.decided.lookup n) (fun n => r.changed.lookup n)
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

end DerivedKey

end Calculus
