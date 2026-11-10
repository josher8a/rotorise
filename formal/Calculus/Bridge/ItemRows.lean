import Calculus.Bridge.KeyRows
import Calculus.Dynamo.Alg.KeyItem

/-!
# The rows of an item with derived keys

The emitter runs the item writer of `src/` on an entry of plain keys and an item. A row holds the
keys of the entry, each with its name, its member (a string or a number) and its key spec as a tree,
the value of the item as a map of attributes, the separator, and what the host did: it refused a key
by a throw, or it wrote the attribute of each key name at a member, or wrote none where the key is
absent. A plain component of a leaf is a `Part.named` with the name of the attribute and a label that
the emitter gives as text. The model evaluates the part at the item, so the empty rule and the read of
a path are in the model, and the host gives only the outcome. A refusal as a returned value is outside the rows: the emitter skips that row, and a test
counts the rows that a throw refuses, so a move of the channel fails that test.

The comparator reads `DerivedItem.keyPartOf` over `DerivedItem.itemOf` of the value of the row, at
the member of each key. The model refuses where one key is refused. Otherwise it gives, for each key
name, no attribute where the key is absent, and the text at the member where the key is built. The row
states that the host wrote the attribute of the same member and the same text at each key name. A
member `B` is outside the rows, as it is outside the model.

A row is read through a view of the strings, as the key codec is. The view of the library is
`libraryView`, `String.toList` with `String.ofList`.
-/

namespace Calculus

namespace DerivedKey

/-- **The view of the strings of the library**: `String.toList` with `String.ofList`. The key codec
    reads a string through a view, and a row is checked at this one. The two cancellation facts are
    core theorems that reach `Classical.choice`, and the list of classical gateways names them. -/
def libraryView : StringView where
  chars := String.toList
  str := String.ofList
  chars_str := fun _ => String.toList_ofList
  str_chars := fun _ => String.ofList_toList

/-- **A plain component of a leaf**: the attribute that it reads, and the label that it prints. An
    absent value and the empty text are an absent part, as the host gives no component
    for either. Any other text is the component at the label. The label is an emitted text: the
    model needs no case rule on a string. -/
def Part.named (n label : String) : Part String :=
  ⟨some n, fun v => match v with
    | none => none
    | some t => if t = "" then none else some (Comp.named label t)⟩

/-- What the host did for an item: it refused a key, or it wrote, at each key name, no attribute or an
    attribute at a member (`false` for a string, `true` for a number) with a text. -/
inductive HostItem where
  | refused
  | written (attrs : List (String × Option (Bool × String)))

/-- A key of the entry: the name, whether the member is a number, and the key spec. -/
structure ItemKey where
  name : String
  numeric : Bool
  spec : KeySpec String

/-- A row of the item: the name, the keys, the value of the item as a map of attributes, the
    separator, and what the host did. -/
structure ItemRow where
  name : String
  keys : List ItemKey
  value : Value
  sep : Char
  host : HostItem

/-- The names of a list, without a repeat. -/
def nameSet (l : List String) : Finset String := ⟨(l.dedup : Multiset String), l.nodup_dedup⟩

/-- The map value of named attributes. -/
def mapValue (pairs : List (String × Attr)) : Value :=
  mA.into (MapOf.ofFun (nameSet (pairs.map Prod.fst)) fun nm => pairs.lookup nm)

/-- The member of a key: a number, or a string. A member `B` is outside the rows. -/
def memberOfNumeric : Bool → DerivedItem.Member
  | true => .n
  | false => .s

/-- **A member of a row is no `B`.** -/
theorem memberOfNumeric_ne_b (b : Bool) : memberOfNumeric b ≠ .b := by
  cases b <;> simp [memberOfNumeric]

/-- The key of a row at a name, or none. -/
def ItemRow.keyAt (r : ItemRow) (name : String) : Option ItemKey :=
  r.keys.find? fun k => k.name == name

/-- The names of the keys of a row. -/
def ItemRow.names (r : ItemRow) : Finset String := nameSet (r.keys.map ItemKey.name)

/-- The member of a key name of a row: a number where the key says so. -/
def ItemRow.mem (r : ItemRow) : {k // k ∈ r.names} → DerivedItem.Member :=
  fun k => memberOfNumeric ((r.keyAt k.1).any ItemKey.numeric)

/-- The key spec of a key name of a row. -/
def ItemRow.specs (r : ItemRow) : {k // k ∈ r.names} → KeySpec String :=
  fun k => ((r.keyAt k.1).map ItemKey.spec).getD (.arm .missing)

/-- The text of a key part at its member: no key is none, a string is the text, and a number is the
    numeral. -/
def renderKey : (m : DerivedItem.Member) → Option m.Carrier → Option (Bool × String)
  | .s, v => v.map fun w => (false, w)
  | .n, v => v.map fun w => (true, w.1)
  | .b, _ => none

/-- **What the model gives for a row**: the key part that `DerivedItem.keyPartOf` builds over the
    item that `DerivedItem.itemOf` reads from the value of the row, or a refusal. Each key name is
    rendered at its member. -/
def ItemRow.model (V : StringView) (r : ItemRow) :
    Option (List (String × Option (Bool × String))) :=
  (DerivedItem.keyPartOf V (mem := r.mem) (fun k => memberOfNumeric_ne_b _) r.sep r.specs
      (DerivedItem.itemOf r.value)).map fun kp =>
    r.keys.map fun k =>
      (k.name, if h : k.name ∈ r.names then renderKey (r.mem ⟨k.name, h⟩) (kp ⟨k.name, h⟩) else none)

/-- **The comparator of an item row.** The host refused where the model refuses, and wrote the
    attributes that the model gives. -/
def itemRowOk (V : StringView) (r : ItemRow) : Bool :=
  match r.host, r.model V with
  | .refused, none => true
  | .written a, some b => decide (a = b)
  | _, _ => false

/-- The names of the rows that fail. -/
def failingItems (V : StringView) (rows : List ItemRow) : List String :=
  (rows.filter fun r => !itemRowOk V r).map ItemRow.name

/-- **A list with no failing row passes at each row.** -/
theorem itemRowOk_of_failing {V : StringView} {rows : List ItemRow}
    (h : failingItems V rows = []) : ∀ r ∈ rows, itemRowOk V r = true := fun r hr =>
  Bool.eq_false_imp_eq_true.mp fun hq => absurd
    ((congrArg (r.name ∈ ·) h).mp
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, by rw [hq]; rfl⟩)))
    List.not_mem_nil

end DerivedKey

end Calculus
