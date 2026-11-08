import Calculus.Bridge.KeyRows
import Calculus.Dynamo.Alg.KeyItem

/-!
# The rows of an item with derived keys

The emitter runs the item writer of `src/` on an entry of plain keys and an item. A row holds the keys of
the entry, each with its name, its member (a string or a number) and its key spec as a tree with the
parts that the host evaluated, the printed text of the attributes of the item that the keys read, the
separator, and what the host did: it refused the key, or it wrote the attribute of each key name at
a member, or wrote none where the key is absent. A throw of a key and a refusal as a value are both a
refusal, because the channel of the refusal is no rule of the model.

The comparator gives each key to `DerivedItem.carrierOf` at the member of the row. The model refuses
where one key is refused. Otherwise it gives, for each key name, no attribute where the key is absent,
and the text at the member where the key is built. The row states that the host wrote the attribute
of the same member and the same text at each key name. A member `B` is outside the rows, as it is
outside the model.

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

/-- A row of the item: the name, the keys, the printed text of the attributes that the keys read, the
    separator, and what the host did. -/
structure ItemRow where
  name : String
  keys : List ItemKey
  item : List (String × String)
  sep : Char
  host : HostItem

/-- The item of a row, as the keys read it. -/
def ItemRow.itemOf (r : ItemRow) : Item String := fun n => r.item.lookup n

/-- **The text that a key writes at its member, or a refusal.** The carrier of the key at a string
    member or at a number member, as text. -/
def itemKeyText (V : StringView) (c : Char) (numeric : Bool) (out : Out) :
    Option (Option (Bool × String)) :=
  match numeric with
  | true =>
      (DerivedItem.carrierOf V c .n (by decide) out).map fun v => v.map fun w => (true, w.1)
  | false =>
      (DerivedItem.carrierOf V c .s (by decide) out).map fun v => v.map fun w => (false, w)

/-- What the model gives for a row: a refusal, or the attribute of each key name. -/
def ItemRow.model (V : StringView) (r : ItemRow) : Option (List (String × Option (Bool × String))) :=
  r.keys.mapM fun k =>
    (itemKeyText V r.sep k.numeric (keyOf false false r.itemOf k.spec)).map fun v => (k.name, v)

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
