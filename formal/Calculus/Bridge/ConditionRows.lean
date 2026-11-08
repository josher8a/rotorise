import Calculus.Bridge.KeyRows
import Calculus.Dynamo.Alg.KeyCondition

/-!
# The rows of a sort condition

The emitter runs the condition builder of `src/` on a sort key of plain components and an
item. A row holds the length of the spec, the parts that the host evaluated for
the item, the separator, and what the host gave: no condition, a refusal, the equality on the whole
key, or the prefix of the leading parts with the boundary. The comparator gives the row to
`DerivedKey.condition`. The model gives no condition where no part is given, a refusal where a part
prints after an absent part, the equality where every part is given, and the prefix otherwise. The
key text of an equality or a prefix is the join of the model's segments. A value that holds the
separator is a throw of the host before the condition, so a row of a condition holds none.
-/

namespace Calculus

namespace DerivedKey

/-- What the host gave for a condition: no condition, a refusal, the equality on a key, or the
    prefix match on a key. -/
inductive HostCondition where
  | nothing
  | refused
  | equals (k : String)
  | prefix (k : String)

/-- A row of the condition builder: the name, the length of the spec, the parts that the host
    evaluated for the item, the separator, and what the host gave. -/
structure ConditionRow where
  name : String
  full : Nat
  parts : List (Option Comp)
  sep : Char
  host : HostCondition

/-- What the model gives for a row. -/
def ConditionRow.out (r : ConditionRow) : Cond := condition r.full r.parts

/-- **The comparator of a condition row.** The host gave no condition where the model gives none,
    a refusal where the model refuses, and a key where the model gives segments of the same kind
    whose join is that key and that hold no separator. -/
def conditionRowOk (r : ConditionRow) : Bool :=
  match r.host, r.out with
  | .nothing, .nothing => true
  | .refused, .refused => true
  | .equals k, .equals ss =>
      !holdsSep r.sep (charSegs ss) && join r.sep (charSegs ss) == k.toList
  | .prefix k, .prefix ss =>
      !holdsSep r.sep (charSegs ss) && join r.sep (charSegs ss) == k.toList
  | _, _ => false

/-- The names of the rows that fail. -/
def failingConditions (rows : List ConditionRow) : List String :=
  (rows.filter fun r => !conditionRowOk r).map ConditionRow.name

/-- **A list with no failing row passes at each row.** -/
theorem conditionRowOk_of_failing {rows : List ConditionRow} (h : failingConditions rows = []) :
    ∀ r ∈ rows, conditionRowOk r = true := fun r hr =>
  Bool.eq_false_imp_eq_true.mp fun hq => absurd
    ((congrArg (r.name ∈ ·) h).mp
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, by rw [hq]; rfl⟩)))
    List.not_mem_nil

end DerivedKey

end Calculus
