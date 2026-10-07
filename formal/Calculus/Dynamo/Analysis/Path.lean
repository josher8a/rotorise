import Calculus.Dynamo.Analysis.Slice
import Calculus.Lang.Path

/-!
# The frontier of a path at DynamoDB, and narrowing against the slice

Each vector reduces in the kernel. A frontier is the shape of each term at the path, or a refusal.
The store refuses a name on a list and a position on a map. A refinement refuses a path, because
the frontier cannot carry its predicate. A position past the prefix of a list shape with a suffix
is a refusal, because the codec of the position depends on the length.

Narrowing keeps each option that the clause meets, and the slice keeps each option that the clause
describes. On a union whose options pin one tag each, the two agree.
-/

namespace Calculus

/-- The shape of a frontier: `none` is a refusal, and each frame is tested against a term. -/
private def frontierShapes (r : Option (List (Alg.Frame dynSyn))) (ts : List Term) :
    Option (List Bool) :=
  r.map fun fs => (fs.zip ts).map (fun p => p.1.1.sameShape p.2) ++
    (if fs.length = ts.length then [] else [false])

private abbrev litS (s : String) : Term := .literal .string s

/-- A union under `m`, whose option `B` declares no `only`. -/
private abbrev optA : Term := .object (.mk {"tag", "only"}
  (fun k => if k.1 = "tag" then .req (litS "A") else .req .number) none)
private abbrev optB : Term := .object (.mk {"tag", "shared"}
  (fun k => if k.1 = "tag" then .req (litS "B") else .req .string) none)
private abbrev itemM : Term := .object (.mk {"m"} (fun _ => .req (.union [optA, optB])) none)

-- the frontier at `m.only` is `[number, never]`: `B` reads maps and refuses `only`
example : frontierShapes (Alg.Term.at (S := dynSyn) itemM [.name "m", .name "only"])
    [.number, .never] = some [true, true] := by decide

-- a name on a list: the store refuses the name on every list, so the frontier is empty
private abbrev itemL : Term := .object (.mk {"xs"} (fun _ => .req (.list [] (some .string) [])) none)
example : frontierShapes (Alg.Term.at (S := dynSyn) itemL [.name "xs", .name "foo"]) [] = some [] := by
  decide
-- a position past the prefix with no suffix is the spread
example : frontierShapes (Alg.Term.at (S := dynSyn) itemL [.name "xs", .pos 7]) [.string] =
    some [true] := by decide
-- a position past the prefix with a suffix is a refusal
private abbrev itemS : Term :=
  .object (.mk {"xs"} (fun _ => .req (.list [.number] (some .string) [.boolean])) none)
example : frontierShapes (Alg.Term.at (S := dynSyn) itemS [.name "xs", .pos 1]) [] = none := by
  decide
example : frontierShapes (Alg.Term.at (S := dynSyn) itemS [.name "xs", .pos 0]) [.number] =
    some [true] := by decide

-- a union of a string and an object: the string option reads no map, so the store refuses
private abbrev itemU : Term := .object (.mk {"m"} (fun _ => .req (.union [.string,
  .object (.mk {"x"} (fun _ => .req .number) none)])) none)
example : frontierShapes (Alg.Term.at (S := dynSyn) itemU [.name "m", .name "x"]) [.number] =
    some [true] := by decide

-- a refinement refuses the path
private abbrev itemR : Term := .object (.mk {"r"} (fun _ => .req (.refine
  (.object (.mk {"x"} (fun _ => .req .number) none)) (.closure fun _ => true) ())) none)
example : frontierShapes (Alg.Term.at (S := dynSyn) itemR [.name "r", .name "x"]) [] = none := by
  decide

-- the path of no segment is the term
example : frontierShapes (Alg.Term.at (S := dynSyn) itemL []) [itemL] = some [true] := by decide

-- a recursive term: `kids.0.v` is `string` under the binder, and `kids.0.kids.3` is the variable
private abbrev tree : Term := .mu (.object (.mk {"v", "kids"}
  (fun k => if k.1 = "v" then .req .string else .req (.list [] (some (.var 0)) [])) none))
example : frontierShapes (Alg.Term.at (S := dynSyn) tree [.name "kids", .pos 0, .name "v"])
    [.string] = some [true] := by decide
example : frontierShapes (Alg.Term.at (S := dynSyn) tree
    [.name "kids", .pos 0, .name "kids", .pos 3, .name "v"]) [.string] = some [true] := by decide
-- the stack under `kids.0.kids.3.v` holds one copy of the binder, as the host holds one thunk
example : ((Alg.Term.at (S := dynSyn) tree
    [.name "kids", .pos 0, .name "kids", .pos 3, .name "v"]).map (·.map (·.2.length))) =
    some [1] := by decide

-- an unguarded binder: the bound refuses instead of a loop
example : frontierShapes (Alg.Term.at (S := dynSyn) (.mu (.var 0)) [.name "x"]) [] = none := by
  decide
-- a guarded inner binder that reaches an outer binder at its input
private abbrev nest : Term := .mu (.object (.mk {"c"} (fun _ => .req (.mu (.union [
  .object (.mk {"y"} (fun _ => .req .number) none), .var 1]))) none))
-- the outer object declares no `y`, so the item at `c` can be an outer object: `[number, never]`
example : frontierShapes (Alg.Term.at (S := dynSyn) nest [.name "c", .name "y"]) [.number, .never]
    = some [true, true] := by decide
example : frontierShapes (Alg.Term.at (S := dynSyn) nest [.name "c", .name "c", .name "y"])
    [.number, .never] = some [true, true] := by decide

-- an opaque attribute: every path is opaque
private abbrev itemO : Term := .object (.mk {"o"} (fun _ => .req .opaq) none)
example : frontierShapes (Alg.Term.at (S := dynSyn) itemO [.name "o", .name "x", .pos 2]) [.opaq] =
    some [true] := by decide

/-! Narrowing against the slice of a certified union -/

private abbrev clA : AltClause := ⟨{"tag"}, fun _ => ([], ⟨.string, NEFinset.of "A" ∅⟩)⟩
private abbrev φA : Term := Alg.clauseTerm {"tag"} fun _ => litS "A"
private abbrev φAB : Term := Alg.clauseTerm {"tag"} fun _ => .union [litS "A", litS "B"]
private abbrev oA : Term := .object (.mk {"tag", "x"}
  (fun k => if k.1 = "tag" then .req (litS "A") else .req .number) none)
private abbrev oAB : Term := .object (.mk {"tag", "x"}
  (fun k => if k.1 = "tag" then .req (.union [litS "A", litS "B"]) else .req .string) none)
private abbrev oB : Term := .object (.mk {"tag", "y"}
  (fun k => if k.1 = "tag" then .req (litS "B") else .req .number) none)
private abbrev oS : Term := .object (.mk {"tag", "z"}
  (fun k => if k.1 = "tag" then .req .string else .req .number) none)

-- narrowing keeps every option that the clause meets; the slice keeps the option it describes
example : (Alg.narrow φA [oA, oAB, oB, oS]).length = 3 := by decide
example : (clA.extract [oA, oAB, oB, oS]).length = 1 := by decide
-- on a union whose options pin one tag each, narrowing is the slice
example : (Alg.narrow φA [oA, oB]).length = 1 ∧ (clA.extract [oA, oB]).length = 1 := by decide
-- `string('A','B')` keeps the options that can hold `A` or `B`
example : (Alg.narrow φAB [oA, oAB, oB, oS]).length = 4 := by decide

end Calculus
