import Calculus.Dynamo.Analysis.Slice
import Calculus.Lang.Path

/-!
# The frontier of a path at DynamoDB, and narrowing against the slice

Each vector reduces in the kernel. A frontier is the shape of each term at the path, or a refusal.
The store refuses a name on a list and a position on a map. A refinement refuses a path, because
the frontier cannot carry its predicate. A position past the prefix of a list shape with a suffix
is a refusal, because the codec of the position depends on the length.

Narrowing keeps each option whose stored view meets the stored view of the clause, and the slice
keeps each option that the clause describes. On a union whose options pin one tag each, the two
agree. A tag behind an adapter separates under the stored view, and not under the raw terms.
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
example : (Alg.narrow .dual φA [oA, oAB, oB, oS]).length = 3 := by decide
example : (clA.extract [oA, oAB, oB, oS]).length = 1 := by decide
-- on a union whose options pin one tag each, narrowing is the slice
example : (Alg.narrow .dual φA [oA, oB]).length = 1 ∧ (clA.extract [oA, oB]).length = 1 := by decide
-- `string('A','B')` keeps the options that can hold `A` or `B`
example : (Alg.narrow .dual φAB [oA, oAB, oB, oS]).length = 4 := by decide

/-! Narrowing by the stored views, against the test of the raw terms

The test reads a raw `held` as disjoint from the bottom alone, so the raw clause separates no
option at a tag behind an adapter. The stored view replaces each `held` by its stored side, and
the stored sides separate. -/

/-- The options that the test of the raw terms does not separate from the clause. -/
private def rawNarrow (φ : Term) (os : List Term) : List Term :=
  os.filter fun o => !Alg.Term.disjoint pair0 φ o

private abbrev decH : Term := Term.held false Term.number Term.string (.decimalText, false) []
private abbrev n1 : Term := .literal .number (WFNumeral.of "1")
private abbrev n2 : Term := .literal .number (WFNumeral.of "2")
-- `number(1)`: a caller adapter over the literal `N 1`
private abbrev num (l : Term) : Term := Term.held false l Term.number (.caller 0, false) []
-- `decimal('1')`: the library text adapter over the literal `N 1`
private abbrev dec (l : Term) (s : String) : Term :=
  Term.held false l (Term.literal .string s) (.decimalText, false) []
private abbrev two (k v : String) (tk tv : Term) : Term :=
  .object (.mk {k, v} (fun x => if x.1 = k then .req tk else .req tv) none)

-- numeric tags behind a caller adapter
private abbrev oN1 : Term := two "k" "a" (num n1) Term.string
private abbrev oN2 : Term := two "k" "a" (num n2) Term.number
private abbrev φN1 : Term := Alg.clauseTerm {"k"} fun _ => num n1
example : (rawNarrow φN1 [oN1, oN2]).length = 2 ∧ (Alg.narrow .dual φN1 [oN1, oN2]).length = 1 := by
  decide
-- decimal tags behind the library text adapter
private abbrev oD1 : Term := two "k" "a" (dec n1 "1") Term.string
private abbrev oD2 : Term := two "k" "a" (dec n2 "2") Term.number
private abbrev φD1 : Term := Alg.clauseTerm {"k"} fun _ => dec n1 "1"
example : (rawNarrow φD1 [oD1, oD2]).length = 2 ∧ (Alg.narrow .dual φD1 [oD1, oD2]).length = 1 := by
  decide
-- `number(1)` against decimal tags: the two adapters store one literal, so the option stays
example : (Alg.narrow .dual φN1 [oD1, oD2]).length = 1 := by decide
-- an object clause against a `decimal` member, which stores a number
private abbrev objZ : Term := .object (.mk {"z"} (fun _ => .req Term.string) none)
private abbrev oVd : Term := two "tag" "v" (litS "A") decH
private abbrev oVo : Term := two "tag" "v" (litS "B") objZ
private abbrev φVo : Term := Alg.clauseTerm {"v"} fun _ => objZ
example : (rawNarrow φVo [oVd, oVo]).length = 2 ∧ (Alg.narrow .dual φVo [oVd, oVo]).length = 1 := by
  decide
-- an adapter clause against a primitive member
private abbrev oPn : Term := two "tag" "v" (litS "A") Term.number
private abbrev oPs : Term := two "tag" "v" (litS "B") Term.string
private abbrev φPd : Term := Alg.clauseTerm {"v"} fun _ => decH
example : (rawNarrow φPd [oPn, oPs]).length = 2 ∧ (Alg.narrow .dual φPd [oPn, oPs]).length = 1 := by
  decide
-- string tags hold no adapter, so the two tests agree
private abbrev oSA : Term := two "k" "a" (litS "A") Term.string
private abbrev oSB : Term := two "k" "a" (litS "B") Term.number
private abbrev φSA : Term := Alg.clauseTerm {"k"} fun _ => litS "A"
example : (rawNarrow φSA [oSA, oSB]).length = 1 ∧ (Alg.narrow .dual φSA [oSA, oSB]).length = 1 := by
  decide

end Calculus
