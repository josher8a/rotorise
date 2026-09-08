import Calculus
import Lean

/-!
Print the external constants this development cites that reach `Classical.choice`.

`#assert_axioms_all` says the advertised base holds. It cannot say *how* a name in that base
is reached, and choice is reached by more than one route, so closing one leaves the others.
This walks every declaration in the `Calculus` namespace, takes the constants its type and its
value cite directly, keeps the ones outside the namespace, and asks `collectAxioms` of each
whether choice is in its base. The answer is a set of routes rather than a count: a count moves
on almost any new proof, and a route is a name a reader can look up.

`scripts/classical_gateways.txt` is the baseline and `gate.sh` diffs this output against it.
-/

open Lean Elab Command

namespace ClassicalRoutes

/-- `ConstantInfo.value?` returns `none` for a `thmInfo`, so match the constructor. The value
    is in the olean; the accessor hides it. -/
def valueOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | _ => none

/-- The constants a declaration cites directly, from its type and from its value. -/
def citedBy (ci : ConstantInfo) : Array Name :=
  match valueOf ci with
  | some v => ci.type.getUsedConstants ++ v.getUsedConstants
  | none   => ci.type.getUsedConstants

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut ours : NameSet := {}
  for i in [0:mods.size] do
    if (`Calculus).isPrefixOf mods[i]! then
      for n in data[i]!.constNames do ours := ours.insert n
  let mut gate : NameSet := {}
  let mut cache : Std.HashMap Name Bool := {}
  for n in ours.toList do
    if let some ci := env.find? n then
      for c in citedBy ci do
        unless ours.contains c || c == ``Classical.choice do
          let hit ← match cache[c]? with
            | some b => pure b
            | none => do
                let b := (← liftCoreM <| collectAxioms c).contains ``Classical.choice
                cache := cache.insert c b
                pure b
          if hit then gate := gate.insert c
  for x in gate.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    IO.println x

end ClassicalRoutes
