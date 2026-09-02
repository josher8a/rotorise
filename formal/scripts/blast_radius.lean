/-
  Deterministic blast radius: which declarations transitively depend on which analysis.

  NOT part of the library — not under `Calculus/`, so `lake build` never touches it:

      docker exec rotorise-lean-dev bash -lc \
        'cd /workspaces/Rotorise/formal && lake env lean scripts/blast_radius.lean'

  The sibling of `scripts/unreferenced.lean` and of `#assert_axioms_all`: one environment
  walk, `Expr.getUsedConstants` over each declaration's type *and* value, closed transitively.

  ## Why this exists

  Costing a refactor by grepping for a name counts **mentions in one file**, misses the
  transitive dependents entirely, and counts occurrences inside docstrings. Every wrong
  refactor estimate in this repo's history has that shape, including a "72 of 126 blocks"
  I produced for this very question. The graph is available; there is no reason to guess.

  ## What it measures here

  The model carries two generations of the same analysis. `Discharge.lean` has §5's
  per-aspect approximations — `adm`, `admA`, `κ`, `ident` — and `Exactness.lean` has
  the joint exact `Adm`/`AdmA`, with bridge theorems between them. The question a refactor
  needs answered is the four-way partition: what depends on the old only (the cost), on the
  new only (already migrated), on both (the bridges), on neither.

  ## It cannot cost a **constructor**, and a control experiment says so

  `86d3a42`'s message claimed this "answers *what breaks if I delete X* for any `X`". **False
  for a constructor of an inductive.** Asked about `Term.object` against `Term.string` — a
  nullary constructor nothing destructures — the partition is:

      depends on OLD only (Term.object)   0
      depends on BOTH                   535
      depends on NEW only (Term.string)   7

  The two are the same set. `Term.casesOn`'s *type* mentions every constructor, so the closure
  of any one of them is "everything that touches `Term`". What this walk measures is dependence
  on a **name**, and a constructor's name is reachable from every case analysis on its type
  whether or not that analysis cares about the constructor's payload.

  So it costs a *declaration* — a definition, a theorem, a whole analysis — and it cannot cost a
  change to a constructor's shape. That question is syntactic and wants a syntactic instrument:
  the `Body` refactor was costed by hand-classifying 60 hits into 57 code sites, and there was
  no shortcut.

  ## The one thing it cannot see

  Members of a `mutual` block do not reference each other in any constant's value — they are
  distinct projections of one induction principle. So the closure from `adm` alone would miss
  `admList`; every member of a mutual family is therefore listed as a root by hand below.
  Nothing else about the walk is heuristic.
-/
import Calculus.Orthogonality
import Calculus.Axioms

open Lean Elab Command

/-- §5's per-aspect analysis: the older generation, every mutual member named. -/
def genOld : List Name :=
  [`Calculus.adm, `Calculus.admA, `Calculus.admList, `Calculus.admAList, `Calculus.admALit,
   `Calculus.SepV, `Calculus.SepA]

/-- The joint exact analysis that replaced it, every mutual member named. -/
def genNew : List Name :=
  [`Calculus.Adm, `Calculus.AdmA, `Calculus.AdmList, `Calculus.AdmAList,
   `Calculus.AdmField, `Calculus.AdmAField, `Calculus.AdmRest, `Calculus.AdmARest,
   `Calculus.SepJV, `Calculus.SepJA]

syntax (name := blastRadius) "#blast_radius" : command

@[command_elab blastRadius]
def elabBlastRadius : CommandElab := fun _ => do
  let env ← getEnv
  let isGen (n : Name) : Bool :=
    match n with
    | .str _ s => s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_"
                  || s.startsWith "binductionOn" || ["injEq","inj","below","brecOn","casesOn",
                     "recOn","ndrec","induct","noConfusion","sizeOf_spec","ibelow"].contains s
    | _ => false
  let source := env.constants.toList.filterMap fun (n, _) =>
    if (`Calculus).isPrefixOf n && !n.isInternalDetail && !isGen n then some n else none
  -- reverse edges: r ↦ everything that mentions r
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let mut refs := ci.type.getUsedConstants
    if let some v := ci.value? then refs := refs ++ v.getUsedConstants
    for r in refs do
      if r != n && (`Calculus).isPrefixOf r then
        rev := rev.insert r ((rev.getD r #[]).push n)
  -- transitive dependents of a root set, by worklist
  let closure (roots : List Name) : Std.HashSet Name := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut work : Array Name := roots.toArray
    while !work.isEmpty do
      let n := work.back!
      work := work.pop
      for d in rev.getD n #[] do
        if !seen.contains d then
          seen := seen.insert d
          work := work.push d
    seen
  let old := closure genOld
  let new := closure genNew
  let mut oldOnly : Array Name := #[]
  let mut both : Array Name := #[]
  let mut newOnly := 0
  let mut neither := 0
  for n in source do
    match old.contains n, new.contains n with
    | true,  false => oldOnly := oldOnly.push n
    | true,  true  => both := both.push n
    | false, true  => newOnly := newOnly + 1
    | false, false => neither := neither + 1
  logInfo m!"source declarations: {source.length}\n\
    depends on OLD only (the refactor cost): {oldOnly.size}\n\
    depends on BOTH (the bridges):           {both.size}\n\
    depends on NEW only (already migrated):  {newOnly}\n\
    depends on neither:                      {neither}\n\
    \n-- OLD only, sorted:\n{String.intercalate "\n" ((oldOnly.map (·.toString)).toList.mergeSort (· ≤ ·))}"

#blast_radius
