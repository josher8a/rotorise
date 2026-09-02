/-
  Which `Calculus` declarations no other `Calculus` declaration mentions.

  NOT part of the library — `lakefile.toml`'s `lean_lib` globs `Calculus/**`, so this file is
  never built by `lake build`. Run it by hand:

      docker exec rotorise-lean-dev bash -lc \
        'cd /workspaces/Rotorise/formal && lake env lean scripts/unreferenced.lean'

  It is the sibling of `#assert_axioms_all`: the same environment walk, with
  `Expr.getUsedConstants` where that one calls `collectAxioms` — `collectAxioms` *is* this
  traversal keeping only the axioms.

  ## Why this is a diff instrument and not a verdict

  Two things it cannot do, and the second is not fixable here.

  **1. Most unreferenced declarations are intended.** In a specification library the advertised
  results are unreferenced by construction — `Adm_exact`, `soundness_both`, every `not_*`
  refutation, every worked example. The count is ~300 of ~1600. So there is no root set to
  measure against, and no build-failing guard to be had: unlike `#assert_axioms_all`, this can
  only report.

  **2. Members of a `mutual` block read as unreferenced even when they are used.** A mutual block
  compiles to one definition and the members project out of it, so the *source* cross-references
  survive in no constant's value. Measured: `Adm_exact`'s source calls `Adm_exactO`, and
  `Adm_exactO` is mentioned by **zero** constants in the whole environment. Nor are they linked
  through a shared helper — `Adm_exact` goes through `Term.binductionOn` and `Adm_exactO` through
  `Term.binductionOn_2`, *different projections* of one induction principle, so there is no edge
  to follow and no cheap way to recover block membership.

  Both defects are **stable across revisions**, which is what makes the diff sound where the
  absolute number is not: snapshot before a change, snapshot after, and compare. What appears in
  the difference is a declaration the change actually orphaned.

  This exists because a claim in `fa9ce05`'s commit message — "a reachability pass over the file
  reports 30 unreferenced declarations against 34 at HEAD" — was a *regex* over the source text,
  counting occurrences inside docstrings and comments, and was wrong by an order of magnitude.
  `WORKING-AGREEMENT.md` says grep is not verification; this is what verification costs.
-/
import Calculus.Orthogonality
import Calculus.Axioms

open Lean Elab Command

/-- Declarations the equation compiler and `deriving` emit. Not source, and not ours to fix. -/
def generatedSuffixes : List String :=
  ["eq_def", "injEq", "inj", "sizeOf_spec", "noConfusion", "below", "brecOn", "casesOn",
   "recOn", "ndrec", "induct", "fun_cases", "ctorIdx", "toCtorIdx", "mk", "binductionOn",
   "ibelow", "binductionOn_1", "binductionOn_2", "binductionOn_3", "binductionOn_4"]

/-- `#unreferenced` prints the orphan set, sorted, one per line, for diffing. -/
syntax (name := unreferenced) "#unreferenced" : command

@[command_elab unreferenced]
def elabUnreferenced : CommandElab := fun _ => do
  let env ← getEnv
  let isGenerated (n : Name) : Bool :=
    match n with
    | .str _ s => generatedSuffixes.contains s || s.startsWith "eq_" || s.startsWith "match_"
                  || s.startsWith "proof_" || s.startsWith "binductionOn"
    | _ => false
  -- CANDIDATES are filtered to source declarations…
  let mine := env.constants.toList.filter fun (n, _) =>
    (`Calculus).isPrefixOf n && !n.isInternalDetail && !isGenerated n
  -- …but EDGES are not. Filtering the edge set severs the paths well-founded and structural
  -- definitions travel through (`_unary`, `brecOn`), which cost 151 false positives when I did it.
  let mut used : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    let mut refs := ci.type.getUsedConstants
    if let some v := ci.value? then refs := refs ++ v.getUsedConstants
    for r in refs do
      if r != n && (`Calculus).isPrefixOf r then used := used.insert r
  let orphans := (mine.filterMap fun (n, _) =>
    if used.contains n then none else some n.toString).mergeSort (· ≤ ·)
  logInfo m!"-- unreferenced: {orphans.length} of {mine.length} source declarations\n\
    {String.intercalate "\n" orphans}"

#unreferenced
