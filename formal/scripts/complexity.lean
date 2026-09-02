/-
  What the kernel actually holds: proof-term size, and the sharing behind it.

  NOT part of the library — not under `Calculus/`, so `lake build` never touches it:

      docker exec rotorise-lean-dev bash -lc \
        'cd /workspaces/Rotorise/formal && lake env lean scripts/complexity.lean'

  The sibling of `scripts/blast_radius.lean`, and it reuses that file's one idea: an
  environment walk over each declaration's type *and* value. `scripts/complexity.py` measures
  the **text** — pattern rows and case tactics — and this measures the **term**. They rank
  differently and neither subsumes the other, which is the reason both exist.

  ## Count the DAG, not the tree — the trap this file exists to stop

  `Expr` is a **directed acyclic graph**. A naive recursive size counts every occurrence of a
  shared subterm, and the number that comes out is not a size:

      AdmA_exact        tree 2754337    dag 7239    sharing 380x
      Adm_exact          tree 168415    dag 8844    sharing  19x

  Read the tree column and `AdmA_exact` is three hundred times the largest thing in the
  development. Read the DAG column, which is what the kernel stores and checks, and it is
  *smaller* than `Adm_exact`. The tree count was very nearly reported here as a finding; it is
  a sharing measurement wearing a size's clothes.

  ## So the sharing ratio is the metric, and it is the sharpest signal in the tree

  Everything measured sits between 2x and 19x. `AdmA_exact` is at **380x**, alone. That is the
  signature of a tactic duplicating one large subterm across every branch — a `simp` or
  `decide` fan — and **no textual measure can see it**: the same proof is calm at 0.58 branches
  per line, and its 104 source lines are unremarkable. When a proof is slow to check and reads
  fine, this is the column to look at.

  ## Transitive dependency count is a dead end, measured, so nobody rebuilds it

  The closure of a declaration's dependencies runs 750 to 3710 across the whole development,
  and the *largest* values belong to `soundness_both` (3650) and `carrier_denote` (3710) — the
  two simplest proofs in any other column, 79 kernel nodes each. It measures which layer of the
  stratification a declaration sits in (§1), not how complex it is. Direct dependency count is
  worth something as coupling — 8 to 225 — and roughly tracks the branch count.

  ## Elaboration heartbeats are not deterministic, and this was checked rather than assumed

  Heartbeats look like the right instrument: Lean's counter is a step count and not a clock, so
  it should reproduce where a timing never does. It does not. `Meta.check` run three times on
  the same value, in one process, same environment:

      AdmA_exact      2852025   2683632   2685219      6.2% spread
      Adm_exact       3565408   3467318   3468851      2.8%
      Adm_kind           7102      6602      6643      7.6%
      soundness_both     5941      5234      5222     13.7%
      ExactV_opaq         677       669       675      1.2%

  Run 1 is systematically the largest — cold instance and `whnf` caches — and runs 2 and 3
  still differ. So heartbeats measure the *cost of checking under this cache state*, which is
  a real thing to want and is not a property of the declaration. **A ratchet on a number with
  13% run-to-run spread fires on noise**, which is why `ratchet.py` holds `branches` and not
  this, and why the earlier claim that heartbeats are deterministic was wrong.

  What they are good for is a tripwire at an order of magnitude: 700 against 3.5 million is not
  a measurement question. And they **corroborate the DAG count against the tree count** — both
  put `Adm_exact` above `AdmA_exact`, which is the ordering the tree number reverses. Two
  instruments disagreeing with a third is how the tree number was caught.

  ## What it cannot see

  Everything `blast_radius.lean`'s header says about names applies here: a `mutual` block's
  members do not reference each other in any constant's value, so a family's size is the sum of
  its projections and not one number. And a `def` that is a table has a large term for the same
  reason it has many branches — the row count is §3's, not a choice.
-/
import Calculus.Axioms
import Calculus.Orthogonality
import Calculus.Vectors

open Lean

/-- Every occurrence of every subterm. **Not a size** — see the header. Kept because the
    ratio against `dagSize` is the metric, and the ratio needs both halves. -/
partial def treeSize : Expr → Nat
  | .app f a         => 1 + treeSize f + treeSize a
  | .lam _ t b _     => 1 + treeSize t + treeSize b
  | .forallE _ t b _ => 1 + treeSize t + treeSize b
  | .letE _ t v b _  => 1 + treeSize t + treeSize v + treeSize b
  | .mdata _ e       => 1 + treeSize e
  | .proj _ _ e      => 1 + treeSize e
  | _                => 1

private partial def dagGo (e : Expr) : StateM ExprSet Unit := do
  if (← get).contains e then return
  modify (·.insert e)
  match e with
  | .app f a         => dagGo f; dagGo a
  | .lam _ t b _     => dagGo t; dagGo b
  | .forallE _ t b _ => dagGo t; dagGo b
  | .letE _ t v b _  => dagGo t; dagGo v; dagGo b
  | .mdata _ x       => dagGo x
  | .proj _ _ x      => dagGo x
  | _                => return

/-- Distinct subterms: what the kernel stores and typechecks. This is the size. -/
def dagSize (e : Expr) : Nat := ((dagGo e).run {}).2.size

/-- Constants named by a declaration's type *and* value — `blast_radius.lean`'s walk, one step
    rather than closed. Coupling, not depth: the closure is a dead end and the header says why. -/
def directDeps (env : Environment) (n : Name) : Nat :=
  match env.find? n with
  | none    => 0
  | some ci =>
    let s := ci.type.getUsedConstants.foldl (·.insert ·) NameSet.empty
    match ci.value? with
    | none   => s.size
    | some v => (v.getUsedConstants.foldl (·.insert ·) s).size

/-- The declarations this file reports on. A whole-environment sweep is possible and is not what
    this instrument is for: like `unreferenced.lean` it is a **diff instrument**, so the useful
    run is a named set before and after a change. These are the leaders each metric found. -/
def watched : List Name :=
  [`Calculus.AdmA_exact, `Calculus.Adm_exact, `Calculus.aeq_sound, `Calculus.occV_sound,
   `Calculus.occA_sound, `Calculus.encSet_isSome_of, `Calculus.Adm_kind,
   `Calculus.soundness_both, `Calculus.carrier_denote, `Calculus.typed_TSub,
   `Calculus.occV, `Calculus.aeq, `Calculus.ExactV_opaq, `Calculus.sepV_refine_disjoint]

run_cmd do
  let env ← Lean.getEnv
  IO.println "      dag      tree  sharing    deps  declaration"
  IO.println "  ─────────────────────────────────────────────────────────────"
  for n in watched do
    match env.find? n with
    | none => IO.println s!"        ?         ?        ?       ?  {n}  (not found)"
    | some ci =>
      match ci.value? with
      | none => IO.println s!"        —         —        —  {(directDeps env n).repr.leftpad 6}  {n}  (no value)"
      | some v =>
        let d := dagSize v
        let t := treeSize v
        IO.println s!"{d.repr.leftpad 9} {t.repr.leftpad 9} {(t / max d 1).repr.leftpad 7}x {(directDeps env n).repr.leftpad 7}  {n}"
  IO.println ""
  IO.println "  dag     distinct subterms — the size the kernel checks"
  IO.println "  tree    every occurrence — not a size, only the ratio's denominator"
  IO.println "  sharing tree/dag; 2-19x is normal here, 380x is a simp fan"
  IO.println "  deps    constants named by type and value; coupling, not depth"
