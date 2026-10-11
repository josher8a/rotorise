import Calculus.Dynamo.Lang.Soundness
import Calculus.Dynamo.Analysis.Merge
import Calculus.Dynamo.Analysis.Slice
import Calculus.Dynamo.Witness.Discharge
import Calculus.Dynamo.Alg.Continuity
import Calculus.Dynamo.Witness.Refutations
import Calculus.Dynamo.Lang.HeldSet
import Calculus.Dynamo.Analysis.Separation
import Calculus.Dynamo.Analysis.Disjoint
import Calculus.Dynamo.Analysis.ScopeDisjoint
import Calculus.Dynamo.Analysis.ScopeCompat
import Calculus.Lang.ScopeDisjoint
import Calculus.Lang.ScopeCompat
import Batteries.Tactic.Lint
import Calculus.Dynamo.Witness.LiteralArity1
import Calculus.Dynamo.Witness.Nesting
import Calculus.Dynamo.Lang.Store
import Calculus.Dynamo.Lang.Scope
import Calculus.Dynamo.Witness.Malleability
import Calculus.Dynamo.Analysis.Orthogonality
import Calculus.Bridge.Vectors
import Calculus.Bridge.Rows
import Calculus.Bridge.Paths
import Calculus.Dynamo.Analysis.Universal
import Calculus.Dynamo.Analysis.Confluence
import Calculus.Dynamo.Analysis.Kernel
import Calculus.Dynamo.Analysis.Compat
import Calculus.JSON.Basic
import Calculus.JSON.Disjoint
import Calculus.JSON.Compat
import Calculus.Alg.Lists
import Calculus.Alg.Positions
import Calculus.Alg.Containers
import Calculus.Alg.Recursion
import Calculus.Alg.System
import Calculus.Lang.Term
import Calculus.Lang.Converse
import Calculus.Lang.Typing
import Calculus.Lang.Guarded
import Calculus.Lang.Sound
import Calculus.Lang.HeldFree
import Calculus.Lang.ExactV
import Calculus.Lang.ExactA
import Calculus.Lang.Shapes
import Calculus.Lang.Disjoint
import Calculus.Lang.DisjointV
import Calculus.Lang.DisjointA
import Calculus.Lang.Path
import Calculus.Lang.Scope
import Calculus.Lang.System
import Calculus.Dynamo.Analysis.Path
import Calculus.Dynamo.Analysis.Precondition
import Lean

/-!
# The axiom base, as a checked claim

**The whole development stands on `propext`, `Classical.choice` and `Quot.sound` — no
`sorryAx`.** `sanctionedAxioms` is that claim, and this file makes
it a build error rather than a sentence a reader verifies by hand with `#print axioms`.

`#assert_axioms` collects the axioms a constant actually
depends on and fails if any of them is outside the sanctioned base.

This is not decoration. `Classical.choice` is easy to acquire by accident: mathlib proves a
great many list facts classically, and a single `by_contra` or an appeal to (say)
`List.filter_eq_nil_iff` silently widens the base of every theorem downstream.
-/

open Lean Elab Command

namespace Calculus

open Alg (Term.depthL)

/-- `#assert_axioms c` errors unless every axiom `c` depends on is in
    `Calculus.sanctionedAxioms`. -/
syntax (name := assertAxioms) "#assert_axioms " ident : command

/-- Elaborator for `#assert_axioms`: one named constant, checked against the base. -/
@[command_elab assertAxioms]
def elabAssertAxioms : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload stx[1]
  let axs ← liftCoreM <| collectAxioms name
  let stray := axs.filter (· ∉ sanctionedAxioms)
  unless stray.isEmpty do
    throwError "{name} depends on unsanctioned axiom(s): {stray.toList}\n\
      The sanctioned base is {sanctionedAxioms}. See docs/architecture.md."

/-- `#assert_axioms_all` is `#assert_axioms` over the whole `Calculus` namespace, found by
    walking the environment instead of by naming constants one at a time.

    An enumerated form is opt-in, and opt-in is the wrong default for a guard: it holds only
    for the theorems someone remembered to list, and says nothing about the ones they did
    not. A theorem is guarded by existing. -/
syntax (name := assertAxiomsAll) "#assert_axioms_all" : command

/-- Elaborator for `#assert_axioms_all`: every theorem in the namespace, found by walking
    the environment, so coverage cannot drift from the list nobody is keeping. -/
@[command_elab assertAxiomsAll]
def elabAssertAxiomsAll : CommandElab := fun _ => do
  let env ← getEnv
  let mut bad : Array (Lean.Name × List Lean.Name) := #[]
  for (n, ci) in env.constants.toList do
    if (`Calculus).isPrefixOf n && ci.isTheorem && !n.isInternal then
      let stray := (← liftCoreM <| collectAxioms n).filter (· ∉ sanctionedAxioms)
      unless stray.isEmpty do bad := bad.push (n, stray.toList)
  unless bad.isEmpty do
    throwError "unsanctioned axiom(s) outside {sanctionedAxioms}:\n\
      {bad.toList.map (fun p => m!"  {p.1}: {p.2}")}\n\
      See docs/architecture.md."

/-! ## The theorems the documentation makes claims about

The soundness of the admission, both halves, fueled and fuel-free. If any of these acquires an axiom, the
build stops here rather than in a reader's `#print axioms`. -/

/-! Both indices of the judgement are claims about the denotation. -/

/-! The refutations of the specification — a counterexample proved classically would still be a counterexample, but these are
constructive and the guard records that. -/

/-! The admission `Adm` cannot pass through `alternate reader` on the read side — the
specification defect, and this is its witness. -/

/-! `≡` is not transitive — the one refutation that is about the equational theory
rather than about a row of it. -/

/-! `ident` has no denotational content to pin. What it has is its relation to `Adm`, which is
what the admission uses it for. -/

/-! The ideal codec: `e` and `p` are mutually inverse between `dom(e)` and `Can(c)`. `retract`
is one half and this is the other, so the bijection is a theorem rather than a reading. -/

/-! The `held`/`refine` split, checked rather than asserted: both are one partial-iso
combinator, and the pair agrees on the nose. -/

/-! The two number gates, as instances of the same combinator. `restrict` gates both
halves by construction, and an ad-hoc gate can forget one half. -/

/-! `through_p` is the fact the `held` row rests on — `g` post-processes a read and is
total, so `dom(p)` is the subterm's exactly. It is cited as a result, so it is guarded
like one. -/

/-! `AdmA`'s `held` row, both directions. A `held`
restricts its side. The read row asks the outer of the attribute where the side of the `held` is
the stored side, the inner term of the entry image, and the outer of the value that the read
gives where the side is the caller side (`AdmA_held_eq`). -/

/-! The lemmas that pin the declaration-time devices of the admission to the denotation. Without them a row
is a transcription of a table rather than a claim about the model, so their axiom base is
part of what the soundness statements rest on. -/

/-! The term-level twins of the rows of `≡`. They meet the table of `≡` through `Codec.Equiv`, with no shared
transport constant, so each is guarded on its own footing. -/

/-! The numeral domain `Numerals`. -/

/-! The `(number)` gate and the two places the bound is forced outward. The `(literal-N)`
rows are `(literal-N)`'s `ℓ ⊆ D`. -/

/-! The kernel `ker p` and the store. `retract_through_store` is **(R)** with DynamoDB in the
middle — the law production actually runs — and the two `decimalCodec` rows are what makes
`Numeral.Stored` the right held set rather than a cautious one: `η ⊆ ker p` holds after the
narrowing and fails before it. -/

/-! The corollary of the codec laws that a pair has two halves: a member a codec cannot write is one it
cannot read. The `opaque`/`NS` defect is its counterexample, and canonical reads are the only
law that sees it — which is why it needs stating rather than following from the rest. -/

/-! The Hold rows of `≡` at term level. The ten `denote_*` bridges are `rfl` and carry no axiom
risk worth a line each; what is guarded is the twins, which go through `Codec.Equiv` and are
what a reviewer checks the table of `≡` against. -/

/-! The continuity results — why fuel is not removable by a fixpoint. -/

/-! The vector checker. `aeq`'s two soundness halves are what a generated vector line is
cashed against, so they carry the whole differential-testing bridge. A comparator built on
mathlib's `DecidableEq (Finset α)` carries `Classical.choice`, and `fsetEq` is the choice-free
comparison. This import is what lets the guard see the comparator: it walks the environment,
and a module it does not import is not in the environment. -/

#assert_axioms_all

/-! ## …and the environment linters, for the same reason

`#assert_axioms_all` guards one property of the environment. Batteries ships more —
`simpNF`, `unusedArguments`, `synTaut`, `dupNamespace`, `checkType` and the rest — and nothing
else `Calculus` needs imports `Batteries.Tactic.Lint`, so this module imports it to run them.

A linter finds a defect that reading does not: a `@[simp]` lemma whose left-hand side cannot
occur in simp-normal form, because the function it names is `@[simp]` too and unfolds first.
Such an attribute asserts something about behaviour that is not true — the same failure class
as a description drifting from what it describes, and the reason this guard is here rather than
a note saying someone should lint occasionally.

`docBlame` is **excluded**, not sanctioned: its hits are helper definitions (`Term.depthL`,
`Codec.e`), and whether this development's docstring convention reaches them is
a judgement, not a defect. Excluding it is visible here; sanctioning each hit would not be.
-/

/-- Linters not run. One entry, and it owes the reason above. -/
def unrunLinters : List Lean.Name := [`docBlame]

/-- Hits this development keeps, as `(linter, declaration)`, each with its reason beside it.

    Empty today. A list rather than a policy, for the reason `sanctionedAxioms` is one: an
    exception nobody can see is an exception nobody rechecks. -/
def sanctionedLintHits : List (Lean.Name × Lean.Name) := []

open Batteries.Tactic.Lint

/-- `#lint_calculus` runs every linter but `unrunLinters` over the `Calculus` namespace and
    fails the build on any hit outside `sanctionedLintHits`. The namespace walk is
    `#assert_axioms_all`'s, and the declaration filter drops what the equation compiler and
    `deriving` emit — those are not source declarations and their shape is not ours to fix. -/
syntax (name := lintCalculus) "#lint_calculus" : command

@[command_elab lintCalculus]
def elabLintCalculus : CommandElab := fun _ => do
  let env ← getEnv
  let linters := (← liftCoreM <| getChecks (slow := true) none none).filter
    fun l => l.name.getString! ∉ unrunLinters.map (·.getString!)
  let decls := env.constants.toList.filterMap fun (n, _) =>
    if (`Calculus).isPrefixOf n && !n.isInternalDetail
       && !(n.getString!.startsWith "eq_") && !(n.getString!.startsWith "match_")
    then some n else none
  let results ← liftCoreM <| lintCore decls.toArray linters
  let mut bad : Array Lean.MessageData := #[]
  for (l, hits) in results do
    for (n, msg) in hits do
      unless sanctionedLintHits.any (fun p => p.1.getString! == l.name.getString! && p.2 == n) do
        bad := bad.push m!"  {l.name} {n}: {msg}"
  unless bad.isEmpty do
    throwError "environment linter(s) reported unsanctioned hits:\n{bad.toList}\n\
      Fix the declaration, or add it to `sanctionedLintHits` with a reason."

#lint_calculus

end Calculus
