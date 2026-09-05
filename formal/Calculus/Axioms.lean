import Calculus.Soundness
import Calculus.Discharge
import Calculus.Continuity
import Calculus.Refutations
import Calculus.HeldSet
import Calculus.Exactness
import Batteries.Tactic.Lint
import Calculus.LiteralArity1
import Calculus.Nesting
import Calculus.Malleability
import Calculus.Orthogonality
import Calculus.Vectors
import Lean

/-!
# The axiom base, as a checked claim

**The whole development stands on `propext`, `Quot.sound`, and §1's numeric host — no
`Classical.choice`, no `sorryAx`.** `sanctionedAxioms` below is that claim, and this file turns
it from a sentence a reader had to verify by hand with `#print axioms` into a build error.

Here it is a build error instead. `#assert_axioms` collects the axioms a constant actually
depends on and fails if any of them is outside the sanctioned base below.

This is not decoration. `Classical.choice` is easy to acquire by accident: mathlib proves a
great many list facts classically, and a single `by_contra` or an appeal to (say)
`List.filter_eq_nil_iff` silently widens the base of every theorem downstream. Both of those
happened while this module was being written, which is why it exists.
-/

open Lean Elab Command

namespace Calculus

/-- The sanctioned base: Lean's two propositional axioms, plus §1's numeric host, which is
    axiomatized deliberately (IEEE-754 facts are not this calculus's theorems).

    Four names where there were seven, and the shrinkage is not the point. `Double.toDec`,
    `Double.ofDec`, `Double.roundtrip` and `Double.decEq` are now *theorems and definitions*
    projecting out of `numericHost : NumericHost Double` (`Domain.lean`), so what this list
    sanctions is one interface rather than five assertions that happen to fit together. That
    it is an interface and not a disguised claim about binary64 is itself checked:
    `numericHost_wfNumeral` and `numericHost_unit` inhabit `NumericHost` at two types with
    provably different decimal images (`numericHost_images_differ`), and the first is built
    with no `Double` axiom at all. -/
def sanctionedAxioms : List Lean.Name :=
  [``propext, ``Quot.sound, `Calculus.Double, `Calculus.numericHost]

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
      The sanctioned base is {sanctionedAxioms}. See ARCHITECTURE.md §6."

/-- `#assert_axioms_all` is `#assert_axioms` over the whole `Calculus` namespace, found by
    walking the environment instead of by naming constants one at a time.

    The enumerated form this replaces was opt-in, and opt-in is the wrong default for a
    guard: it holds only for the theorems someone remembered to list, and says nothing
    about the ones they did not. 125 lines named 125 theorems; the namespace has 1199, and
    one of the 1074 unnamed (`not_equiv_tupleTail_tuple`) had already acquired
    `Classical.choice` from a `simp`, exactly as the note above predicts. A theorem is now
    guarded by existing. -/
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
      See ARCHITECTURE.md §6."

/-! ## The theorems the documentation makes claims about

§5's soundness, both halves, fueled and fuel-free. If any of these acquires an axiom, the
build stops here rather than in a reader's `#print axioms`. -/

/-! Both indices of the judgement are claims about the denotation (§3). -/

/-! The dischargers of (U) (§5), and the three refutations that repaired the specification
(§4) — a counterexample proved classically would still be a counterexample, but these are
constructive and the guard records that. -/

/-! §5's `adm` cannot pass through `legacy` on the read side — the specification defect
that had no witness until it had this one. -/

/-! §6's `≡` is not transitive — the one refutation that is about the equational theory
rather than about a row of it. -/

/-! `ident` has no denotational content to pin — what it has is its relation to `adm`,
which is what §5 uses it for, and ~~SepV~~'s right to drop §5's two `ident` conjuncts
rests on it. -/

/-! §2's ideal: `e` and `p` are mutually inverse between `dom(e)` and `Can(c)`. `retract`
is one half and this is the other, so the bijection is a theorem rather than a reading. -/

/-! §5's two outright dischargers, as one theorem: label each side by a projection of the
input, keep the options' label sets disjoint. `uniqueAdmission_of_kinds` and
`uniqueAdmission_byTag` are its two instances. -/

/-! §3's `held`/`refine` split, checked rather than asserted: both are one partial-iso
combinator, and the pair agrees on the nose. -/

/-! §1's two number gates, as instances of the same combinator. `restrict` gates both
halves by construction, which is what §3 argues an ad-hoc gate forgets. -/

/-! §3 `(nullable)`'s guard. `nullHonest_of_not_ownsNull` is the premise that stopped
being one — it derives both honesty halves from lawfulness — and `withNull_ownsNull` is
why §6's idempotence is a construction rather than an equation. -/

/-! `(union)`'s residue, and the bridge every discharger now crosses. The two witnesses
are one union seen by both residues: `UAtCan` refutes it at an input it never writes,
`UAtAct` holds of it. -/

/-! `through_p` is the fact the `held` row rests on — `g` post-processes a read and is
total, so `dom(p)` is the subterm's exactly. It is cited as a result now, so it is guarded
like one. -/

/-! `AdmA`'s `held` row, both directions. §5 gave `held` one `⊤` row on both sides; its
opacity is one-sided — `f` gates the write, `g` only post-processes the read — so the
readable side passes through, and these two are the pair it separates and the pair it
still does not. -/

/-! The lemmas that pin §5's declaration-time devices to the denotation. Without them a row
is a transcription of a table rather than a claim about the model, so their axiom base is
part of what the soundness statements rest on. -/

/-! The fuel-free twins. They meet §6's table through `Codec.Equiv` rather than through a
shared transport constant — ~~denote_eq~~ was the ω-layer's and went with the layer
(`Denote.lean`) — so each is guarded on its own footing. -/

/-! §3's `Uν` for `opaque`, and §1's numeral domain. `opaq_T_identity` is the row
closed for `opaque`; its proof sits behind seven
`omega` calls in `HeldSet.lean`, and `omega` is a known `Classical.choice` route — which
makes it the single constant in this file with the most to lose from going unguarded. -/

/-! §3's `(number)` gate and the two places the bound is forced outward. `opaq_T_identity`
above is guarded for `Uν` *after* `HOpaque.num` gained its premise, which is the half of this
change that reaches the depth machinery. The `(literal-N)` rows are the half that does not:
they are `(literal-N)`'s `ℓ ⊆ D`, added to §3 once the shipped `literal(NaN)` settled the
question the conditional refutations leave open. -/

/-! §2's kernel and §1's store. `retract_through_store` is **(R)** with DynamoDB in the
middle — the law production actually runs — and the two `decimal` rows are what makes
`Numeral.Stored` the right held set rather than a cautious one: `η ⊆ ker p` holds after the
narrowing and fails before it. -/

/-! §2's corollary that a pair has two halves: a member a codec cannot write is one it
cannot read. The `opaque`/`NS` defect is its counterexample, and (MP) is the only law that
sees it — which is why it needs stating rather than following from the rest. -/

/-! §6's Hold rows at term level. The ten `denote_*` bridges are `rfl` and carry no axiom
risk worth a line each; what is guarded is the twins, which go through `Codec.Equiv` and are
what a reviewer checks §6's table against. -/

/-! §7's continuity results — why fuel is not removable by a fixpoint. -/

/-! The vector checker. `aeq`'s two soundness halves are what a generated vector line is
cashed against, so they carry the whole differential-testing bridge — and the comparator
reached this guard already carrying `Classical.choice`, from mathlib's `DecidableEq (Finset α)`
of all places. `fsetEq` is the repair. This import is the reason the guard saw it: it walks
the environment, and a module it does not import is not in the environment. -/

#assert_axioms_all

/-! ## …and the environment linters, for the same reason

`#assert_axioms_all` guards one property of the environment. Batteries ships fifteen more —
`simpNF`, `unusedArguments`, `synTaut`, `dupNamespace`, `checkType` and the rest — and this
development had **never run them**, because `Batteries.Tactic.Lint` is not imported by
anything `Calculus` needed and so was never built.

The first run over 1674 declarations found one substantive defect and it was invisible by
reading: `SetBase.setMember_elemMember` was `@[simp]` with a left-hand side that cannot occur
in simp-normal form, because `SetBase.elemMember` is `@[simp]` too and unfolds first. An
attribute asserting something about behaviour that had quietly stopped being true — the same
failure class as a description drifting from what it describes, and the reason this guard is
here rather than a note saying someone should lint occasionally.

`docBlame` is **excluded**, not sanctioned: its 90 hits are helper definitions (`allPA`,
`Term.depthL`, `Codec.e`), and whether this development's docstring convention reaches them is
a judgement, not a defect. Excluding it is visible here; sanctioning 90 hits would not be.
-/

/-- Linters not run. One entry, and it owes the reason above. -/
def unrunLinters : List Lean.Name := [`docBlame]

/-- Hits this development sanctions, as `(linter, declaration)`.

    Both are `fun _ => true` — the ⊤ predicate and the ⊤ occupancy — so the unused argument
    *is* the content. Two entries, named individually, for the reason `sanctionedAxioms` is a
    list rather than a policy: an exception nobody can see is an exception nobody rechecks. -/
def sanctionedLintHits : List (Lean.Name × Lean.Name) :=
  [(`unusedArguments, `Calculus.qTop), (`unusedArguments, `Calculus.occTop)]

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
