import Calculus.Denote
import Calculus.Opaque

/-!
# The ω-denotation *was* the denotation

This file used to be 314 lines: a second, fuel-free denotation `denoteω` with eight companions,
its own bridge lemmas, its own `denoteω_μ`, a `termDepth` measure, and `denoteω_eq` — the
transport proving `denoteω t = denote n t` once `n` covered the term.

`denote` is fuel-free now (`Denote.lean`), and it is *the same definition*, companion for
companion. So there is nothing here to define and nothing to transport: `denoteω` is a name for
`denote`, and `denoteω_eq` is `rfl` with the fuel argument deleted from the statement it related.

`termDepth` is gone too. The measure survives as `Term.depth` in `Term.lean`, where `Soundness`
needs it — and it is the *same function*, which is the sharpest way to say what this file was:
the fuel-free denotation and the measure that justified it, sitting one import downstream of the
place they belonged.

The names are kept as aliases so the ω-results downstream read unchanged. Retiring them is a
rename, and a separate commit.
-/

namespace Calculus

noncomputable section

/-- `denote`, under the name the ω-results use. -/
@[reducible] def denoteω : Term → Codec := denote

/-- …and its companions. -/
@[reducible] def denoteωL : List Term → List Codec := denoteList
@[reducible] def denoteωO : Option Term → Option Codec := denoteOpt
@[reducible] def denoteωField : Field → FieldSem := fieldSem
@[reducible] def denoteωR : Rest → RestSem := restSem
@[reducible] def denoteωOpts : List Term → List OptionSem := optionSems
@[reducible] def denoteωMems : List Term → List (Option Member) := denoteμs
@[reducible] def denoteωTags (d : Name) : List Term → List (Finset String × Codec) :=
  denoteTagged d

/-- The object field table, denoted. -/
def denoteωF (fields : Finset Name) (f : {k // k ∈ fields} → Field) : MapOf FieldSem :=
  ⟨fields, fun k => denoteωField (f k)⟩

theorem denoteωL_eq (ts : List Term) : denoteωL ts = ts.map denoteω := denoteList_eq ts
theorem denoteωO_eq (t? : Option Term) : denoteωO t? = t?.map denoteω := denoteOpt_eq t?

theorem denoteωOpts_eq (ts : List Term) :
    denoteωOpts ts = ts.map fun t => optionSemOf (denoteω t) (specOf t) := optionSems_eq ts

theorem denoteωMems_eq (ts : List Term) :
    denoteωMems ts = ts.map fun t => (denoteω t).μ := denoteμs_eq_map ts

theorem denoteωTags_eq (d : Name) (ts : List Term) :
    denoteωTags d ts = ts.map fun t => (tagsOf d t, denoteω t) := denoteTagged_eq d ts

/-- The member index, as before. -/
theorem denoteω_μ (t : Term) : (denoteω t).μ = μSyn t := denote_μ t

theorem denoteω_μList (opts : List Term) : denoteωMems opts = μSynList opts :=
  denoteμs_eq opts

end

end Calculus
