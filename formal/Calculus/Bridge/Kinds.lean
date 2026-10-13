import Calculus.Dynamo.Lang.Term

/-!
# The decision of a path row, and the equality of two leaves

`PathKind` names the decision of `at` at a path, and `kindOf` gives the decision from three tests on
a frontier. `groundEq` and `predSame` decide that two leaves of a frame are one leaf. Each
declaration here reads data, and no term, so a path row of a term and of a closed codec read them.
-/

namespace Calculus

/-- **Two primitives are one primitive**: the same base, or the same literal of one kind. -/
def groundEq : Ground → Ground → Bool
  | .base k, .base k' => decide (k = k')
  | .literal k v, .literal k' v' => if h : k = k' then decide (h ▸ v = v') else false
  | _, _ => false

/-- **Two predicates of one datum**: the same alternatives at one kind. A closure is not read. -/
def predSame : Pred → Pred → Bool
  | .members k ls, .members k' ls' | .except k ls, .except k' ls' =>
      if h : k = k' then
        decide (∀ x ∈ (h ▸ ls).1, x ∈ ls'.1) && decide ((h ▸ ls).1.card = ls'.1.card)
      else false
  | .closure _, .closure _ => true
  | _, _ => false

/-- **The decision of `at` at a path**, without the frames. -/
inductive PathKind where
  | refused | vacant | someVariants | ambiguous | resolved
  deriving DecidableEq

/-- **The decision of a frontier with a first frame**, from three tests: some frame has the head
    `never`, each frame has it, and each frame is the first frame. No `never` and one frame is one
    codec, and no `never` and two frames is two declarations. Each frame `never` is no codec, and
    some frames `never` is some options. -/
def kindOf : Bool → Bool → Bool → PathKind
  | false, _, true => .resolved
  | false, _, false => .ambiguous
  | true, true, _ => .vacant
  | true, false, _ => .someVariants

end Calculus
