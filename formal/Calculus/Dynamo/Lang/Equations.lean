import Calculus.Dynamo.Lang.Term
import Calculus.Dynamo.Alg.Opaque
import Calculus.Alg.System

/-!
# Equations

Which rewrites preserve the pair. `≡` reads as: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

The rows of `≡` that read only the combinators take the carriers as parameters, as `Codec.Equiv`
does. This file states the one row that reads the member index of a union: `union` associativity
needs no condition, because a nested union and its flattening consult the same options in the same
order, so the two are equal on both halves.

The rows that read a term are stated over the codec of a scope term in `ScopeEquations.lean`:
`held`'s composition, `refine`'s meet and its full case, and the member preservation of the
wrappers. The "Do not hold" table is settled in `Refutations.lean`.
-/

namespace Calculus

/-! ## `union` is associative

The row of `≡`, stated outright. Both forms take the first admitter in the same order, so the
two maps are equal at each orientation (`Alg.altCodec_nest`), and the row carries no condition. -/

/-- The member index nests the same way it flattens. Both sides conclude the head member
    or `⊤`, so the content is entirely in whether the condition agrees. -/
theorem unanimous_pair_assoc (a b c : Option Member) :
    unanimous [a, unanimous [b, c]] = unanimous [a, b, c] := by
  show (if ([unanimous [b, c]].all (· == a)) = true then a else none)
      = (if ([b, c].all (· == a)) = true then a else none)
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  by_cases hcb : (c == b) = true
  · have hu : unanimous [b, c] = b := by
      show (if ([c].all (· == b)) = true then b else none) = b
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_pos hcb]
    rw [hu, eq_of_beq hcb, Bool.and_self]
  · have hu : unanimous [b, c] = none := by
      show (if ([c].all (· == b)) = true then b else none) = none
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_neg hcb]
    rw [hu]
    cases a with
    | none => simp
    | some x =>
      have hne : ((b == some x) && (c == some x)) = false := by
        cases hbx : (b == some x) with
        | false => simp
        | true =>
          cases hcx : (c == some x) with
          | false => simp
          | true =>
            exact absurd (by rw [eq_of_beq hbx, eq_of_beq hcx]; simp) hcb
      simp [hne]

/-- `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : Codec) :
    Codec.Equiv
      (altCodec [o₁, (altCodec [o₂, o₃] (unanimous [o₂.μ, o₃.μ]))]
        (unanimous [o₁.μ, unanimous [o₂.μ, o₃.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.μ, o₂.μ, o₃.μ])) := by
  refine ⟨Alg.altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    exact Option.some.inj ((hn.symm.trans (Alg.altCodec_nest o₁ o₂ o₃ _ _ _ (o := .host) v)).trans hf)
  · intro a v v' hn hf
    exact Option.some.inj ((hn.symm.trans (Alg.altCodec_nest o₁ o₂ o₃ _ _ _ (o := .dual) a)).trans hf)

end Calculus
