import Calculus.Dynamo.Witness.ScopeNesting

/-!
# The nesting bound: the ground fragment and the containers

`Domain.lean` states the bound: `Attr.Storable n a` is `Attr.nesting a ≤ n`, counting `L` and
`M` and nothing else. The bound `n` is a parameter, because the ideal algebra has no depth
limit. A port instantiates it (`Dynamo/Lang/Store.lean`). The nesting bound is the one place
where `𝔸` is larger in the model than in the store.

Two facts are proved here:

* **the ground fragment is safe**: every ground codec writes nesting `0`, so the bound is
  never a question for the codecs that do not nest;
* **the containers are exact**: `array` adds exactly one level, so the bound is
  compositional and not a global search.

A typed closed codec can still write an attribute that the store refuses
(`Closed.not_storable_of_typed`), and the port refuses that write (`Closed.storeCodec_refuses_deep`).
-/

namespace Calculus

/-! ## The ground fragment writes flat -/

/-- Every ground codec writes a scalar or a wire set, and neither is a document type. -/
theorem nesting_zero_of_ground (k : GroundKind) (v : Value) (a : Attr)
    (h : (baseCodec k).e v = some a) : Attr.nesting a = 0 := by
  -- the base writes the datum it was given, and the datum carries a scalar member
  simp only [baseCodec, Alg.fiberCodec, Alg.Codec.e] at h
  split at h
  · next hm => cases h; cases k <;> cases v <;> simp_all [Attr.nesting]
  · exact nomatch h

/-! ## The containers add exactly one

Compositional in both directions, which is what a bound has to be if it is to be checked
anywhere but at the top: `array` adds one level and nothing else, so a nesting budget divides
down a term rather than being recomputed at every node. -/

/-- A written list nests one deeper than its deepest element. -/
theorem nesting_l (as : List Attr) :
    Attr.nesting (.l as) = Attr.nestingL as + 1 := rfl

/-- And an element never nests deeper than the list holding it. -/
theorem nestingL_of_mem {as : List Attr} {a : Attr} (h : a ∈ as) :
    Attr.nesting a ≤ Attr.nestingL as := by
  induction as with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact le_trans (ih h') (Nat.le_max_right _ _)

end Calculus
