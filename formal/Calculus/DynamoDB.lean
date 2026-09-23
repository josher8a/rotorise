import Calculus.Nesting

/-!
# The DynamoDB port

The ideal algebra has no depth limit. DynamoDB has one, and this module instantiates the
parameter of `Attr.Storable` at the store's number.

`docs/dynamo-datatypes.md:130`: *"The document types are list and map. These data types can
be nested within each other, to represent complex data structures up to 32 levels deep."*
-/

namespace Calculus.DynamoDB

/-- The store's nesting bound. -/
def maxNesting : Nat := 32

/-- At the store's bound, a derivable term writes an attribute that DynamoDB refuses. -/
theorem not_storable_of_typed :
    ∃ (t : Term) (T : Held) (μ : Option Member) (v : Value) (a : Attr),
      Typed t T μ ∧ (denote t).e v = some a ∧ ¬ Attr.Storable maxNesting a :=
  Calculus.not_storable_of_typed maxNesting

end Calculus.DynamoDB
