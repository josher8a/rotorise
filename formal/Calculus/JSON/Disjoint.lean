import Calculus.JSON.Basic

/-!
# The leaves and the shape classes of JSON

The scoped disjointness reads the leaves of a universe, the laws of the leaves, and the shape
classes. JSON supplies its leaves and its shape classes here. Two kinds are apart where they are
two kinds. A JSON predicate is a function, so the leaves compare no predicate. JSON has no set
former, no list former and no map former in its signature, so every value is a primitive.
-/

namespace Calculus.JSON

/-- **The leaves of JSON.** Two kinds are apart where they are two kinds. A JSON predicate is a
    function, so no two predicates are apart. -/
instance jsonLeaf : Alg.Leaf jsonSig where
  primsApart m m' := !decide (m = m')
  isData _ _ := false
  predicatesApart _ _ _ := false

/-- **The shape classes of JSON.** Every value and every attribute is a primitive, and JSON has
    no set, list or map former to land elsewhere. -/
instance jsonShapes : Alg.Shapes jsonSyn where
  former _ := .prim
  prim _ _ _ _ := rfl
  set _ h := nomatch h
  list _ h := nomatch h
  map _ h := nomatch h

/-- A JSON predicate is a function, so the leaves keep no two predicates apart. -/
instance jsonLeafMeet : Alg.LeafMeet jsonSig := ⟨fun _ _ _ h => nomatch h⟩

end Calculus.JSON
