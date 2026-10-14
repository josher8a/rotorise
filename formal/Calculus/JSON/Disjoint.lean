import Calculus.JSON.Basic

/-!
# The leaves and the shape classes of JSON

The scoped disjointness reads the leaf of a universe and the shape classes. JSON supplies its
leaf and its shape classes here. Two kinds are apart where they are two kinds. JSON has no set
former, no list former and no map former in its signature, so every value is a primitive.
-/

namespace Calculus.JSON

/-- **The leaf of JSON.** Two kinds are apart where they are two kinds. -/
instance jsonLeaf : Alg.Leaf jsonSig where
  primsApart m m' := !decide (m = m')

/-- **The shape classes of JSON.** Every value and every attribute is a primitive, and JSON has
    no set, list or map former to land elsewhere. -/
instance jsonShapes : Alg.Shapes jsonSyn where
  former _ := .prim
  prim _ _ _ _ := rfl
  set _ h := nomatch h
  list _ h := nomatch h
  map _ h := nomatch h

end Calculus.JSON
