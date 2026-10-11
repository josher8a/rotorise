import Calculus.Dynamo.Analysis.ScopeDisjoint
import Calculus.Lang.ScopeCompat

/-!
# Compatibility of closed codecs at DynamoDB

`Closed.compatPair` is the scoped compatibility decision over the graph at DynamoDB. The laws that
the decision reads hold at each orientation (`dynLaws`), so the two meanings of a pair that the
decision accepts agree at the host and at the dual (`Closed.compatPair_sound`). Over two lawful
meanings, the two halves are `Compat` in each order (`Closed.compat_of_compatPair`), which is the
obligation of a union of the two.
-/

namespace Calculus

/-- **One half of the compatibility of two closed codecs**, at the orientation. -/
def Closed.compat (o : Alg.Orient) (x y : Closed) : Bool :=
  Alg.Scoped.compat o x.scopes x.root y.scopes y.root

/-- **The compatibility of two closed codecs**: both halves. -/
def Closed.compatPair (x y : Closed) : Bool :=
  Alg.Scoped.compatPair x.scopes x.root y.scopes y.root

/-- **The decision is sound**: the two meanings of an accepted pair agree at the host and at the
    dual, at each caller table. -/
theorem Closed.compatPair_sound {x y : Closed} (h : x.compatPair y = true) (α : Table) :
    Alg.Agree .host (x.meaning α) (y.meaning α) ∧ Alg.Agree .dual (x.meaning α) (y.meaning α) :=
  Alg.Scoped.compatPair_sound (S := dynSyn) dynLaws h

/-- **The decision discharges the obligation of a union** of two lawful closed options: each
    meaning is `Compat` with the other. -/
theorem Closed.compat_of_compatPair {x y : Closed} (h : x.compatPair y = true) (α : Table)
    (hx : Lawful (x.meaning α)) (hy : Lawful (y.meaning α)) :
    Alg.Compat (x.meaning α) (y.meaning α) ∧ Alg.Compat (y.meaning α) (x.meaning α) := by
  have hxy := (Alg.compat_iff_agree hx hy).mpr (x.compatPair_sound h α)
  exact ⟨hxy, Alg.compat_symm hx hy hxy⟩

end Calculus
