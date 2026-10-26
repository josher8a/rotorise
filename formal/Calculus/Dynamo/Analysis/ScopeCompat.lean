import Calculus.Dynamo.Analysis.ScopeDisjoint
import Calculus.Lang.ScopeCompat

/-!
# Compatibility of closed codecs at DynamoDB

`Closed.compatPair` is the scoped compatibility decision over the graph at DynamoDB. The laws that
the decision reads hold at each orientation (`dynLaws`), so the two meanings of a pair that the
decision accepts agree at the host and at the dual (`Closed.compatPair_sound`). Over two lawful
meanings, the two halves are `Compat` in each order (`Closed.compat_of_compatPair`), which is the
obligation of a union of the two. Two options of one scope are two roots of one table of bodies
(`Closed.Shared`), and the decision identifies each entry with itself.
-/

namespace Calculus

/-- **One half of the compatibility of two closed codecs**, at the orientation. -/
def Closed.compat (o : Alg.Orient) (x y : Closed) : Bool :=
  Alg.Scoped.compat o Alg.Scoped.twoScopes x.scope x.root y.scope y.root

/-- **The compatibility of two closed codecs**: both halves. The two codecs are two scopes, so the
    decision identifies no entry of one with an entry of the other. -/
def Closed.compatPair (x y : Closed) : Bool :=
  Alg.Scoped.compatPair Alg.Scoped.twoScopes x.scope x.root y.scope y.root

/-- **The decision is sound**: the two meanings of an accepted pair agree at the host and at the
    dual, at each caller table. -/
theorem Closed.compatPair_sound {x y : Closed} (h : x.compatPair y = true) (α : Table) :
    Alg.Agree .host (x.meaning α) (y.meaning α) ∧ Alg.Agree .dual (x.meaning α) (y.meaning α) :=
  Alg.Scoped.compatPair_sound (S := dynSyn) dynLaws (Alg.Scoped.identSound_twoScopes _ _) h

/-- **The decision discharges the obligation of a union** of two lawful closed options: each
    meaning is `Compat` with the other. -/
theorem Closed.compat_of_compatPair {x y : Closed} (h : x.compatPair y = true) (α : Table)
    (hx : Lawful (x.meaning α)) (hy : Lawful (y.meaning α)) :
    Alg.Compat (x.meaning α) (y.meaning α) ∧ Alg.Compat (y.meaning α) (x.meaning α) := by
  have hxy := (Alg.compat_iff_agree hx hy).mpr (x.compatPair_sound h α)
  exact ⟨hxy, Alg.compat_symm hx hy hxy⟩

/-- **Two options of one scope**: two roots of one table of bodies. An entry that both roots reach
    is one entry, so the decision identifies it with itself. A closed codec with itself is the pair
    of one root twice. -/
structure Closed.Shared where
  N : Nat
  scope : Alg.Scoped.Closed dynSig N
  left : Fin N
  right : Fin N

/-- **The meaning of a root of a shared scope** at the caller table `α`: the solution of the one
    scope at the root. -/
def Closed.Shared.meaning (α : Table) (x : Closed.Shared) (r : Fin x.N) : Codec :=
  Alg.Scoped.Closed.meaning (Alg.tables dynSyn.o α dynTableA) x.scope r

/-- **The compatibility of two options of one scope**: the decision identifies each entry with
    itself, by the index of the entry. -/
def Closed.Shared.compatPair (x : Closed.Shared) : Bool :=
  Alg.Scoped.compatPair Alg.Scoped.oneScope x.scope x.left x.scope x.right

/-- **The decision over one scope discharges the obligation of a union** of two lawful options of
    the scope: each meaning is `Compat` with the other. -/
theorem Closed.Shared.compat_of_compatPair {x : Closed.Shared} (h : x.compatPair = true) (α : Table)
    (hl : Lawful (x.meaning α x.left)) (hr : Lawful (x.meaning α x.right)) :
    Alg.Compat (x.meaning α x.left) (x.meaning α x.right) ∧
      Alg.Compat (x.meaning α x.right) (x.meaning α x.left) := by
  have hxy := (Alg.compat_iff_agree hl hr).mpr
    (Alg.Scoped.compatPair_sound (S := dynSyn) dynLaws (Alg.Scoped.identSound_oneScope _) h)
  exact ⟨hxy, Alg.compat_symm hl hr hxy⟩

end Calculus
