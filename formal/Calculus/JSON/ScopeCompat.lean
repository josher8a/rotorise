import Calculus.JSON.ScopeDisjoint
import Calculus.Lang.ScopeCompat

/-!
# Compatibility of closed codecs at JSON

The scoped decision `Alg.Scoped.compatPair` and its soundness hold at every universe. The decision
reads the laws of the universe (`jsonLaws`) and no oracle, so JSON supplies nothing more. Every
answer of the decision at JSON comes from its structural rows.
-/

namespace Calculus.JSON

/-- **The decision is sound at JSON**: an accepted pair agrees at the host and at the dual. -/
theorem closed_compat_sound {τ : (s : Bool) → Alg.TableAt jsonSig s} {NL NR : Nat}
    {dL : Alg.Scoped.Closed jsonSig NL} {dR : Alg.Scoped.Closed jsonSig NR} {rL : Fin NL}
    {rR : Fin NR} {ι : Fin NL → Fin NR → Bool} (hι : Alg.Scoped.IdentSound (S := jsonSyn) (τ := τ) dL dR ι)
    (h : Alg.Scoped.compatPair ι dL rL dR rR = true) :
    Alg.Agree .host (Alg.Scoped.Closed.meaning τ dL rL) (Alg.Scoped.Closed.meaning τ dR rR) ∧
      Alg.Agree .dual (Alg.Scoped.Closed.meaning τ dL rL) (Alg.Scoped.Closed.meaning τ dR rR) :=
  Alg.Scoped.compatPair_sound (S := jsonSyn) jsonLaws hι h

end Calculus.JSON
