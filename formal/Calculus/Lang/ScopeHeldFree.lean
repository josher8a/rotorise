import Calculus.Lang.ScopeDisjoint

/-!
# Held-free closed codecs are restrictions of the top, for every universe

An adapter reads its argument through caller code: a `held`, a `legacy`, or an object with a
`fill` slot. A closed codec is held-free at a root when the root reaches no adapter on the graph
(`Scoped.Closed.HF`). Each other operation over restrictions of the top is a restriction of the
top, so the meaning at a held-free root is a restriction of the top (`Scoped.Closed.meaning_sub`).
-/

namespace Calculus.Alg.Scoped

variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

/-- **A closed codec is held-free at a root** when the root reaches no adapter on the graph. The
    test is the definition, so a literal closed codec is shown held-free by `rfl`. -/
abbrev Closed.HF {N : Nat} (d : Closed B N) (root : Fin N) : Prop :=
  belowTop d.graph (.leaf root) = true

/-- **Confluence of a closed codec**: the meaning at a held-free root is a restriction of the top. -/
theorem Closed.meaning_sub [TopLaws ⟨B, .host⟩] {N : Nat} (d : Closed B N) {root : Fin N}
    (h : Closed.HF d root) : Sub (Closed.meaning τ d root) idCodec :=
  sub_of_belowTop (S := ⟨B, .host⟩) (Closed.toG (S := ⟨B, .host⟩) τ d) h

end Calculus.Alg.Scoped
