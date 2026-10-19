import Calculus.JSON.ScopeDisjoint
import Calculus.Lang.ScopeExact

/-!
# Exactness of disjointness at JSON

The witness laws hold at JSON. Two kinds that the leaf does not keep apart are one kind, and the
datum of the kind is a witness. JSON has no set former, so the law of the set lift holds with no
case.
-/

namespace Calculus.JSON

/-- One datum of each JSON member. -/
def jWit : JMember → Json
  | .null => .null
  | .bool => .bool true
  | .num => .num 0
  | .str => .str ""
  | .arr => .arr []
  | .obj => .obj []

/-- **The witness laws hold at JSON**, at each orientation and each set rule. -/
theorem jsonWLaws (o : Alg.Orient) (setOk : JMember → Bool) :
    Alg.Scoped.WLaws jsonSyn o setOk where
  prim m m' h := by
    simp only [Alg.Leaf.primsApart, Bool.not_eq_false', decide_eq_true_eq] at h
    subst h
    have e : ((Alg.Mean.ground (B := jsonSig) m).f o (jWit m)).isSome = true :=
      (Alg.fiberCodec_isSome Json.member m o (jWit m)).trans (by cases m <;> rfl)
    exact ⟨jWit m, e, e⟩
  set _ hL := nomatch hL

/-- **The decision is exact over the fragment at JSON.** JSON has no list, object or set former,
    so the fragment holds the primitives, the unions and the bottom. -/
theorem closed_exact {τ : (s : Bool) → Alg.TableAt jsonSig s} {NL NR : Nat}
    {dL : Alg.Scoped.Closed jsonSig NL} {dR : Alg.Scoped.Closed jsonSig NR} {rL : Fin NL}
    {rR : Fin NR}
    (hL : ∀ i, Alg.Scoped.Frag (S := jsonSyn) (fun _ => false) (dL.graph i) = true)
    (hR : ∀ j, Alg.Scoped.Frag (S := jsonSyn) (fun _ => false) (dR.graph j) = true)
    (o : Alg.Orient) :
    Alg.Scoped.disjoint dL rL dR rR = true ↔ ∀ v : Json,
      (((Alg.Scoped.Closed.meaning τ dL rL).f o v).isSome &&
        ((Alg.Scoped.Closed.meaning τ dR rR).f o v).isSome) = false :=
  Alg.Scoped.disjoint_exact (S := jsonSyn) (jsonLaws o) (jsonWLaws o _) hL hR

/-- **Inhabitation at JSON.** A closed codec whose entries are in the fragment accepts a datum
    exactly where `disjoint` answers `false` at the pair of the codec with itself. -/
theorem closed_inhabited_iff {τ : (s : Bool) → Alg.TableAt jsonSig s} {N : Nat}
    {d : Alg.Scoped.Closed jsonSig N} {r : Fin N}
    (h : ∀ i, Alg.Scoped.Frag (S := jsonSyn) (fun _ => false) (d.graph i) = true) (o : Alg.Orient) :
    (∃ v : Json, ((Alg.Scoped.Closed.meaning τ d r).f o v).isSome = true) ↔
      Alg.Scoped.disjoint d r d r = false :=
  Alg.Scoped.inhabited_iff (S := jsonSyn) (jsonLaws o) (jsonWLaws o _) h

end Calculus.JSON
