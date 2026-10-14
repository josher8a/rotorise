import Calculus.JSON.Disjoint
import Calculus.Lang.ScopeDisjoint

/-!
# Disjointness of closed codecs at JSON

The scoped decision `Alg.Scoped.disjoint` and its soundness hold at every universe. JSON supplies
its leaf (`jsonLeaf`), its shape classes (`jsonShapes`), the laws of its top
(`id_topLaws`), and the laws that the decision reads (`jsonLaws`). Two kinds that the leaf keeps
apart share no datum. JSON has no set former, so the law of the set lift holds with no case.

An entry of a closed codec is its body at the fixed point (`meaning_node`). So an entry whose body
is a kind acts exactly at the data of the kind, and an entry whose body is a former that JSON lacks
acts nowhere.
-/

namespace Calculus.JSON

/-- **The laws that the decision reads hold at JSON**, at each orientation. -/
theorem jsonLaws (o : Alg.Orient) : Alg.Scoped.Laws jsonSyn o where
  prim m m' hp v := by
    simp only [Alg.Leaf.primsApart, Bool.not_eq_true', decide_eq_false_iff_not] at hp
    have e : ∀ m'' : JMember, ((Alg.Mean.ground (B := jsonSig) m'').f o v).isSome =
        decide (v.member = m'') := fun m'' => Alg.fiberCodec_isSome Json.member m'' o v
    rw [e, e]
    refine Bool.eq_false_iff.mpr fun h => ?_
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
    exact hp (h.1.symm.trans h.2)
  set _ hL := nomatch hL

/-- **An entry of a closed codec is its body**, at the fixed point. -/
theorem meaning_node (τ : (s : Bool) → Alg.TableAt jsonSig s) {N : Nat}
    (d : Alg.Scoped.Closed jsonSig N) (i : Fin N) {op : Alg.Scoped.TOp jsonSig}
    {b : op.Pos → Alg.Scoped.Graph jsonSig N} (hg : d.graph i = .node op b) :
    (Alg.Scoped.Closed.meaning τ d i).f = (Alg.Scoped.TOp.run τ op fun p =>
      Alg.Scoped.mng (S := jsonSyn) τ (Alg.Scoped.Closed.toG (S := jsonSyn) τ d) (b p)).f := by
  have h := Alg.Scoped.mng_leaf (Alg.Scoped.Closed.toG (S := jsonSyn) τ d) i
  change (Alg.Scoped.Closed.meaning τ d i).f =
    (Alg.Scoped.mng (S := jsonSyn) τ (Alg.Scoped.Closed.toG (S := jsonSyn) τ d) (d.graph i)).f at h
  rw [hg] at h
  exact h

/-- **An entry whose body is a kind acts exactly at the data of the kind**, at each orientation. -/
theorem closed_prim (τ : (s : Bool) → Alg.TableAt jsonSig s) {N : Nat}
    (d : Alg.Scoped.Closed jsonSig N) (i : Fin N) {m : JMember}
    {b : (Alg.Scoped.TOp.prim m : Alg.Scoped.TOp jsonSig).Pos → Alg.Scoped.Graph jsonSig N}
    (hg : d.graph i = .node (.prim m) b) (o : Alg.Orient) (v : Json) :
    ((Alg.Scoped.Closed.meaning τ d i).f o v).isSome = decide (v.member = m) := by
  rw [meaning_node τ d i hg]
  exact Alg.fiberCodec_isSome Json.member m o v

/-- **An entry whose body is a former that JSON lacks acts nowhere**: no set, no list, no object. -/
theorem closed_former_empty (τ : (s : Bool) → Alg.TableAt jsonSig s) {N : Nat}
    (d : Alg.Scoped.Closed jsonSig N) (i : Fin N) {op : Alg.Scoped.TOp jsonSig}
    {b : op.Pos → Alg.Scoped.Graph jsonSig N} (hg : d.graph i = .node op b)
    (hk : op.kind = .down) (o : Alg.Orient) (v : Json) :
    ((Alg.Scoped.Closed.meaning τ d i).f o v).isSome = false := by
  rw [meaning_node τ d i hg]
  match op, hk with
  | .set, _ => rfl
  | .list _ _ _, _ => rfl
  | .obj _ _ _, _ => rfl

/-- **Two closed codecs that the decision keeps apart at JSON share no datum.** -/
theorem closed_orthogonal {τ : (s : Bool) → Alg.TableAt jsonSig s} {NL NR : Nat}
    {dL : Alg.Scoped.Closed jsonSig NL} {dR : Alg.Scoped.Closed jsonSig NR} {rL : Fin NL}
    {rR : Fin NR} (h : Alg.Scoped.disjoint dL rL dR rR = true) (o : Alg.Orient) (v : Json) :
    (((Alg.Scoped.Closed.meaning τ dL rL).f o v).isSome &&
      ((Alg.Scoped.Closed.meaning τ dR rR).f o v).isSome) = false :=
  Alg.Scoped.disjoint_sound (S := jsonSyn) (jsonLaws o) h v

end Calculus.JSON
