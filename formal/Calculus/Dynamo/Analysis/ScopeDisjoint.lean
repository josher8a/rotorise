import Calculus.Lang.ScopeDisjoint
import Calculus.Dynamo.Analysis.Disjoint
import Calculus.Dynamo.Analysis.ExactA
import Calculus.Dynamo.Lang.Scope
import Calculus.Dynamo.Lang.HeldFree

/-!
# Disjointness of closed codecs at DynamoDB

`Closed.disjoint` and `Closed.viewsDisjoint` are the scoped decision over the graph at DynamoDB.
The laws that the decision reads hold at each orientation (`dynLaws`), so the decision separates
no two meanings that share a datum (`Closed.disjoint_sound`), and the certificate separates no two
meanings that share a value or an attribute (`Closed.viewsDisjoint_sound`).
-/

namespace Calculus

open Alg in
/-- **The laws that the decision reads hold at DynamoDB**, at each orientation. -/
theorem dynLaws (o : Orient) : Alg.Scoped.Laws dynSyn o where
  prim g g' hp v := by
    have h := Adm_prim_apart (α := fun _ => (id, id)) g g' hp v
    have e : ∀ g'' : Ground, Adm (fun _ => (id, id)) (.prim g'') v =
        ((Mean.ground (B := dynSig) g'').f .host v).isSome := fun g'' =>
      Bool.eq_iff_iff.mpr (PrimAdm.admV_exact (S := dynSyn) g'' v)
    rw [e, e] at h
    clear e
    revert v
    refine Orient.both (P := fun o => ∀ v, (((Mean.ground (B := dynSig) g).f .host v).isSome &&
      ((Mean.ground (B := dynSig) g').f .host v).isSome) = false →
        (((Mean.ground (B := dynSig) g).f o v).isSome && ((Mean.ground (B := dynSig) g').f o v).isSome) = false)
      (fun _ h => h) (fun v h => ?_) o
    have h1 := congrFun (ground_selfdual g) v
    have h2 := congrFun (ground_selfdual g') v
    simp only [Codec.e, Codec.p] at h1 h2
    show (((groundCodec g).f .dual v).isSome && ((groundCodec g').f .dual v).isSome) = false
    rw [← h1, ← h2]; exact h
  set L hL c c' h v := by
    obtain rfl : dSet = L := Option.some.inj hL
    exact Bool.eq_false_iff.mpr fun hv => by
      rw [Bool.and_eq_true] at hv
      exact setCodec_apart (o := o) (fun w h1 h2 => by have := h w; rw [h1, h2] at this; exact nomatch this) v hv.1 hv.2

/-- **Whether two closed codecs share no value and no attribute**: the decision over the graphs. -/
def Closed.disjoint (x y : Closed) : Bool := Alg.Scoped.disjoint x.scopes x.root y.scopes y.root

/-- **Whether the two pairs of views of two closed codecs are disjoint.** -/
def Closed.viewsDisjoint (x y : Closed) : Bool :=
  Alg.Scoped.viewsDisjoint x.scopes x.root y.scopes y.root

/-- **The decision is sound**: two closed codecs that it separates share no datum at either
    orientation. -/
theorem Closed.disjoint_sound {x y : Closed} (h : x.disjoint y = true) (α : Table) (o : Alg.Orient)
    (v : Value) : (((x.meaning α).f o v).isSome && ((y.meaning α).f o v).isSome) = false :=
  Alg.Scoped.disjoint_sound (S := dynSyn) (dynLaws o) h v

/-- **The certificate is sound**: two closed codecs whose views it separates share no value at the
    host and no attribute at the dual. -/
theorem Closed.viewsDisjoint_sound {x y : Closed} (h : x.viewsDisjoint y = true) (α : Table) :
    (∀ v, (((x.meaning α).e v).isSome && ((y.meaning α).e v).isSome) = false) ∧
      ∀ a, (((x.meaning α).p a).isSome && ((y.meaning α).p a).isSome) = false := by
  simp only [Closed.viewsDisjoint, Alg.Scoped.viewsDisjoint, Bool.and_eq_true] at h
  exact ⟨fun v => Alg.Scoped.views_apart (S := dynSyn) (dynLaws .host) h.1 v,
    fun a => Alg.Scoped.views_apart (S := dynSyn) (dynLaws .dual) h.2 a⟩

end Calculus
