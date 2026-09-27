import Calculus.JSON.Basic
import Calculus.Lang.DisjointA

/-!
# Disjointness at JSON

The structural test `Alg.Term.disjoint` and its soundness hold at every signature, and JSON
supplies only its leaves and the laws of the leaves and of the formers. Two kinds meet at the
kind where they are one kind, and at the bottom elsewhere. A JSON predicate is a function, so the
test compares no predicate. JSON has no set former, no list former and no map former in its
signature, so a term of those formers admits nothing, and each former law holds because both
sides are empty.
-/

namespace Calculus.JSON

/-- **The leaves of JSON.** Two kinds meet where they are one kind. -/
instance jsonLeaf : Alg.Leaf jsonSyn where
  prim m m' := if m = m' then some m else none
  isData _ := false
  pmeet _ _ := none

/-- A kind admits a value of that kind, on the write side. -/
theorem adm_prim (m : JMember) (v : Json) :
    Alg.Adm (.prim m : Alg.Term jsonSyn) [] v = decide (v.member = m) := by
  simp [Alg.Adm, Alg.PrimAdm.admV]

/-- …and on the read side. -/
theorem admA_prim (m : JMember) (a : Json) :
    Alg.AdmA (.prim m : Alg.Term jsonSyn) [] a = decide (a.member = m) := by
  simp [Alg.AdmA, Alg.PrimAdmA.admA]

/-- A term of a former that JSON lacks admits nothing: no set, no list, no object. -/
theorem adm_former_empty (v : Json) :
    (∀ t : Alg.Term jsonSyn, Alg.Adm (.set t) [] v = false) ∧
    (∀ pre sp suf, Alg.Adm (.list pre sp suf : Alg.Term jsonSyn) [] v = false) ∧
    (∀ b : Alg.Body jsonSyn, Alg.Adm (.object b) [] v = false) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun b => by cases b; rfl⟩

/-- …and reads nothing. -/
theorem admA_former_empty (a : Json) :
    (∀ t : Alg.Term jsonSyn, Alg.AdmA (.set t) [] a = false) ∧
    (∀ pre sp suf, Alg.AdmA (.list pre sp suf : Alg.Term jsonSyn) [] a = false) ∧
    (∀ b : Alg.Body jsonSyn, Alg.AdmA (.object b) [] a = false) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun b => by cases b; rfl⟩

/-- **The shape classes of JSON.** Every value and every attribute is a primitive, and JSON has
    no set, list or map former to land elsewhere. -/
instance jsonShapes : Alg.Shapes jsonSyn where
  former _ := .prim
  formerA _ := .prim
  prim _ _ _ := rfl
  primA _ _ _ := rfl
  set _ h := nomatch h
  setA _ h := nomatch h
  list _ h := nomatch h
  listA _ h := nomatch h
  map _ h := nomatch h
  mapA _ h := nomatch h

/-- The formers of JSON, on the write side: every former term admits nothing. -/
instance jsonFormerAdm : Alg.FormerAdm jsonSyn where
  set_never _ _ _ v := by simp [(adm_former_empty v).1]

/-- Two kinds that the leaf keeps apart share no value. -/
instance jsonLeafAdm : Alg.LeafAdm jsonSyn where
  prim_none m m' hp v := by
    simp only [Alg.Leaf.prim] at hp
    split at hp
    · exact nomatch hp
    · next hne =>
        rw [adm_prim, adm_prim]
        cases hv : decide (v.member = m) with
        | false => rfl
        | true =>
            have h1 : v.member = m := of_decide_eq_true hv
            exact decide_eq_false (fun h2 => hne (h1.symm.trans h2))
  pmeet_none _ _ h := nomatch h

/-- The formers of JSON, on the read side: every former term reads nothing. -/
instance jsonFormerAdmA : Alg.FormerAdmA jsonSyn where
  set_never _ _ _ a := by simp [(admA_former_empty a).1]

/-- …and read no attribute in common. -/
instance jsonLeafAdmA : Alg.LeafAdmA jsonSyn where
  prim_none m m' hp a := by
    simp only [Alg.Leaf.prim] at hp
    split at hp
    · exact nomatch hp
    · next hne =>
        rw [admA_prim, admA_prim]
        cases ha : decide (a.member = m) with
        | false => rfl
        | true =>
            have h1 : a.member = m := of_decide_eq_true ha
            exact decide_eq_false (fun h2 => hne (h1.symm.trans h2))

/-- The test computes at JSON: two kinds are disjoint. -/
example : Alg.Term.disjoint (S := jsonSyn) Alg.pair0 (.prim .str) (.prim .num) = true := by rfl

/-- …and a union that holds a kind is not disjoint from the kind. -/
example : Alg.Term.disjoint (S := jsonSyn) Alg.pair0 strOrNumTerm (.prim .str) = false := by rfl

/-- **Two terms that the test keeps apart at JSON are orthogonal.** `Alg.disjoint_orthogonal` at
    `jsonSyn`: no value has two writers, and no attribute has two readers. -/
theorem orthogonal (p : Alg.Pairing) (x y : Alg.Term jsonSyn)
    (h : Alg.Term.disjoint p x y = true) :
    (∀ ρ ρ', Alg.ApartV p ρ ρ' → ∀ v, (Alg.Adm x ρ v && Alg.Adm y ρ' v) = false) ∧
    (∀ ρ ρ', Alg.ApartA p ρ ρ' → ∀ a, (Alg.AdmA x ρ a && Alg.AdmA y ρ' a) = false) :=
  Alg.disjoint_orthogonal h

end Calculus.JSON
