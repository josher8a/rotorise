import Calculus.JSON.Basic
import Calculus.Lang.MeetV
import Calculus.Lang.MeetA
import Calculus.Lang.MeetWrites
import Calculus.Lang.MeetTyped
import Calculus.Lang.Occupancy

/-!
# The meet at JSON

The structural meet `Alg.Term.meet` and its theorems hold at every signature, and JSON supplies
only its leaf meet and the laws of the leaf meet and of the formers. Two kinds meet at the kind
where they are one kind, and at the bottom elsewhere. Every kind is inside the top, because the
top is the identity codec. A JSON predicate is a function, so the meet carries no predicate. JSON
has no set former, no list former and no map former in its signature, so a term of those formers
admits nothing, and each former law holds because both sides are empty.
-/

namespace Calculus.JSON

/-- **The leaf meet of JSON.** Two kinds meet where they are one kind. -/
instance jsonLeaf : Alg.Leaf jsonSyn where
  prim m m' := if m = m' then some m else none
  primTop _ := true
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

/-- **The shapes of JSON**: the kind, on both sides. JSON has no set, list or map former, so their
    shapes are never occupied by a written value, and any kind serves. -/
instance jsonOcc : Alg.Occ jsonSyn where
  ShV := JMember
  ShA := JMember
  decV := inferInstance
  decA := inferInstance
  allV := [.null, .bool, .num, .str, .arr, .obj]
  mem_allV m := by cases m <;> decide
  allA := [.null, .bool, .num, .str, .arr, .obj]
  mem_allA m := by cases m <;> decide
  primV m := occOnly m
  primA m := occOnly m
  setV _ := none
  setA _ := none
  listV := .arr
  listA := .arr
  mapV := .obj
  mapA := .obj

/-- The shape maps of JSON are the kind, and a kind writes and reads only values of that kind. -/
instance jsonOccSound : Alg.OccSound jsonSyn where
  shapeV := Json.member
  shapeA := Json.member
  prim_e m v h := by
    have h' := (Alg.PrimAdm.admV_exact (S := jsonSyn) m v).mpr h
    exact show occOnly m v.member = true by simpa [Alg.PrimAdm.admV, occOnly] using h'
  prim_p m a h := by
    have h' := (Alg.PrimAdmA.admA_exact (S := jsonSyn) m a).mpr h
    exact show occOnly m a.member = true by simpa [Alg.PrimAdmA.admA, occOnly] using h'
  set_e _ h := nomatch h
  set_p _ h := nomatch h
  list_e _ h := nomatch h
  list_p _ h := nomatch h
  map_e _ h := nomatch h
  map_p _ h := nomatch h

/-- The shape test is computable at JSON: a string and a number occupy different kinds. -/
theorem orth1_str_num : Alg.Orth1 (.prim .str : Alg.Term jsonSyn) (.prim .num) = true := by decide

/-- The formers of JSON, on the write side: every former term admits nothing. -/
instance jsonFormerAdm : Alg.FormerAdm jsonSyn where
  set_meet _ _ _ _ _ _ _ v := by simp [(adm_former_empty v).1]
  set_never _ _ _ v := by simp [(adm_former_empty v).1]

/-- The leaf meet of JSON is exact on the write side. -/
instance jsonLeafAdm : Alg.LeafAdm jsonSyn where
  prim_some m m' h hp v := by
    simp only [Alg.Leaf.prim] at hp
    split at hp
    · next he => cases hp; subst he; exact (Bool.and_self _).symm
    · exact nomatch hp
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
  prim_top _ _ _ _ := rfl
  pmeet_some _ _ _ h := nomatch h
  pmeet_none _ _ h := nomatch h

/-- The formers of JSON, on the read side: every former term reads nothing. -/
instance jsonFormerAdmA : Alg.FormerAdmA jsonSyn where
  set_meet _ _ _ _ _ _ _ := ⟨fun a => by simp [(admA_former_empty a).1],
    fun a ha _ => by simp [(admA_former_empty a).1] at ha⟩
  set_never _ _ _ a := by simp [(admA_former_empty a).1]

/-- The leaf meet of JSON is exact on the read side, and reads as each factor reads: a kind reads
    an attribute of that kind as itself, and so does the top. -/
instance jsonLeafAdmA : Alg.LeafAdmA jsonSyn where
  prim_some m m' h hp := by
    simp only [Alg.Leaf.prim] at hp
    split at hp
    · next he => cases hp; subst he; exact ⟨fun a => (Bool.and_self _).symm, fun a _ _ => ⟨rfl, rfl⟩⟩
    · exact nomatch hp
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
  prim_top m _ := ⟨fun a => by
      show Alg.AdmA (.prim m : Alg.Term jsonSyn) [] a
        = (Alg.AdmA (.prim m : Alg.Term jsonSyn) [] a && true)
      rw [Bool.and_true],
    fun a ha _ => by
      rw [admA_prim] at ha
      refine ⟨rfl, ?_⟩
      show gate m a = some a
      exact gate_eq_some.mpr ⟨of_decide_eq_true ha, rfl⟩⟩

/-- A kind meets only its own kind, so the met kind is each factor's member. -/
instance jsonLeafWrites : Alg.LeafWrites jsonSyn where
  prim_μ m m' h hp k hk := by
    simp only [Alg.Leaf.prim] at hp
    split at hp
    · next he =>
        cases hp; subst he
        exact ⟨fun _ h1 => Option.some.inj (h1.symm.trans hk),
          fun _ h1 => Option.some.inj (h1.symm.trans hk)⟩
    · exact nomatch hp

/-- The meet computes at JSON: two kinds meet at the bottom. -/
example : Alg.Term.meet (S := jsonSyn) Alg.pair0 (.prim .str) (.prim .num) = some .never := by rfl

/-- …and a union meets a kind at the kind. -/
example : Alg.Term.meet (S := jsonSyn) Alg.pair0 strOrNumTerm (.prim .str) = some (.prim .str) := by
  rfl

/-- **The meet at JSON admits exactly what both factors admit.** `Alg.Adm_meet` at `jsonSyn`. -/
theorem adm_meet (p : Alg.Pairing) (x y z : Alg.Term jsonSyn) (h : Alg.Term.meet p x y = some z)
    {ρ ρ' ρ'' : List jsonSyn.C} (hp : Alg.PairedV p ρ ρ' ρ'') (v : Json) :
    Alg.Adm z ρ'' v = (Alg.Adm x ρ v && Alg.Adm y ρ' v) :=
  Alg.Adm_meet p x y z h ρ ρ' ρ'' hp v

/-- **…reads exactly what both read, as each reads it.** `Alg.AdmA_meet_both` at `jsonSyn`. -/
theorem admA_meet_both (p : Alg.Pairing) (x y z : Alg.Term jsonSyn)
    (h : Alg.Term.meet p x y = some z) {ρ ρ' ρ'' : List jsonSyn.C} (hp : Alg.PairedA p ρ ρ' ρ'') :
    Alg.AdmAAt ρ ρ' ρ'' x y z :=
  Alg.AdmA_meet_both p x y z h ρ ρ' ρ'' hp

end Calculus.JSON
